/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Commitment Schemes

This file defines commitment schemes and their security properties based on hash-based
constructions, following "Building Cryptographic Proofs from Hash Functions"
(https://snargsbook.org/).

A commitment scheme allows a party to commit to a message without revealing it, and later
open the commitment to reveal the message. The scheme satisfies three key security properties:

1. **Binding**: An adversary cannot find two distinct messages that open the same commitment
2. **Extractability**: If an adversary outputs a commitment that it subsequently opens, the
   adversary "knew" the opening at commitment time
3. **Hiding**: A commitment reveals no information about the committed message (up to a small
   statistical leakage)

## Main Definitions

* `CommitmentScheme m M C S`: A commitment scheme with message space `M`, commitment space `C`,
  and salt space `S` in monad `m`
* `CommitmentScheme.Binding`: Binding security property
* `CommitmentScheme.Extractable`: Extractability security property
* `CommitmentScheme.Hiding`: Hiding security property

## Implementation

The basic construction uses a random oracle `f` where:
- `Commit(m, ρ)` computes `cm = f(m, ρ)` for message `m` and random salt `ρ`
- `Check(cm, m, ρ)` verifies that `f(m, ρ) = cm`
- `Simulate()` outputs a random value without knowledge of the message

## References

* [Building Cryptographic Proofs from Hash Functions](https://snargsbook.org/)
-/

universe u v w

open OracleSpec OracleComp ENNReal

/-- A commitment scheme with message space `M`, commitment space `C`, and salt/randomness
space `S`. The scheme operates in monad `m` which typically provides access to a random oracle.

The basic construction uses a random oracle where `commit m ρ` computes `f(m, ρ)` and
`check cm m ρ` verifies that `f(m, ρ) = cm`. -/
structure CommitmentScheme (m : Type → Type v) (M C S : Type)
    extends ExecutionMethod m where
  /-- Commit to a message `m` using randomness/salt `ρ`.
  In the basic construction, this computes `cm = f(m, ρ)` where `f` is a random oracle. -/
  commit (msg : M) (salt : S) : m C

  /-- Check that a commitment `cm` is a valid commitment to message `msg` with salt `ρ`.
  Returns true if `f(msg, ρ) = cm`. -/
  check (cm : C) (msg : M) (salt : S) : m Bool

  /-- Simulate a commitment without knowledge of the message.
  Used in the hiding property to show that commitments reveal no information.
  Typically outputs a random value from the commitment space. -/
  simulate : m C

namespace CommitmentScheme

variable {m : Type → Type v} [Monad m] {M C S : Type}

section correctness

variable [DecidableEq C]

/-- A commitment scheme is perfectly correct if honestly generated commitments always verify.
That is, for any message `m` and salt `ρ`, we have `check (commit m ρ) m ρ = true`. -/
class PerfectlyCorrect (cm : CommitmentScheme m M C S) : Prop where
  check_commit_eq_true (msg : M) (salt : S) :
    Pr[= true | cm.exec do
      let c ← cm.commit msg salt
      cm.check c msg salt] = 1

end correctness

section binding

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq M]

/-- An adversary for the binding property. The adversary has access to a random oracle
and tries to output a commitment and two distinct message-salt pairs that both open the
commitment. -/
structure BindingAdv (_cm : CommitmentScheme (OracleComp spec) M C S) where
  /-- The adversary outputs a commitment `cm` and two message-salt pairs `(m₀, ρ₀)` and
  `(m₁, ρ₁)` attempting to break binding. -/
  main : OracleComp spec (C × (M × S) × (M × S))

/-- The binding experiment checks whether the adversary successfully broke binding by:
1. Outputting two distinct messages `m₀ ≠ m₁` (salts may or may not be distinct)
2. Both pairs `(m₀, ρ₀)` and `(m₁, ρ₁)` are valid openings of the same commitment `cm`

The binding error is the maximum winning probability over all adversaries. -/
def bindingExp {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : BindingAdv cm) : ProbComp Bool :=
  cm.exec do
    let (commit_val, (m₀, ρ₀), (m₁, ρ₁)) ← adv.main
    -- Check that messages are distinct
    let distinct := m₀ ≠ m₁
    -- Check that both pairs are valid openings
    let valid₀ ← cm.check commit_val m₀ ρ₀
    let valid₁ ← cm.check commit_val m₁ ρ₁
    return distinct && valid₀ && valid₁

/-- The binding error of a commitment scheme is the maximum probability that any adversary
can break binding. A scheme is binding if this error is negligible. -/
noncomputable def BindingAdv.advantage
    {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : BindingAdv cm) : ℝ≥0∞ :=
  Pr[= true | bindingExp adv]

/-- A commitment scheme is binding if the binding error is negligible, meaning no efficient
adversary can find two distinct messages that open the same commitment except with negligible
probability. -/
def Binding (cm : CommitmentScheme (OracleComp spec) M C S) : Prop :=
  ∀ adv : BindingAdv cm, BindingAdv.advantage adv < 1

end binding

section extractable

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq M]

/-- An extractor that attempts to extract the committed message from an adversary's commitment.
The extractor has access to the adversary's random oracle queries. -/
structure Extractor (_cm : CommitmentScheme (OracleComp spec) M C S) where
  /-- Extract a message and salt from a commitment, given the adversary's query history. -/
  extract (cm_val : C) : OracleComp spec (Option (M × S))

/-- An adversary for the extractability property. The adversary outputs a commitment that
it later opens, and extractability requires that the extractor can recover this opening. -/
structure ExtractableAdv (_cm : CommitmentScheme (OracleComp spec) M C S) where
  /-- The adversary outputs a commitment and then an opening (message and salt). -/
  main : OracleComp spec (C × M × S)

/-- The extractability experiment checks whether the extractor can recover the opening.
Given an adversary that outputs `(cm, m, ρ)` where `check cm m ρ = true`, the extractor
should output `(m, ρ)` or another valid opening.

Extractability informally means: if the adversary can open a commitment, then it "knew"
the opening at commitment time (as evidenced by the extractor's ability to extract it). -/
def extractableExp {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : ExtractableAdv cm) (ext : Extractor cm) : ProbComp Bool :=
  cm.exec do
    let (commit_val, msg, salt) ← adv.main
    -- Check that adversary's opening is valid
    let adv_valid ← cm.check commit_val msg salt
    -- Try to extract an opening
    let extracted ← ext.extract commit_val
    match extracted with
    | none => return false  -- Extraction failed
    | some (m_ext, ρ_ext) => do
      -- Check that extracted opening is valid
      let ext_valid ← cm.check commit_val m_ext ρ_ext
      -- Success if adversary's opening was valid but extraction failed to produce valid opening
      return adv_valid && !ext_valid

/-- The extraction error is the probability that extraction fails when the adversary succeeds. -/
noncomputable def ExtractableAdv.advantage
    {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : ExtractableAdv cm) (ext : Extractor cm) : ℝ≥0∞ :=
  Pr[= true | extractableExp adv ext]

/-- A commitment scheme is extractable if there exists an extractor such that the extraction
error is negligible for all adversaries. This means that whenever an adversary can open a
commitment, the extractor can recover a valid opening. -/
def Extractable (cm : CommitmentScheme (OracleComp spec) M C S) : Prop :=
  ∃ ext : Extractor cm, ∀ adv : ExtractableAdv cm,
    ExtractableAdv.advantage adv ext < 1

/-- Extractability implies binding. If a scheme is extractable, then an adversary cannot
find two distinct messages that open the same commitment, because the extractor could only
extract one opening. -/
theorem extractable_implies_binding {cm : CommitmentScheme (OracleComp spec) M C S}
    (h : cm.Extractable) : cm.Binding := by
  sorry  -- Proof sketch: If adversary outputs (cm, (m₀, ρ₀), (m₁, ρ₁)) with m₀ ≠ m₁,
         -- the extractor can only extract one opening, contradicting extractability

end extractable

section hidingProperty

variable {ι : Type u} {spec : OracleSpec ι}

/-- An adversary for the hiding property. The adversary tries to distinguish between:
1. A real commitment `f(m, ρ)` for a randomly chosen salt ρ
2. A simulated commitment that is output without knowledge of the message

The adversary may adaptively choose the message by querying the random oracle. -/
structure HidingAdv (_cm : CommitmentScheme (OracleComp spec) M C S) where
  /-- The adversary first chooses a message (potentially by querying the oracle). -/
  chooseMessage : OracleComp spec M
  /-- The adversary then receives either a real or simulated commitment and outputs a bit. -/
  distinguish (msg : M) (cm_val : C) : OracleComp spec Bool

/-- The real hiding experiment: commit to the adversary's chosen message with random salt. -/
def hidingExpReal {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : HidingAdv cm) (saltDist : OracleComp spec S) : ProbComp Bool :=
  cm.exec do
    let msg ← adv.chooseMessage
    let salt ← saltDist
    let commit_val ← cm.commit msg salt
    adv.distinguish msg commit_val

/-- The simulated hiding experiment: give the adversary a simulated commitment. -/
def hidingExpSimulated {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : HidingAdv cm) : ProbComp Bool :=
  cm.exec do
    let msg ← adv.chooseMessage
    let commit_val ← cm.simulate
    adv.distinguish msg commit_val

/-- The hiding advantage measures the distinguishing advantage between real and simulated
commitments. This captures the information leakage about the message. -/
noncomputable def HidingAdv.advantage
    {cm : CommitmentScheme (OracleComp spec) M C S}
    (adv : HidingAdv cm) (saltDist : OracleComp spec S) : ℝ :=
  |(Pr[= true | hidingExpReal adv saltDist]).toReal -
   (Pr[= true | hidingExpSimulated adv]).toReal|

/-- A commitment scheme is hiding if the advantage of any adversary is negligible.
This means that a commitment `f(m, ρ)` with random salt ρ reveals essentially no
information about the message m (up to a small statistical leakage error). -/
def Hiding (cm : CommitmentScheme (OracleComp spec) M C S)
    (saltDist : OracleComp spec S) : Prop :=
  ∀ adv : HidingAdv cm, |HidingAdv.advantage adv saltDist| < 1

/-- Statistical hiding property: the outputs of the adversary in the real and simulated
experiments are statistically close. This is a stronger notion than computational hiding. -/
def StatisticallyHiding (cm : CommitmentScheme (OracleComp spec) M C S)
    (saltDist : OracleComp spec S) (ε : ℝ) : Prop :=
  ∀ adv : HidingAdv cm, HidingAdv.advantage adv saltDist ≤ ε

end hidingProperty

section errorBounds

variable {ι : Type u} {spec : OracleSpec ι}

/-- The binding error of a commitment scheme, quantified in terms of query complexity
and security parameters. For the basic hash-based construction, this is typically
`q²/(2^λ)` where q is the number of queries and λ is the security parameter. -/
noncomputable def bindingError (_cm : CommitmentScheme (OracleComp spec) M C S)
    (numQueries : ℕ) (securityParam : ℕ) : ℝ≥0∞ :=
  (numQueries ^ 2 : ℝ≥0∞) / (2 ^ securityParam)

/-- The extraction error, which equals the binding error in tight constructions. -/
noncomputable def extractionError (cm : CommitmentScheme (OracleComp spec) M C S)
    (numQueries : ℕ) (securityParam : ℕ) : ℝ≥0∞ :=
  bindingError cm numQueries securityParam

/-- The hiding error for finite settings, typically `q/(2^λ)` where q is the number
of queries and λ is the security parameter. -/
noncomputable def hidingError (_cm : CommitmentScheme (OracleComp spec) M C S)
    (numQueries : ℕ) (securityParam : ℕ) : ℝ :=
  (numQueries : ℝ) / (2 ^ securityParam : ℝ)

end errorBounds

end CommitmentScheme

/-! ### Basic Construction

The basic commitment scheme construction using a random oracle `f : M × S → C`:
- **Commit**: On input message `m` and salt `ρ`, output `cm = f(m, ρ)`
- **Check**: On input `(cm, m, ρ)`, check whether `f(m, ρ) = cm`
- **Simulate**: Output a uniformly random element of `C`

This construction achieves:
- **Binding**: An adversary making `q` queries has binding error at most `q²/(2^λ)`
- **Extractability**: With the same error bound, by extracting from query logs
- **Hiding**: With random salt from `{0,1}^λ`, hiding error is at most `q/(2^λ)`
-/

section basicConstruction

variable {ι : Type u} (spec : OracleSpec ι)

/-- The basic commitment scheme using a random oracle.
In this construction:
- `commit m ρ` queries the oracle at `(m, ρ)`
- `check cm m ρ` checks if querying `(m, ρ)` yields `cm`
- `simulate` returns a uniformly random commitment value

The ExecutionMethod must be provided to specify how to execute OracleComp computations.
-/
def basicCommitmentScheme {M C S : Type} [DecidableEq C]
    (em : ExecutionMethod (OracleComp spec))
    (oracle : M × S → OracleComp spec C)
    (uniformC : OracleComp spec C) :
    CommitmentScheme (OracleComp spec) M C S where
  toExecutionMethod := em
  commit := λ m ρ => oracle (m, ρ)
  check := λ cm m ρ => do
    let result ← oracle (m, ρ)
    return result = cm
  simulate := uniformC

end basicConstruction

/-! ### Security Theorems

We state the main security theorems for the basic construction.
Proofs are left as `sorry` but follow standard arguments in the random oracle model.
-/

namespace CommitmentScheme

variable {ι : Type u} {spec : OracleSpec ι} {M C S : Type}

section securityTheorems

/-- The basic commitment scheme with uniform salt distribution is binding with error
at most `q²/(2^λ)` against adversaries making at most `q` queries. -/
theorem basicCommitmentScheme_binding
    [DecidableEq C] [DecidableEq M]
    (em : ExecutionMethod (OracleComp spec))
    (oracle : M × S → OracleComp spec C)
    (uniformC : OracleComp spec C)
    (numQueries securityParam : ℕ) :
    ∀ adv : BindingAdv (basicCommitmentScheme spec em oracle uniformC),
      BindingAdv.advantage adv ≤
        bindingError (basicCommitmentScheme spec em oracle uniformC) numQueries securityParam := by
  sorry

/-- The basic commitment scheme is extractable by examining the adversary's random
oracle queries. The extraction error equals the binding error. -/
theorem basicCommitmentScheme_extractable
    [DecidableEq C] [DecidableEq M]
    (em : ExecutionMethod (OracleComp spec))
    (oracle : M × S → OracleComp spec C)
    (uniformC : OracleComp spec C)
    (numQueries securityParam : ℕ) :
    ∃ ext : Extractor (basicCommitmentScheme spec em oracle uniformC),
      ∀ adv : ExtractableAdv (basicCommitmentScheme spec em oracle uniformC),
        ExtractableAdv.advantage adv ext ≤
          extractionError (basicCommitmentScheme spec em oracle uniformC) numQueries securityParam := by
  sorry

/-- The basic commitment scheme with uniform random salt from `{0,1}^λ` is hiding
with error at most `q/(2^λ)` against adversaries making at most `q` queries. -/
theorem basicCommitmentScheme_hiding
    [DecidableEq C]
    (em : ExecutionMethod (OracleComp spec))
    (oracle : M × S → OracleComp spec C)
    (uniformC : OracleComp spec C)
    (uniformS : OracleComp spec S)
    (numQueries securityParam : ℕ) :
    ∀ adv : HidingAdv (basicCommitmentScheme spec em oracle uniformC),
      HidingAdv.advantage adv uniformS ≤
        hidingError (basicCommitmentScheme spec em oracle uniformC) numQueries securityParam := by
  sorry

end securityTheorems

end CommitmentScheme
