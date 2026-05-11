/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support
import Examples.MerkleCommitmentScheme.Collision
import Examples.CommitmentScheme.Support.Collision
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Merkle Commitment Scheme — Extractability Basic Definitions
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

structure OpeningData (M : Type) (S : Type) (C : Type) (depth : ℕ) where
  I : IndexSet depth
  message : Subvector M I
  proof : Proof S C I

/-- A two-phase Merkle extractability adversary with an overall query budget. -/
structure ExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth t : ℕ) where
  /-- Commit phase: outputs a commitment and auxiliary state. -/
  commit : OracleComp (Oracle M S C) (C × AUX)
  /-- Open phase: outputs the opened index set, messages, and Merkle proofs. -/
  open_ : AUX → OracleComp (Oracle M S C) (OpeningData M S C depth)
  /-- Commit-phase query budget. -/
  t₁ : ℕ
  /-- Open-phase query budget. -/
  t₂ : ℕ
  /-- Total adversarial budget. The selected verifier path is accounted for
  separately by `extractabilityErrorTerm`. -/
  totalBound : t₁ + t₂ ≤ t
  /-- Query-bound certificate for `commit`. -/
  commitBound : IsTotalQueryBound commit t₁
  /-- Query-bound certificate for `open_`. -/
  openBound : ∀ aux, IsTotalQueryBound (open_ aux) t₂

/-- The partial extractor state reconstructed from a commit trace. -/
def extractedStateOfTrace {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    ExtractedState M S C depth :=
  let labels := buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
    commitment trace
  let leaves := populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth) trace labels
  ⟨labels, leaves⟩

/-- The extractor output computed from a commit trace. -/
def extractedOutputOfTrace {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    Leaves M depth × Trapdoor S C depth :=
  extract (M := M) (S := S) (C := C) (depth := depth) commitment trace

/-- Transcript of the Merkle extractability experiment. -/
structure ExtractTranscript (M : Type) (S : Type) (C : Type) (AUX : Type) (depth : ℕ) where
  commitment : C
  aux : AUX
  commitTrace : QueryLog (Oracle M S C)
  opening : OpeningData M S C depth
  openTrace : QueryLog (Oracle M S C)

/-- The extractor output induced by the commit trace stored in a transcript. -/
def extractedOutputOfTranscript {depth : ℕ} [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) :
    Leaves M depth × Trapdoor S C depth :=
  extractedOutputOfTrace (M := M) (S := S) (C := C) (depth := depth)
    x.commitment x.commitTrace

def authPathMismatch [DecidableEq S] [DecidableEq C] {depth : ℕ}
    (p q : AuthPath S C depth) : Prop :=
  p.salt ≠ q.salt ∨ ∃ layer : Fin depth, p.siblings.get layer ≠ q.siblings.get layer

theorem not_authPathMismatch_of_eq [DecidableEq S] [DecidableEq C] {depth : ℕ}
    {p q : AuthPath S C depth} (h : p = q) :
    ¬ authPathMismatch (S := S) (C := C) p q := by
  rintro (hsalt | hsiblings)
  · exact hsalt (by simp [h])
  · rcases hsiblings with ⟨layer, hsiblings⟩
    exact hsiblings (by simp [h])

/-- A selected witness index for the extractor/opening mismatch. -/
def WitnessMismatch [DecidableEq S] [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) (i : {j // j ∈ x.opening.I}) : Prop :=
  (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get i.1 ≠
      x.opening.message i ∨
    authPathMismatch (S := S) (C := C)
      (openSingle (S := S) (C := C)
        (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 i.1)
      (x.opening.proof i)

/-- Deterministically select the first opened index where the extracted output
differs from the adversary opening. Message mismatches are tested before proof
mismatches at each index. -/
noncomputable def selectWitness? [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) :
    Option {i // i ∈ x.opening.I} :=
  by
    classical
    exact x.opening.I.attach.toList.find? fun i =>
      if (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get i.1 ≠
          x.opening.message i then
        true
      else if authPathMismatch (S := S) (C := C)
          (openSingle (S := S) (C := C)
            (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 i.1)
          (x.opening.proof i) then
        true
      else
        false

theorem selectWitness?_some {depth : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {x : ExtractTranscript M S C AUX depth} {i : {j // j ∈ x.opening.I}}
    (h : selectWitness? (M := M) (S := S) (C := C) x = some i) :
    WitnessMismatch (M := M) (S := S) (C := C) x i := by
  classical
  unfold selectWitness? at h
  have hpred := List.find?_some h
  by_cases hmsg :
      (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get i.1 ≠
        x.opening.message i
  · exact .inl hmsg
  · by_cases hproof :
        authPathMismatch (S := S) (C := C)
          (openSingle (S := S) (C := C)
            (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 i.1)
          (x.opening.proof i)
    · exact .inr hproof
    · simp [hmsg, hproof] at hpred

/-- The honest batch verifier computation induced by a transcript. -/
noncomputable def honestCheckComp [DecidableEq C] {depth : ℕ}
    (x : ExtractTranscript M S C AUX depth) :
    OracleComp (Oracle M S C) Bool :=
  check (M := M) (S := S) (C := C)
    x.commitment x.opening.I x.opening.message x.opening.proof

/-- The honest verifier's query-answer trace induced by a transcript. -/
noncomputable def honestTraceOfTranscript [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) :
    QueryLog (Oracle M S C) :=
  (logEval f (honestCheckComp (M := M) (S := S) (C := C) x)).2

/-- The honest verifier's acceptance bit induced by a transcript. -/
noncomputable def acceptedOfTranscript [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Bool :=
  (logEval f (honestCheckComp (M := M) (S := S) (C := C) x)).1

/-- Transcript for the witness-index extractability experiment. The verifier
log is present exactly when a mismatch witness was selected. -/
structure WitnessExtractTranscript (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth : ℕ) where
  base : ExtractTranscript M S C AUX depth
  witness? : Option {i // i ∈ base.opening.I}
  singleCheck? : Option (Bool × QueryLog (Oracle M S C))

/-- The inner two-phase extractability experiment prior to running under
`cachingOracle`. -/
noncomputable def extractabilityInner {depth t : ℕ} [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth) := do
  let ((commitment, aux), commitTrace) ← (simulateQ loggingOracle A.commit).run
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let _ ←
    (simulateQ loggingOracle
      (check (M := M) (S := S) (C := C)
        commitment opening.I opening.message opening.proof)).run
  pure
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }

/-- The witness-index extractability experiment before running under
`cachingOracle`. It runs only the selected single-leaf verifier path. -/
noncomputable def extractabilityWitnessInner {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (WitnessExtractTranscript M S C AUX depth) := do
  let ((commitment, aux), commitTrace) ← (simulateQ loggingOracle A.commit).run
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  match selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      pure { base := base, witness? := none, singleCheck? := none }
  | some i =>
      let single ←
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))).run
      pure { base := base, witness? := some i, singleCheck? := some single }

/-- The Merkle extractability game run with a shared cache. -/
noncomputable def extractabilityGame {depth t : ℕ} [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle (extractabilityInner (M := M) (S := S) (C := C) A)).run ∅

/-- The witness-index Merkle extractability game in the random-oracle model.

Lean event/game: this is the selected-witness version of the textbook
experiment. It logs the adversary commit phase, logs the adversary open phase,
selects one mismatching opened index if one exists, and logs only that
`checkSingle` verifier path. -/
noncomputable def extractabilityWitnessGame {depth t : ℕ}
    [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C)
      (WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle
    (extractabilityWitnessInner (M := M) (S := S) (C := C) A)).run ∅

/-- The fixed-oracle extractability failure event for the full batch.

Lean event/game: the honest batch verifier accepts, but the extractor output
restricted to the opened index set does not match the adversary opening.

Scope note: this predicate is used by the full-batch conditional combiner; the
final ROM bound is stated over the selected-witness variant below. -/
def ExtractabilityWin [DecidableEq C] {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Prop :=
  acceptedOfTranscript (M := M) (S := S) (C := C) f x = true ∧
    (Subvector.ofVector (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1 x.opening.I
        ≠ x.opening.message ∨
      «open» (S := S) (C := C)
          (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 x.opening.I
        ≠ x.opening.proof)

/-- The commit trace already contains a random-oracle collision. -/
def CommitCollisionEvent {depth : ℕ} (x : ExtractTranscript M S C AUX depth) : Prop :=
  LogHasCollision x.commitTrace

/-- The extractor's partial tree changes after processing the open-phase trace. -/
def ExtractorStateChangedEvent {depth : ℕ} [DecidableEq C]
    (x : ExtractTranscript M S C AUX depth) : Prop :=
  extractedStateOfTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment x.commitTrace ≠
    extractedStateOfTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment (x.commitTrace ++ x.openTrace)

/-- The honest verifier uses a query outside the commit trace while still
accepting. -/
def HonestTraceEscapeEvent [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Prop :=
  acceptedOfTranscript (M := M) (S := S) (C := C) f x = true ∧
    ¬ LogContains (honestTraceOfTranscript (M := M) (S := S) (C := C) f x) x.commitTrace

/-- The three bad events in the textbook single-commitment extractability proof.

Lean event/game: commit-trace collision, extractor-state change after the
open-phase trace, or an accepting honest verifier trace that is not contained
in the commit trace. -/
def BadEvent {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Prop :=
  CommitCollisionEvent (M := M) (S := S) (C := C) x ∨
    ExtractorStateChangedEvent (M := M) (S := S) (C := C) x ∨
    HonestTraceEscapeEvent (M := M) (S := S) (C := C) f x

/-- ROM extractability failure for the cached game output, interpreting the
final cache as a total fixed oracle on sampled points. -/
noncomputable def ExtractabilityWinROM [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (z : ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  ExtractabilityWin (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- Fixed-oracle success for the witness-index extractability experiment.

Lean event/game: a mismatch witness was selected and its single verifier path
accepts. This is the event bounded by the public selected-witness ROM theorem. -/
def WitnessExtractabilityWin [DecidableEq S] [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) : Prop :=
  ∃ i : {j // j ∈ x.base.opening.I},
    x.witness? = some i ∧
      WitnessMismatch (M := M) (S := S) (C := C) x.base i ∧
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.base.commitment i.1 (x.base.opening.message i) (x.base.opening.proof i)) = true

/-- ROM witness failure for the cached game output, using the final cache as a
total fixed oracle. -/
noncomputable def WitnessExtractabilityWinROM [DecidableEq S] [DecidableEq C]
    {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  WitnessExtractabilityWin (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- ROM bad event for the cached game output. -/
noncomputable def BadEventROM {depth : ℕ} [DecidableEq C]
    [Inhabited C]
    (z : ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  BadEvent (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- The selected single-check trace escapes the commit trace while accepting. -/
def WitnessTraceEscapeEvent [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) : Prop :=
  ∃ i : {j // j ∈ x.base.opening.I},
    x.witness? = some i ∧
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.base.commitment i.1 (x.base.opening.message i) (x.base.opening.proof i)) = true ∧
      ¬ LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.base.commitment i.1
            (x.base.opening.message i) (x.base.opening.proof i))).2
        x.base.commitTrace

/-- The fixed-oracle bad-event disjunction for the witness-index experiment.

Lean event/game: this is the same bad-event decomposition as `BadEvent`, but
the verifier escape branch is only the selected `checkSingle` trace. -/
def WitnessBadEvent {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) : Prop :=
  CommitCollisionEvent (M := M) (S := S) (C := C) x.base ∨
    ExtractorStateChangedEvent (M := M) (S := S) (C := C) x.base ∨
    WitnessTraceEscapeEvent (M := M) (S := S) (C := C) f x

/-- The ROM bad-event disjunction for the witness-index experiment. -/
noncomputable def WitnessBadEventROM {depth : ℕ} [DecidableEq C]
    [Inhabited C]
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  WitnessBadEvent (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- Number of known non-dummy labels used in the extractability fresh-hit bound.

The extractor can learn at most `2 * t₁ + 1` labels from a `t₁`-query commit
trace, and the full perfect tree has at most `2^(depth + 1)` labels.

Bound expression: `min (2 * t₁ + 1, 2^(depth + 1))`. This is the number of
known non-dummy labels that a fresh post-commit query can hit. Textbook
notation writes the full tree size as `2L`; here the perfect binary tree has
`L = 2^depth` leaves and `2^(depth + 1)` possible labels. -/
def extractabilityCountingTerm (depth t₁ : ℕ) : ℕ :=
  min (2 * t₁ + 1) (2 ^ (depth + 1))

/-- Commit-trace birthday summand in the selected-witness Merkle
extractability bound. -/
noncomputable def extractabilityBirthdayTerm (C : Type) [Fintype C]
    (t₁ : ℕ) : ℝ≥0∞ :=
  ((t₁ ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)

/-- Post-commit fresh-hit summand in the selected-witness Merkle
extractability bound.

The first factor is the post-commit query budget: adversary open phase plus one
selected verifier path. The second factor is the number of known labels that a
fresh query could hit. -/
noncomputable def extractabilityFreshHitTerm (C : Type) [Fintype C]
    (depth t₁ t₂ : ℕ) : ℝ≥0∞ :=
  (((t₂ + depth + 1) * extractabilityCountingTerm depth t₁ : ℕ) : ℝ≥0∞) *
    (Fintype.card C : ℝ≥0∞)⁻¹

/-- Selected-witness single-commitment extractability error expression.

Textbook statement: this is the ROM bad-event decomposition for the
selected-witness single-commitment experiment.

Lean event/game: `extractabilityWitnessGame` and `WitnessBadEventROM`.

Bound expression, with `d = depth` and `|C| = 2^λ`:

* commit-trace birthday term: `t₁^2 / (2 * |C|)`;
* fresh-hit term:
  `(t₂ + d + 1) * min (2 * t₁ + 1, 2^(d + 1)) / |C|`.

The textbook full-batch macro is
`MTExtractabilityExpression(λ, q, L, d) =
  1/2 * (q - 1) * q / 2^λ + (d + 1) * 2L / 2^λ`.

Scope note: `depth + 1` is one selected verifier path, not a full batch
verifier cost.
-/
noncomputable def extractabilityErrorTerm (C : Type) [Fintype C]
    (depth t₁ t₂ : ℕ) : ℝ≥0∞ :=
  extractabilityBirthdayTerm C t₁ + extractabilityFreshHitTerm C depth t₁ t₂

@[simp] theorem extractabilityGame_eq {depth t : ℕ} [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityGame (M := M) (S := S) (C := C) A =
      (simulateQ cachingOracle (extractabilityInner (M := M) (S := S) (C := C) A)).run ∅ := rfl

@[simp] theorem extractabilityWitnessGame_eq {depth t : ℕ}
    [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityWitnessGame (M := M) (S := S) (C := C) A =
      (simulateQ cachingOracle
        (extractabilityWitnessInner (M := M) (S := S) (C := C) A)).run ∅ := rfl

end MerkleTree
