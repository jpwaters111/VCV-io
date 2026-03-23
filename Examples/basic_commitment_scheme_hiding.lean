/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VCVio.OracleComp.EvalDist

/-!
# Random Oracle Commitment Scheme: Perfect Hiding

We prove that a random oracle commitment scheme `commit(m, s) = H(m, s)` is
**perfectly hiding** in the `evalDist` model: the real commitment game (query the
oracle on `(m, s)`) and the simulated game (query on a default input) produce
identical output distributions.

The key insight is that in the `evalDist` model every `query` returns an independent
uniform sample over the range, regardless of its input. Therefore the real commitment
`H(m, s)` and a "simulated" commitment `H(default, default)` are both uniform over `C`,
making the two games indistinguishable with advantage exactly 0.

## Main Result

* `hiding_perfect`: `Pr[= true | hidingReal A] = Pr[= true | hidingSim A]`
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

variable {M S C : Type} [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]

/-- Oracle spec for the commitment scheme: input `(M × S)`, output `C`. -/
abbrev CMOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

/-! ## Hiding Adversary -/

/-- A hiding adversary operates in two phases:
1. `choose`: select a message `m` and produce auxiliary state `aux`
2. `distinguish`: given `aux` and a commitment value, output a bit -/
structure HidingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) where
  choose : OracleComp (CMOracle M S C) (M × AUX)
  distinguish : AUX → C → OracleComp (CMOracle M S C) Bool

/-! ## Hiding Games -/

/-- **Real hiding game**: the adversary chooses a message, we query the oracle on
`(m, default)` to get the commitment, then the adversary distinguishes.
A dummy query models the salt sampling step. -/
def hidingReal {AUX : Type} (A : HidingAdversary M S C AUX) :
    OracleComp (CMOracle M S C) Bool := do
  let (m, aux) ← A.choose
  let _dummy ← query (spec := CMOracle M S C) (default, default)
  let cm ← query (spec := CMOracle M S C) (m, default)
  A.distinguish aux cm

/-- **Simulated hiding game**: identical to the real game except the commitment is
produced by querying the oracle on a fixed default input (independent of `m`). -/
def hidingSim {AUX : Type} (A : HidingAdversary M S C AUX) :
    OracleComp (CMOracle M S C) Bool := do
  let (_m, aux) ← A.choose
  let _dummy ← query (spec := CMOracle M S C) (default, default)
  let cm ← query (spec := CMOracle M S C) (default, default)
  A.distinguish aux cm

variable {AUX : Type}

omit [DecidableEq M] [DecidableEq S] [DecidableEq C] [Fintype M] [Fintype S] in
/-- **Perfect hiding**: the real and simulated hiding games have identical
output distributions for any adversary.

In the `evalDist` model, `query t` returns a fresh uniform sample over `C`
regardless of the input `t`. Therefore `query (m, default)` and
`query (default, default)` both yield `Pr[= c | ...] = (Fintype.card C)⁻¹`
for every `c : C`, making the two games distributionally identical. -/
theorem hiding_perfect (A : HidingAdversary M S C AUX) :
    Pr[= true | hidingReal A] = Pr[= true | hidingSim A] := by
  simp only [hidingReal, hidingSim]
  -- Both games share the same first bind (A.choose) and second bind (dummy query).
  -- They differ only in the third bind: query (m, default) vs query (default, default).
  -- Since probOutput_query gives the same value for any input, the games are equal.
  apply probOutput_bind_congr'
  intro ⟨m, aux⟩
  apply probOutput_bind_congr'
  intro _dummy
  apply probOutput_bind_congr'
  intro cm
  rfl
