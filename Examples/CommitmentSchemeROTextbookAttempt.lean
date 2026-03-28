/-
Copyright (c) 2026 JPWaters111. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JPWaters111
-/
import Examples.CommitmentSchemeRO

/-!
# Random Oracle Commitment Scheme: Textbook Hiding Attempt

This file records a textbook-style attempt for the remaining hiding bad-mass
bound in [`Examples.CommitmentSchemeRO`](Examples/CommitmentSchemeRO.lean).

The main file currently proves a substantial amount of infrastructure for the
random oracle commitment scheme, but still leaves the final theorem
`sum_probEvent_hidingBad_le` with one `sorry`.

This module now serves as the external endpoint for the remaining hiding
bad-mass theorem while the detailed proof infrastructure remains in
[`Examples.CommitmentSchemeRO`](Examples/CommitmentSchemeRO.lean).

It also records the intended textbook route:

1. Rewrite the bad-mass sum using the existing averaged bridge
   `sum_probEvent_hidingBad_eq_avg_bad_mass`.
2. Bound the averaged bad event by the averaged selected-count-pred quantity.
3. Show that the scaled selected-count-pred quantity is at most `t`.
4. Conclude the original bad-mass bound.

The detailed diagonal/counting proof still belongs in
`Examples.CommitmentSchemeRO`. This file does not duplicate that internal
infrastructure.

## Missing Internal Bridge

The intended internal theorem in `Examples.CommitmentSchemeRO` is:

```lean
private lemma sum_wp_challenge_then_distinguish_countPred_le_t_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose :
      qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (qchoose.1.1, s)).run qchoose.2)
        (fun qch =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z => (z.2.2 s - 1 : ℝ≥0∞)))) ≤
      t
```

Once that theorem exists in the main file, the textbook route documented below
can replace the direct call to the main theorem.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]

instance : DecidableEq (M × S) := instDecidableEqProd

/-- Textbook-style outer bad-mass bound.

This theorem is the public endpoint for the bad-mass bound while the detailed
proof remains in `Examples.CommitmentSchemeRO`. The comments below record the
textbook route that should eventually justify this theorem directly. -/
theorem textbook_sum_probEvent_hidingBad_le_attempt {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) ≤ t := by
  /-
  Intended next steps, all in `Examples.CommitmentSchemeRO`:

  1. Apply the public averaged bridge:
       `sum_probEvent_hidingBad_eq_avg_bad_mass`

  2. Apply the internal averaged bad-event bound to selected-count-pred:
       `probEvent_hidingAvg_bad_le_wp_selectedCountPred`

  3. Rewrite the scaled averaged selected-count-pred quantity into the per-salt
     sum of count-pred expectations:
       `card_mul_wp_hidingAvg_selectedCountPred_eq_sum_wp_countPred`

  4. Prove the missing internal theorem:
       `sum_wp_challenge_then_distinguish_countPred_le_t_of_choose_support`

  5. Deduce the outer count-pred bound:
       `sum_wp_countPred_le_t`

  6. Chain those facts to recover `sum_probEvent_hidingBad_le`.
  -/
  simpa using sum_probEvent_hidingBad_le (M := M) (S := S) (C := C) A
