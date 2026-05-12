/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Binding.Basic
import Examples.MerkleCommitmentScheme.Support.QueryBound

/-!
# Merkle Commitment Scheme — Binding Query Bounds

This file is intentionally only about budgets. The binding probability proof
uses these lemmas to justify the numeric verifier terms:

* `bindingWitnessRest` logs two selected `checkSingle` paths, each costing
  `bindingVerifierPathQueryCount depth = depth + 1` random-oracle queries, so
  the rest cost is `bindingWitnessVerifierQueryCount depth = 2 * (depth + 1)`.
* `bindingWitnessInner` first runs the adversary for `t` queries and then the
  rest phase, so the ordinary witness game has budget
  `t + bindingWitnessVerifierQueryCount depth`.

The probability file decides how to charge those queries: either to the
conservative whole-cache birthday term or to the origin-aware textbook split.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- Operational normal form for the ordinary witness binding game.

It separates the adversary/commit phase from the selected-verifier rest phase,
which is the split used by the probability proof. -/
theorem bindingWitnessInner_eq_bind [DecidableEq C] {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    bindingWitnessInner (M := M) (S := S) (C := C) A =
      bindingWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun out =>
        bindingWitnessRest (M := M) (S := S) (C := C) out := by
  rfl

/-- The selected-verifier rest phase uses at most
`bindingWitnessVerifierQueryCount depth` queries.

If no mismatch witness is selected, it is pure and costs `0`. If a witness is
selected, the rest phase logs two `checkSingle` computations. Each path checks
one leaf query plus `depth` internal queries, so each costs `depth + 1`. -/
theorem bindingWitnessRest_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth) :
    IsTotalQueryBound
      (bindingWitnessRest (M := M) (S := S) (C := C) out)
      (bindingWitnessVerifierQueryCount depth) := by
  classical
  unfold bindingWitnessRest
  split
  · trivial
  · rename_i w heq
    let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
    let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
    let check₀ :=
      checkSingle (M := M) (S := S) (C := C)
        out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
    let check₁ :=
      checkSingle (M := M) (S := S) (C := C)
        out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
    have hcheck₀ :
        IsTotalQueryBound ((simulateQ loggingOracle check₀).run) (depth + 1) := by
      exact
        (isTotalQueryBound_run_simulateQ_loggingOracle_iff check₀ (depth + 1)).mpr
          (by
            dsimp [check₀]
            exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
              out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀))
    have hcheck₁ :
        IsTotalQueryBound ((simulateQ loggingOracle check₁).run) (depth + 1) := by
      exact
        (isTotalQueryBound_run_simulateQ_loggingOracle_iff check₁ (depth + 1)).mpr
          (by
            dsimp [check₁]
            exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
              out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁))
    have htwoRaw :
        IsTotalQueryBound
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))
          ((depth + 1) + ((depth + 1) + 0)) := by
      exact
        isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := (depth + 1) + 0)
          hcheck₀ fun _ =>
            isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 0) hcheck₁
              fun _ => trivial
    exact htwoRaw.mono (by
      simp [bindingWitnessVerifierQueryCount, bindingVerifierPathQueryCount]
      omega)

/-- The origin-aware textbook rest phase has the same query budget as the
ordinary rest phase.

It merely carries the post-adversary cache in the transcript; it does not add
any oracle queries beyond the two selected `checkSingle` logs. -/
theorem bindingTextbookWitnessRest_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (commitCache : QueryCache (Oracle M S C))
    (out : BindingOutput M S C depth) :
    IsTotalQueryBound
      (bindingTextbookWitnessRest (M := M) (S := S) (C := C) commitCache out)
      (bindingWitnessVerifierQueryCount depth) := by
  unfold bindingTextbookWitnessRest
  have hraw :
      IsTotalQueryBound
        (bindingWitnessRest (M := M) (S := S) (C := C) out >>= fun base =>
          pure
            ({ out := base.out
               commitCache := commitCache
               witness? := base.witness?
               single₀? := base.single₀?
               single₁? := base.single₁? } :
              BindingTextbookWitnessTranscript M S C depth))
        ((bindingWitnessVerifierQueryCount depth) + 0) := by
    exact isTotalQueryBound_bind (n₁ := bindingWitnessVerifierQueryCount depth) (n₂ := 0)
      (bindingWitnessRest_totalQueryBound (M := M) (S := S) (C := C) out)
      fun _ => trivial
  exact hraw.mono (by omega)

/-- The full ordinary witness inner computation costs
`t + bindingWitnessVerifierQueryCount depth` queries.

This is the budget used by the unconditional whole-cache fallback theorem
`binding_bound`, whose conservative birthday term charges adversary and
selected-verifier queries together. -/
theorem bindingWitnessInner_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    IsTotalQueryBound
      (bindingWitnessInner (M := M) (S := S) (C := C) A)
      (t + bindingWitnessVerifierQueryCount depth) := by
  rw [bindingWitnessInner_eq_bind (M := M) (S := S) (C := C) A]
  refine isTotalQueryBound_bind (n₁ := t) (n₂ := bindingWitnessVerifierQueryCount depth)
    A.queryBound ?_
  intro out
  exact bindingWitnessRest_totalQueryBound (M := M) (S := S) (C := C) out

end MerkleTree
