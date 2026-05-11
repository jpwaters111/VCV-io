/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Binding.Basic
import Examples.MerkleCommitmentScheme.Support.QueryBound

/-!
# Merkle Commitment Scheme — Binding Query Bounds
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

theorem bindingWitnessInner_eq_bind [DecidableEq C] {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    bindingWitnessInner (M := M) (S := S) (C := C) A =
      bindingWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun out =>
        bindingWitnessRest (M := M) (S := S) (C := C) out := by
  rfl

theorem bindingWitnessRest_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth) :
    IsTotalQueryBound
      (bindingWitnessRest (M := M) (S := S) (C := C) out)
      (2 * (depth + 1)) := by
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
    exact htwoRaw.mono (by omega)

theorem bindingTextbookWitnessRest_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (commitCache : QueryCache (Oracle M S C))
    (out : BindingOutput M S C depth) :
    IsTotalQueryBound
      (bindingTextbookWitnessRest (M := M) (S := S) (C := C) commitCache out)
      (2 * (depth + 1)) := by
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
        ((2 * (depth + 1)) + 0) := by
    exact isTotalQueryBound_bind (n₁ := 2 * (depth + 1)) (n₂ := 0)
      (bindingWitnessRest_totalQueryBound (M := M) (S := S) (C := C) out)
      fun _ => trivial
  exact hraw.mono (by omega)

theorem bindingWitnessInner_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    IsTotalQueryBound
      (bindingWitnessInner (M := M) (S := S) (C := C) A)
      (t + 2 * (depth + 1)) := by
  rw [bindingWitnessInner_eq_bind (M := M) (S := S) (C := C) A]
  refine isTotalQueryBound_bind (n₁ := t) (n₂ := 2 * (depth + 1))
    A.queryBound ?_
  intro out
  exact bindingWitnessRest_totalQueryBound (M := M) (S := S) (C := C) out

end MerkleTree
