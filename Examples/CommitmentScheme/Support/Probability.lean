/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, jpwaters
-/

import Examples.CommitmentScheme.Support.QueryBound

/-!
# Commitment Scheme local probability support

Small generic probability combinators used by commitment-scheme ROM proofs.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

universe u

namespace OracleComp

theorem probEvent_bind_le_of_forall_support
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {α β : Type u} {mx : m α} {my : α → m β}
    {E : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ E | my x] ≤ ε) :
    Pr[ E | mx >>= my] ≤ ε := by
  rw [probEvent_bind_eq_tsum]
  calc
    ∑' x, Pr[= x | mx] * Pr[ E | my x]
        ≤ ∑' x, Pr[= x | mx] * ε := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : x ∈ support mx
          · exact mul_le_mul' le_rfl (h x hx)
          · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx]) * ε := by
          rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ε := by
          exact mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = ε := by simp

theorem probEvent_bind_congr_hetero
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {α β γ : Type u}
    (mx : m α) (my : α → m β) (mz : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x, Pr[ p | my x] = Pr[ q | mz x]) :
    Pr[ p | mx >>= my] = Pr[ q | mx >>= mz] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  simp_rw [h]

theorem probEvent_bind_mono_hetero
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {α β γ : Type u}
    (mx : m α) (my : α → m β) (mz : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x, Pr[ p | my x] ≤ Pr[ q | mz x]) :
    Pr[ p | mx >>= my] ≤ Pr[ q | mx >>= mz] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by
    gcongr
    exact h x

theorem probEvent_bind_pure_congr_hetero
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {α β γ : Type u}
    (mx : m α) (f : α → β) (g : α → γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x, p (f x) ↔ q (g x)) :
    Pr[ p | mx >>= fun x => pure (f x)] =
      Pr[ q | mx >>= fun x => pure (g x)] := by
  classical
  apply probEvent_bind_congr_hetero
  intro x
  by_cases hp : p (f x)
  · rw [probEvent_pure, probEvent_pure]
    simp [hp, (h x).mp hp]
  · rw [probEvent_pure, probEvent_pure]
    simp [hp, mt (h x).mpr hp]

end OracleComp
