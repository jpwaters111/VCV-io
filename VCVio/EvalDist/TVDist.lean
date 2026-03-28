/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.Probability.ProbabilityMassFunction.TotalVariation
import VCVio.EvalDist.Defs.Basic
import VCVio.EvalDist.Defs.NeverFails

/-!
# Total Variation Distance for SPMFs and Monadic Computations

This file extends the TV distance from `PMF` (defined in
`ToMathlib.ProbabilityTheory.TotalVariation`) to:

1. `SPMF.tvDist` — on sub-probability mass functions (via `toPMF`)
2. `tvDist` — on any monad with `HasEvalSPMF` (via `evalDist`)
-/

noncomputable section

open ENNReal

universe u v

/-! ### PMF tvDist convexity under a shared left bind -/

namespace PMF

section DataProcessing

universe w

variable {α' : Type w} {β : Type w}

private lemma etvDist_bind_left_le (p : PMF α') (f g : α' → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ ∑' a, p a * (f a).etvDist (g a) := by
  have hrhs :
      (∑' a, p a * (f a).etvDist (g a)) =
        (∑' a, p a * ∑' y, ENNReal.absDiff (f a y) (g a y)) / 2 := by
    calc
      (∑' a, p a * (f a).etvDist (g a))
        = ∑' a, (p a * ∑' y, ENNReal.absDiff (f a y) (g a y)) / 2 := by
            refine tsum_congr fun a => ?_
            rw [PMF.etvDist, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      _ = (∑' a, p a * ∑' y, ENNReal.absDiff (f a y) (g a y)) / 2 := by
            simpa [div_eq_mul_inv] using
              (ENNReal.tsum_mul_right
                (f := fun a => p a * ∑' y, ENNReal.absDiff (f a y) (g a y))
                (a := (2 : ℝ≥0∞)⁻¹))
  rw [PMF.etvDist, hrhs]
  apply ENNReal.div_le_div_right
  calc
    ∑' y, ENNReal.absDiff (∑' a, p a * f a y) (∑' a, p a * g a y)
      ≤ ∑' y, ∑' a, ENNReal.absDiff (p a * f a y) (p a * g a y) := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          exact ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' y, ∑' a, ENNReal.absDiff (f a y) (g a y) * p a := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          refine ENNReal.tsum_le_tsum fun a => ?_
          simpa [mul_comm] using ENNReal.absDiff_mul_right_le (f a y) (g a y) (p a)
    _ = ∑' a, ∑' y, ENNReal.absDiff (f a y) (g a y) * p a := by
          rw [ENNReal.tsum_comm]
    _ = ∑' a, p a * ∑' y, ENNReal.absDiff (f a y) (g a y) := by
          refine tsum_congr fun a => ?_
          rw [ENNReal.tsum_mul_right, mul_comm]

lemma tvDist_bind_left_le (p : PMF α') (f g : α' → PMF β) :
    (p.bind f).tvDist (p.bind g) ≤ ∑' a, (p a).toReal * (f a).tvDist (g a) := by
  have hfinite_sum : (∑' a, p a * (f a).etvDist (g a)) ≠ ∞ := by
    refine ne_top_of_le_ne_top one_ne_top ?_
    calc
      ∑' a, p a * (f a).etvDist (g a)
        ≤ ∑' a, p a * 1 := by
            refine ENNReal.tsum_le_tsum fun a => ?_
            exact mul_le_mul' le_rfl (PMF.etvDist_le_one _ _)
      _ = 1 := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
  rw [PMF.tvDist]
  refine le_trans
    (ENNReal.toReal_mono hfinite_sum (etvDist_bind_left_le p f g)) ?_
  rw [ENNReal.tsum_toReal_eq]
  · refine le_of_eq ?_
    refine tsum_congr fun a => ?_
    rw [ENNReal.toReal_mul, PMF.tvDist_def]
  · intro a
    exact ENNReal.mul_ne_top (by simp) (PMF.etvDist_ne_top _ _)

end DataProcessing

end PMF

/-! ### SPMF.tvDist -/

namespace SPMF

variable {α : Type*}

/-- Total variation distance on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def tvDist (p q : SPMF α) : ℝ := p.toPMF.tvDist q.toPMF

@[simp] lemma tvDist_self (p : SPMF α) : p.tvDist p = 0 := PMF.tvDist_self _
lemma tvDist_comm (p q : SPMF α) : p.tvDist q = q.tvDist p := PMF.tvDist_comm _ _
lemma tvDist_nonneg (p q : SPMF α) : 0 ≤ p.tvDist q := PMF.tvDist_nonneg _ _

lemma tvDist_triangle (p q r : SPMF α) :
    p.tvDist r ≤ p.tvDist q + q.tvDist r := PMF.tvDist_triangle _ _ _

lemma tvDist_le_one (p q : SPMF α) : p.tvDist q ≤ 1 := PMF.tvDist_le_one _ _

@[simp] lemma tvDist_eq_zero_iff {p q : SPMF α} : p.tvDist q = 0 ↔ p.toPMF = q.toPMF :=
  PMF.tvDist_eq_zero_iff

universe w in
lemma tvDist_map_le {α' : Type w} {β : Type w} (f : α' → β)
    (p q : SPMF α') : SPMF.tvDist (f <$> p) (f <$> q) ≤ SPMF.tvDist p q := by
  unfold SPMF.tvDist
  rw [SPMF.toPMF_map, SPMF.toPMF_map]
  exact PMF.tvDist_map_le (Option.map f) p.toPMF q.toPMF

universe w in
lemma tvDist_bind_right_le {α' : Type w} {β : Type w} (f : α' → SPMF β)
    (p q : SPMF α') : SPMF.tvDist (p >>= f) (q >>= f) ≤ SPMF.tvDist p q := by
  unfold SPMF.tvDist
  rw [SPMF.toPMF_bind, SPMF.toPMF_bind]
  exact PMF.tvDist_bind_right_le _ p.toPMF q.toPMF

end SPMF

/-! ### Monadic tvDist -/

section monadic

variable {m : Type u → Type v} [Monad m] [HasEvalSPMF m] {α : Type u}

/-- Total variation distance between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def tvDist (mx my : m α) : ℝ :=
  SPMF.tvDist (evalDist mx) (evalDist my)

@[simp] lemma tvDist_self (mx : m α) : tvDist mx mx = 0 := SPMF.tvDist_self _

lemma tvDist_comm (mx my : m α) : tvDist mx my = tvDist my mx :=
  SPMF.tvDist_comm _ _

lemma tvDist_nonneg (mx my : m α) : 0 ≤ tvDist mx my := SPMF.tvDist_nonneg _ _

lemma tvDist_triangle (mx my mz : m α) :
    tvDist mx mz ≤ tvDist mx my + tvDist my mz :=
  SPMF.tvDist_triangle _ _ _

lemma tvDist_le_one (mx my : m α) : tvDist mx my ≤ 1 := SPMF.tvDist_le_one _ _

lemma tvDist_map_le [LawfulMonad m] {β : Type u} (f : α → β) (mx my : m α) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my := by
  simp only [tvDist, evalDist_def, MonadHom.mmap_map]
  exact SPMF.tvDist_map_le f _ _

lemma tvDist_bind_right_le [LawfulMonad m] {β : Type u} (f : α → m β) (mx my : m α) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my := by
  simp only [tvDist, evalDist_def, MonadHom.mmap_bind]
  exact SPMF.tvDist_bind_right_le _ _ _

/-! ### TV distance bounds -/

lemma tvDist_le_probEvent_of_probOutput_eq_of_not
    {mx my : m α} [NeverFail mx] [NeverFail my]
    (p : α → Prop) [DecidablePred p]
    (h_eq : ∀ x, ¬p x → Pr[= x | mx] = Pr[= x | my])
    (h_event_eq : Pr[p | mx] = Pr[p | my]) :
    tvDist mx my ≤ Pr[p | mx].toReal := by
  rw [tvDist, SPMF.tvDist, PMF.tvDist]
  refine ENNReal.toReal_mono probEvent_ne_top ?_
  rw [PMF.etvDist, tsum_option _ ENNReal.summable]
  have hfailx : (evalDist mx).toPMF none = 0 := by
    rw [← SPMF.run_eq_toPMF (p := evalDist mx), ← probFailure_def (mx := mx)]
    exact probFailure_eq_zero (mx := mx)
  have hfaily : (evalDist my).toPMF none = 0 := by
    rw [← SPMF.run_eq_toPMF (p := evalDist my), ← probFailure_def (mx := my)]
    exact probFailure_eq_zero (mx := my)
  have hsum :
      (∑' x, ENNReal.absDiff ((evalDist mx).toPMF (some x)) ((evalDist my).toPMF (some x))) =
        ∑' x, ENNReal.absDiff (Pr[= x | mx]) (Pr[= x | my]) := by
    refine tsum_congr fun x => ?_
    simp [probOutput_def, SPMF.apply_eq_toPMF_some]
  rw [hfailx, hfaily, ENNReal.absDiff_self, zero_add]
  rw [hsum]
  calc
    (∑' x, ENNReal.absDiff (Pr[= x | mx]) (Pr[= x | my])) / 2
      ≤ (∑' x, if p x then (Pr[= x | mx] + Pr[= x | my]) else 0) / 2 := by
          exact ENNReal.div_le_div_right
            (ENNReal.tsum_le_tsum fun x => by
              by_cases hx : p x
              · simpa [hx] using ENNReal.absDiff_le_add (Pr[= x | mx]) (Pr[= x | my])
              · simp [hx, h_eq x hx, ENNReal.absDiff_self]) _
    _ = (Pr[p | mx] + Pr[p | my]) / 2 := by
        rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
        congr 1
        calc
          (∑' x, if p x then (Pr[= x | mx] + Pr[= x | my]) else 0)
              = (∑' x, ((if p x then Pr[= x | mx] else 0) +
                  (if p x then Pr[= x | my] else 0))) := by
                  refine tsum_congr fun x => ?_
                  by_cases hx : p x <;> simp [hx]
          _ = (∑' x, if p x then Pr[= x | mx] else 0) +
              (∑' x, if p x then Pr[= x | my] else 0) := by
                rw [ENNReal.tsum_add]
    _ = (Pr[p | mx] + Pr[p | mx]) / 2 := by
        rw [← h_event_eq]
    _ = Pr[p | mx] := by
        rw [← two_mul, mul_div_assoc]
        simp [ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top]

end monadic

section monadic_bind_left

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [HasEvalPMF m] {α β : Type u}

private lemma spmf_toPMF_bind_liftM_eq_map_some (p : PMF α) (f : α → PMF β) :
    (((liftM p : SPMF α) >>= fun a => liftM (f a)).toPMF) = Option.some <$> (p.bind f) := by
  ext o
  cases o with
  | none =>
      simp [SPMF.toPMF_bind, Option.elimM, Functor.map, PMF.bind_apply]
  | some b =>
      simp [SPMF.toPMF_bind, Option.elimM, Functor.map, PMF.bind_apply]

private lemma pmf_tvDist_map_some_eq (p q : PMF β) :
    PMF.tvDist (Option.some <$> p) (Option.some <$> q) = PMF.tvDist p q := by
  classical
  rw [PMF.tvDist_def, PMF.tvDist_def, PMF.etvDist, PMF.etvDist]
  have hp : (Option.some <$> p) none = 0 := by
    simp [Functor.map, PMF.bind_apply]
  have hq : (Option.some <$> q) none = 0 := by
    simp [Functor.map, PMF.bind_apply]
  congr 1
  rw [tsum_option _ ENNReal.summable, hp, hq, ENNReal.absDiff_self, zero_add]
  have hsome :
      (∑' x : β, ENNReal.absDiff ((Option.some <$> p) (some x)) ((Option.some <$> q) (some x))) =
        ∑' x : β, ENNReal.absDiff (p x) (q x) := by
    refine tsum_congr fun x : β => ?_
    simp [Functor.map, PMF.bind_apply]
  exact congrArg (fun z : ℝ≥0∞ => z / 2) hsome

private lemma spmf_tvDist_bind_left_le_liftM (p : PMF α) (f g : α → PMF β) :
    SPMF.tvDist
        ((liftM p : SPMF α) >>= fun a => liftM (f a))
        ((liftM p : SPMF α) >>= fun a => liftM (g a)) ≤
      ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
  rw [SPMF.tvDist, spmf_toPMF_bind_liftM_eq_map_some, spmf_toPMF_bind_liftM_eq_map_some,
    pmf_tvDist_map_some_eq]
  exact PMF.tvDist_bind_left_le p f g

omit [LawfulMonad m] in
private lemma tvDist_eq_pmf_tvDist (x y : m β) :
    tvDist x y = PMF.tvDist (HasEvalPMF.toPMF x) (HasEvalPMF.toPMF y) := by
  rw [tvDist, HasEvalPMF.evalDist_of_hasEvalPMF_def, HasEvalPMF.evalDist_of_hasEvalPMF_def,
    SPMF.tvDist, SPMF.toPMF_liftM, SPMF.toPMF_liftM]
  simpa [Functor.map] using
    (pmf_tvDist_map_some_eq (HasEvalPMF.toPMF x) (HasEvalPMF.toPMF y))

lemma tvDist_bind_left_le (mx : m α) (f g : α → m β) :
    tvDist (mx >>= f) (mx >>= g) ≤ ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a) := by
  rw [tvDist, evalDist_bind, evalDist_bind]
  simp_rw [HasEvalPMF.evalDist_of_hasEvalPMF_def]
  calc
    SPMF.tvDist
        ((liftM (HasEvalPMF.toPMF mx) : SPMF α) >>= fun a => liftM (HasEvalPMF.toPMF (f a)))
        ((liftM (HasEvalPMF.toPMF mx) : SPMF α) >>= fun a => liftM (HasEvalPMF.toPMF (g a)))
      ≤ ∑' a, (HasEvalPMF.toPMF mx a).toReal *
          PMF.tvDist (HasEvalPMF.toPMF (f a)) (HasEvalPMF.toPMF (g a)) := by
            exact spmf_tvDist_bind_left_le_liftM (HasEvalPMF.toPMF mx)
              (fun a => HasEvalPMF.toPMF (f a))
              (fun a => HasEvalPMF.toPMF (g a))
    _ = ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a) := by
          refine tsum_congr fun a => ?_
          have hprob : Pr[= a | mx] = HasEvalPMF.toPMF mx a := by
            simp [probOutput_def, HasEvalPMF.evalDist_of_hasEvalPMF_def]
          rw [hprob, ← tvDist_eq_pmf_tvDist (x := f a) (y := g a)]

end monadic_bind_left

section bool_tvdist

variable {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- For any `Bool` computation, the difference of `Pr[= true]` values is bounded by
TV distance. -/
lemma abs_probOutput_toReal_sub_le_tvDist
    (game₁ game₂ : m Bool) :
    |Pr[= true | game₁].toReal - Pr[= true | game₂].toReal| ≤ tvDist game₁ game₂ := by
  simp only [probOutput_def, SPMF.apply_eq_toPMF_some, tvDist, SPMF.tvDist, PMF.tvDist]
  have happ : ∀ (p : PMF (Option Bool)),
      ((fun x : Option Bool => if x = some true then some () else none) <$> p) (some ()) =
        p (some true) := fun p => by
    simp [PMF.map_apply_eq, tsum_fintype]
  rw [← ENNReal.absDiff_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  apply ENNReal.toReal_mono (PMF.etvDist_ne_top _ _)
  rw [← happ (evalDist game₁).toPMF, ← happ (evalDist game₂).toPMF,
      ← PMF.etvDist_option_punit]
  exact PMF.etvDist_map_le (fun x : Option Bool => if x = some true then some () else none)
    (evalDist game₁).toPMF (evalDist game₂).toPMF

end bool_tvdist

end
