/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Random Oracle Commitment Scheme: Binding and Extractability

We model a commitment scheme where `commit(m, s) = H(m, s)` for a random oracle `H`.
We prove that both the binding and extractability games succeed with probability at most
`(Fintype.card C)⁻¹`, where `C` is the commitment space.

In the `evalDist` model each oracle query returns an independent uniform sample,
so any "fresh" verification query is independent of the adversary's prior computation.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

variable {M S C : Type} [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]

/-- Oracle spec for the commitment scheme: input `(M × S)`, output `C`. -/
abbrev CMOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

/-! ## Helper Lemmas -/

/-- Bounding `Pr[= y | mx >>= my]` when each inner probability is at most `r`. -/
lemma probOutput_bind_le {ι' : Type} {spec' : OracleSpec ι'}
    [spec'.Fintype] [spec'.Inhabited]
    {β γ : Type}
    {mx : OracleComp spec' β} {my : β → OracleComp spec' γ}
    {y : γ} {r : ℝ≥0∞}
    (h : ∀ x : β, Pr[= y | my x] ≤ r) :
    Pr[= y | mx >>= my] ≤ r := by
  rw [probOutput_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[= y | my x]
      ≤ ∑' x, Pr[= x | mx] * r :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = (∑' x, Pr[= x | mx]) * r := ENNReal.tsum_mul_right
    _ ≤ 1 * r := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = r := one_mul r

/-- A weighted sum where only one term can be nonzero is bounded by the weight. -/
private lemma tsum_query_weight_le (target : C)
    (f : C → ℝ≥0∞) (hf : ∀ c, c ≠ target → f c = 0)
    (hle : f target ≤ 1) :
    ∑' c : C, (↑(Fintype.card C))⁻¹ * f c ≤ (Fintype.card C : ℝ≥0∞)⁻¹ := by
  calc ∑' c : C, (↑(Fintype.card C))⁻¹ * f c
      ≤ ∑' c : C, if c = target then (↑(Fintype.card C))⁻¹ else 0 := by
        apply ENNReal.tsum_le_tsum; intro c
        by_cases hc : c = target
        · subst hc; rw [if_pos rfl]; exact mul_le_of_le_one_right (zero_le _) hle
        · simp [hf c hc]
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ := tsum_ite_eq target _

/-! ## Binding Game -/

/-- A binding adversary produces `(c, m₀, s₀, m₁, s₁)`. -/
structure BindingAdversary (M : Type) (S : Type) (C : Type) where
  run : OracleComp (CMOracle M S C) (C × M × S × M × S)

/-- The binding game: the adversary outputs `(c, m₀, s₀, m₁, s₁)`, then we
verify both openings via fresh oracle queries and check they collide on distinct inputs. -/
def bindingGame (A : BindingAdversary M S C) : OracleComp (CMOracle M S C) Bool := do
  let (c, m₀, s₀, m₁, s₁) ← A.run
  let c₀ ← query (spec := CMOracle M S C) (m₀, s₀)
  let c₁ ← query (spec := CMOracle M S C) (m₁, s₁)
  pure (c₀ == c && c₁ == c && decide ((m₀, s₀) ≠ (m₁, s₁)))

/-- **Binding theorem**: The probability that any adversary wins the binding game
is at most `(Fintype.card C)⁻¹`. -/
theorem binding_bound (A : BindingAdversary M S C) :
    Pr[= true | bindingGame A] ≤ (Fintype.card C : ℝ≥0∞)⁻¹ := by
  unfold bindingGame
  apply probOutput_bind_le
  intro ⟨c, m₀, s₀, m₁, s₁⟩
  apply probOutput_bind_le
  intro c₀
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_query, probOutput_pure, Bool.true_eq]
  apply tsum_query_weight_le c
  · intro c₁ hc₁
    have : (c₁ == c) = false := by simp [hc₁]
    simp [this]
  · split_ifs <;> simp

/-! ## Extractability Game -/

/-- An extractability adversary has a commit phase and an open phase. -/
structure ExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) where
  commit : OracleComp (CMOracle M S C) (C × AUX)
  open_ : AUX → OracleComp (CMOracle M S C) (M × S)

/-- Extract from a query log: find the first entry whose output matches `cm`. -/
def CMExtract (cm : C) (tr : QueryLog (CMOracle M S C)) : Option (M × S) :=
  match tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => some entry.1
  | none => none

/-- The extractability game: run commit with logging, open, verify via fresh query,
and check whether the extractor's output differs from the adversary's opening. -/
def extractabilityGame {AUX : Type} (A : ExtractAdversary M S C AUX) :
    OracleComp (CMOracle M S C) Bool := do
  let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
  let (m, τ) ← A.open_ aux
  let c ← query (spec := CMOracle M S C) (m, τ)
  let extracted := CMExtract cm tr
  pure (match extracted with
  | some (m', τ') => (c == cm && decide ((m', τ') ≠ (m, τ)))
  | none => (c == cm))

variable {AUX : Type}

/-- **Extractability theorem**: The probability that any adversary wins the
extractability game is at most `(Fintype.card C)⁻¹`. -/
theorem extractability_bound (A : ExtractAdversary M S C AUX) :
    Pr[= true | extractabilityGame A] ≤ (Fintype.card C : ℝ≥0∞)⁻¹ := by
  unfold extractabilityGame
  apply probOutput_bind_le
  intro ⟨⟨cm, aux⟩, tr⟩
  apply probOutput_bind_le
  intro ⟨m, τ⟩
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_query, probOutput_pure, Bool.true_eq]
  apply tsum_query_weight_le cm
  · intro c hc
    have hbeq : (c == cm) = false := by simp [hc]
    cases CMExtract cm tr <;> simp [hbeq]
  · split_ifs <;> simp
