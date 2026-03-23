/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.EvalDist

/-!
# ROM Collision Resistance — Union Bound Approach

Following the SNARGs textbook (Thaler, Lemma rom-cr), we prove:

> For every t-query algorithm A, the probability that A's query trace contains
> a collision (two distinct inputs with the same output) is ≤ t(t-1)/(2·|C|).

## Proof (textbook, Section 4)

Let q₁,...,qₜ be the queries. For each pair (i,j) with i ≠ j, define
  E_{i,j} = "qᵢ ≠ qⱼ AND H(qᵢ) = H(qⱼ)".

Then:
- Pr[E_{i,j}] ≤ 1/|C| (if qᵢ = qⱼ then E doesn't hold; if qᵢ ≠ qⱼ then
  the outputs are independent uniform, so Pr[equal] = 1/|C|).
- Collision = ∃ (i,j) with i ≠ j such that E_{i,j}.
- Union bound: Pr[collision] ≤ ∑ Pr[E_{i,j}] ≤ C(t,2)/|C| = t(t-1)/(2|C|).

## Status

The per-pair bound `Pr[E_{i,j}] ≤ 1/|C|` and the union bound over pairs are
the two key steps. Both are stated; the per-pair bound requires showing that
`loggingOracle` outputs at distinct positions are independent uniform draws,
which is the core ROM property.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0,0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-! ## Collision Predicates -/

/-- A query log has a collision: two entries at distinct positions with
distinct inputs but HEq-equal outputs. -/
def LogHasCollision (log : QueryLog spec) : Prop :=
  ∃ (i j : Fin log.length), i ≠ j ∧
    log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2

/-- A cache has a collision: two distinct inputs map to the same output. -/
def CacheHasCollision (cache : QueryCache spec) : Prop :=
  ∃ (t₁ t₂ : spec.Domain) (u₁ : spec.Range t₁) (u₂ : spec.Range t₂),
    t₁ ≠ t₂ ∧ cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ HEq u₁ u₂

/-! ## Gauss Sum Arithmetic -/

/-- The Gauss sum `∑_{k=0}^{n-1} k/N ≤ n²/(2N)`, the arithmetic core of the birthday bound. -/
private lemma gauss_sum_inv_le (n : ℕ) (N : ℝ≥0∞) (_hN : 0 < N) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ ≤
      (n ^ 2 : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  -- Key inequality in ℕ: 2 * ∑_{k<n} k = n*(n-1) ≤ n^2
  have hnat : 2 * (∑ k ∈ range n, k) ≤ n ^ 2 := by
    have := Finset.sum_range_id_mul_two n; nlinarith [Nat.sub_le n 1]
  -- Lift to ENNReal
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num,
      show (n : ℝ≥0∞) ^ 2 = ((n ^ 2 : ℕ) : ℝ≥0∞) from by push_cast; ring,
      ← Nat.cast_mul]
    exact_mod_cast hnat
  -- From 2 * sum ≤ n^2, derive sum ≤ n^2 / 2
  have hle : (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
    rwa [mul_comm]
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      ≤ ((n : ℝ≥0∞) ^ 2 / 2) * N⁻¹ := mul_le_mul_left hle N⁻¹
    _ = (n : ℝ≥0∞) ^ 2 / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

/-! ## Total Query Bound -/

/-- A total query bound: the computation makes at most `n` queries total
(across all oracle indices). -/
def IsTotalQueryBound {α : Type} (oa : OracleComp spec α) (n : ℕ) : Prop :=
  IsQueryBound oa n (fun _ b => 0 < b) (fun _ b => b - 1)

lemma isTotalQueryBound_query_bind_iff {α : Type} {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound (liftM (query t) >>= mx) n ↔
      0 < n ∧ ∀ u, IsTotalQueryBound (mx u) (n - 1) := by
  simp [IsTotalQueryBound, IsQueryBound, OracleComp.construct_query_bind]

/-- Per-index bound implies total bound (sum over indices). -/
theorem IsTotalQueryBound.of_perIndex [Fintype ι] {α : Type}
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i, qb i) := by
  sorry -- Bridge from per-index to total via Finset.sum

/-! ## Per-Pair Collision Bound (Textbook Step 3)

For each pair (i,j) of positions in the log with distinct inputs,
Pr[outputs equal] ≤ 1/|C|. This is because in the evalDist model,
each query returns an independent uniform sample. -/

/-- **Per-pair collision bound**: For any two positions in a `loggingOracle` trace
with distinct inputs, the probability that their outputs are HEq-equal is ≤ 1/|C|.

This is the core ROM property: distinct oracle inputs yield independent uniform outputs.
In the `evalDist` model, each `query` call returns a fresh uniform sample. -/
theorem probEvent_pair_collision_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n)
    (i j : Fin n) (hij : i ≠ j) :
    Pr[fun z => z.2.length > i.val ∧ z.2.length > j.val ∧
        z.2[i]?.bind (fun ei => z.2[j]?.map (fun ej =>
          ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  sorry

/-! ## Union Bound Birthday (Textbook Steps 4-5)

Collision = ∃ pair with collision. Union bound over C(n,2) pairs gives n²/(2|C|). -/

/-- **Birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ n²/(2|C|).

Proof: express collision as ∃ pair (i,j), then union bound using
`probEvent_pair_collision_le` for each pair. -/
theorem probEvent_logCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Strategy: express LogHasCollision as ∃ (i,j) ∈ Fin n × Fin n with i < j,
  -- then apply union bound, bounding each pair by 1/|C|.
  -- Step 1: LogHasCollision z.2 implies there exist indices i < j < n
  -- (assuming the log length is ≤ n from the query bound)
  -- Step 2: Union bound over pairs
  -- Step 3: Each pair contributes ≤ 1/|C| by probEvent_pair_collision_le
  -- Step 4: Number of pairs × 1/|C| = gauss_sum_inv_le
  let C := Fintype.card (spec.Range default)
  -- Bound by union over pairs using probEvent_pair_collision_le
  calc Pr[fun z => LogHasCollision z.2 | (simulateQ loggingOracle oa).run]
      ≤ ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
          (C : ℝ≥0∞)⁻¹ := by
        sorry -- Union bound: LogHasCollision ⟹ ∃ pair, then bound each pair by 1/|C|
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * C) := by
        -- The sum of constant C⁻¹ over pairs = |pairs| * C⁻¹
        rw [Finset.sum_const, nsmul_eq_mul]
        -- Suffices to show |pairs| * C⁻¹ ≤ n²/(2C)
        -- |pairs| = n*(n-1)/2, and n*(n-1)/2 ≤ n²/2
        -- We use gauss_sum_inv_le: ∑ k < n, k * C⁻¹ ≤ n²/(2C)
        -- Note ∑ k < n, k = n*(n-1)/2 = |pairs|
        -- So it suffices to show |pairs| ≤ ∑ k < n, k ... actually they're equal!
        -- |{(i,j) : Fin n × Fin n | i < j}| = ∑_{j<n} j = n(n-1)/2
        have hcard_eq : ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card : ℝ≥0∞)
            = ∑ k ∈ range n, (k : ℝ≥0∞) := by
          -- |{(i,j) | i < j}| = ∑_{j<n} j = n*(n-1)/2
          -- |{(i,j) : Fin n × Fin n | i < j}| = ∑_{k<n} k
          -- Proved as a separate lemma for clarity.
          have hcard_nat : ∀ m : ℕ,
              (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card =
                ∑ k ∈ range m, k := by
            intro m; induction m with
            | zero => simp
            | succ k ih =>
              rw [Finset.sum_range_succ, ← ih]
              -- Split the set of pairs in Fin (k+1) into:
              -- (1) pairs (i,j) with both < k (embedded from Fin k), and
              -- (2) pairs (i, last k) for i < last k
              -- Count: |old pairs| + k
              have hsplit :
                  (Finset.univ.filter (fun p : Fin (k+1) × Fin (k+1) => p.1 < p.2)).card =
                  (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).card + k := by
                -- Define the embedding from Fin k pairs to Fin (k+1) pairs
                let emb : Fin k × Fin k ↪ Fin (k+1) × Fin (k+1) :=
                  ⟨fun p => (p.1.castSucc, p.2.castSucc), fun a b h => by
                    simp [Prod.ext_iff, Fin.castSucc_inj] at h; exact Prod.ext h.1 h.2⟩
                -- Define the embedding for new pairs (i, last k)
                let newEmb : Fin k ↪ Fin (k+1) × Fin (k+1) :=
                  ⟨fun i => (i.castSucc, Fin.last k), fun a b h => by
                    simp [Prod.ext_iff, Fin.castSucc_inj] at h; exact h⟩
                -- The filtered set splits as a disjoint union
                have hunion :
                    Finset.univ.filter (fun p : Fin (k+1) × Fin (k+1) => p.1 < p.2) =
                    (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb ∪
                    Finset.univ.map newEmb := by
                  ext ⟨i, j⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_union, Finset.mem_map, emb, newEmb,
                    Function.Embedding.coeFn_mk]
                  constructor
                  · intro hij
                    by_cases hj : j = Fin.last k
                    · subst hj; right
                      exact ⟨i.castPred (Fin.ne_last_of_lt hij), by
                        ext <;> simp [Fin.castSucc_castPred]⟩
                    · left
                      have hj' : j ≠ Fin.last k := hj
                      have hi' : i ≠ Fin.last k :=
                        Fin.ne_last_of_lt (lt_trans hij (lt_of_le_of_ne (Fin.le_last j) hj'))
                      refine ⟨(i.castPred hi', j.castPred hj'), ?_, ?_⟩
                      · exact Fin.castPred_lt_castPred hij hj'
                      · ext <;> simp [Fin.castSucc_castPred]
                  · intro hij
                    rcases hij with ⟨⟨a, b⟩, hab, heq₁⟩ | ⟨a, ha, heq₂⟩
                    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₁
                      exact Fin.castSucc_lt_castSucc_iff.mpr hab
                    · have h := Prod.mk.inj heq₂
                      rw [← h.1, ← h.2]
                      exact Fin.castSucc_lt_last a
                have hdisj : Disjoint
                    ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb)
                    (Finset.univ.map newEmb) := by
                  rw [Finset.disjoint_left]
                  intro ⟨x1, x2⟩ hx hy
                  rw [Finset.mem_map] at hx hy
                  obtain ⟨⟨_, b⟩, _, rfl⟩ := hx
                  obtain ⟨_, _, hc⟩ := hy
                  simp [emb, newEmb, Prod.ext_iff] at hc
                  exact absurd hc.2 (Fin.castSucc_ne_last b)
                rw [hunion, Finset.card_union_of_disjoint hdisj,
                  Finset.card_map, Finset.card_map, Finset.card_univ, Fintype.card_fin]
              omega
          have := hcard_nat n; push_cast [this]; rfl
        rw [hcard_eq, Finset.sum_mul]
        exact gauss_sum_inv_le n C (by exact_mod_cast hC)

/-- **Birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n²/(2|C|). -/
theorem probEvent_cacheCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n)
    (_hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Derive from log version: cache collision ⟹ log collision
  -- (caching only merges repeated inputs, which can't create new collisions)
  sorry

/-! ## Per-Index Bound Versions -/

/-- Birthday bound for `cachingOracle` with per-index query bound. -/
theorem probEvent_cacheCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal := IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  have h := probEvent_cacheCollision_le_birthday_total oa _ htotal hC
  simp only [Nat.cast_mul] at h; exact h

/-- Birthday bound for single-index oracle specs (typical ROM case: `t²/(2|C|)`). -/
theorem probEvent_cacheCollision_le_birthday' {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have h := probEvent_cacheCollision_le_birthday oa hbound hC
  simp only [Fintype.card_unique, Nat.cast_one, one_mul] at h
  exact h

/-! ## Unpredictability -/

section Unpredictability

variable {spec' : OracleSpec.{0,0} ι} [spec'.DecidableEq] [spec'.Fintype] [spec'.Inhabited]

omit [spec'.DecidableEq] in
/-- **Fresh query uniformity**: querying `cachingOracle` at an uncached point
yields each value with probability `1/|C|`. -/
theorem probOutput_fresh_cachingOracle_query
    (t : spec'.Domain) (u : spec'.Range t)
    (cache₀ : QueryCache spec') (hfresh : cache₀ t = none) :
    Pr[= (u, cache₀.cacheQuery t u) | (cachingOracle t).run cache₀] =
      (Fintype.card (spec'.Range t) : ℝ≥0∞)⁻¹ := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hfresh]
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.run_lift, bind_assoc,
    pure_bind]
  simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, StateT.run]
  rw [show (do let x ← PFunctor.FreeM.lift (query t); pure (x, cache₀.cacheQuery t x)) =
    (fun x => (x, cache₀.cacheQuery t x)) <$> PFunctor.FreeM.lift (query t) from by
      simp [Functor.map, bind_pure_comp]]
  rw [probOutput_map_injective _ (fun a b hab => by exact Prod.ext_iff.mp hab |>.1)]
  exact probOutput_query t u

omit [spec'.DecidableEq] in
/-- **Unpredictability bound**: `Pr[cache miss] * 1/|C| ≤ 1/|C|`. -/
theorem probEvent_unqueried_match_le {α : Type} {t : ℕ}
    (oa : OracleComp spec' α)
    (_hbound : IsPerIndexQueryBound oa (fun _ => t))
    (predict : spec'.Domain) (_target : spec'.Range predict) :
    Pr[fun z => z.2 predict = none |
      (simulateQ cachingOracle oa).run ∅] *
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ ≤
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := by
  calc Pr[fun z => z.2 predict = none | (simulateQ cachingOracle oa).run ∅] *
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ :=
        mul_le_mul' probEvent_le_one le_rfl
    _ = (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := one_mul _

end Unpredictability

/-! ## Collision-Based Win Bound -/

/-- If winning implies a cache collision, the win probability is bounded by the birthday bound. -/
theorem probEvent_collision_win_le {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (win : α × QueryCache spec → Prop)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default))
    (hwin : ∀ z ∈ support ((simulateQ cachingOracle oa).run ∅),
      win z → CacheHasCollision z.2) :
    Pr[win | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
  le_trans (probEvent_mono hwin) (probEvent_cacheCollision_le_birthday' oa hbound hC)

end OracleComp
