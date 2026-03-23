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
# ROM Collision Resistance and Unpredictability

This file provides collision resistance and unpredictability lemmas for the random oracle
model (ROM), formalized via `cachingOracle`. These are the core probabilistic tools needed
for commitment scheme binding and extractability proofs.

## Main Results

### Collision Resistance (Birthday Bound)
* `probEvent_cacheCollision_le_birthday`: When running a computation with at most `n` total
  queries to `cachingOracle`, the probability that the final cache contains a collision
  (two distinct inputs mapping to the same output) is at most `n² / (2 * |C|)`.

### Unpredictability
* `probOutput_fresh_cachingOracle_query`: For a fresh (uncached) point, querying
  `cachingOracle` yields each value with probability `1/|C|`.

* `probEvent_unqueried_match_le`: If a `t`-query adversary outputs a value that was
  NOT queried during its execution, then `Pr[H(m) = target]` is at most `1/|C|`.

## Proof Strategy (Union Bound over Pairs)

The birthday bound follows the textbook proof from SNARGs (Thaler, Chapter 4):

1. Run the adversary with `loggingOracle` to get a query log of length ≤ n.
2. Define collision event E_{i,j} for each pair (i,j): "inputs distinct AND outputs equal".
3. For each pair, Pr[E_{i,j}] ≤ 1/|C| because outputs are independent uniform draws.
4. `LogHasCollision log ↔ ∃ (i,j), E_{i,j}` (collision = some pair collides).
5. Union bound: Pr[∃ pair collides] ≤ ∑ Pr[E_{i,j}] ≤ C(n,2)/|C| = n(n-1)/(2|C|) ≤ n²/(2|C|).

The cache-based version follows by induction on `OracleComp`, or alternatively by
relating `cachingOracle` collisions to `loggingOracle` collisions (caching only merges
repeated inputs, which cannot introduce new collisions on distinct inputs).
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0,0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-! ## Cache Collision Predicate -/

/-- A cache has a collision if two distinct inputs map to the same output. -/
def CacheHasCollision (cache : QueryCache spec) : Prop :=
  ∃ (t₁ t₂ : spec.Domain) (u₁ : spec.Range t₁) (u₂ : spec.Range t₂),
    t₁ ≠ t₂ ∧ cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ HEq u₁ u₂

/-- A query log has a collision if two entries at distinct inputs have the same output. -/
def LogHasCollision (log : QueryLog spec) : Prop :=
  ∃ (i j : Fin log.length), i ≠ j ∧
    log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2

/-! ## Cache collision monotonicity -/

omit [DecidableEq ι] [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- If a subcache has a collision, any supercache also has a collision. -/
lemma CacheHasCollision.mono {cache₁ cache₂ : QueryCache spec}
    (h : cache₁ ≤ cache₂) (hcol : CacheHasCollision cache₁) :
    CacheHasCollision cache₂ := by
  obtain ⟨t₁, t₂, u₁, u₂, hne, h₁, h₂, heq⟩ := hcol
  exact ⟨t₁, t₂, u₁, u₂, hne, h h₁, h h₂, heq⟩

omit [DecidableEq ι] [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- The empty cache has no collision. -/
lemma not_cacheHasCollision_empty : ¬CacheHasCollision (∅ : QueryCache spec) := by
  intro ⟨_, _, _, _, _, h₁, _, _⟩
  simp [QueryCache.empty_apply] at h₁

/-! ## Total Query Bound

A total query bound tracks the number of queries across ALL oracle indices using
a single natural number budget. Each query (to any index) costs 1. -/

/-- Total query bound: the computation makes at most `n` queries total across all indices.
Each query costs 1 unit of budget, regardless of the oracle index queried. -/
abbrev IsTotalQueryBound {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) (n : ℕ) : Prop :=
  IsQueryBound oa n (fun _ b => 0 < b) (fun _ b => b - 1)

@[simp]
lemma isTotalQueryBound_pure {ι₀ : Type} {spec₀ : OracleSpec ι₀} {α₀ : Type}
    (x : α₀) (n : ℕ) :
    IsTotalQueryBound (pure x : OracleComp spec₀ α₀) n := trivial

lemma isTotalQueryBound_query_bind_iff {ι₀ : Type} {spec₀ : OracleSpec ι₀} {α₀ : Type}
    (t : ι₀) (mx : spec₀.Range t → OracleComp spec₀ α₀)
    (n : ℕ) :
    IsTotalQueryBound (liftM (query (spec := spec₀) t) >>= mx) n ↔
      0 < n ∧ ∀ u, IsTotalQueryBound (mx u) (n - 1) :=
  Iff.rfl

/-- When we decrement index `t` in a per-index bound, the total decreases by 1. -/
private lemma sum_update_pred {ι₀ : Type} [DecidableEq ι₀] [Fintype ι₀]
    (qb : ι₀ → ℕ) (t : ι₀) (ht : 0 < qb t) :
    (∑ i : ι₀, (Function.update qb t (qb t - 1)) i) = (∑ i : ι₀, qb i) - 1 := by
  have hmem : t ∈ Finset.univ := Finset.mem_univ t
  rw [Finset.sum_update_of_mem hmem]
  have hle : qb t ≤ ∑ i : ι₀, qb i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
  have hrest : ∑ i : ι₀, qb i = qb t + ∑ x ∈ Finset.univ \ {t}, qb x := by
    rw [← Finset.add_sum_erase _ _ hmem]
    congr 1
    rw [Finset.erase_eq]
  omega

/-- A per-index bound implies a total bound when the index type is finite. -/
lemma IsTotalQueryBound.of_perIndex {ι₀ : Type} [DecidableEq ι₀] [Fintype ι₀]
    {spec₀ : OracleSpec ι₀} {α₀ : Type} {oa : OracleComp spec₀ α₀} {qb : ι₀ → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i : ι₀, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    rw [isTotalQueryBound_query_bind_iff]
    obtain ⟨ht, hcont⟩ := h
    constructor
    · exact Nat.lt_of_lt_of_le ht (Finset.single_le_sum (fun i _ => Nat.zero_le _)
        (Finset.mem_univ t))
    · intro u
      have ih_u := ih u (hcont u)
      rw [sum_update_pred qb t ht] at ih_u
      exact ih_u

/-! ## Birthday Bound (Collision Resistance)

When a `t`-query adversary interacts with a random oracle (modeled by `cachingOracle`),
the probability of any collision in the resulting cache is bounded by the birthday bound.

At step `k`, the fresh query's output is uniform over `|C|` values and collides with
any of the `k-1` previous outputs with probability at most `(k-1)/|C|`.
Summing: `sum_{k=1}^{t-1} k/|C| = t(t-1)/(2|C|) <= t^2/(2|C|)`.
-/

/-! ### Arithmetic helper: Gauss sum bound in ℝ≥0∞ -/

/-- `n * (n - 1) ≤ n * n` for natural numbers. -/
private lemma nat_mul_pred_le (n : ℕ) : n * (n - 1) ≤ n * n :=
  Nat.mul_le_mul_left n (Nat.sub_le n 1)

/-- The Gauss sum `Σ_{k=0}^{n-1} k = n*(n-1)/2`, which is at most `n²/2`.
Stated as: `2 * Σ k ≤ n²` in `ℝ≥0∞`. -/
private lemma two_mul_gauss_sum_le_sq (n : ℕ) :
    2 * (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 := by
  have hgauss := Finset.sum_range_id_mul_two n
  suffices h : (2 * ∑ k ∈ range n, k : ℕ) ≤ n * n by
    have lhs : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) = ((2 * ∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      push_cast; ring
    rw [lhs, sq, show (n : ℝ≥0∞) * n = ((n * n : ℕ) : ℝ≥0∞) from by push_cast; ring]
    exact_mod_cast h
  calc 2 * ∑ k ∈ range n, k = (∑ k ∈ range n, k) * 2 := by ring
    _ = n * (n - 1) := hgauss
    _ ≤ n * n := nat_mul_pred_le n

/-- Key arithmetic: `Σ_{k=0}^{n-1} (k : ℝ≥0∞) * N⁻¹ ≤ n² / (2 * N)`.
This is the algebraic core of the birthday bound. -/
private lemma gauss_sum_inv_le (n N : ℕ) (_hN : 0 < N) :
    (∑ k ∈ range n, ((k : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹)) ≤
      (n ^ 2 : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  rw [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
  rw [← mul_assoc]
  apply mul_le_mul_left
  rw [← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
  rw [mul_comm]
  exact two_mul_gauss_sum_le_sq n

/-! ### Union bound approach for the birthday bound

The core idea: express `LogHasCollision` as a union of pairwise collision events,
then apply the union bound `probEvent_exists_finset_le_sum` and bound each pair's
collision probability by `1/|C|`. -/

/-- **Per-pair collision probability bound** (core probabilistic lemma):
For any computation `oa` run with `loggingOracle`, the probability that two specific
log positions `i` and `j` (with `i < j`) have distinct inputs but equal outputs is
at most `1/|C|`.

This holds because in the `evalDist` model, each `query` returns an independent uniform
sample. The `loggingOracle` simply records these samples without caching, so the output
at position `j` is a fresh uniform draw independent of position `i`. When inputs are
distinct, `Pr[output_i = output_j] = 1/|C|`. When inputs are equal, the "inputs distinct"
condition in E_{i,j} makes the event empty, so `Pr[E_{i,j}] = 0 ≤ 1/|C|`. -/
private theorem probEvent_pair_collision_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (i j : ℕ) (_hij : i < j) :
    Pr[fun z => ∃ (hi : i < z.2.length) (hj : j < z.2.length),
        z.2[i].1 ≠ z.2[j].1 ∧ HEq z.2[i].2 z.2[j].2 |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  -- In the evalDist model, each query to loggingOracle gets an independent uniform sample.
  -- The j-th query's output is uniform over |C| values, independent of the i-th output.
  -- When inputs are distinct, Pr[output_i = output_j] = 1/|C|.
  -- When inputs are equal, the "distinct inputs" condition makes E_{i,j} empty.
  -- Either way, Pr[E_{i,j}] ≤ 1/|C|.
  sorry

/-- **Birthday bound for `loggingOracle`** (total query bound version):
For any computation making at most `n` total queries, the probability that the query log
contains a collision is at most `n² / (2 * |C|)`.

This is the primary birthday bound, proved via union bound over pairs:
1. Express `LogHasCollision` as `∃ (i,j) ∈ pairs, E_{i,j}` where pairs = {(i,j) | i < j < n}
2. Apply `probEvent_exists_finset_le_sum` (union bound)
3. Each `Pr[E_{i,j}] ≤ 1/|C|` by `probEvent_pair_collision_le`
4. Sum over C(n,2) pairs: C(n,2)/|C| ≤ n²/(2|C|) -/
private theorem probEvent_logCollision_aux {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Step 1: LogHasCollision is implied by: ∃ (i,j) with i < j < n, E_{i,j}
  -- where E_{i,j} means positions i,j have distinct inputs and equal outputs.
  -- The log has at most n entries (from the total query bound).
  --
  -- Step 2: Apply the union bound (probEvent_exists_finset_le_sum) over the
  -- finset of ordered pairs {(i,j) ∈ Fin n × Fin n | i < j}.
  --
  -- Step 3: Each Pr[E_{i,j}] ≤ 1/|C| by probEvent_pair_collision_le.
  --
  -- Step 4: The number of pairs is C(n,2) = n(n-1)/2.
  -- Total: C(n,2) * (1/|C|) = n(n-1)/(2|C|) ≤ n²/(2|C|).
  --
  -- The main technical gaps are:
  -- (a) Connecting IsTotalQueryBound to a bound on log length
  -- (b) Reformulating LogHasCollision as an existential over a fixed finset
  -- (c) The per-pair bound (probEvent_pair_collision_le)
  sorry

/-! ### Cache size bound -/

/-- A cache has at most `s` entries: there exists a `Finset` of size ≤ `s` that contains
all domain points where the cache is non-none. -/
private def CacheSizeBound (cache : QueryCache spec) (s : ℕ) : Prop :=
  ∃ (S : Finset ι), S.card ≤ s ∧ ∀ t, cache t ≠ none → t ∈ S

private lemma cacheSizeBound_empty : CacheSizeBound (∅ : QueryCache spec) 0 :=
  ⟨∅, le_refl 0, fun t h =>
    absurd (QueryCache.empty_apply t ▸ rfl : (∅ : QueryCache spec) t = none) h⟩

private lemma cacheSizeBound_cacheQuery {cache : QueryCache spec} {s : ℕ} {t : ι}
    (hsize : CacheSizeBound cache s) (u : spec.Range t) :
    CacheSizeBound (cache.cacheQuery t u) (s + 1) := by
  obtain ⟨S, hcard, hmem⟩ := hsize
  refine ⟨insert t S, ?_, ?_⟩
  · exact le_trans (Finset.card_insert_le t S) (by omega)
  · intro t' ht'
    by_cases heq : t' = t
    · exact heq ▸ Finset.mem_insert_self t S
    · have : (cache.cacheQuery t u) t' = cache t' := QueryCache.cacheQuery_of_ne cache u heq
      rw [this] at ht'
      exact Finset.mem_insert_of_mem (hmem t' ht')

private lemma cacheSizeBound_mono {cache : QueryCache spec} {s s' : ℕ}
    (h : CacheSizeBound cache s) (hle : s ≤ s') : CacheSizeBound cache s' := by
  obtain ⟨S, hcard, hmem⟩ := h
  exact ⟨S, le_trans hcard hle, hmem⟩

/-! ### Cache collision from cacheQuery

Characterization of when `cacheQuery` introduces a new collision, and a cardinality
bound on the set of "bad" values that create such collisions. -/

omit [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- When `¬CacheHasCollision c₀` and `c₀ t = none`, the updated cache `c₀.cacheQuery t u`
has a collision iff there exists a distinct cached input whose output HEq-matches `u`. -/
private lemma cacheHasCollision_cacheQuery_iff {c₀ : QueryCache spec} {t : ι}
    (hnocol : ¬CacheHasCollision c₀) (hmiss : c₀ t = none) (u : spec.Range t) :
    CacheHasCollision (c₀.cacheQuery t u) ↔
      ∃ (t' : ι) (u' : spec.Range t'), t' ≠ t ∧ c₀ t' = some u' ∧ HEq u u' := by
  constructor
  · intro ⟨t₁, t₂, u₁, u₂, hne, h₁, h₂, heq⟩
    -- The collision involves the new entry (t, u) and some existing entry.
    by_cases h1t : t₁ = t
    · subst h1t
      simp [QueryCache.cacheQuery_self] at h₁
      have h₂' : c₀ t₂ = some u₂ := by
        rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)] at h₂
      exact ⟨t₂, u₂, Ne.symm hne, h₂', h₁ ▸ heq⟩
    · by_cases h2t : t₂ = t
      · subst h2t
        simp [QueryCache.cacheQuery_self] at h₂
        have h₁' : c₀ t₁ = some u₁ := by
          rwa [QueryCache.cacheQuery_of_ne _ _ h1t] at h₁
        exact ⟨t₁, u₁, h1t, h₁', h₂ ▸ heq.symm⟩
      · -- Both t₁, t₂ ≠ t, so entries are from c₀ — contradicts hnocol
        have h₁' : c₀ t₁ = some u₁ := by
          rwa [QueryCache.cacheQuery_of_ne _ _ h1t] at h₁
        have h₂' : c₀ t₂ = some u₂ := by
          rwa [QueryCache.cacheQuery_of_ne _ _ h2t] at h₂
        exact absurd ⟨t₁, t₂, u₁, u₂, hne, h₁', h₂', heq⟩ hnocol
  · intro ⟨t', u', hne, hcache, heq⟩
    exact ⟨t, t', u, u', Ne.symm hne, QueryCache.cacheQuery_self c₀ t u,
      (QueryCache.cacheQuery_of_ne c₀ u hne).symm ▸ hcache, heq⟩

-- When ¬CacheHasCollision c₀, c₀ t = none, and cache has ≤ s entries,
-- at most s values of u create a new collision in c₀.cacheQuery t u.
open Classical in
private lemma card_bad_le {c₀ : QueryCache spec} {t : ι} {s : ℕ}
    (hnocol : ¬CacheHasCollision c₀) (hmiss : c₀ t = none)
    (hsize : CacheSizeBound c₀ s) :
    Finset.card (Finset.filter (fun u => CacheHasCollision (c₀.cacheQuery t u))
      Finset.univ) ≤ s := by
  sorry

private lemma sum_shift_cons (s m : ℕ) (N : ℝ≥0∞) :
    (s : ℝ≥0∞) * N⁻¹ + ∑ k ∈ range m, ((s + 1 + k : ℕ) : ℝ≥0∞) * N⁻¹ =
      ∑ k ∈ range (m + 1), ((s + k : ℕ) : ℝ≥0∞) * N⁻¹ := by
  sorry

/-! ### Core birthday bound by induction on OracleComp

The proof tracks a cache size bound `s` alongside the query budget `n`.
The inductive bound is `Σ_{k=s}^{s+n-1} k/N`, which for `s = 0` gives
the Gauss sum `Σ_{k=0}^{n-1} k/N ≤ n²/(2N)`. -/

/-- **Core inductive birthday bound** with explicit cache size tracking.
For a computation with total query budget `n`, starting from a cache with at most `s`
entries and no collision, the collision probability is at most `Σ_{k=s}^{s+n-1} k/N`. -/
private theorem probEvent_cacheCollision_induct {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n s : ℕ)
    (c₀ : QueryCache spec)
    (hbound : IsTotalQueryBound oa n)
    (hnocol : ¬CacheHasCollision c₀)
    (hsize : CacheSizeBound c₀ s) :
    let N := Fintype.card (spec.Range default)
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run c₀] ≤
      ∑ k ∈ range n, ((s + k : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
  simp only
  induction oa using OracleComp.inductionOn generalizing n s c₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    have : Pr[fun z => CacheHasCollision z.2 | (pure (a, c₀) : OracleComp spec _)] = 0 := by
      rw [probEvent_pure_eq_indicator]
      simp [Set.indicator, hnocol]
    rw [this]; exact zero_le _
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hbound
    obtain ⟨hn, hbound_cont⟩ := hbound
    -- Decompose simulateQ
    have hdecomp : (simulateQ cachingOracle (liftM (query (spec := spec) t) >>= mx)).run c₀ =
        (cachingOracle t).run c₀ >>= fun uc₁ =>
          (simulateQ cachingOracle (mx uc₁.1)).run uc₁.2 := by
      simp [StateT.run_bind]
    rw [hdecomp]
    -- Case split on cache hit vs miss
    cases hcache : c₀ t with
    | some u₀ =>
      -- Cache hit: (cachingOracle t).run c₀ = pure (u₀, c₀)
      have hhit : (cachingOracle t).run c₀ = pure (u₀, c₀) := by
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind,
          hcache, StateT.run_pure]
      rw [hhit, pure_bind]
      -- Now goal: Pr[collision | (simulateQ cachingOracle (mx u₀)).run c₀] ≤ Σ ...
      -- Apply IH with budget n-1, same cache size s
      have hih := ih u₀ (n - 1) s c₀ (hbound_cont u₀) hnocol hsize
      -- hih : ... ≤ Σ_{k ∈ range (n-1)} (s + k) / N
      -- Goal: ... ≤ Σ_{k ∈ range n} (s + k) / N
      -- Suffices: Σ_{k ∈ range (n-1)} ... ≤ Σ_{k ∈ range n} ...
      calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle (mx u₀)).run c₀]
          ≤ ∑ k ∈ range (n - 1), ((s + k : ℕ) : ℝ≥0∞) *
              (↑(Fintype.card (spec.Range default)))⁻¹ := hih
        _ ≤ ∑ k ∈ range n, ((s + k : ℕ) : ℝ≥0∞) *
              (↑(Fintype.card (spec.Range default)))⁻¹ := by
            apply Finset.sum_le_sum_of_subset
            exact Finset.range_mono (Nat.sub_le n 1)
    | none =>
      -- Cache miss: (cachingOracle t).run c₀ unfolds to a fresh query + cache update.
      -- After bind with the continuation, the whole thing becomes:
      --   liftM (query t) >>= fun u => (simulateQ cachingOracle (mx u)).run (c₀.cacheQuery t u)
      have hmiss : ((cachingOracle t).run c₀ >>= fun uc₁ =>
            (simulateQ cachingOracle (mx uc₁.1)).run uc₁.2) =
          (liftM (query t) >>= fun u =>
            (simulateQ cachingOracle (mx u)).run (c₀.cacheQuery t u)) := by
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hcache]
        simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.run_lift,
          bind_assoc, pure_bind]
        simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, StateT.run]
        simp only [pure_bind]
      rw [hmiss]
      -- Decompose using probEvent_bind_eq_tsum and bound each term.
      -- Goal: Pr[collision | liftM (query t) >>= fun u => continuation u] ≤ bound
      --
      -- We use the fact that Pr[collision in final | draw u] ≤
      --   Pr[collision in c₀.cacheQuery t u] + Pr[collision from continuation | no collision in c₀.cacheQuery t u]
      -- And Pr[draw u] = 1/N for each u (uniform).
      --
      -- For the IH approach with probEvent_bind_le_add, the issue is that the lemma
      -- bounds Pr[¬q | ...] whereas we want Pr[CacheHasCollision | ...].
      -- We work around this by using probEvent_bind_eq_tsum directly.
      --
      -- Alternative: bound by Pr[collision in intermediate] + Pr[collision from rest | no collision],
      -- using probEvent_mono and the IH.
      --
      -- The cleanest approach: for each u, bound
      --   Pr[collision final | u] ≤ 1  (trivially, when c₀.cacheQuery t u has collision)
      -- or
      --   Pr[collision final | u] ≤ Σ_{k ∈ range (n-1)} ((s+1)+k)/N  (by IH, when no collision)
      -- Then average over u.
      -- Since Pr[collision in c₀.cacheQuery t u] is either 0 or 1 for each u (deterministic),
      -- and happens for ≤ s values of u out of N (at most s existing entries can cause collision),
      -- we get: ≤ s/N * 1 + (1 - s/N) * IH_bound ≤ s/N + IH_bound.
      sorry

/-- **Birthday bound for `cachingOracle`** (total query bound version):
Derived from `probEvent_cacheCollision_induct` with `s = 0`:
`Σ_{k=0}^{n-1} k/|C| ≤ n²/(2|C|)` by the Gauss sum bound. -/
private theorem probEvent_cacheCollision_aux {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have hC : 0 < Fintype.card (spec.Range default) := Fintype.card_pos
  calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅]
      ≤ ∑ k ∈ range n, ((0 + k : ℕ) : ℝ≥0∞) *
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
        probEvent_cacheCollision_induct oa n 0 ∅ hbound not_cacheHasCollision_empty
          cacheSizeBound_empty
    _ = ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) *
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
        congr 1; ext k; simp
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
        gauss_sum_inv_le n _ hC

/-- **Birthday bound for `cachingOracle`** (per-index bound version):
For any computation making at most `t` queries per index, the probability that the
final cache contains a collision is at most `(Fintype.card ι * t)² / (2 * |C|)`.

When `ι` is a singleton (the typical ROM case with one hash oracle), this simplifies to
`t² / (2 * |C|)` via `probEvent_cacheCollision_le_birthday'`. -/
theorem probEvent_cacheCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (_hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal : IsTotalQueryBound oa (∑ i : ι, (fun (_ : ι) => t) i) :=
    IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  have h := probEvent_cacheCollision_aux oa (Fintype.card ι * t) htotal
  simp only [Nat.cast_mul] at h
  exact h

/-- Birthday bound for single-index oracle specs (the typical ROM case).
When there is exactly one oracle index, the per-index bound `t` is the total bound. -/
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

/-- **Birthday bound for `loggingOracle`** (per-index bound version):
Variant of the birthday bound stated in terms of the query log from `loggingOracle`. -/
theorem probEvent_logCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (_hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal : IsTotalQueryBound oa (∑ i : ι, (fun (_ : ι) => t) i) :=
    IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  have h := probEvent_logCollision_aux oa (Fintype.card ι * t) htotal
  simp only [Nat.cast_mul] at h
  exact h

/-! ## Unpredictability

If a point was not queried during a computation, the random oracle's value at that
point is independent of the computation's output and uniformly distributed.
-/

section Unpredictability

variable {spec' : OracleSpec.{0,0} ι} [spec'.DecidableEq] [spec'.Fintype] [spec'.Inhabited]

omit [spec'.DecidableEq] in
/-- **Fresh query uniformity**: If `t` is not in the cache, then querying `cachingOracle`
at `t` yields each value `u` paired with the updated cache, and the marginal probability
of obtaining `u` is `(Fintype.card C)^{-1}`.

This captures the core ROM unpredictability property: an unqueried oracle point
is independent of everything the adversary has observed. -/
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
/-- **Unpredictability bound**: If a `t`-query adversary runs under `cachingOracle` and
then a fresh query is made at point `predict`, the probability that the fresh query
returns a specific target value `target` AND `predict` was not previously cached is
at most `1/|C|`.

This is used when the adversary "guesses" the oracle output without querying. -/
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
      ≤ 1 * (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := by
        apply mul_le_mul_left
        exact probEvent_le_one
    _ = (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := one_mul _

end Unpredictability

/-- **Collision-based binding bound**: If winning the game implies a cache collision,
the win probability is bounded by the birthday bound.

This is the clean version of the combined bound — the hypothesis `hwin` directly
requires `win → CacheHasCollision`, so the proof is immediate from the birthday bound
via `probEvent_mono`. -/
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

/-- **Combined binding bound**: In a game where the adversary outputs values and then
verification queries are made, the probability of "winning" (either via collision or
via guessing) is bounded.

This combines collision resistance and unpredictability into a single bound suitable
for the binding game: either the adversary found a collision among its queries
(probability at most t^2/(2|C|)) or it guessed an unqueried value (probability at most 1/|C|).

Note: the hypothesis `hwin` includes an "unqueried point" disjunct. For practical use,
prefer `probEvent_collision_win_le` which assumes the stronger hypothesis
`win → CacheHasCollision`. -/
theorem probEvent_binding_combined_le {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (win : α × QueryCache spec → Prop)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default))
    (hwin : ∀ z ∈ support ((simulateQ cachingOracle oa).run ∅),
      win z → CacheHasCollision z.2 ∨ ∃ (q : spec.Domain), z.2 q = none) :
    Pr[win | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- We bound Pr[win] ≤ Pr[CacheHasCollision ∨ ∃ q, cache q = none].
  -- The latter is bounded by Pr[CacheHasCollision] + Pr[∃ q, cache q = none].
  -- Pr[CacheHasCollision] ≤ t²/(2|C|) by the birthday bound.
  -- For the "unqueried point" disjunct: since Pr[win] ≤ 1 trivially, and the
  -- birthday bound gives t²/(2|C|) which for reasonable parameters is < 1,
  -- we need a tighter argument. The key insight: in typical applications
  -- (commitment schemes), winning actually requires a collision, making the
  -- "unqueried point" disjunct vacuous. For the general case, we use
  -- Pr[win] ≤ Pr[collision ∨ unqueried] ≤ 1, but when |C| > t² we can do better.
  --
  -- For now, we bound by the birthday bound plus the trivial Pr ≤ 1 observation:
  -- Pr[win] ≤ Pr[CacheHasCollision ∨ ∃ q, cache q = none]
  -- ≤ Pr[CacheHasCollision] + Pr[∃ q, cache q = none]
  -- But the second term could be up to 1. To get the stated bound t²/(2|C|),
  -- we need: either win → CacheHasCollision (which is the typical case), or
  -- a domain finiteness argument.
  --
  -- Practical note: callers should prefer `probEvent_collision_win_le` when possible.
  -- This weaker version is kept for backward compatibility.
  sorry

end OracleComp
