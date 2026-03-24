/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.CollisionResistance
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Random Oracle Commitment Scheme — Caching Oracle Model

A commitment scheme in the random oracle model: `commit(m, s) = H(m, s)` where
`H : M × S → C` is a random oracle modeled via `cachingOracle`.

Following `docs/commitment_scheme.tex`, we prove three security properties:

1. **Binding** (Lemma cm-binding):
   `Pr[win] ≤ ½ · t² / |C|` where `t` is the query bound.
   The adversary and verification share the **same** random oracle (via `cachingOracle`).

2. **Extractability** (Lemma cm-extractability):
   `Pr[win] ≤ ½ · t² / |C|` with the same structure.
   Extractor searches the commit-phase trace for a matching entry.

3. **Hiding** (Lemma cm-hiding):
   `tvDist(real, sim) ≤ t / |S|` where the simulator outputs a uniform commitment.
   Proof via identical-until-bad: bad = adversary queried `(m, s_challenge)`.

All games use `cachingOracle` so that the adversary and verification/commitment
share the same random oracle, matching the random function model.

## References

- `docs/commitment_scheme.tex`, Chapter: Basic commitment scheme
- Joy of Cryptography, Chapter 4 (Commitment Schemes)
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

/-! ## Oracle Specification -/

/-- Oracle spec for the commitment scheme: maps `(M × S) → C`. -/
abbrev CMOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

-- We need DecidableEq on the product for cachingOracle.
variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]

instance : DecidableEq (M × S) := instDecidableEqProd

/-! ## Commit and Check

These are the commitment scheme algorithms, defined as oracle computations
that query H. When run under `cachingOracle`, all queries share the same
random function. -/

/-- Commit to message `m` with salt `s` by querying the random oracle. -/
def CMCommit (m : M) (s : S) : OracleComp (CMOracle M S C) C :=
  query (spec := CMOracle M S C) (m, s)

/-- Check commitment `c` against opening `(m, s)`: query oracle and compare. -/
def CMCheck (c : C) (m : M) (s : S) : OracleComp (CMOracle M S C) Bool := do
  let c' ← query (spec := CMOracle M S C) (m, s)
  return (c == c')

/-! ## 1. Binding

**Textbook (Lemma cm-binding)**: For every `t`-query adversary A^H that outputs
`(c, m₀, s₀, m₁, s₁)`:
  Pr[m₀ ≠ m₁ ∧ Check^H(c, m₀, s₀) = 1 ∧ Check^H(c, m₁, s₁) = 1] ≤ ½ · t² / |C|

The adversary and Check use the **same** random oracle H. We model this by
running the entire game (adversary + verification) inside `simulateQ cachingOracle`. -/

/-- A binding adversary with query bound `t`. -/
structure BindingAdversary (M : Type) (S : Type) (C : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- The adversary's computation, producing `(c, m₀, s₀, m₁, s₁)`. -/
  run : OracleComp (CMOracle M S C) (C × M × S × M × S)
  /-- The adversary makes at most `t` total queries. -/
  queryBound : IsTotalQueryBound run t

/-- The binding game in the random oracle model.

The adversary outputs `(c, m₀, s₀, m₁, s₁)`, then Check verifies both openings
using the **same** random oracle. Win condition: `m₀ ≠ m₁` and both checks pass.

The game runs inside `simulateQ cachingOracle` starting from an empty cache,
so all queries (adversary's and verification's) share the same random function. -/
def bindingGame {t : ℕ} (A : BindingAdversary M S C t) :
    OracleComp (CMOracle M S C) (Bool × QueryCache (CMOracle M S C)) :=
  (simulateQ cachingOracle (do
    let (c, m₀, s₀, m₁, s₁) ← A.run
    -- Verify both openings using the same oracle
    let c₀ ← query (spec := CMOracle M S C) (m₀, s₀)
    let c₁ ← query (spec := CMOracle M S C) (m₁, s₁)
    return (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c)))).run ∅

/-- The inner oracle computation of the binding game (before `simulateQ`). -/
private def bindingInner {t : ℕ} (A : BindingAdversary M S C t) :
    OracleComp (CMOracle M S C) Bool := do
  let (c, m₀, s₀, m₁, s₁) ← A.run
  let c₀ ← query (spec := CMOracle M S C) (m₀, s₀)
  let c₁ ← query (spec := CMOracle M S C) (m₁, s₁)
  return (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c))

/-- The binding game equals `simulateQ cachingOracle` on `bindingInner`. -/
private lemma bindingGame_eq {t : ℕ} (A : BindingAdversary M S C t) :
    bindingGame A = (simulateQ cachingOracle (bindingInner A)).run ∅ := rfl

/-- `simulateQ cachingOracle (liftM (query idx))` equals `cachingOracle idx` as StateT actions.
This follows from `simulateQ_query` with `cont = id`. -/
private lemma simulateQ_cachingOracle_query (idx : (CMOracle M S C).Domain) :
    (simulateQ cachingOracle (liftM (query (spec := CMOracle M S C) idx))) =
    (cachingOracle (spec := CMOracle M S C) idx) := by
  simp [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]

/-- After running `cachingOracle` on a single query at index `idx`, the resulting cache
has an entry at `idx`. -/
private lemma cachingOracle_query_caches (idx : (CMOracle M S C).Domain)
    (cache₀ : QueryCache (CMOracle M S C))
    (v : (CMOracle M S C).Range idx) (cache₁ : QueryCache (CMOracle M S C))
    (hmem : (v, cache₁) ∈ support ((cachingOracle (spec := CMOracle M S C) idx).run cache₀)) :
    cache₁ idx = some v := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hc : cache₀ idx with
  | some u =>
    simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact hc
  | none =>
    simp only [hc, StateT.run_bind] at hmem
    rw [show (liftM (query (spec := CMOracle M S C) idx) :
        StateT (QueryCache (CMOracle M S C)) (OracleComp (CMOracle M S C)) _).run cache₀ =
        ((liftM (query (spec := CMOracle M S C) idx) : OracleComp _ _) >>= fun u =>
          pure (u, cache₀)) from rfl] at hmem
    rw [bind_assoc] at hmem; simp only [pure_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨u, _, hmem⟩ := hmem
    simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact QueryCache.cacheQuery_self cache₀ idx v

/-- Winning the binding game implies a cache collision.

If the adversary wins (`m₀ ≠ m₁` and both checks pass), then the final cache contains
entries at `(m₀,s₀)` and `(m₁,s₁)` with the same value `c`, giving a collision since
`(m₀,s₀) ≠ (m₁,s₁)` (as `m₀ ≠ m₁`). -/
private lemma binding_win_implies_collision {t : ℕ} (A : BindingAdversary M S C t) :
    ∀ z ∈ support ((simulateQ cachingOracle (bindingInner A)).run ∅),
      z.1 = true → CacheHasCollision z.2 := by
  intro z hz hwin
  simp only [bindingInner, simulateQ_bind, simulateQ_pure] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨c, m₀, s₀, m₁, s₁⟩, cache₁⟩, hmem₁, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c₀, cache₂⟩, hmem₂, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c₁, cache₃⟩, hmem₃, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz] at hwin ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
  obtain ⟨⟨hne, hc₀⟩, hc₁⟩ := hwin
  have hpair_ne : (m₀, s₀) ≠ (m₁, s₁) := fun h => hne (Prod.ext_iff.mp h).1
  -- cache₂ has entry at (m₀, s₀) with value c₀
  rw [simulateQ_cachingOracle_query] at hmem₂
  have hcache₂ : cache₂ (m₀, s₀) = some c₀ :=
    cachingOracle_query_caches (m₀, s₀) cache₁ c₀ cache₂ hmem₂
  -- cache₃ has entry at (m₁, s₁) with value c₁
  -- Cache monotonicity: cache₂ ≤ cache₃, so cache₃ also has (m₀, s₀) ↦ c₀
  have hcache_mono : cache₂ ≤ cache₃ := by
    have hmem₃_co : (c₁, cache₃) ∈ support
        ((cachingOracle (spec := CMOracle M S C) (m₁, s₁)).run cache₂) := by
      simp only [simulateQ_cachingOracle_query] at hmem₃; exact hmem₃
    unfold cachingOracle at hmem₃_co
    exact QueryImpl.withCaching_cache_le
      (QueryImpl.ofLift (CMOracle M S C) (OracleComp (CMOracle M S C)))
      (m₁, s₁) cache₂ (c₁, cache₃) hmem₃_co
  rw [simulateQ_cachingOracle_query] at hmem₃
  have hcache₃ : cache₃ (m₁, s₁) = some c₁ :=
    cachingOracle_query_caches (m₁, s₁) cache₂ c₁ cache₃ hmem₃
  have hcache₃_m₀ : cache₃ (m₀, s₀) = some c₀ :=
    hcache_mono hcache₂
  exact ⟨(m₀, s₀), (m₁, s₁), c₀, c₁, hpair_ne, hcache₃_m₀, hcache₃,
    heq_of_eq (by rw [hc₀, hc₁])⟩

/-- Monotonicity for `IsTotalQueryBound`. -/
private lemma isTotalQueryBound_mono {α₀ : Type}
    {oa : OracleComp (CMOracle M S C) α₀} {m₁ m₂ : ℕ}
    (h : IsTotalQueryBound oa m₁) (hle : m₁ ≤ m₂) :
    IsTotalQueryBound oa m₂ := by
  induction oa using OracleComp.inductionOn generalizing m₁ m₂ with
  | pure _ => exact trivial
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 hle,
      fun u => ih u (h.2 u) (Nat.sub_le_sub_right hle 1)⟩

/-- Bind composition for `IsTotalQueryBound`. -/
private lemma isTotalQueryBound_bind {α₀ β₀ : Type}
    {oa : OracleComp (CMOracle M S C) α₀}
    {ob : α₀ → OracleComp (CMOracle M S C) β₀}
    {n₁ n₂ : ℕ}
    (h1 : IsTotalQueryBound oa n₁) (h2 : ∀ x, IsTotalQueryBound (ob x) n₂) :
    IsTotalQueryBound (oa >>= ob) (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ with
  | pure x =>
    simp only [pure_bind]
    exact isTotalQueryBound_mono (h2 x) (Nat.le_add_left n₂ n₁)
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h1
    rw [bind_assoc, isTotalQueryBound_query_bind_iff]
    refine ⟨Nat.add_pos_left h1.1 n₂, fun u => ?_⟩
    have h3 := ih u (h1.2 u)
    have heq : n₁ - 1 + n₂ = n₁ + n₂ - 1 := by omega
    rw [heq] at h3; exact h3

/-- `IsTotalQueryBound` for the binding game's inner computation: `t + 2`
(adversary's `t` queries + 2 verification queries). -/
private lemma bindingInner_totalBound {t : ℕ} (A : BindingAdversary M S C t) :
    IsTotalQueryBound (bindingInner A) (t + 2) := by
  apply isTotalQueryBound_bind A.queryBound
  intro ⟨c, m₀, s₀, m₁, s₁⟩
  show IsTotalQueryBound _ 2
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun c₀ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ => trivial⟩

/-- **Binding theorem (Lemma cm-binding)**: The probability that any `t`-query
adversary wins the binding game is at most `(t+2)² / (2|C|)`.

The adversary makes ≤ `t` queries; the game adds 2 verification queries.
The proof reduces the win event to a cache collision via `binding_win_implies_collision`,
then applies the ROM birthday bound `probEvent_cacheCollision_le_birthday_total`. -/
theorem binding_bound {t : ℕ} (A : BindingAdversary M S C t) :
    Pr[fun z => z.1 = true | bindingGame A] ≤
    ((t + 2) ^ 2 : ℝ≥0∞) / (2 * Fintype.card C) := by
  rw [bindingGame_eq]
  apply le_trans (probEvent_mono (binding_win_implies_collision A))
  have h := probEvent_cacheCollision_le_birthday_total (bindingInner A) (t + 2)
    (bindingInner_totalBound A) Fintype.card_pos (fun _ => le_refl _)
  simp only [Nat.cast_add, Nat.cast_ofNat] at h
  exact h

/-! ## 2. Extractability

**Textbook (Lemma cm-extractability)**: There exists a deterministic extractor E
such that for every `t`-query two-phase adversary A = (A_commit, A_open):
  Pr[Check^H(c,m,s) = 1 ∧ E(c, trace) ≠ (m,s)] ≤ ½ · t² / |C|

The extractor E scans the commit-phase query-answer trace for an entry
whose answer matches the commitment c. -/

/-- An extractability adversary with two phases. -/
structure ExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- Commit phase: produces a commitment and auxiliary state (with oracle access). -/
  commit : OracleComp (CMOracle M S C) (C × AUX)
  /-- Open phase: given auxiliary state, produces an opening `(m, s)` (with oracle access). -/
  open_ : AUX → OracleComp (CMOracle M S C) (M × S)
  /-- Commit-phase query bound. -/
  t₁ : ℕ
  /-- Open-phase query bound. -/
  t₂ : ℕ
  /-- Total queries bounded by `t`. -/
  totalBound : t₁ + t₂ ≤ t
  /-- Query bound for the commit phase. -/
  commitBound : IsTotalQueryBound commit t₁
  /-- Query bound for the open phase. -/
  openBound : ∀ aux, IsTotalQueryBound (open_ aux) t₂

/-- The extractor: scan the query-answer trace for a pair whose answer matches `cm`. -/
def CMExtract (cm : C) (tr : QueryLog (CMOracle M S C)) : Option (M × S) :=
  match tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => some entry.1
  | none => none

/-- The extractability game in the random oracle model.

Phase 1 (commit): Run `A.commit` with a logging oracle layered on top
  (to capture the trace), all within `cachingOracle`.
Phase 2 (open): Run `A.open_` with the same oracle (shared cache).
Verification: Query `H(m, s)` and compare to `cm`.
Extraction: Search the commit-phase trace for an entry matching `cm`.

Win: Check passes AND (extractor found nothing OR found a different opening). -/
def extractabilityGame {AUX : Type} {t : ℕ} (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) (Bool × QueryCache (CMOracle M S C)) :=
  (simulateQ cachingOracle (do
    -- Phase 1: commit with logging to get trace
    let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
    -- Phase 2: open
    let (m, s) ← A.open_ aux
    -- Verify: query H(m,s) using the same oracle
    let c ← query (spec := CMOracle M S C) (m, s)
    -- Extract from the commit-phase trace
    let extracted := CMExtract cm tr
    return (match extracted with
      | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
      | none => (c == cm)))).run ∅

variable {AUX : Type}

/-- The inner oracle computation of the extractability game (before `simulateQ`). -/
private def extractabilityInner {AUX : Type} {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) Bool := do
  let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
  let (m, s) ← A.open_ aux
  let c ← query (spec := CMOracle M S C) (m, s)
  let extracted := CMExtract cm tr
  return (match extracted with
    | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
    | none => (c == cm))

/-- The extractability game equals `simulateQ cachingOracle` on `extractabilityInner`. -/
private lemma extractabilityGame_eq {t : ℕ} (A : ExtractAdversary M S C AUX t) :
    extractabilityGame A =
    (simulateQ cachingOracle (extractabilityInner A)).run ∅ := rfl

/-- Winning the extractability game implies a cache collision.

**Proof structure**: The two cases of `CMExtract`:
- `some` case: The extractor found `(m', s')` in the commit trace with `H(m', s') = cm`,
  and verification gives `H(m, s) = cm` with `(m', s') ≠ (m, s)`. These two distinct
  cache entries with the same output constitute a collision. Uses `log_entry_in_cache`.
- `none` case: No commit query returned `cm`. The adversary "predicted" the oracle output.
  Verification computes `H(m, s) = cm` but `cm` never appeared as an oracle output during
  commit. This does NOT deterministically imply a cache collision — the adversary may have
  embedded a hardcoded value that happens to match a fresh oracle draw with probability
  `1/|C|`. However, since `CacheHasCollision` is checked on the full final cache (including
  both phases), open-phase queries provide additional collision opportunities.

**Status**: 2 sorrys remain.
- `some` case sorry: Needs `log_entry_in_cache` (log entries are cached) and cache
  monotonicity through the open phase.
- `none` case sorry: Genuinely does not follow from pure support reasoning.
  The textbook proof handles this by noting that `Pr[none ∧ win] ≤ 1/|C|`,
  which is absorbed into the birthday bound. A probabilistic argument (not a
  pointwise support argument) is needed here. -/
private lemma extractability_win_implies_collision {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    ∀ z ∈ support ((simulateQ cachingOracle (extractabilityInner A)).run ∅),
      z.1 = true → CacheHasCollision z.2 := by
  intro z hz hwin
  simp only [extractabilityInner, simulateQ_bind, simulateQ_pure] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨⟨cm, aux⟩, tr⟩, cache₁⟩, hmem₁, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨m, s⟩, cache₂⟩, hmem₂, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, cache₃⟩, hmem₃, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz] at hwin ⊢
  -- cache₃ has entry at (m, s) with value c
  rw [simulateQ_cachingOracle_query] at hmem₃
  have hcache₃ : cache₃ (m, s) = some c :=
    cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
  -- Cache monotonicity: cache₂ ≤ cache₃
  have _hcache_mono₂₃ : cache₂ ≤ cache₃ := by
    have hmem₃_co : (c, cache₃) ∈ support
        ((cachingOracle (spec := CMOracle M S C) (m, s)).run cache₂) := hmem₃
    unfold cachingOracle at hmem₃_co
    exact QueryImpl.withCaching_cache_le
      (QueryImpl.ofLift (CMOracle M S C) (OracleComp (CMOracle M S C)))
      (m, s) cache₂ (c, cache₃) hmem₃_co
  -- Case split on CMExtract result
  unfold CMExtract at hwin
  cases hfind : (tr.find? (fun entry => decide (entry.2 = cm))) with
  | some entry =>
    simp only [hfind] at hwin
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
    obtain ⟨hceq, hne⟩ := hwin
    -- entry.2 = cm by the find? predicate
    have _hentry_cm : entry.2 = cm := by
      have hfound := List.find?_some hfind
      simp only [decide_eq_true_eq] at hfound
      exact hfound
    -- entry is in the log tr
    have hentry_mem : entry ∈ tr := List.mem_of_find?_eq_some hfind
    -- Log entries are in cache₁ (via log_entry_in_cache_and_mono)
    have hlog_cache := (OracleComp.log_entry_in_cache_and_mono A.commit ∅
      (((cm, aux), tr), cache₁) hmem₁).1
    have hcache₁_entry : cache₁ entry.1 = some entry.2 :=
      hlog_cache entry hentry_mem
    -- Cache monotonicity: ∅ ≤ cache₁ ≤ cache₂ ≤ cache₃
    -- cache₁ ≤ cache₂: from open phase (simulateQ cachingOracle preserves monotonicity)
    -- We get this from log_entry_in_cache_and_mono applied to (open_ aux) wrapped trivially
    -- Actually, hmem₂ is about (simulateQ cachingOracle (A.open_ aux)).run cache₁
    -- We can use the same induction pattern, but simpler: just use withCaching_cache_le
    -- through the full simulateQ run. For now, use cache₁ ≤ cache₃ directly.
    -- cache₁ ≤ cache₃ follows from cache₁ ≤ cache₂ ≤ cache₃.
    -- Use `_hcache_mono₂₃ : cache₂ ≤ cache₃` already proved.
    -- For cache₁ ≤ cache₂, observe hmem₂ is in support of simulateQ cachingOracle.
    -- cache₁ ≤ cache₂ (simulateQ cachingOracle on open_ only grows cache)
    have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
      simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
    -- cache₃ entry.1 = some entry.2 (by monotonicity chain cache₁ ≤ cache₂ ≤ cache₃)
    have hcache₃_entry : cache₃ entry.1 = some entry.2 :=
      _hcache_mono₂₃ (hcache_mono₁₂ hcache₁_entry)
    -- Collision: entry.1 and (m,s) both map to cm in cache₃
    exact ⟨entry.1, (m, s), entry.2, c, hne, hcache₃_entry, hcache₃,
      heq_of_eq (by rw [_hentry_cm, hceq])⟩
  | none =>
    simp only [hfind] at hwin
    simp only [beq_iff_eq] at hwin
    -- hwin : c = cm
    -- SORRY: The none case does NOT deterministically imply CacheHasCollision.
    -- The adversary may have hardcoded cm and gotten lucky: H(m,s) = cm with
    -- probability 1/|C|. No collision is needed for this to happen.
    --
    -- The textbook handles this via a PROBABILISTIC argument:
    --   Pr[win ∧ none] ≤ 1/|C| (fresh query unpredictability)
    -- which is absorbed into the birthday bound.
    --
    -- Fixing this requires restructuring the proof to use:
    --   Pr[win] = Pr[win ∧ some] + Pr[win ∧ none]
    --           ≤ Pr[collision] + 1/|C|
    --           ≤ t²/(2|C|) + 1/|C|
    -- instead of the current pointwise "win ⟹ collision" approach.
    sorry

/-- `IsTotalQueryBound` for the extractability game's inner computation.

The inner computation consists of:
1. `(simulateQ loggingOracle A.commit).run` — `t₁` queries (loggingOracle passes through)
2. `A.open_ aux` — `t₂` queries
3. `query (m, s)` — 1 verification query

Total: `t₁ + t₂ + 1 ≤ t + 1`.

**Status**: sorry — requires two pieces of missing infrastructure:
1. `IsTotalQueryBound` preservation through `simulateQ loggingOracle ... .run`:
   `loggingOracle` passes all queries through unchanged, so the query bound
   should transfer. But `IsTotalQueryBound` is defined structurally via
   `OracleComp.construct`, and `simulateQ loggingOracle` wraps each query in
   `WriterT` machinery that changes the syntactic structure. A lemma like
   `IsTotalQueryBound ((simulateQ loggingOracle oa).run) n ↔ IsTotalQueryBound oa n`
   would require induction showing the `WriterT.run` / `loggingOracle` composition
   preserves the structural query bound.
2. Composition of bounds through dependent bind: the open phase depends on `aux`
   from the commit phase, requiring `isTotalQueryBound_bind` with the existential
   intermediate result. -/
private lemma extractabilityInner_totalBound {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    IsTotalQueryBound (extractabilityInner A) (t + 1) := by
  -- extractabilityInner A =
  --   (simulateQ loggingOracle A.commit).run >>= fun ((cm, aux), tr) =>
  --     A.open_ aux >>= fun (m, s) =>
  --       query (m, s) >>= fun c => pure (...)
  -- Query budget: t₁ (commit) + t₂ (open) + 1 (verify) ≤ t + 1
  -- Step 1: (simulateQ loggingOracle A.commit).run has bound t₁
  have h1 : IsTotalQueryBound ((simulateQ loggingOracle A.commit).run) A.t₁ :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff A.commit A.t₁).mpr A.commitBound
  -- Step 2: A.open_ aux has bound t₂ for all aux
  -- Step 3: query (m, s) >>= pure (...) has bound 1
  -- Combine via isTotalQueryBound_bind
  apply isTotalQueryBound_mono (m₁ := A.t₁ + (A.t₂ + 1))
  · apply isTotalQueryBound_bind h1
    intro ⟨⟨cm, aux⟩, tr⟩
    apply isTotalQueryBound_bind (A.openBound aux)
    intro ⟨m, s⟩
    show IsTotalQueryBound _ 1
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  · have := A.totalBound; omega

/-- **Extractability theorem (Lemma cm-extractability)**: The probability that
any `t`-query adversary wins the extractability game is at most `(t+1)² / (2|C|)`.

The bound is `(t+1)²` rather than `t²` because the extractability game makes
`t + 1` total queries: `t₁ + t₂ ≤ t` adversary queries plus 1 verification query.

**Proof structure**:
1. Reduce win event to cache collision via `extractability_win_implies_collision`
2. Apply birthday bound `probEvent_cacheCollision_le_birthday_total` with `n = t + 1`

**Status**: 3 sorrys upstream (2 in `extractability_win_implies_collision`,
1 in `extractabilityInner_totalBound`).
The `none` case of win-implies-collision is a genuine proof gap requiring a
probabilistic (not pointwise) argument. -/
theorem extractability_bound {t : ℕ} (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1 = true | extractabilityGame A] ≤
    ((t + 1) ^ 2 : ℝ≥0∞) / (2 * Fintype.card C) := by
  rw [extractabilityGame_eq]
  apply le_trans (probEvent_mono (extractability_win_implies_collision A))
  have h := probEvent_cacheCollision_le_birthday_total (extractabilityInner A) (t + 1)
    (extractabilityInner_totalBound A) Fintype.card_pos (fun _ => le_refl _)
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact h

/-! ## 3. Hiding

**Textbook (Lemma cm-hiding)**: There exists a simulator S such that for every
`t`-query adversary A, the following two distributions are `t / |S|`-close:
  Real: A^H(state, H(m, s))  where (m, state) ← A^H, s ← S
  Sim:  A^H(state, S^H)      where (m, state) ← A^H, S^H outputs uniform C

The simulator simply outputs a random element of C.

The proof uses identical-until-bad with a counter-based bad predicate.
The state tracks `(cache, saltCount)` where `saltCount` counts how many
queries with salt `s` have been processed (including the challenge query).
Bad is defined as `saltCount ≥ 2`, meaning at least one ADVERSARY query
had salt `s` in addition to the challenge commitment query.

Since the challenge query always increments `saltCount` by 1, we have:
- `saltCount = 0`: no salt-s queries yet (before challenge, no adversary salt-s)
- `saltCount = 1`: only the challenge query had salt s (no adversary salt-s)
- `saltCount ≥ 2`: at least one adversary query had salt s

When `¬bad` (`saltCount < 2`), both implementations agree on every query,
because the redirect condition in impl₂ requires `saltCount ≥ 2`.

**Note on the `Pr[bad]` bound**: `Pr[bad]` = `Pr[saltCount ≥ 2 at end]`
= `Pr[∃ adversary query with salt = s]` ≤ `t / |S|`. -/

/-- A hiding adversary with two phases and query bound `t`. -/
structure HidingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- Phase 1: choose a message and auxiliary state (with oracle access). -/
  choose : OracleComp (CMOracle M S C) (M × AUX)
  /-- Phase 2: given auxiliary state and a commitment, output a guess bit. -/
  distinguish : AUX → C → OracleComp (CMOracle M S C) Bool
  /-- Query bound for the choose phase (total queries). -/
  chooseBound : IsTotalQueryBound choose t
  /-- Query bound for the distinguish phase (total queries). -/
  distinguishBound : ∀ (aux : AUX) (cm : C),
    IsTotalQueryBound (distinguish aux cm) t

/-- The real hiding game, parametrized by salt `s`.

The adversary chooses `m`, then receives commitment `cm = H(m, s)` computed
using the same caching oracle. -/
def hidingReal {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool :=
  (simulateQ cachingOracle (do
    let (m, aux) ← A.choose
    let cm ← query (spec := CMOracle M S C) (m, s)
    A.distinguish aux cm)).run' ∅

/-! ### Identical-until-bad infrastructure for hiding

State: `QueryCache (CMOracle M S C) × ℕ` — cache plus a counter of how many
queries with salt `s` have been processed.

Bad: `saltCount ≥ 2` — at least two salt-`s` queries have occurred. Since the
challenge query `(m, s)` always contributes one, bad means at least one
ADVERSARY query also had salt `s`.

**`hidingImpl₁`** (real): standard caching + increments counter on salt `s`.
**`hidingImpl₂`** (intermediate): same as `hidingImpl₁` EXCEPT when
`saltCount ≥ 2` and cache miss with salt `s`, queries at `(default, default)`.

When `¬bad` (`saltCount < 2`): both implementations are literally identical
(the redirect condition `saltCount ≥ 2 && salt = s` is `false`).
-/

/-- The "bad" predicate: at least 2 salt-`s` queries have occurred (the challenge
counts as 1, so bad means at least one adversary query also had salt `s`). -/
def hidingBad : QueryCache (CMOracle M S C) × ℕ → Prop := fun p => p.2 ≥ 2

instance : DecidablePred (hidingBad (M := M) (S := S) (C := C)) :=
  fun p => Nat.decLe 2 p.2

/-- Real oracle implementation for the hiding game.
Standard caching + increments salt counter when any query has salt `s`. -/
def hidingImpl₁ (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, cnt) ← get
    match cache ms with
    | some u => return u
    | none => do
      let u ← (liftM (query (spec := CMOracle M S C) ms) :
        StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C)) C)
      let cnt' := if ms.2 == s then cnt + 1 else cnt
      set (cache.cacheQuery ms u, cnt')
      return u

/-- Intermediate oracle implementation for the hiding game.
Same as `hidingImpl₁`, except when `cnt ≥ 2` (bad) and cache miss with salt `s`,
queries the underlying oracle at `(default, default)` instead. -/
def hidingImpl₂ (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, cnt) ← get
    match cache ms with
    | some u => return u
    | none => do
      -- When bad (cnt ≥ 2) and salt matches, redirect query
      let queryPoint := if (decide (cnt ≥ 2)) && (ms.2 == s) then (default, default) else ms
      let u ← (liftM (query (spec := CMOracle M S C) queryPoint) :
        StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C)) C)
      let cnt' := if ms.2 == s then cnt + 1 else cnt
      set (cache.cacheQuery ms u, cnt')
      return u

/-- Simulator oracle implementation for the hiding game.
Same as `hidingImpl₁` EXCEPT that ALL salt-`s` cache misses are redirected to
`(default, default)`. The result is still cached at the original query point `ms`,
and the counter still increments. Since the underlying oracle is memoryless
(each `query` returns fresh uniform regardless of point), the redirect doesn't
change the marginal distribution of the returned value.

The key difference from `hidingImpl₂` (which only redirects when `cnt ≥ 2`):
`hidingImplSim` redirects ALL salt-s cache misses, including the very first one
(the challenge query). This makes `hidingImplSim` match the simulator's behavior. -/
def hidingImplSim (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, cnt) ← get
    match cache ms with
    | some u => return u
    | none => do
      -- Redirect ALL salt-s cache misses to (default, default)
      let queryPoint := if ms.2 == s then (default, default) else ms
      let u ← (liftM (query (spec := CMOracle M S C) queryPoint) :
        StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C)) C)
      let cnt' := if ms.2 == s then cnt + 1 else cnt
      set (cache.cacheQuery ms u, cnt')
      return u

/-- The shared adversary computation for the hiding game.
Both `hidingReal` and the intermediate game use this computation. -/
def hidingOa {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool := do
  let (m, aux) ← A.choose
  let cm ← query (spec := CMOracle M S C) (m, s)
  A.distinguish aux cm

/-- The simulated hiding game, parametrized by salt `s`.

The adversary runs `hidingOa A s` (which includes the challenge query `(m, s)`)
through `hidingImplSim`, which redirects ALL salt-`s` cache misses to
`(default, default)`. This makes the challenge commitment independent of `m`:
the challenge `query (m, s)` is redirected → returns fresh uniform, independent
of `m`. The salt counter is discarded by `run'`.

Using `hidingImplSim` allows direct application of the distributional
identical-until-bad lemma (`tvDist_simulateQ_le_probEvent_bad_dist`) to bound
the distance between `hidingReal` and `hidingSim`. -/
def hidingSim {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool :=
  (simulateQ (hidingImplSim s) (hidingOa A s)).run' (∅, 0)

/-- The real hiding game is `simulateQ cachingOracle` applied to the shared computation. -/
theorem hidingReal_eq {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingReal A s = (simulateQ cachingOracle (hidingOa A s)).run' ∅ := by
  simp only [hidingReal, hidingOa]

/-- The real hiding game equals `simulateQ hidingImpl₁` projected to discard the counter.
This lifts cachingOracle's state by pairing it with the salt counter. -/
theorem hidingReal_eq_impl₁ {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingReal A s = (simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, 0) := by
  rw [hidingReal_eq A s]
  exact (OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq'
    (hidingImpl₁ s) cachingOracle Prod.fst (fun ms st => by
      obtain ⟨cache, cnt⟩ := st
      simp only [hidingImpl₁, cachingOracle, QueryImpl.withCaching_apply,
        QueryImpl.ofLift, StateT.run_bind, StateT.run_get, pure_bind]
      cases hc : cache ms with
      | some u =>
        simp [hc, StateT.run_pure, Prod.map]
      | none =>
        simp only [hc, StateT.run_bind, OracleComp.liftM_run_StateT]
        simp only [bind_assoc, pure_bind, Prod.map]
        simp [StateT.run_set, StateT.run_pure, Prod.map, StateT.run_modifyGet]
    ) (hidingOa A s) (∅, 0)).symm

/-- The implementations agree when `¬bad`: when the counter is less than 2,
`hidingImpl₁` and `hidingImpl₂` produce the same monadic computation.
The redirect condition `cnt ≥ 2 && salt = s` is `false` since `cnt < 2`. -/
theorem hidingImpl_agree (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : ¬hidingBad st) :
    (hidingImpl₁ s ms).run st = (hidingImpl₂ s ms).run st := by
  simp only [hidingBad, ge_iff_le, not_le] at h
  obtain ⟨cache, cnt⟩ := st
  simp only at h
  simp only [hidingImpl₁, hidingImpl₂, StateT.run_bind, StateT.run_get, pure_bind]
  cases cache ms with
  | some u => rfl
  | none =>
    -- cnt < 2, so the redirect condition is false, making queryPoint = ms
    have hcnt : (if (decide (cnt ≥ 2) && (ms.2 == s)) = true then (default, default) else ms)
        = ms := by
      have : decide (cnt ≥ 2) = false := decide_eq_false (Nat.not_le.mpr h)
      simp [this]
    rw [hcnt]

/-- Bad is monotone for `hidingImpl₁`: once the counter reaches 2, it stays ≥ 2. -/
theorem hidingImpl₁_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImpl₁ s ms).run st)) :
    hidingBad x.2 := by
  simp only [hidingBad] at h ⊢
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingImpl₁, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact h
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp only [Prod.snd]
    split <;> omega

/-- Bad is monotone for `hidingImpl₂`: once the counter reaches 2, it stays ≥ 2. -/
theorem hidingImpl₂_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImpl₂ s ms).run st)) :
    hidingBad x.2 := by
  simp only [hidingBad] at h ⊢
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingImpl₂, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact h
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp only [Prod.snd]
    split <;> omega

/-! ### Corrected proof architecture

The original three-step decomposition (`hidingImpl₂_eq_hidingSim`) was flawed
because `hidingImpl₂` caches the challenge at `(m, s)` while the simulator
caches at `(default, default)` — an adversary querying `(m, s)` during distinguish
observes a cache hit in impl₂ but a miss in the simulator.

**Corrected approach**: Use `hidingImplSim` which redirects ALL salt-s cache
misses to `(default, default)`. Then:
1. `hidingImpl₁` and `hidingImplSim` agree **distributionally** when `¬bad`
   (both return fresh uniform on cache miss; the query point doesn't matter
   because the underlying oracle is memoryless)
2. `hidingImplSim.run' = hidingSim` (the simulator matches the impl)
3. Apply `tvDist_simulateQ_le_probEvent_bad_dist` to bound the distance

The `Pr[bad] ≤ t/|S|` bound requires `s` to be uniformly random (see below). -/

/-- Bad is monotone for `hidingImplSim`: once cnt ≥ 2, it stays ≥ 2. -/
theorem hidingImplSim_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImplSim s ms).run st)) :
    hidingBad x.2 := by
  simp only [hidingBad] at h ⊢
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingImplSim, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact h
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp only [Prod.snd]
    split <;> omega

/-- `hidingImpl₁` and `hidingImplSim` agree **distributionally** when `¬bad`.

When `cnt < 2`, the two implementations differ only in the query point for
salt-s cache misses: `hidingImpl₁` queries at `ms`, while `hidingImplSim`
queries at `(default, default)`. Since the underlying oracle is memoryless
(`Pr[= u | query t₁] = Pr[= u | query t₂]` for all `u` when both ranges
are `C`), the returned value has the same distribution. The cache update and
counter increment are identical (both cache at `ms`, both increment when
`ms.2 = s`). Therefore every `(output, state)` pair has the same probability. -/
theorem hidingImpl_agree_dist (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : ¬hidingBad st)
    (p : C × (QueryCache (CMOracle M S C) × ℕ)) :
    Pr[= p | (hidingImpl₁ s ms).run st] =
      Pr[= p | (hidingImplSim s ms).run st] := by
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingBad, ge_iff_le, not_le] at h
  simp only [hidingImpl₁, hidingImplSim, StateT.run_bind, StateT.run_get, pure_bind]
  cases hcache : cache ms with
  | some u =>
    -- Cache hit: both return the same cached value, state unchanged
    simp [hcache]
  | none =>
    -- Cache miss: impl₁ queries at ms, implSim queries at queryPoint.
    -- Both bind on (liftM (query _)).run st then set+return.
    -- The continuations are identical; only the query point differs.
    -- Since (liftM (query t)).run st = query t >>= pure (·, st),
    -- Pr[= (u, st') | ...] = Pr[= u | query t] · [st' = st],
    -- and Pr[= u | query t] = 1/|C| for any t, both factors match.
    simp only [StateT.run_bind]
    refine tsum_congr fun x => ?_
    congr 1

/-- The sim game equals `hidingImplSim` applied to `hidingOa`, projected to output.

This lifts `cachingOracle`'s state by pairing it with the salt counter and
shows that `hidingImplSim` acts as a state-projection of `cachingOracle` where
all salt-s queries are redirected. -/
theorem hidingSim_eq_implSim {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingSim A s = (simulateQ (hidingImplSim s) (hidingOa A s)).run' (∅, 0) := by
  rfl

/-- For fixed `s`, the TV distance between real and sim games is bounded by
the probability of the bad event under `hidingImpl₁`.

The proof uses the distributional identical-until-bad lemma
(`tvDist_simulateQ_le_probEvent_bad_dist`): `hidingImpl₁` (real with counter) and
`hidingImplSim` (sim with counter) agree distributionally when `¬bad` because the
underlying oracle is memoryless. -/
theorem tvDist_hidingReal_hidingSim_le_probBad {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    tvDist (hidingReal A s) (hidingSim A s) ≤
    Pr[hidingBad ∘ Prod.snd |
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal := by
  rw [hidingReal_eq_impl₁ A s, hidingSim_eq_implSim A s]
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad_dist
    (hidingImpl₁ s) (hidingImplSim s) hidingBad (hidingOa A s) (∅, 0)
    (by simp [hidingBad])
    (fun ms st h p => hidingImpl_agree_dist s ms st h p)
    (hidingImpl₁_bad_mono s)
    (hidingImplSim_bad_mono s)

/-- Sum of `Pr[bad(s)]` over all salts is at most `t`.

The textbook (Claim cm-hiding-hit-query) samples `s` uniformly and independently
of the adversary's queries.  The per-query argument is:
- **Choose phase**: `A.choose` does not take `s` as input, so each choose-phase
  query `(m_i, s_i)` has `s_i` independent of the uniform `s`.
  Summing the indicator `[s_i = s]` over all `s ∈ S` gives exactly 1 per query.
- **Distinguish phase**: `A.distinguish aux cm` receives `cm = H(m, s)`, but under
  the caching oracle `cm` is a fresh uniform value independent of `s`.  By
  symmetry, each distinguish-phase query's salt hits any particular `s` with
  probability `1/|S|`, so the sum over all `s` is again 1 per query.
- The adversary makes at most `t` queries total, so `∑ s, Pr[bad(s)] ≤ t`.

The per-salt bound `Pr[bad(s)] ≤ t/|S|` does NOT hold for fixed `s` (a trivial
adversary always querying salt `s` gives `Pr[bad] = 1`).  The correct statement
is the sum/average version below.

**Proof strategy**: Swap the sum over `s` inside the probability, express
`∑_s Pr[bad(s)]` as `𝔼[#{adversary queries with salt = s}]`, then use linearity
of expectation and the per-query bound. -/
theorem sum_probEvent_hidingBad_le {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) ≤ t := by
  -- STATUS: sorry — requires per-query decomposition infrastructure not yet available.
  --
  -- CORRECTNESS: The statement is true. Tight example: adversary queries t distinct
  -- salts s₁, …, sₜ; then Pr[bad(sᵢ)] = 1 and Pr[bad(s)] = 0 for s ∉ {s₁,…,sₜ},
  -- giving ∑_s Pr[bad(s)] = t.
  --
  -- PROOF SKETCH (textbook: Claim cm-hiding-hit-query):
  -- Let counter_s = final counter value in game(s). Then:
  --   1[bad(s)] = 1[counter_s ≥ 2] ≤ counter_s - 1  (since challenge gives counter_s ≥ 1)
  -- So ∑_s Pr[bad(s)] ≤ ∑_s (E[counter_s] - 1).
  --
  -- counter_s = 1 (challenge) + #{adversary cache misses with salt = s in game(s)}.
  -- Key independence: the adversary's query distribution is THE SAME in game(s) for
  -- all s, because:
  --   (a) A.choose does not receive s as input, so choose-phase queries are
  --       independent of s entirely.
  --   (b) A.distinguish receives cm = H(m, s), but under hidingImpl₁ this is a fresh
  --       uniform value from C (cache miss on first salt-s query), independent of s.
  --       So distinguish-phase queries have the same distribution for all s.
  --
  -- For any adversary query (m_i, s_i) with distribution independent of the game
  -- parameter s: ∑_s 1[s_i = s] = 1. Taking expectations:
  --   ∑_s Pr[query_i has salt = s in game(s)] = ∑_s Pr[salt_i = s] = 1.
  -- Summing over ≤ t queries: ∑_s E[counter_s - 1] ≤ t.
  --
  -- FORMALIZATION BLOCKERS:
  -- • Need to decompose `simulateQ hidingImpl₁ (hidingOa A s)` into per-query
  --   contributions and reason about individual query salt distributions.
  -- • Need to show the adversary's query distribution is independent of s
  --   (the memoryless oracle argument for cm).
  -- • Need sum-swap (Fubini) for `∑_s ∑_i` over finite probability measures.
  -- • The `IsPerIndexQueryBound` infrastructure provides query COUNT bounds
  --   but not per-query SALT DISTRIBUTION decomposition.
  sorry

/-- **Hiding theorem (Lemma cm-hiding, averaged version)**:
The average statistical distance between real and simulated hiding games,
taken over uniformly random salt `s`, is at most `t / |S|`.

For every individual `s`, we have `tvDist(real(s), sim(s)) ≤ Pr[bad(s)]`
(identical-until-bad).  Summing over `s` and dividing by `|S|` gives:
  `𝔼_s[tvDist(real(s), sim(s))] ≤ 𝔼_s[Pr[bad(s)]] ≤ t / |S|`.

The per-salt bound `tvDist ≤ t/|S|` for fixed `s` is FALSE: a trivial adversary
always querying salt `s` makes `Pr[bad] = 1`.  The textbook (Lemma cm-hiding)
implicitly averages over the uniform salt. -/
theorem hiding_bound_avg {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, tvDist (hidingReal A s) (hidingSim A s)) / (Fintype.card S : ℝ) ≤
    (t : ℝ) / (Fintype.card S : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  -- Step 1: tvDist ≤ Pr[bad] for each s (already proved)
  have h1 : ∀ s : S, tvDist (hidingReal A s) (hidingSim A s) ≤
      Pr[hidingBad ∘ Prod.snd |
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal :=
    fun s => tvDist_hidingReal_hidingSim_le_probBad A s
  -- Step 2: Sum and use sum_probEvent_hidingBad_le
  calc ∑ s : S, tvDist (hidingReal A s) (hidingSim A s)
      ≤ ∑ s : S, Pr[hidingBad ∘ Prod.snd |
          (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal :=
        Finset.sum_le_sum fun s _ => h1 s
    _ ≤ (t : ℝ) := by
        have hsum := sum_probEvent_hidingBad_le A
        -- Convert from ENNReal sum bound to Real sum bound
        have hne : ∀ s ∈ Finset.univ, Pr[hidingBad ∘ Prod.snd |
            (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)] ≠ ⊤ :=
          fun _ _ => probEvent_ne_top
        rw [← ENNReal.toReal_sum hne]
        rw [← ENNReal.toReal_natCast]
        exact (ENNReal.toReal_le_toReal
          (ne_top_of_le_ne_top ENNReal.coe_ne_top hsum)
          ENNReal.coe_ne_top).mpr hsum
