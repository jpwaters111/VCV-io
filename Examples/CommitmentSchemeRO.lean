/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.CollisionResistance
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Notation
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Random Oracle Commitment Scheme — Caching Oracle Model

A commitment scheme in the random oracle model: `commit(m, s) = H(m, s)` where
`H : M × S → C` is a random oracle modeled via `cachingOracle`.

Following `docs/commitment_scheme.tex`, we prove three security properties:

1. **Binding** (Lemma cm-binding):
   `Pr[win] ≤ (t(t-1)+2) / (2|C|)` where `t` is the query bound.
   The adversary and verification share the **same** random oracle (via `cachingOracle`).

2. **Extractability** (Lemma cm-extractability):
   `Pr[win] ≤ (t(t-1)+2) / (2|C|)` with the same structure.
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

/-- `IsTotalQueryBound` for the binding game's inner computation: `t + 2`
(adversary's `t` queries + 2 verification queries). -/
private lemma bindingInner_totalBound {t : ℕ} (A : BindingAdversary M S C t) :
    IsTotalQueryBound (bindingInner A) (t+2) := by
  apply isTotalQueryBound_bind A.queryBound
  intro ⟨c, m₀, s₀, m₁, s₁⟩
  show IsTotalQueryBound _ 2
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun c₀ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ => trivial⟩

/-- In a collision-free cache, a value determines at most one query input. -/
private lemma cache_lookup_eq_of_noCollision
    {cache : QueryCache (CMOracle M S C)}
    {t₀ t₁ : (CMOracle M S C).Domain} {v : C}
    (hno : ¬ CacheHasCollision cache)
    (h₀ : cache t₀ = some v) (h₁ : cache t₁ = some v) :
    t₀ = t₁ := by
  by_contra hne
  exact hno ⟨t₀, t₁, v, v, hne, h₀, h₁, heq_of_eq rfl⟩

/-- If a fixed fresh query is the only way to win, its success probability is `1 / |C|`. -/
private lemma probEvent_from_fresh_query_le_inv
    (t : (CMOracle M S C).Domain)
    (target : C)
    (cache₀ : QueryCache (CMOracle M S C))
    (hfresh : cache₀ t = none)
    (cont : C → OracleComp (CMOracle M S C) Bool)
    (hzero : ∀ u, u ≠ target →
      Pr[fun z => z.1 = true |
        (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)] = 0) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle
        ((liftM (query (spec := CMOracle M S C) t)) >>= cont)).run cache₀] ≤
      (Fintype.card C : ℝ≥0∞)⁻¹ := by
  have hrun :
      (simulateQ cachingOracle
        ((liftM (query (spec := CMOracle M S C) t)) >>= cont)).run cache₀ =
      (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
        (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)) := by
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
    have hstep :
        (liftM (cachingOracle (spec := CMOracle M S C) t) :
          StateT (QueryCache (CMOracle M S C))
            (OracleComp (CMOracle M S C)) _).run cache₀ =
        (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
          pure (u, cache₀.cacheQuery t u) : OracleComp (CMOracle M S C) _) := by
      simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.run_bind, StateT.run_get, pure_bind, hfresh]
      show (StateT.lift (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t)) cache₀ >>= _) = _
      simp only [StateT.lift, bind_assoc, pure_bind,
        modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
    rw [hstep, bind_assoc]
    simpa [OracleQuery.cont_query]
  rw [hrun, probEvent_bind_eq_tsum]
  calc
    ∑' u, Pr[= u | (liftM (query (spec := CMOracle M S C) t) : OracleComp _ _)] *
        Pr[fun z => z.1 = true |
          (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)]
      ≤ ∑' u, if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by
        refine ENNReal.tsum_le_tsum fun u => ?_
        by_cases hu : u = target
        · calc
            Pr[= u | (liftM (query (spec := CMOracle M S C) t) : OracleComp _ _)] *
                Pr[fun z => z.1 = true |
                  (simulateQ cachingOracle (cont u)).run
                    (cache₀.cacheQuery t u)]
              ≤ Pr[= u | (liftM (query (spec := CMOracle M S C) t) : OracleComp _ _)] * 1 :=
                  mul_le_mul' le_rfl probEvent_le_one
            _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
                rw [mul_one]
                simpa using (probOutput_query (spec := CMOracle M S C) t u)
            _ = if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by simp [hu]
        · rw [hzero u hu]
          simp [hu]
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
        rw [tsum_ite_eq target]

/-- Under a collision-free adversary cache, winning requires one fresh verification
query to hit the commitment value `c`. -/
private lemma binding_rest_noCollision_le_inv
    (c : C) (m₀ m₁ : M) (s₀ s₁ : S)
    (cache₁ : QueryCache (CMOracle M S C))
    (hno : ¬ CacheHasCollision cache₁) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle
        ((liftM (query (spec := CMOracle M S C) (m₀, s₀))) >>= fun c₀ =>
          (liftM (query (spec := CMOracle M S C) (m₁, s₁))) >>= fun c₁ =>
          pure (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c)))).run cache₁] ≤
      (Fintype.card C : ℝ≥0∞)⁻¹ := by
  by_cases hneq : m₀ ≠ m₁
  · let q₀ : (CMOracle M S C).Domain := (m₀, s₀)
    let q₁ : (CMOracle M S C).Domain := (m₁, s₁)
    have hqne : q₀ ≠ q₁ := by
      intro hq
      exact hneq (Prod.ext_iff.mp hq).1
    by_cases hq₀_none : cache₁ q₀ = none
    · simpa [q₀, q₁] using probEvent_from_fresh_query_le_inv
        (t := q₀) (target := c) (cache₀ := cache₁) hq₀_none
        (cont := fun u =>
          (liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
            pure (decide (m₀ ≠ m₁) && (u == c) && (c₁ == c))) (by
          intro u hu
          apply probEvent_eq_zero
          intro z hz hwin
          simp only [simulateQ_bind, simulateQ_pure] at hz
          rw [StateT.run_bind] at hz
          rw [support_bind] at hz
          simp only [Set.mem_iUnion] at hz
          obtain ⟨⟨c₁, cache₂⟩, _, hz⟩ := hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz] at hwin
          simp [hneq, hu] at hwin)
    · rcases Option.ne_none_iff_exists'.mp hq₀_none with ⟨v₀, hq₀⟩
      have hrun₀ :
          (simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) q₀)) >>= fun c₀ =>
              (liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
              pure (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c)))).run cache₁ =
          (simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
              pure (decide (m₀ ≠ m₁) && (v₀ == c) && (c₁ == c)))).run cache₁ := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hcache :
            (liftM (cachingOracle (spec := CMOracle M S C) q₀) :
              StateT (QueryCache (CMOracle M S C))
                (OracleComp (CMOracle M S C)) _).run cache₁ =
            pure (v₀, cache₁) := by
          simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, hq₀, pure_bind, StateT.run_pure]
        rw [hcache, pure_bind]
        simp [OracleQuery.cont_query]
      by_cases hv₀ : v₀ = c
      · by_cases hq₁_none : cache₁ q₁ = none
        · rw [hrun₀]
          simpa [hv₀, q₁] using probEvent_from_fresh_query_le_inv
            (t := q₁) (target := c) (cache₀ := cache₁) hq₁_none
            (cont := fun u =>
              pure (decide (m₀ ≠ m₁) && (v₀ == c) && (u == c))) (by
              intro u hu
              simp [simulateQ_pure, StateT.run_pure, hv₀, hneq, hu])
        · rcases Option.ne_none_iff_exists'.mp hq₁_none with ⟨v₁, hq₁⟩
          have hv₁ : v₁ ≠ c := by
            intro hv₁
            apply hqne
            exact cache_lookup_eq_of_noCollision hno (hv₀ ▸ hq₀) (hv₁ ▸ hq₁)
          have hrun₁ :
              (simulateQ cachingOracle
                ((liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
                  pure (decide (m₀ ≠ m₁) && (v₀ == c) && (c₁ == c)))).run cache₁ =
              pure (decide (m₀ ≠ m₁) && (v₀ == c) && (v₁ == c), cache₁) := by
            simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
            have hcache :
                (liftM (cachingOracle (spec := CMOracle M S C) q₁) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run cache₁ =
                pure (v₁, cache₁) := by
              simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, hq₁, pure_bind, StateT.run_pure]
            rw [hcache, pure_bind]
            simp [OracleQuery.cont_query, StateT.run_pure]
          rw [hrun₀]
          rw [hrun₁]
          simp [hneq, hv₀, hv₁]
      · rw [hrun₀]
        refine le_of_eq_of_le ?_ (zero_le _)
        apply probEvent_eq_zero
        intro z hz hwin
        simp only [simulateQ_bind, simulateQ_pure] at hz
        rw [StateT.run_bind] at hz
        rw [support_bind] at hz
        simp only [Set.mem_iUnion] at hz
        obtain ⟨⟨c₁, cache₂⟩, _, hz⟩ := hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hwin
        simp [hneq, hv₀] at hwin
  · refine le_of_eq_of_le ?_ (zero_le _)
    apply probEvent_eq_zero
    intro z hz hwin
    simp only [simulateQ_bind, simulateQ_pure] at hz
    rw [StateT.run_bind] at hz
    rw [support_bind] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨⟨c₀, cache₂⟩, _, hz⟩ := hz
    rw [StateT.run_bind] at hz
    rw [support_bind] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨⟨c₁, cache₃⟩, _, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hwin
    simp [hneq] at hwin

/-- Winning the binding game either implies a collision in the adversary's cache
(the cache after `A.run`, before verification) or that a fresh verification query
matched the commitment `c`. We bound each case separately:
- Case 1 (collision in adversary's cache): ≤ `t(t-1)/(2|C|)` by tight birthday bound
- Case 2 (no collision, fresh query matches `c`): ≤ `1/|C|` by unpredictability -/
private lemma binding_win_le_advCollision_add_fresh {t : ℕ}
    (A : BindingAdversary M S C t) :
    Pr[fun z => z.1 = true | bindingGame A] ≤
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle A.run).run ∅] +
    (Fintype.card C : ℝ≥0∞)⁻¹ := by
  let restPart : (C × M × S × M × S) → OracleComp (CMOracle M S C) Bool
    | (c, m₀, s₀, m₁, s₁) =>
        (liftM (query (spec := CMOracle M S C) (m₀, s₀))) >>= fun c₀ =>
          (liftM (query (spec := CMOracle M S C) (m₁, s₁))) >>= fun c₁ =>
          pure (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c))
  have hdecomp : bindingInner A = A.run >>= restPart := by
    simp [bindingInner, restPart]
  rw [bindingGame_eq, hdecomp, simulateQ_bind, StateT.run_bind]
  simpa using
    (probEvent_bind_le_add
      (mx := (simulateQ cachingOracle A.run).run ∅)
      (my := fun x => (simulateQ cachingOracle (restPart x.1)).run x.2)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => z.1 ≠ true)
      (ε₁ := Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle A.run).run ∅])
      (ε₂ := (Fintype.card C : ℝ≥0∞)⁻¹)
      (by simpa)
      (by
        rintro ⟨⟨c, m₀, s₀, m₁, s₁⟩, cache₁⟩ _ hno
        simpa [restPart] using binding_rest_noCollision_le_inv c m₀ m₁ s₀ s₁ cache₁ hno))

/-- **Binding theorem (Lemma cm-binding)**: `Pr[win] ≤ (t(t-1)+2) / (2|C|)`.

Decomposes via `binding_win_le_advCollision_add_fresh` into birthday bound on the
adversary's `t` queries (`t(t-1)/(2|C|)`) plus unpredictability (`1/|C|`). -/
theorem binding_bound {t : ℕ} (A : BindingAdversary M S C t) :
    Pr[fun z => z.1 = true | bindingGame A] ≤
    ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
  calc Pr[fun z => z.1 = true | bindingGame A]
      ≤ Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle A.run).run ∅] +
        (Fintype.card C : ℝ≥0∞)⁻¹ := binding_win_le_advCollision_add_fresh A
    _ ≤ ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
        (Fintype.card C : ℝ≥0∞)⁻¹ := by
        gcongr
        exact probEvent_cacheCollision_le_birthday_total_tight A.run t A.queryBound
          Fintype.card_pos (fun _ => le_refl _)
    _ = ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
        -- Arithmetic: a/(2C) + 1/C = a/(2C) + 2/(2C) = (a+2)/(2C)
        set D := (2 * (Fintype.card C : ℝ≥0∞))
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        have hD_inv : (Fintype.card C : ℝ≥0∞)⁻¹ = D⁻¹ * 2 := by
          simp only [D]
          rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)),
            mul_comm (2 : ℝ≥0∞)⁻¹ _, mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
        rw [hD_inv, ← mul_add]
        congr 1
        push_cast
        ring

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

/-- The extractability game in the random oracle model, parameterized by an extractor `E`.

Phase 1 (commit): Run `A.commit` with a logging oracle layered on top
  (to capture the trace), all within `cachingOracle`.
Phase 2 (open): Run `A.open_` with the same oracle (shared cache).
Verification: Query `H(m, s)` and compare to `cm`.
Extraction: Apply `E` to the commitment and commit-phase trace.

Win: Check passes AND (extractor found nothing OR found a different opening). -/
def extractabilityGame {AUX : Type} {t : ℕ}
    (E : C → QueryLog (CMOracle M S C) → Option (M × S))
    (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) (Bool × QueryCache (CMOracle M S C)) :=
  (simulateQ cachingOracle (do
    -- Phase 1: commit with logging to get trace
    let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
    -- Phase 2: open
    let (m, s) ← A.open_ aux
    -- Verify: query H(m,s) using the same oracle
    let c ← query (spec := CMOracle M S C) (m, s)
    -- Extract from the commit-phase trace
    let extracted := E cm tr
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
    extractabilityGame CMExtract A =
    (simulateQ cachingOracle (extractabilityInner A)).run ∅ := rfl

/-- Tagged inner computation: returns `(win, isNoneCase)` where `isNoneCase = true`
iff the extractor found no matching entry in the commit trace.

This decomposition allows separate handling of the two win cases:
- `some` case (`win ∧ ¬isNoneCase`): implies cache collision (pointwise)
- `none` case (`win ∧ isNoneCase`): requires probabilistic bound -/
private def extractabilityInner_tagged {AUX : Type} {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) (Bool × Bool) := do
  let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
  let (m, s) ← A.open_ aux
  let c ← query (spec := CMOracle M S C) (m, s)
  let extracted := CMExtract cm tr
  return (match extracted with
    | some (m', s') => ((c == cm) && decide ((m', s') ≠ (m, s)), false)
    | none => ((c == cm), true))

/-- The untagged inner computation is the first projection of the tagged one. -/
private lemma extractabilityInner_eq_fst_tagged {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    extractabilityInner A = Prod.fst <$> extractabilityInner_tagged A := by
  simp only [extractabilityInner, extractabilityInner_tagged, map_eq_bind_pure_comp,
    bind_assoc, Function.comp, pure_bind]
  congr 1; ext ⟨⟨cm, aux⟩, tr⟩
  congr 1; ext ⟨m, s⟩
  congr 1; ext c
  simp only [CMExtract]
  cases tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => simp
  | none => simp

/-- The some-case win (extractor found a different opening) implies cache collision.

When `CMExtract` finds an entry `(m', s')` in the commit trace with `H(m', s') = cm`,
and verification gives `H(m, s) = cm` with `(m', s') ≠ (m, s)`, both distinct inputs
map to `cm` in the final cache. -/
private lemma extractability_someWin_implies_collision {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    ∀ z ∈ support ((simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅),
      z.1.1 = true → z.1.2 = false → CacheHasCollision z.2 := by
  intro z hz hwin hsome
  simp only [extractabilityInner_tagged, simulateQ_bind, simulateQ_pure] at hz
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
  rw [hz] at hwin hsome ⊢
  -- cache₃ has entry at (m, s) with value c
  rw [simulateQ_cachingOracle_query] at hmem₃
  have hcache₃ : cache₃ (m, s) = some c :=
    cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
  -- Cache monotonicity: cache₂ ≤ cache₃
  have hcache_mono₂₃ : cache₂ ≤ cache₃ := by
    have hmem₃_co : (c, cache₃) ∈ support
        ((cachingOracle (spec := CMOracle M S C) (m, s)).run cache₂) := hmem₃
    unfold cachingOracle at hmem₃_co
    exact QueryImpl.withCaching_cache_le
      (QueryImpl.ofLift (CMOracle M S C) (OracleComp (CMOracle M S C)))
      (m, s) cache₂ (c, cache₃) hmem₃_co
  -- The tag tells us this is the some case
  unfold CMExtract at hwin hsome
  cases hfind : (tr.find? (fun entry => decide (entry.2 = cm))) with
  | none => simp [hfind] at hsome
  | some entry =>
    simp only [hfind] at hwin
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
    obtain ⟨hceq, hne⟩ := hwin
    -- entry.2 = cm by the find? predicate
    have hentry_cm : entry.2 = cm := by
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
    -- cache₁ ≤ cache₂ (simulateQ cachingOracle on open_ only grows cache)
    have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
      simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
    -- cache₃ entry.1 = some entry.2 (by monotonicity chain cache₁ ≤ cache₂ ≤ cache₃)
    have hcache₃_entry : cache₃ entry.1 = some entry.2 :=
      hcache_mono₂₃ (hcache_mono₁₂ hcache₁_entry)
    -- Collision: entry.1 and (m,s) both map to cm in cache₃
    exact ⟨entry.1, (m, s), entry.2, c, hne, hcache₃_entry, hcache₃,
      heq_of_eq (by rw [hentry_cm, hceq])⟩

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
  have hbind :
      IsTotalQueryBound
        (((simulateQ loggingOracle A.commit).run) >>= fun
          | ((cm, aux), tr) =>
              A.open_ aux >>= fun (m, s) =>
                query (spec := CMOracle M S C) (m, s) >>= fun c =>
                  have extracted : Option (M × S) := CMExtract cm tr
                  pure
                    (match extracted with
                    | some (m', s') => c == cm && decide ((m', s') ≠ (m, s))
                    | none => c == cm))
        (A.t₁ + (A.t₂ + 1)) := by
    apply isTotalQueryBound_bind h1
    intro ⟨⟨cm, aux⟩, tr⟩
    apply isTotalQueryBound_bind (A.openBound aux)
    intro ⟨m, s⟩
    show IsTotalQueryBound _ 1
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  exact hbind.mono (by
    have := A.totalBound
    omega)

/-- The tagged inner computation has the same query bound as the untagged one. -/
private lemma extractabilityInner_tagged_totalBound {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    IsTotalQueryBound (extractabilityInner_tagged A) (t + 1) := by
  have h := extractabilityInner_totalBound A
  rw [extractabilityInner_eq_fst_tagged] at h
  rwa [show IsTotalQueryBound (Prod.fst <$> extractabilityInner_tagged A) (t + 1) ↔
    IsTotalQueryBound (extractabilityInner_tagged A) (t + 1) from
    isQueryBound_map_iff _ _ _ _ _] at h

/-- The some-case win event on the tagged game implies cache collision.

Wraps `extractability_someWin_implies_collision` for use with `probEvent_mono`. -/
private lemma extractability_someWin_le_collision {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1.1 = true ∧ z.1.2 = false |
      (simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅] ≤
    Pr[fun z => CacheHasCollision z.2 |
      (simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅] :=
  probEvent_mono fun z hz ⟨hwin, hsome⟩ =>
    extractability_someWin_implies_collision A z hz hwin hsome

/-- The none-case win event has probability at most `(t+1)/|C|`.

When `CMExtract` returns `none`, no commit-phase query returned `cm`. Winning
requires the verification query at `(m,s)` to return `cm`. The value at `(m,s)` was
determined by a single fresh uniform draw — either during the open phase or at
verification time. However, the open-phase adversary can adaptively choose `(m,s)`:
it can query multiple points and output whichever one returned `cm`. With at most
`t₂ + 1` chances (open queries + verification), by union bound the probability
that any fresh draw equals `cm` is `≤ (t₂ + 1)/|C| ≤ (t + 1)/|C|`.

The inner computation has total query bound `t + 1` (commit ≤ t₁, open ≤ t₂,
verify = 1, total ≤ t + 1). The proof uses the per-query uniformity bound
(`probEvent_log_entry_eq_le`) and a union bound over all queries.

For the main theorem with `t ≥ 3`, the three-case textbook analysis gives the
tighter `(t(t-1)+2)/(2|C|)` bound. -/
private lemma extractability_noneWin_le_inv_card {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1.1 = true ∧ z.1.2 = true |
      (simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅] ≤
    (↑(t + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
  -- Step 1: Decompose extractabilityInner_tagged as commitPart >>= restPart.
  let commitPart := (simulateQ loggingOracle A.commit).run
  let restPart := fun (x : (C × AUX) × QueryLog (CMOracle M S C)) =>
    let ((cm, aux), tr) := x
    (A.open_ aux >>= fun (m, s) =>
      (query (spec := CMOracle M S C) (m, s)) >>= fun c =>
        let extracted := CMExtract cm tr
        pure (match extracted with
          | some (m', s') => ((c == cm) && decide ((m', s') ≠ (m, s)), false)
          | none => ((c == cm), true)))
  have hdecomp : extractabilityInner_tagged A = commitPart >>= restPart := by
    simp only [extractabilityInner_tagged, commitPart, restPart]
  rw [hdecomp, simulateQ_bind, StateT.run_bind]
  -- Step 2: Bound via probEvent_bind_eq_tsum
  rw [probEvent_bind_eq_tsum]
  -- For each commit outcome, Pr[win ∧ none | rest] ≤ (t+1)/|C|
  -- Since ∑ Pr[=x] ≤ 1, the total is ≤ (t+1)/|C|
  calc ∑' x, Pr[= x | (simulateQ cachingOracle commitPart).run ∅] *
          Pr[fun z => z.1.1 = true ∧ z.1.2 = true |
            (simulateQ cachingOracle (restPart x.1)).run x.2]
      ≤ ∑' x, Pr[= x | (simulateQ cachingOracle commitPart).run ∅] *
          ((↑(t + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) := by
        apply ENNReal.tsum_le_tsum; intro ⟨⟨⟨cm, aux⟩, tr⟩, cache₁⟩
        -- For each commit outcome, bound the rest's probability
        by_cases hx : ((⟨⟨cm, aux⟩, tr⟩, cache₁) :
            ((C × AUX) × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C)) ∈
            support ((simulateQ cachingOracle commitPart).run ∅)
        · -- In support: bound the conditional probability
          apply mul_le_mul' le_rfl
          simp only [restPart]
          cases hfind : CMExtract cm tr with
          | some ms =>
            -- Some case: tag = false, so event (tag = true) is impossible
            apply le_of_eq_of_le _ (zero_le _)
            apply probEvent_eq_zero
            intro z hz ⟨_, h2⟩
            -- z is in support of computation returning (_, false)
            -- So z.1.2 = false, contradicting h2 : z.1.2 = true
            simp only [simulateQ_bind, simulateQ_pure] at hz
            rw [StateT.run_bind] at hz
            rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
            obtain ⟨⟨⟨m, s⟩, cache₂⟩, _, hz⟩ := hz
            rw [StateT.run_bind] at hz
            rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
            obtain ⟨⟨c, cache₃⟩, _, hz⟩ := hz
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            have := congr_arg (·.1.2) hz
            simp at this -- this : false = true from z.1.2 path
            rw [this] at h2; exact Bool.false_ne_true h2
          | none =>
            -- None case: event is (c == cm, true), i.e., c = cm
            -- Step A: Show no cache₁ entry equals cm.
            have hno_cm : ∀ (t₀ : (CMOracle M S C).Domain) (v : (CMOracle M S C).Range t₀),
                cache₁ t₀ = some v → ¬HEq v cm := by
              intro t₀ v hcache₁ hheq
              have hlog := cache_entry_in_log_or_initial A.commit ∅
                (((cm, aux), tr), cache₁) hx
              have h := hlog t₀ v hcache₁
              rcases h with h_in_empty | ⟨entry, hentry_mem, hentry_eq, hentry_heq⟩
              · -- cache₀ = ∅, so ∅ t₀ = some v is impossible
                exact absurd h_in_empty (by simp)
              · -- entry ∈ tr with entry.1 = t₀ and HEq entry.2 v
                -- HEq v cm, so entry.2 = cm, contradicting CMExtract cm tr = none
                have hentry_cm : entry.2 = cm := eq_of_heq (hentry_heq.trans hheq)
                -- List.find? finds entry (since entry.2 = cm and entry ∈ tr)
                have hfound : (tr.find? (fun e => decide (e.2 = cm))).isSome = true := by
                  rw [List.find?_isSome]
                  exact ⟨entry, hentry_mem, by simp [hentry_cm]⟩
                -- But CMExtract cm tr = none means find? returned none
                simp only [CMExtract] at hfind
                cases hf : tr.find? (fun e => decide (e.2 = cm)) with
                | some _ => simp [hf] at hfind
                | none => simp [hf] at hfound
            -- Step B: Bound via probEvent_cache_has_value_le
            have hrest_bound : IsTotalQueryBound
                (A.open_ aux >>= fun (m, s) =>
                  (query (spec := CMOracle M S C) (m, s)) >>= fun c =>
                    pure ((c == cm), true)) (t + 1) := by
              have hbind :
                  IsTotalQueryBound
                    (A.open_ aux >>= fun (m, s) =>
                      (query (spec := CMOracle M S C) (m, s)) >>= fun c =>
                        pure ((c == cm), true))
                    (A.t₂ + 1) := by
                apply isTotalQueryBound_bind (A.openBound aux)
                intro ⟨m, s⟩
                show IsTotalQueryBound _ 1
                rw [isTotalQueryBound_query_bind_iff]
                exact ⟨Nat.one_pos, fun _ => trivial⟩
              exact hbind.mono (by
                have := A.totalBound
                omega)
            calc Pr[fun z => z.1.1 = true ∧ z.1.2 = true |
                    (simulateQ cachingOracle (A.open_ aux >>= fun (m, s) =>
                      query (spec := CMOracle M S C) (m, s) >>= fun c =>
                        pure ((c == cm), true))).run cache₁]
                ≤ Pr[fun z => ∃ t₀ : (CMOracle M S C).Domain,
                    ∃ v : (CMOracle M S C).Range t₀,
                    z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v cm |
                    (simulateQ cachingOracle (A.open_ aux >>= fun (m, s) =>
                      query (spec := CMOracle M S C) (m, s) >>= fun c =>
                        pure ((c == cm), true))).run cache₁] := by
                  apply probEvent_mono
                  intro z hz ⟨hwin, _⟩
                  simp only [simulateQ_bind, simulateQ_pure] at hz
                  rw [StateT.run_bind] at hz
                  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
                  obtain ⟨⟨⟨m, s⟩, cache₂⟩, hmem₂, hz⟩ := hz
                  rw [StateT.run_bind] at hz
                  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
                  obtain ⟨⟨c, cache₃⟩, hmem₃, hz⟩ := hz
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                  -- z = (((c == cm), true), cache₃)
                  have hc_eq : c = cm := by
                    have h1 : z.1.1 = (c == cm) := congr_arg (·.1.1) hz
                    rw [h1] at hwin; exact beq_iff_eq.mp hwin
                  rw [simulateQ_cachingOracle_query] at hmem₃
                  have hcache₃ : cache₃ (m, s) = some c :=
                    cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
                  have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
                    simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
                  have hcache₁_none : cache₁ (m, s) = none := by
                    by_contra h
                    push_neg at h; obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
                    have hcache₂_ms := hcache_mono₁₂ hv
                    simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get,
                      pure_bind, hcache₂_ms, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff] at hmem₃
                    have hcv : c = v := (Prod.mk.inj hmem₃).1
                    exact hno_cm (m, s) v hv (heq_of_eq (hcv ▸ hc_eq))
                  have hcache_final_eq : z.2 = cache₃ := congr_arg (·.2) hz
                  rw [hcache_final_eq]
                  exact ⟨(m, s), c, hcache₃, hcache₁_none, heq_of_eq hc_eq⟩
              _ ≤ (↑(t + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ :=
                  probEvent_cache_has_value_le _ (t + 1) hrest_bound
                    (fun _ => le_refl _) cm cache₁ hno_cm
        · -- Not in support: Pr[=x] = 0, so the product is 0
          rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul]; exact zero_le _
    _ = (∑' x, Pr[= x | (simulateQ cachingOracle commitPart).run ∅]) *
          ((↑(t + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * ((↑(t + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) :=
        mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = (↑(t + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := one_mul _

/-- Arithmetic: `a/(2C) + b/C = (a + 2b)/(2C)`. -/
private lemma add_div_two_card
    (a b : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
      ((b : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ =
    ((a + 2 * b : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
  set D := (2 * (Fintype.card C : ℝ≥0∞))
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [mul_comm (((b : ℕ) : ℝ≥0∞)) ((Fintype.card C : ℝ≥0∞)⁻¹)]
  have hD_inv : (Fintype.card C : ℝ≥0∞)⁻¹ = D⁻¹ * 2 := by
    simp only [D]
    rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)),
      mul_comm (2 : ℝ≥0∞)⁻¹ _, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
  rw [hD_inv, mul_assoc, ← mul_add]
  congr 1
  push_cast
  ring

/-- Textbook arithmetic: if `t₁ + t₂ ≤ t` and `t ≥ 3`, then
`t₁(t₁-1) + 2t₂ ≤ t(t-1)`. -/
private lemma extractability_num_le
    {t t₁ t₂ : ℕ} (ht : 3 ≤ t) (hbound : t₁ + t₂ ≤ t) :
    t₁ * (t₁ - 1) + 2 * t₂ ≤ t * (t - 1) := by
  have ht₁_le : t₁ ≤ t := by omega
  have ht₂_le : t₂ ≤ t - t₁ := Nat.le_sub_of_add_le' hbound
  have htwo : 2 ≤ t - 1 := by omega
  calc
    t₁ * (t₁ - 1) + 2 * t₂ ≤ t₁ * (t₁ - 1) + 2 * (t - t₁) := by
      gcongr
    _ ≤ t₁ * (t - 1) + (t - 1) * (t - t₁) := by
      apply add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ht₁_le 1)
      · simpa [Nat.mul_comm] using Nat.mul_le_mul_right (t - t₁) htwo
    _ = t * (t - 1) := by
      rw [Nat.mul_comm (t - 1) (t - t₁), ← Nat.add_mul, Nat.add_sub_of_le ht₁_le]

set_option maxHeartbeats 400000 in
/-- The post-commit/open extractability computation for a fixed commit outcome. -/
private def extractabilityRestOa {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    (cm : C) (aux : AUX) (tr : QueryLog (CMOracle M S C)) :
    OracleComp (CMOracle M S C) Bool :=
  A.open_ aux >>= fun (m, s) =>
    (liftM (query (spec := CMOracle M S C) (m, s))) >>= fun c =>
    let extracted := CMExtract cm tr
    pure (match extracted with
      | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
      | none => (c == cm))

set_option maxHeartbeats 400000 in
/-- Under a collision-free commit cache, any extractability win must create a fresh
post-commit cache entry equal to the commitment value. -/
private lemma extractability_rest_win_implies_fresh_cm {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    {cm : C} {aux : AUX} {tr : QueryLog (CMOracle M S C)}
    {cache₁ : QueryCache (CMOracle M S C)}
    (hx : (((cm, aux), tr), cache₁) ∈
      support ((simulateQ cachingOracle ((simulateQ loggingOracle A.commit).run)).run ∅))
    (hno : ¬ CacheHasCollision cache₁) :
  ∀ z ∈ support ((simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁),
      z.1 = true →
      ∃ t₀ : (CMOracle M S C).Domain, ∃ v : (CMOracle M S C).Range t₀,
        z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v cm := by
  intro z hz hwin
  unfold extractabilityRestOa at hz
  rw [simulateQ_bind] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨m, s⟩, cache₂⟩, hmem₂, hz⟩ := hz
  rw [simulateQ_bind] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, cache₃⟩, hmem₃, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz] at hwin
  unfold CMExtract at hwin
  cases hfind : tr.find? (fun entry => decide (entry.2 = cm)) with
  | none =>
      simp only [hfind, beq_iff_eq] at hwin
      have hc_eq : c = cm := hwin
      rw [simulateQ_cachingOracle_query] at hmem₃
      have hcache₃ : cache₃ (m, s) = some c :=
        cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
      have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
        simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
      have hcache₁_none : cache₁ (m, s) = none := by
        by_contra h
        push_neg at h
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
        have hno_cm : ∀ (t₀ : (CMOracle M S C).Domain) (v' : (CMOracle M S C).Range t₀),
            cache₁ t₀ = some v' → ¬HEq v' cm := by
          intro t₀ v' hcache₁ hheq
          have hlog := cache_entry_in_log_or_initial A.commit ∅
            (((cm, aux), tr), cache₁) hx
          have h' := hlog t₀ v' hcache₁
          rcases h' with h_empty | ⟨entry, hentry_mem, _, hentry_heq⟩
          · exact absurd h_empty (by simp)
          · have hentry_cm : entry.2 = cm := eq_of_heq (hentry_heq.trans hheq)
            have hfound : (tr.find? (fun e => decide (e.2 = cm))).isSome = true := by
              rw [List.find?_isSome]
              exact ⟨entry, hentry_mem, by simp [hentry_cm]⟩
            simp [hfind] at hfound
        have hcache₂_ms := hcache_mono₁₂ hv
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get,
          pure_bind, hcache₂_ms, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem₃
        have hcv : c = v := (Prod.mk.inj hmem₃).1
        exact hno_cm (m, s) v hv (heq_of_eq (hcv ▸ hc_eq))
      have hcache_final_eq : z.2 = cache₃ := congr_arg (·.2) hz
      rw [hcache_final_eq]
      exact ⟨(m, s), c, hcache₃, hcache₁_none, heq_of_eq hc_eq⟩
  | some entry =>
      simp only [hfind, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
      obtain ⟨hc_eq, hne⟩ := hwin
      rw [simulateQ_cachingOracle_query] at hmem₃
      have hcache₃ : cache₃ (m, s) = some c :=
        cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
      have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
        simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
      have hentry_cm : entry.2 = cm := by
        have hfound := List.find?_some hfind
        simpa only [decide_eq_true_eq] using hfound
      have hentry_mem : entry ∈ tr := List.mem_of_find?_eq_some hfind
      have hlog_cache := (OracleComp.log_entry_in_cache_and_mono A.commit ∅
        (((cm, aux), tr), cache₁) hx).1
      have hcache₁_entry : cache₁ entry.1 = some entry.2 :=
        hlog_cache entry hentry_mem
      have hcache₁_none : cache₁ (m, s) = none := by
        by_contra h
        push_neg at h
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
        have hcache₂_ms := hcache_mono₁₂ hv
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get,
          pure_bind, hcache₂_ms, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem₃
        have hcv : c = v := (Prod.mk.inj hmem₃).1
        have hv_entry : v = entry.2 := by
          rw [← hcv, hc_eq, ← hentry_cm]
        have hcache₁_ms : cache₁ (m, s) = some entry.2 := by
          simpa [hv_entry] using hv
        have hsame : entry.1 = (m, s) :=
          cache_lookup_eq_of_noCollision hno hcache₁_entry hcache₁_ms
        exact hne hsame
      have hcache_final_eq : z.2 = cache₃ := congr_arg (·.2) hz
      rw [hcache_final_eq]
      exact ⟨(m, s), c, hcache₃, hcache₁_none, heq_of_eq hc_eq⟩

set_option maxHeartbeats 1000000 in
/-- Conditioned on a collision-free commit trace, the later extractability failure
probability is bounded by the fresh-hit term `(t₂ + 1) / |C|`. -/
private lemma extractability_rest_noCollision_le_inv {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    (cm : C) (aux : AUX) (tr : QueryLog (CMOracle M S C))
    (cache₁ : QueryCache (CMOracle M S C))
    (hx : (((cm, aux), tr), cache₁) ∈
      support ((simulateQ cachingOracle ((simulateQ loggingOracle A.commit).run)).run ∅))
    (hno : ¬ CacheHasCollision cache₁) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁] ≤
      (↑(A.t₂ + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
  have hrest_bound : IsTotalQueryBound
      (extractabilityRestOa A cm aux tr) (A.t₂ + 1) := by
    apply isTotalQueryBound_bind (A.openBound aux)
    intro ⟨m, s⟩
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  calc
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁]
      ≤ Pr[fun z => ∃ t₀ : (CMOracle M S C).Domain, ∃ v : (CMOracle M S C).Range t₀,
            z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v cm |
          (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁] := by
          apply probEvent_mono
          intro z hz hwin
          exact extractability_rest_win_implies_fresh_cm A hx hno z hz hwin
    _ ≤ (↑(A.t₂ + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ :=
      OracleComp.probEvent_cache_has_value_le_of_noCollision
        (oa := extractabilityRestOa A cm aux tr)
        (n := A.t₂ + 1) hrest_bound (fun _ => le_refl _)
        cm cache₁ hno

/-- The extraction error decomposes into collision in commit trace plus fresh query
matching `cm`. The commit trace has `≤ t₁` entries (birthday bound `t₁(t₁-1)/(2|C|)`),
and the open+verify phase has `≤ t₂+1` fresh queries matching `cm` (`(t₂+1)/|C|`).
Maximizing `t₁(t₁-1)/2 + t₂ + 1` over `t₁+t₂ ≤ t` gives `max{t+1, t(t-1)/2+1}`.
For `t ≥ 3` this is `t(t-1)/2+1`, yielding `(t(t-1)+2)/(2|C|)`. -/
private lemma extractability_win_le_textbook_bound {t : ℕ} (ht : 3 ≤ t)
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1 = true | extractabilityGame CMExtract A] ≤
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
    (Fintype.card C : ℝ≥0∞)⁻¹ := by
  let commitPart := (simulateQ loggingOracle A.commit).run
  let restPart := fun (x : (C × AUX) × QueryLog (CMOracle M S C)) =>
    let ((cm, aux), tr) := x
    extractabilityRestOa A cm aux tr
  have hdecomp : extractabilityInner A = commitPart >>= restPart := by
    simp [extractabilityInner, commitPart, restPart, extractabilityRestOa]
  have hcommit_bound : IsTotalQueryBound commitPart A.t₁ :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff A.commit A.t₁).mpr A.commitBound
  have hmain :
      Pr[fun z => z.1 = true |
        (simulateQ cachingOracle commitPart).run ∅ >>= fun x =>
          (simulateQ cachingOracle (restPart x.1)).run x.2] ≤
        ((A.t₁ * (A.t₁ - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
        ((A.t₂ + 1 : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
    simpa [not_not] using
      (probEvent_bind_le_add
        (mx := (simulateQ cachingOracle commitPart).run ∅)
        (my := fun x => (simulateQ cachingOracle (restPart x.1)).run x.2)
        (p := fun x => ¬ CacheHasCollision x.2)
        (q := fun z => z.1 ≠ true)
        (ε₁ := ((A.t₁ * (A.t₁ - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C))
        (ε₂ := ((A.t₂ + 1 : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹)
        (by
          simpa using
            (probEvent_cacheCollision_le_birthday_total_tight commitPart A.t₁
              hcommit_bound Fintype.card_pos (fun _ => le_refl _)))
        (by
          rintro ⟨⟨⟨cm, aux⟩, tr⟩, cache₁⟩ hx hno
          simpa [restPart, extractabilityRestOa] using
            extractability_rest_noCollision_le_inv A cm aux tr cache₁ hx hno))
  rw [extractabilityGame_eq, hdecomp, simulateQ_bind, StateT.run_bind]
  calc
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle commitPart).run ∅ >>= fun x =>
        (simulateQ cachingOracle (restPart x.1)).run x.2]
      ≤ ((A.t₁ * (A.t₁ - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
          ((A.t₂ + 1 : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := hmain
    _ = ((A.t₁ * (A.t₁ - 1) + 2 * (A.t₂ + 1) : ℕ) : ℝ≥0∞) /
          (2 * Fintype.card C) := by
          simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            add_div_two_card (C := C) (A.t₁ * (A.t₁ - 1)) (A.t₂ + 1)
    _ ≤ ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
          have hnat :
              A.t₁ * (A.t₁ - 1) + 2 * (A.t₂ + 1) ≤ t * (t - 1) + 2 := by
            simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              Nat.add_le_add_right (extractability_num_le ht A.totalBound) 2
          gcongr
    _ = ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
          (Fintype.card C : ℝ≥0∞)⁻¹ := by
          symm
          simpa [Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            add_div_two_card (C := C) (t * (t - 1)) 1

/-- **Extractability theorem (Lemma cm-extractability)**: for `t ≥ 3`,
`Pr[win] ≤ (t(t-1)+2) / (2|C|)`. Combines the case-split decomposition
`extractability_win_le_textbook_bound` with arithmetic. -/
theorem extractability_bound {t : ℕ} (ht : 3 ≤ t)
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1 = true | extractabilityGame CMExtract A] ≤
    ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
  calc Pr[fun z => z.1 = true | extractabilityGame CMExtract A]
      ≤ ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
        (Fintype.card C : ℝ≥0∞)⁻¹ := extractability_win_le_textbook_bound ht A
    _ = ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
        set D := (2 * (Fintype.card C : ℝ≥0∞))
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        have hD_inv : (Fintype.card C : ℝ≥0∞)⁻¹ = D⁻¹ * 2 := by
          simp only [D]
          rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)),
            mul_comm (2 : ℝ≥0∞)⁻¹ _, mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
        rw [hD_inv, ← mul_add]
        congr 1
        push_cast
        ring

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

/-- A hiding adversary with two phases and total adversary query budget `t`.

The computation includes one additional challenge query between the phases, so
the full two-phase game computation has total bound `t + 1`. -/
structure HidingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- Phase 1: choose a message and auxiliary state (with oracle access). -/
  choose : OracleComp (CMOracle M S C) (M × AUX)
  /-- Phase 2: given auxiliary state and a commitment, output a guess bit. -/
  distinguish : AUX → C → OracleComp (CMOracle M S C) Bool
  /-- Total query bound for the full two-phase game computation, including the
  single challenge query between the phases. Equivalently, the adversary itself
  makes at most `t` oracle queries across both phases. -/
  totalBound : ∀ s : S, IsTotalQueryBound
    (choose >>= fun x =>
      let (m, aux) := x
      (liftM (query (spec := CMOracle M S C) (m, s)) >>= fun cm =>
        distinguish aux cm))
    (t + 1)

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

/-- Shared counted hiding implementation: same cache semantics as `cachingOracle`,
with a per-salt miss counter `S → ℕ` updated at the queried salt on cache miss. -/
def hidingImplCountAll :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × (S → ℕ)) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, counts) ← get
    match cache ms with
    | some u => return u
    | none => do
      let u ← (liftM (query (spec := CMOracle M S C) ms) :
        StateT (QueryCache (CMOracle M S C) × (S → ℕ)) (OracleComp (CMOracle M S C)) C)
      let counts' := Function.update counts ms.2 (counts ms.2 + 1)
      set (cache.cacheQuery ms u, counts')
      return u

private lemma hidingImpl₁_step_totalBound (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) :
    IsTotalQueryBound ((hidingImpl₁ s ms).run st) 1 := by
  obtain ⟨cache, cnt⟩ := st
  cases hcache : cache ms with
  | some u =>
      simpa [hidingImpl₁, hcache, StateT.run_bind, StateT.run_get, pure_bind] using
        (show IsTotalQueryBound
            (pure (u, (cache, cnt)) :
              OracleComp (CMOracle M S C) (C × (QueryCache (CMOracle M S C) × ℕ))) 1 from
          trivial)
  | none =>
      simpa [hidingImpl₁, hcache, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_set, StateT.run_pure, OracleComp.liftM_run_StateT, MonadLift.monadLift]
        using
          (show IsTotalQueryBound
              (((liftM (query (spec := CMOracle M S C) ms) :
                  OracleComp (CMOracle M S C) C) >>= fun u =>
                pure (u, (cache.cacheQuery ms u,
                  if ms.2 == s then cnt + 1 else cnt))))
              1 from by
            rw [isTotalQueryBound_query_bind_iff]
            exact ⟨Nat.one_pos, fun _ => trivial⟩)

private lemma hidingImplCountAll_step_totalBound (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    IsTotalQueryBound ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st) 1 := by
  obtain ⟨cache, counts⟩ := st
  cases hcache : cache ms with
  | some u =>
      simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind] using
        (show IsTotalQueryBound
            (pure (u, (cache, counts)) :
              OracleComp (CMOracle M S C)
                (C × (QueryCache (CMOracle M S C) × (S → ℕ)))) 1 from
          trivial)
  | none =>
      simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_set, StateT.run_pure, OracleComp.liftM_run_StateT, MonadLift.monadLift]
        using
          (show IsTotalQueryBound
              (((liftM (query (spec := CMOracle M S C) ms) :
                  OracleComp (CMOracle M S C) C) >>= fun u =>
                pure (u, (cache.cacheQuery ms u,
                  Function.update counts ms.2 (counts ms.2 + 1)))))
              1 from by
            rw [isTotalQueryBound_query_bind_iff]
            exact ⟨Nat.one_pos, fun _ => trivial⟩)

/-- Single-step projection: projecting `hidingImplCountAll` to one salt counter
recovers `hidingImpl₁ s`. -/
theorem hidingImplCountAll_proj_eq_hidingImpl₁
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    Prod.map id (fun st => (st.1, st.2 s)) <$>
        (hidingImplCountAll (M := M) (S := S) (C := C) ms).run st =
      (hidingImpl₁ (M := M) (S := S) (C := C) s ms).run (st.1, st.2 s) := by
  obtain ⟨cache, counts⟩ := st
  cases hcache : cache ms with
  | some u =>
      simp [hidingImplCountAll, hidingImpl₁, hcache, StateT.run_bind, StateT.run_get,
        pure_bind]
  | none =>
      simp [hidingImplCountAll, hidingImpl₁, hcache, StateT.run_bind, StateT.run_get,
        pure_bind, StateT.run_set, StateT.run_pure, Function.update, Prod.map]
      congr
      funext a
      by_cases h : ms.2 = s
      · simp [h, eq_comm]
      · have hs : ¬ s = ms.2 := by simpa [eq_comm] using h
        simp [h, hs, eq_comm]

private theorem hidingImplCountAll_proj_eq_cachingOracle
    (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    Prod.map id Prod.fst <$>
        (hidingImplCountAll (M := M) (S := S) (C := C) ms).run st =
      (cachingOracle (spec := CMOracle M S C) ms).run st.1 := by
  rcases st with ⟨cache, counts⟩
  cases hcache : cache ms with
  | some u =>
      simp [hidingImplCountAll, cachingOracle, QueryImpl.withCaching_apply, hcache,
        StateT.run_bind, StateT.run_get, pure_bind]
  | none =>
      simp [hidingImplCountAll, cachingOracle, QueryImpl.withCaching_apply, hcache,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure,
        StateT.run_modifyGet, Prod.map]

private theorem run_hidingImplCountAll_proj_eq_cachingOracle
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    Prod.map id Prod.fst <$> (simulateQ hidingImplCountAll oa).run st =
      (simulateQ cachingOracle oa).run st.1 := by
  simpa using
    (OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
      hidingImplCountAll cachingOracle (fun st => st.1)
      (fun ms st => by
        simpa [Prod.map] using
          hidingImplCountAll_proj_eq_cachingOracle
            (M := M) (S := S) (C := C) ms st)
      oa st)

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

/-- Total query bound for the full two-phase hiding computation, matching the
textbook's bounded-query setting: `t` adversary queries plus one challenge
query. -/
private lemma hidingOa_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound (hidingOa A s) (t + 1) := by
  simpa [hidingOa] using A.totalBound s

private lemma hiding_choose_totalBound {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    IsTotalQueryBound A.choose t := by
  simpa [hidingOa] using
    (OracleComp.IsTotalQueryBound.of_bind_query_prefix
      (spec := CMOracle M S C)
      (oa := A.choose)
      (next := fun x : M × AUX => (x.1, default))
      (ob := fun x cm => A.distinguish x.2 cm)
      (n := t)
      (A.totalBound default))

private lemma hiding_distinguish_totalBound_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {x : (M × AUX) × QueryCount (M × S)}
    (hx : x ∈ support (countingOracle.simulate A.choose 0)) :
    ∀ cm : C, IsTotalQueryBound (A.distinguish x.1.2 cm) (t - ∑ ms, x.2 ms) := by
  have hres :
      IsTotalQueryBound
        ((liftM (query (spec := CMOracle M S C) (x.1.1, s))) >>= fun cm =>
          A.distinguish x.1.2 cm)
        ((t + 1) - ∑ ms, x.2 ms) := by
    simpa [hidingOa] using
      (IsTotalQueryBound.residual_of_mem_support_counting
        (spec := CMOracle M S C)
        (oa := A.choose)
        (ob := fun a =>
          (liftM (query (spec := CMOracle M S C) (a.1, s))) >>= fun cm =>
            A.distinguish a.2 cm)
        (n := t + 1)
        (h := A.totalBound s)
        hx)
  rw [isTotalQueryBound_query_bind_iff] at hres
  intro cm
  have hcm : IsTotalQueryBound (A.distinguish x.1.2 cm) (((t + 1) - ∑ ms, x.2 ms) - 1) := by
    simpa using hres.2 cm
  have hbudget : (((t + 1) - ∑ ms, x.2 ms) - 1) = t - ∑ ms, x.2 ms := by
    omega
  simpa [hbudget] using hcm

private lemma hidingImpl₁_run_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound
      ((simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0))
      (t + 1) := by
  exact (hidingOa_totalBound_current A s).simulateQ_run_of_step
    (fun ms st => hidingImpl₁_step_totalBound s ms st) (∅, 0)

private lemma hidingImplCountAll_run_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (t + 1) := by
  exact (hidingOa_totalBound_current A s).simulateQ_run_of_step
    (fun ms st => hidingImplCountAll_step_totalBound ms st) (∅, fun _ => 0)

/-- Run-level projection: for any fixed `s`, the shared counted implementation
projects to the `hidingImpl₁ s` execution on `hidingOa`. -/
theorem hidingRun_countAll_proj_eq_impl₁ {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    (simulateQ hidingImplCountAll (hidingOa A s)).run' (∅, fun _ => 0) =
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, 0) := by
  simpa [StateT.run'] using
    (OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq'
      hidingImplCountAll (hidingImpl₁ s) (fun st => (st.1, st.2 s))
      (fun ms st => by
        simpa [Prod.map] using hidingImplCountAll_proj_eq_hidingImpl₁
          (M := M) (S := S) (C := C) s ms st)
      (hidingOa A s) (∅, fun _ => 0))

/-- Probability bridge for bad events:
`Pr[bad]` under `hidingImpl₁ s` is equal to the corresponding event on the
shared counted run, projected at `s`. -/
theorem probEvent_hidingBad_eq_countAll {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)] =
    Pr[fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => 2 ≤ z.2.2 s |
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] := by
  have hrun :
      Prod.map id (fun st : QueryCache (CMOracle M S C) × (S → ℕ) => (st.1, st.2 s)) <$>
          (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0) =
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0) := by
    simpa using
      (OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
        hidingImplCountAll (hidingImpl₁ s) (fun st => (st.1, st.2 s))
        (fun ms st => by
          simpa [Prod.map] using hidingImplCountAll_proj_eq_hidingImpl₁
            (M := M) (S := S) (C := C) s ms st)
        (hidingOa A s) (∅, fun _ => 0))
  rw [← hrun]
  rw [probEvent_map]
  rfl

/-- Updating one coordinate by `+1` increases the total sum by exactly one. -/
private lemma sum_update_succ_count {ι : Type} [Fintype ι] [DecidableEq ι]
    (counts : ι → ℕ) (i : ι) :
    ∑ j : ι, Function.update counts i (counts i + 1) j =
      (∑ j : ι, counts j) + 1 := by
  classical
  calc
    ∑ j : ι, Function.update counts i (counts i + 1) j =
        Function.update counts i (counts i + 1) i +
          Finset.sum (Finset.univ.erase i)
            (fun j : ι => Function.update counts i (counts i + 1) j) := by
          symm
          exact Finset.univ.add_sum_erase
            (f := fun j : ι => Function.update counts i (counts i + 1) j) (Finset.mem_univ i)
    _ = counts i + 1 + Finset.sum (Finset.univ.erase i) (fun j : ι => counts j) := by
          simp only [Function.update_self]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    _ = counts i + Finset.sum (Finset.univ.erase i) (fun j : ι => counts j) + 1 := by
          omega
    _ = (∑ j : ι, counts j) + 1 := by
          rw [← Finset.univ.add_sum_erase (f := fun j : ι => counts j) (Finset.mem_univ i)]

/-- One-step growth bound for the shared counted hiding implementation:
the total count increases by at most one. -/
private lemma sum_counts_step_le_succ_hidingImplCountAll (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    (∑ s' : S, x.2.2 s') ≤ (∑ s' : S, st.2 s') + 1 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
      exact Nat.le_succ _
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      rw [hx]
      simp [sum_update_succ_count]

private lemma hiding_distinguish_totalBound_of_choose_count_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {x : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hx : x ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    ∀ cm : C, IsTotalQueryBound (A.distinguish x.1.2 cm) (t - ∑ s : S, x.2.2 s) := by
  have hres :
      IsTotalQueryBound
        ((liftM (query (spec := CMOracle M S C) (x.1.1, default))) >>= fun cm =>
          A.distinguish x.1.2 cm)
        ((t + 1) - (∑ s : S, x.2.2 s)) := by
    simpa [hidingOa] using
      (IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
        (spec := CMOracle M S C)
        (oa := A.choose)
        (ob := fun a =>
          (liftM (query (spec := CMOracle M S C) (a.1, default))) >>= fun cm =>
            A.distinguish a.2 cm)
        (n := t + 1)
        (impl := hidingImplCountAll)
        (cost := fun st : QueryCache (CMOracle M S C) × (S → ℕ) => ∑ s : S, st.2 s)
        (hstep := fun t st y hy =>
          sum_counts_step_le_succ_hidingImplCountAll (M := M) (S := S) (C := C) t st y hy)
        (h := A.totalBound default)
        hx)
  rw [isTotalQueryBound_query_bind_iff] at hres
  intro cm
  have hcm :
      IsTotalQueryBound (A.distinguish x.1.2 cm)
        ((((t + 1) - ∑ s : S, x.2.2 s)) - 1) := by
    simpa using hres.2 cm
  have hbudget : ((((t + 1) - ∑ s : S, x.2.2 s)) - 1) = t - ∑ s : S, x.2.2 s := by
    omega
  simpa [hbudget] using hcm

/-- A single counted query can only increase a fixed salt counter. -/
private lemma count_mono_step_hidingImplCountAll (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      rw [hx]
      by_cases hs : ms.2 = s
      · subst hs
        simp [Function.update]
      · have hs' : s ≠ ms.2 := by
          intro hEq
          exact hs hEq.symm
        simpa [Function.update_of_ne hs'] using (Nat.le_refl (counts s))

/-- A single counted query changes any fixed salt counter by at most one. -/
private lemma count_coord_le_succ_of_mem_support_step_hidingImplCountAll
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s ∧ x.2.2 s ≤ st.2 s + 1 := by
  obtain ⟨cache, counts⟩ := st
  have hmono :
      counts s ≤ x.2.2 s :=
    count_mono_step_hidingImplCountAll (M := M) (S := S) (C := C) s ms (cache, counts) x hx
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hmono, Nat.le_succ _⟩
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      constructor
      · exact hmono
      · by_cases hs : ms.2 = s
        · subst hs
          simp [Function.update]
        · have hs' : s ≠ ms.2 := by
            intro hEq
            exact hs hEq.symm
          simpa [Function.update_of_ne hs'] using (Nat.le_succ (counts s))

/-- A single counted query only changes the counter at its queried salt. -/
private lemma count_coord_le_add_hit_of_mem_support_step_hidingImplCountAll
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    x.2.2 s ≤ st.2 s + if ms.2 = s then 1 else 0 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      by_cases hs : ms.2 = s
      · subst hs
        simp
      · have hs' : s ≠ ms.2 := by
          intro hEq
          exact hs hEq.symm
        simp [Function.update_of_ne hs', hs]
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      by_cases hs : ms.2 = s
      · subst hs
        simp [Function.update]
      · have hs' : s ≠ ms.2 := by
          intro hEq
          exact hs hEq.symm
        simp [Function.update_of_ne hs', hs]

/-- After the challenge step at salt `s`, removing the mandatory challenge hit leaves
at most the pre-challenge salt count. -/
private lemma challenge_countPred_le_initialCount_of_mem_support_step_hidingImplCountAll
    (m : M) (s : S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    {x : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)) :
    x.2.2 s - 1 ≤ st.2 s := by
  have hsucc :
      x.2.2 s ≤ st.2 s + 1 :=
    (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
      (M := M) (S := S) (C := C) s (m, s) st x hx).2
  omega

/-- Any support point of a counted step caches the queried point with the returned value. -/
private lemma self_mem_cache_of_mem_support_step_hidingImplCountAll (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    x.2.1 ms = some x.1 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simpa [hcache]
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      simp

/-- The counted hiding invariant: every cached salt has a positive counter. -/
private def HidingCountInv (st : QueryCache (CMOracle M S C) × (S → ℕ)) : Prop :=
  ∀ ms : M × S, ∀ u : C, st.1 ms = some u → 1 ≤ st.2 ms.2

/-- The counted implementation preserves the hiding count invariant. -/
private lemma hidingCountInv_step_hidingImplCountAll (ms₀ : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) (hInv : HidingCountInv st)
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms₀).run st)) :
    HidingCountInv x.2 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms₀ with
  | some u₀ =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simpa using hInv
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u₀, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      intro ms u hms
      by_cases hEq : ms = ms₀
      · subst hEq
        simpa using Nat.succ_le_succ (Nat.zero_le (counts ms₀.2))
      · have hcache_ms : cache ms = some u := by
          simpa [QueryCache.cacheQuery, Function.update, hEq] using hms
        have h_old : 1 ≤ counts ms.2 := hInv ms u hcache_ms
        have h_mono : counts ms.2 ≤ Function.update counts ms₀.2 (counts ms₀.2 + 1) ms.2 := by
          by_cases hs : ms.2 = ms₀.2
          · rw [hs]
            simpa [Function.update_self] using Nat.le_succ (counts ms₀.2)
          · simpa [Function.update_of_ne hs] using (Nat.le_refl (counts ms.2))
        exact le_trans h_old h_mono

/-- Support points of `simulateQ hidingImplCountAll` have coordinatewise monotone counts. -/
private lemma count_mono_of_mem_support_run_hidingImplCountAll {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀))
    (s : S) :
    st₀.2 s ≤ z.2.2 s := by
  suffices h : ∀ {β : Type} (ob : OracleComp (CMOracle M S C) β)
      (st : QueryCache (CMOracle M S C) × (S → ℕ))
      (y : β × (QueryCache (CMOracle M S C) × (S → ℕ))),
      y ∈ support ((simulateQ hidingImplCountAll ob).run st) →
      ∀ s' : S, st.2 s' ≤ y.2.2 s' by
    exact h oa st₀ z hz s
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro st y hy s'
      simp [simulateQ_pure] at hy
      subst y
      exact Nat.le_refl _
  | query_bind t mx ih =>
      intro st y hy s'
      rw [simulateQ_query_bind, StateT.run_bind] at hy
      rw [support_bind] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨qu, hqu, hy'⟩ := hy
      exact le_trans
        (count_mono_step_hidingImplCountAll (M := M) (S := S) (C := C) s' t st qu hqu)
        (ih qu.1 qu.2 y hy' s')

/-- Every cached salt has a positive counter along the support of the counted run. -/
private lemma hidingCountInv_of_mem_support_run_hidingImplCountAll {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (hInv : HidingCountInv st₀)
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    HidingCountInv z.2 := by
  suffices h : ∀ (β : Type) (ob : OracleComp (CMOracle M S C) β)
      (st : QueryCache (CMOracle M S C) × (S → ℕ)),
      HidingCountInv st →
      ∀ y : β × (QueryCache (CMOracle M S C) × (S → ℕ)),
        y ∈ support ((simulateQ hidingImplCountAll ob).run st) →
        HidingCountInv y.2 from
    h α oa st₀ hInv z hz
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro st hInv y hy
      simp [simulateQ_pure] at hy
      subst hy
      exact hInv
  | query_bind t mx ih =>
      intro st hInv y hy
      rw [simulateQ_query_bind, StateT.run_bind] at hy
      rw [support_bind] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨qu, hqu, hy'⟩ := hy
      have hInv' :
          HidingCountInv qu.2 :=
        hidingCountInv_step_hidingImplCountAll (M := M) (S := S) (C := C) t st hInv qu hqu
      exact ih qu.1 qu.2 hInv' y hy'

/-- On the support of the counted choose run, a zero salt-count means no cache entry
at that salt can already exist. -/
private lemma cache_none_of_zero_count_of_mem_support_run_hidingChoose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (m : M) (s : S)
    (hzero : qchoose.2.2 s = 0) :
    qchoose.2.1 (m, s) = none := by
  have hInv₀ : HidingCountInv ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0) := by
    intro ms u hms
    simp at hms
  have hInv :
      HidingCountInv qchoose.2 :=
    hidingCountInv_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C)
      (oa := A.choose)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      hInv₀
      (z := qchoose)
      hqchoose
  by_cases hcache : qchoose.2.1 (m, s) = none
  · exact hcache
  · cases hsome : qchoose.2.1 (m, s) with
    | none =>
        contradiction
    | some u =>
        have hpos : 1 ≤ qchoose.2.2 s :=
          hInv (m, s) u hsome
        omega

/-- For a fresh salt after the choose phase, the challenge step of
`hidingImplCountAll` is necessarily the cache-miss branch and sets that salt count to `1`. -/
private abbrev HidingCountState (M : Type) (S : Type) (C : Type) :=
  QueryCache (CMOracle M S C) × (S → ℕ)

private lemma fresh_step_state_of_mem_support_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)) :
    qch.2 =
      (qchoose.2.1.cacheQuery (qchoose.1.1, s) qch.1,
        Function.update qchoose.2.2 s 1) := by
  have hnone : qchoose.2.1 (qchoose.1.1, s) = none :=
    cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind, hnone] at hqch
  rw [mem_support_bind_iff] at hqch
  obtain ⟨u, _, hu⟩ := hqch
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
  rcases hu with ⟨rfl, rfl⟩
  simp [hzero]

private lemma wp_fresh_challenge_branch_eq
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (F : C × (QueryCache (CMOracle M S C) × (S → ℕ)) → ℝ≥0∞) :
    OracleComp.ProgramLogic.wp
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
      F
    =
    OracleComp.ProgramLogic.wp
      (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
        OracleComp (CMOracle M S C) C)
      (fun cm =>
        F (cm, (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
          Function.update qchoose.2.2 s 1))) := by
  have hnone : qchoose.2.1 (qchoose.1.1, s) = none :=
    cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  simp [hidingImplCountAll, hnone, hzero,
    StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set]
  rw [OracleComp.ProgramLogic.wp_map]
  rfl

private lemma wp_freshDistinguishIncrement_eq
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S) :
    OracleComp.ProgramLogic.wp
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
      (fun qch : C × HidingCountState M S C =>
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
          (fun z : Bool × HidingCountState M S C =>
            OracleComp.ProgramLogic.propInd
              (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) =
      OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
        OracleComp.ProgramLogic.wp
          (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
            OracleComp (CMOracle M S C) C)
          (fun cm =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
                (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                  Function.update qchoose.2.2 s 1))
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (1 < z.2.2 s))) := by
  by_cases hzero : qchoose.2.2 s = 0
  · rw [wp_fresh_challenge_branch_eq
        (M := M) (S := S) (C := C) A hqchoose s hzero]
    simp [hzero]
  · have hpost :
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) = fun _ => 0 := by
      funext qch
      simp [hzero]
    rw [hpost, OracleComp.ProgramLogic.wp_const]
    simp [hzero]

/-- On the support of the counted hiding run, the total count is at most `n`
plus the initial total count. -/
private lemma sum_counts_le_of_mem_support_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    (∑ s' : S, z.2.2 s') ≤ n + ∑ s' : S, st₀.2 s' := by
  suffices h : ∀ {β : Type} (ob : OracleComp (CMOracle M S C) β)
      (m : ℕ), IsTotalQueryBound ob m →
      ∀ (st : QueryCache (CMOracle M S C) × (S → ℕ))
        (y : β × (QueryCache (CMOracle M S C) × (S → ℕ))),
        y ∈ support ((simulateQ hidingImplCountAll ob).run st) →
        (∑ s' : S, y.2.2 s') ≤ m + ∑ s' : S, st.2 s' by
    exact h oa n hbound st₀ z hz
  intro β ob m hm st y hy
  induction ob using OracleComp.inductionOn generalizing m st y with
  | pure x =>
      simp [simulateQ_pure] at hy
      subst y
      exact Nat.le_add_left _ _
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at hm
      rw [simulateQ_query_bind, StateT.run_bind] at hy
      rw [support_bind] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨qu, hqu, hy'⟩ := hy
      have hstep :
          (∑ s' : S, qu.2.2 s') ≤ (∑ s' : S, st.2 s') + 1 :=
        sum_counts_step_le_succ_hidingImplCountAll (M := M) (S := S) (C := C) t st qu hqu
      have hrest :
          (∑ s' : S, y.2.2 s') ≤ (m - 1) + ∑ s' : S, qu.2.2 s' :=
        (ih (u := qu.1) (m := m - 1) (hm.2 qu.1)) (st := qu.2) (y := y) hy'
      omega

private lemma cache_le_of_mem_support_run_hidingImplCountAll
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : HidingCountState M S C}
    {z : α × HidingCountState M S C}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    st₀.1 ≤ z.2.1 := by
  have hz' :
      (z.1, z.2.1) ∈ support ((simulateQ cachingOracle oa).run st₀.1) := by
    have hzmap :
        (z.1, z.2.1) ∈ support
          (Prod.map id Prod.fst <$> (simulateQ hidingImplCountAll oa).run st₀) := by
      rw [support_map]
      exact ⟨z, hz, by simp [Prod.map]⟩
    simpa [run_hidingImplCountAll_proj_eq_cachingOracle (M := M) (S := S) (C := C) oa st₀] using hzmap
  exact simulateQ_cachingOracle_cache_le (spec := CMOracle M S C) oa st₀.1 (z.1, z.2.1) hz'

private lemma exists_new_salt_cacheEntry_of_count_gt_one
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    (m0 : M) (s : S)
    {cache₀ : QueryCache (CMOracle M S C)} {counts₀ : S → ℕ}
    (hcount : counts₀ s = 1)
    (hself : ∃ v : C, cache₀ (m0, s) = some v)
    (hunique : ∀ m : M, m ≠ m0 → cache₀ (m, s) = none)
    {z : α × HidingCountState M S C}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run (cache₀, counts₀)))
    (hgt : 1 < z.2.2 s) :
    ∃ m : M, ∃ v : C, m ≠ m0 ∧ z.2.1 (m, s) = some v := by
  induction oa using OracleComp.inductionOn generalizing cache₀ counts₀ z with
  | pure x =>
      simp [simulateQ_pure] at hz
      subst z
      exfalso
      simpa [hcount] using hgt
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      cases hcache : cache₀ t with
      | some u =>
          have hqu_eq : qu = (u, (cache₀, counts₀)) := by
            simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind] using hqu
          subst qu
          exact ih (u := u) (cache₀ := cache₀) (counts₀ := counts₀) (z := z)
            hcount hself hunique hz' hgt
      | none =>
          have hqu_eq :
              ∃ u : C,
                (u,
                  (cache₀.cacheQuery t u,
                    Function.update counts₀ t.2 (counts₀ t.2 + 1))) = qu := by
            simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind]
              using hqu
          obtain ⟨u, rfl⟩ := hqu_eq
          by_cases hs : t.2 = s
          · have htne : t.1 ≠ m0 := by
              intro hEq
              subst hEq
              rcases hself with ⟨v0, hv0⟩
              have ht_some : cache₀ t = some v0 := by
                change cache₀ (t.1, t.2) = some v0
                rw [hs]
                exact hv0
              have : some v0 = none := ht_some.symm.trans hcache
              cases this
            have hentry : (cache₀.cacheQuery t u) (t.1, s) = some u := by
              subst s
              simpa using QueryCache.cacheQuery_self cache₀ t u
            have hmono :
                cache₀.cacheQuery t u ≤ z.2.1 :=
              cache_le_of_mem_support_run_hidingImplCountAll
                (M := M) (S := S) (C := C) (oa := mx u)
                (st₀ := (cache₀.cacheQuery t u, Function.update counts₀ t.2 (counts₀ t.2 + 1)))
                (z := z) hz'
            refine ⟨t.1, u, htne, ?_⟩
            exact hmono hentry
          · have hcount' :
                (Function.update counts₀ t.2 (counts₀ t.2 + 1)) s = 1 := by
              by_cases hst : s = t.2
              · exact False.elim (hs hst.symm)
              · simp [Function.update, hst, hcount]
            have hself' : ∃ v : C, (cache₀.cacheQuery t u) (m0, s) = some v := by
              rcases hself with ⟨v0, hv0⟩
              refine ⟨v0, ?_⟩
              have hne : (m0, s) ≠ t := by
                intro hEq
                exact hs (by simpa using congrArg Prod.snd hEq.symm)
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hne] using hv0
            have hunique' : ∀ m : M, m ≠ m0 → (cache₀.cacheQuery t u) (m, s) = none := by
              intro m hm
              have hne : (m, s) ≠ t := by
                intro hEq
                exact hs (by simpa using congrArg Prod.snd hEq.symm)
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hne] using hunique m hm
            exact ih (u := u) (cache₀ := cache₀.cacheQuery t u)
              (counts₀ := Function.update counts₀ t.2 (counts₀ t.2 + 1)) (z := z)
              hcount' hself' hunique' hz' hgt

/-- Along the counted choose run, the total per-salt miss count is bounded by the
adversary query budget `t`. -/
private lemma sum_counts_le_queryBound_of_mem_support_run_hidingChoose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S, qchoose.2.2 s) ≤ t := by
  simpa using
    (sum_counts_le_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C)
      (oa := A.choose)
      (hbound := hiding_choose_totalBound (M := M) (S := S) (C := C) A)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      (z := qchoose)
      hqchoose)

private lemma wp_choose_sumCounts_le_queryBound
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
        (∑ s : S, qchoose.2.2 s : ℝ≥0∞)) ≤ t := by
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qchoose,
        Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] *
          (∑ s : S, qchoose.2.2 s : ℝ≥0∞)
      ≤
        ∑' qchoose,
          Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] * t := by
            refine ENNReal.tsum_le_tsum fun qchoose => ?_
            by_cases hqchoose :
                qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
            · exact mul_le_mul'
                le_rfl
                (by
                  exact_mod_cast
                    (sum_counts_le_queryBound_of_mem_support_run_hidingChoose
                      (M := M) (S := S) (C := C) A hqchoose))
            · rw [probOutput_eq_zero_of_not_mem_support hqchoose]
              simp
    _ = t := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

/-- Every support point of the shared counted run is dominated by some exact-query
support point of `countingOracle.simulate` on the same computation. -/
private lemma exists_counting_support_of_mem_support_run_hidingImplCountAll
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    ∃ qc : QueryCount (M × S),
      (z.1, qc) ∈ support (countingOracle.simulate oa 0) ∧
      (∑ s : S, z.2.2 s) ≤ (∑ s : S, st₀.2 s) + ∑ ms : M × S, qc ms := by
  classical
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp [simulateQ_pure] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa using
          (countingOracle.mem_support_simulate_pure_iff
            (x := x) (qc := (0 : QueryCount (M × S))) (z := (x, 0))).2 rfl
      · simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qcRest, hqcRest, hsumRest⟩
      have hstep :
          (∑ s : S, qu.2.2 s) ≤ (∑ s : S, st₀.2 s) + 1 :=
        sum_counts_step_le_succ_hidingImplCountAll
          (M := M) (S := S) (C := C) t st₀ qu hqu
      let qc : QueryCount (M × S) := Function.update qcRest t (qcRest t + 1)
      have hpred : Function.update qc t (qc t - 1) = qcRest := by
        funext j
        by_cases hj : j = t
        · subst hj
          simp [qc]
        · simp [qc, Function.update, hj]
      have hqc :
          (z.1, qc) ∈ support
            (countingOracle.simulate
              (((liftM (query (spec := CMOracle M S C) t)) : OracleComp (CMOracle M S C) _) >>=
                mx) 0) := by
        rw [countingOracle.mem_support_simulate_queryBind_iff]
        refine ⟨by simp [qc], qu.1, ?_⟩
        simpa [hpred] using hqcRest
      have hqcsum : (∑ ms : M × S, qc ms) = (∑ ms : M × S, qcRest ms) + 1 := by
        simpa [qc] using sum_update_succ_count (counts := qcRest) t
      refine ⟨qc, hqc, ?_⟩
      omega

private lemma exists_counting_support_of_mem_support_run_hidingImplCountAll_coord
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    ∃ qc : QueryCount (M × S),
      (z.1, qc) ∈ support (countingOracle.simulate oa 0) ∧
      ∀ s : S, z.2.2 s ≤ st₀.2 s + ∑ m : M, qc (m, s) := by
  classical
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp [simulateQ_pure] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa using
          (countingOracle.mem_support_simulate_pure_iff
            (x := x) (qc := (0 : QueryCount (M × S))) (z := (x, 0))).2 rfl
      · intro s
        simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qcRest, hqcRest, hcoordRest⟩
      let qc : QueryCount (M × S) := Function.update qcRest t (qcRest t + 1)
      have hpred : Function.update qc t (qc t - 1) = qcRest := by
        funext j
        by_cases hj : j = t
        · subst hj
          simp [qc]
        · simp [qc, Function.update, hj]
      have hqc :
          (z.1, qc) ∈ support
            (countingOracle.simulate
              (((liftM (query (spec := CMOracle M S C) t)) : OracleComp (CMOracle M S C) _) >>=
                mx) 0) := by
        rw [countingOracle.mem_support_simulate_queryBind_iff]
        refine ⟨by simp [qc], qu.1, ?_⟩
        simpa [hpred] using hqcRest
      refine ⟨qc, hqc, ?_⟩
      intro s
      have hstep :
          qu.2.2 s ≤ st₀.2 s + if t.2 = s then 1 else 0 :=
        count_coord_le_add_hit_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s t st₀ qu hqu
      have hrest :
          z.2.2 s ≤ qu.2.2 s + ∑ m : M, qcRest (m, s) :=
        hcoordRest s
      by_cases hs : t.2 = s
      · subst hs
        have hcoord :
            (fun m : M => qc (m, t.2)) =
              Function.update (fun m : M => qcRest (m, t.2)) t.1 (qcRest t + 1) := by
          funext m
          by_cases hm : m = t.1
          · subst hm
            simp [qc]
          · have hne : (m, t.2) ≠ t := by
              intro hEq
              exact hm (by simpa using congrArg Prod.fst hEq)
            simp [qc, Function.update_of_ne hne, hm]
        have hsum :
            (∑ m : M, qc (m, t.2)) = (∑ m : M, qcRest (m, t.2)) + 1 := by
          rw [hcoord]
          simpa using
            sum_update_succ_count (counts := fun m : M => qcRest (m, t.2)) t.1
        have hstep' :
            qu.2.2 t.2 + ∑ m : M, qcRest (m, t.2) ≤
              st₀.2 t.2 + ∑ m : M, qc (m, t.2) := by
          rw [hsum]
          have := add_le_add_right hstep (∑ m : M, qcRest (m, t.2))
          simpa [add_assoc, add_left_comm, add_comm] using this
        exact le_trans hrest hstep'
      · have hsum :
            (∑ m : M, qc (m, s)) = ∑ m : M, qcRest (m, s) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hne : (m, s) ≠ t := by
            intro hEq
            exact hs (by simpa using congrArg Prod.snd hEq.symm)
          rw [show qc (m, s) = qcRest (m, s) by
            simp [qc, Function.update_of_ne hne]]
        have hstep' :
            qu.2.2 s + ∑ m : M, qcRest (m, s) ≤
              st₀.2 s + ∑ m : M, qc (m, s) := by
          rw [hsum]
          have := add_le_add_right hstep (∑ m : M, qcRest (m, s))
          simpa [hs, add_assoc, add_left_comm, add_comm] using this
        exact le_trans hrest hstep'

/-- On the support of the counted hiding run, the challenge salt count is positive. -/
private theorem challenge_count_pos_of_mem_support_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    1 ≤ z.2.2 s := by
  have hInv0 : HidingCountInv (M := M) (S := S) (C := C)
      ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0) := by
    intro ms u h
    simp at h
  rw [hidingOa, simulateQ_bind, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨qchoose, hchoose, hz⟩ := hz
  rcases qchoose with ⟨⟨m, aux⟩, st₁⟩
  have hInv₁ : HidingCountInv st₁ :=
    hidingCountInv_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) (oa := A.choose)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      (hInv := hInv0) (z := ((m, aux), st₁)) hchoose
  rw [simulateQ_query_bind, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨qch, hch, hz'⟩ := hz
  have hInv₂ : HidingCountInv qch.2 :=
    hidingCountInv_step_hidingImplCountAll
      (M := M) (S := S) (C := C) (m, s) st₁ hInv₁ qch hch
  have hcache₂ : qch.2.1 (m, s) = some qch.1 :=
    self_mem_cache_of_mem_support_step_hidingImplCountAll
      (M := M) (S := S) (C := C) (m, s) st₁ qch hch
  have hqch_pos : 1 ≤ qch.2.2 s :=
    hInv₂ (m, s) qch.1 hcache₂
  exact le_trans hqch_pos
    (count_mono_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) (oa := A.distinguish aux qch.1)
      (st₀ := qch.2) (z := z) hz' s)

/-- On support of the counted hiding run, the bad-event indicator at the challenge salt
is bounded by the excess of that salt count over the mandatory challenge hit. -/
private lemma bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    (if 2 ≤ z.2.2 s then (1 : ℝ≥0∞) else 0) ≤ z.2.2 s - 1 := by
  have hpos : 1 ≤ z.2.2 s :=
    challenge_count_pos_of_mem_support_hidingImplCountAll
      (M := M) (S := S) (C := C) A s hz
  by_cases hbad : 2 ≤ z.2.2 s
  · have hcount : (1 : ℕ) ≤ z.2.2 s - 1 := by omega
    simp [hbad]
    exact_mod_cast hcount
  · simp [hbad]

/-- On support of the counted hiding run, bad at salt `s` can only happen if the
choose phase already queried salt `s`, or if the distinguish phase later
increased the salt-`s` counter after the challenge step. -/
private lemma bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2))
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)) :
    OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s) ≤
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s) := by
  by_cases hbad : 2 ≤ z.2.2 s
  · by_cases hchoose : 0 < qchoose.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hbad, hchoose]
    · have hqzero : qchoose.2.2 s = 0 := Nat.eq_zero_of_not_pos hchoose
      have hmono :
          qch.2.2 s ≤ z.2.2 s :=
        count_mono_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := A.distinguish qchoose.1.2 qch.1)
          (st₀ := qch.2) (z := z) hz s
      have hstep :
          qch.2.2 s ≤ qchoose.2.2 s + 1 :=
        (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s (qchoose.1.1, s) qchoose.2 qch hqch).2
      have hinc : qch.2.2 s < z.2.2 s := by
        by_contra hnot
        have hzle : z.2.2 s ≤ qch.2.2 s := Nat.le_of_not_gt hnot
        have hEq : z.2.2 s = qch.2.2 s := le_antisymm hzle hmono
        have hzle1 : z.2.2 s ≤ 1 := by
          rw [hEq]
          simpa [hqzero] using hstep
        omega
      simp [OracleComp.ProgramLogic.propInd, hbad, hchoose, hinc]
  · simp [OracleComp.ProgramLogic.propInd, hbad]

/-- Strengthened version of
`bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator`:
the distinguish-increment term is only charged on salts that were fresh after
the choose phase. -/
private lemma bad_indicator_le_chooseHitIndicator_add_freshDistinguishIncrementIndicator
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2))
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)) :
    OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s) ≤
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.propInd
          (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s) := by
  by_cases hbad : 2 ≤ z.2.2 s
  · by_cases hchoose : 0 < qchoose.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hbad, hchoose]
    · have hqzero : qchoose.2.2 s = 0 := Nat.eq_zero_of_not_pos hchoose
      have hmono :
          qch.2.2 s ≤ z.2.2 s :=
        count_mono_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := A.distinguish qchoose.1.2 qch.1)
          (st₀ := qch.2) (z := z) hz s
      have hstep :
          qch.2.2 s ≤ qchoose.2.2 s + 1 :=
        (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s (qchoose.1.1, s) qchoose.2 qch hqch).2
      have hinc : qch.2.2 s < z.2.2 s := by
        by_contra hnot
        have hzle : z.2.2 s ≤ qch.2.2 s := Nat.le_of_not_gt hnot
        have hEq : z.2.2 s = qch.2.2 s := le_antisymm hzle hmono
        have hzle1 : z.2.2 s ≤ 1 := by
          rw [hEq]
          simpa [hqzero] using hstep
        omega
      simp [OracleComp.ProgramLogic.propInd, hbad, hchoose, hqzero, hinc]
  · simp [OracleComp.ProgramLogic.propInd, hbad]

/-- On support of the counted hiding run, the challenge-salt excess count is bounded
by the adversary's total query budget. -/
private lemma count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    z.2.2 s - 1 ≤ t := by
  have hsum :
      (∑ s' : S, z.2.2 s') ≤ t + 1 :=
    by
      simpa using
        (sum_counts_le_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := hidingOa A s)
          (hbound := hidingOa_totalBound_current (M := M) (S := S) (C := C) A s)
          (st₀ := (∅, fun _ => 0)) (z := z) hz)
  have hs_le : z.2.2 s ≤ ∑ s' : S, z.2.2 s' := by
    classical
    simpa using Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  omega

/-- Combined pointwise bound used when converting the bad event to an indicator
expectation over counted support points. -/
private lemma bad_indicator_le_queryBound_of_mem_support_run_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    (if 2 ≤ z.2.2 s then (1 : ℝ≥0∞) else 0) ≤ t := by
  exact le_trans
    (bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) A s hz)
    (by
      exact_mod_cast
        (count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C) A s hz))

/-- Fixed-salt bridge from the counted bad event to the expected excess count. -/
private lemma probEvent_countAll_bad_le_wp_countPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr[fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => 2 ≤ z.2.2 s |
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] ≤
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) := by
  rw [OracleComp.ProgramLogic.probEvent_eq_wp_propInd,
    OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
  · simp only [OracleComp.ProgramLogic.propInd_eq_ite]
    exact mul_le_mul'
      le_rfl
      (bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
        (M := M) (S := S) (C := C) A s hz)
  · rw [probOutput_eq_zero_of_not_mem_support hz]
    simp [OracleComp.ProgramLogic.propInd_eq_ite]

/-- Fixed-salt expectation bound for the counted excess at the challenge salt. -/
private lemma wp_countPred_le_queryBound_of_run_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) ≤ t := by
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z, Pr[= z | (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] *
        (z.2.2 s - 1 : ℝ≥0∞)
      ≤
        ∑' z, Pr[= z | (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] * t := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
          · exact mul_le_mul'
              le_rfl
              (by
                exact_mod_cast
                  (count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
                    (M := M) (S := S) (C := C) A s hz))
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = t := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

/-- For a fixed computation under the shared counted implementation, the sum of
expected per-salt count increments is bounded by the total query bound. -/
private lemma sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          (z.2.2 s - st₀.2 s : ℝ≥0∞))) ≤ n := by
  classical
  let run := ((simulateQ hidingImplCountAll oa).run st₀)
  have hsum :
      (∑ s : S,
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
            (z.2.2 s - st₀.2 s : ℝ≥0∞))) =
      OracleComp.ProgramLogic.wp run
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          ∑ s : S, (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
    have hsumFin :
        ∀ ss : Finset S,
          (ss.sum fun s =>
            OracleComp.ProgramLogic.wp run
              (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
                (z.2.2 s - st₀.2 s : ℝ≥0∞))) =
          OracleComp.ProgramLogic.wp run
            (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
              ss.sum fun s => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
      intro ss
      refine Finset.induction_on ss ?_ ?_
      · simp [OracleComp.ProgramLogic.wp_const]
      · intro s ss hs ih
        simp [hs, ih, OracleComp.ProgramLogic.wp_add]
    simpa [run] using hsumFin Finset.univ
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z, Pr[= z | run] * (∑ s : S, (z.2.2 s - st₀.2 s : ℝ≥0∞))
      ≤ ∑' z, Pr[= z | run] * (n : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support run
          · have hmono :
                ∀ s : S, st₀.2 s ≤ z.2.2 s :=
              fun s =>
                count_mono_of_mem_support_run_hidingImplCountAll
                  (M := M) (S := S) (C := C) (oa := oa) (st₀ := st₀) (z := z) hz s
            have hsum_counts :
                (∑ s : S, z.2.2 s) ≤ n + ∑ s : S, st₀.2 s :=
              sum_counts_le_of_mem_support_run_hidingImplCountAll
                (M := M) (S := S) (C := C) (oa := oa) hbound (st₀ := st₀) (z := z) hz
            have hdecomp :
                (∑ s : S, (z.2.2 s - st₀.2 s)) + ∑ s : S, st₀.2 s =
                  ∑ s : S, z.2.2 s := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro s hs
              exact Nat.sub_add_cancel (hmono s)
            have hdiff :
                (∑ s : S, (z.2.2 s - st₀.2 s)) ≤ n := by
              omega
            exact mul_le_mul'
              le_rfl
              (by
                exact_mod_cast hdiff)
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

/-- For a fixed computation under the shared counted implementation, the sum of
expected indicators of whether each salt counter ever increases is bounded by the
total query bound. -/
private lemma sum_wp_countIncrementIndicators_le_queryBound_of_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))) ≤ n := by
  classical
  let run := ((simulateQ hidingImplCountAll oa).run st₀)
  have hsum :
      (∑ s : S,
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
            OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))) =
      OracleComp.ProgramLogic.wp run
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          ∑ s : S, OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s)) := by
    have hsumFin :
        ∀ ss : Finset S,
          (ss.sum fun s =>
            OracleComp.ProgramLogic.wp run
              (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
                OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))) =
          OracleComp.ProgramLogic.wp run
            (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
              ss.sum fun s => OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s)) := by
      intro ss
      refine Finset.induction_on ss ?_ ?_
      · simp [OracleComp.ProgramLogic.wp_const]
      · intro s ss hs ih
        simp [hs, ih, OracleComp.ProgramLogic.wp_add]
    simpa [run] using hsumFin Finset.univ
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z, Pr[= z | run] *
        (∑ s : S, OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))
      ≤
        ∑' z, Pr[= z | run] * (n : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support run
          · rcases
                exists_counting_support_of_mem_support_run_hidingImplCountAll_coord
                  (M := M) (S := S) (C := C)
                  (oa := oa) (st₀ := st₀) (z := z) hz with
              ⟨qc, hqc, hcoord⟩
            have hcoordSum :
                (∑ s : S, OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s) : ℝ≥0∞) ≤
                  (∑ s : S, ∑ m : M, qc (m, s) : ℝ≥0∞) := by
              refine Finset.sum_le_sum ?_
              intro s hs
              by_cases hslt : st₀.2 s < z.2.2 s
              · have hsle : z.2.2 s ≤ st₀.2 s + ∑ m : M, qc (m, s) := hcoord s
                have hnat : 1 ≤ ∑ m : M, qc (m, s) := by
                  omega
                simp [OracleComp.ProgramLogic.propInd, hslt]
                exact_mod_cast hnat
              · simp [OracleComp.ProgramLogic.propInd, hslt]
            have htotal :
                (∑ ms : M × S, qc ms) ≤ n := by
              exact IsTotalQueryBound.counting_total_le
                (spec := CMOracle M S C)
                (ι := M × S)
                (oa := oa)
                (n := n)
                (h := hbound)
                hqc
            have hswap :
                (∑ s : S, ∑ m : M, qc (m, s)) = ∑ ms : M × S, qc ms := by
              calc
                (∑ s : S, ∑ m : M, qc (m, s)) = ∑ m : M, ∑ s : S, qc (m, s) := by
                  simpa using (Finset.sum_comm : (∑ s : S, ∑ m : M, qc (m, s)) =
                    ∑ m : M, ∑ s : S, qc (m, s))
                _ = ∑ ms : M × S, qc ms := by
                  symm
                  simpa [Fintype.sum_prod_type]
            have hswap' :
                (∑ s : S, ∑ m : M, qc (m, s) : ℝ≥0∞) =
                  ∑ ms : M × S, qc ms := by
              exact_mod_cast hswap
            have htotal' : (∑ ms : M × S, qc ms : ℝ≥0∞) ≤ n := by
              exact_mod_cast htotal
            exact mul_le_mul'
              le_rfl
              (le_trans hcoordSum (by simpa [hswap'] using htotal'))
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

/-- A selected final count decomposes into the initial selected count plus the
new increments made during the run. -/
private lemma wp_countPred_le_initialPred_add_wp_countIncrement
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (s : S) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll oa).run st₀)
      (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) ≤
    (st₀.2 s - 1 : ℝ≥0∞) +
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
  let run := ((simulateQ hidingImplCountAll oa).run st₀)
  calc
    OracleComp.ProgramLogic.wp run
      (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞))
      ≤
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
            ((st₀.2 s - 1 : ℝ≥0∞) + (z.2.2 s - st₀.2 s : ℝ≥0∞))) := by
              rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
              refine ENNReal.tsum_le_tsum fun z => ?_
              by_cases hz : z ∈ support run
              · have hmono :
                    st₀.2 s ≤ z.2.2 s :=
                  count_mono_of_mem_support_run_hidingImplCountAll
                    (M := M) (S := S) (C := C) (oa := oa) (st₀ := st₀) (z := z) hz s
                have hnat :
                    z.2.2 s - 1 ≤ (st₀.2 s - 1) + (z.2.2 s - st₀.2 s) := by
                  omega
                exact mul_le_mul'
                  le_rfl
                  (by exact_mod_cast hnat)
              · rw [probOutput_eq_zero_of_not_mem_support hz]
                simp
    _ =
      (st₀.2 s - 1 : ℝ≥0∞) +
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
            rw [OracleComp.ProgramLogic.wp_add, OracleComp.ProgramLogic.wp_const]

private lemma sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞))) ≤
    (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) +
      ∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll oa).run st₀)
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)))
      ≤
        ∑ s : S,
          ((st₀.2 s - 1 : ℝ≥0∞) +
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll oa).run st₀)
              (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞))) := by
                refine Finset.sum_le_sum ?_
                intro s hs
                exact wp_countPred_le_initialPred_add_wp_countIncrement
                  (M := M) (S := S) (C := C) oa st₀ s
    _ =
      (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) +
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll oa).run st₀)
            (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
              rw [Finset.sum_add_distrib]

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

private abbrev HidingAvgSpec (M : Type) (S : Type) (C : Type) :=
  (Unit →ₒ S) + CMOracle M S C

private abbrev hidingAvgLeftImpl :
    QueryImpl (Unit →ₒ S)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  (QueryImpl.ofLift (Unit →ₒ S) (OracleComp (HidingAvgSpec M S C))).liftTarget
    (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C)))

private abbrev hidingAvgRightImpl :
    QueryImpl (CMOracle M S C)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  fun t =>
    StateT.mk fun st =>
      OracleComp.liftComp
        ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
        (HidingAvgSpec M S C)

private def hidingAvgQueryImpl :
    QueryImpl (HidingAvgSpec M S C)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  hidingAvgLeftImpl (M := M) (S := S) (C := C) +
    hidingAvgRightImpl (M := M) (S := S) (C := C)

private def hidingAvgComp {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp (HidingAvgSpec M S C) (S × Bool) := do
  let s ← query (spec := HidingAvgSpec M S C) (Sum.inl ())
  let b ← OracleComp.liftComp (hidingOa A s) (HidingAvgSpec M S C)
  pure (s, b)

private lemma run_simulateQ_hidingAvgRightImpl_eq_liftComp {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st : HidingCountState M S C) :
    (simulateQ hidingAvgRightImpl oa).run st =
      OracleComp.liftComp ((simulateQ hidingImplCountAll oa).run st) (HidingAvgSpec M S C) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind,
        OracleComp.liftComp_bind]
      have hstep :
          (hidingAvgRightImpl (M := M) (S := S) (C := C) t).run st =
            OracleComp.liftComp
              ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
              (HidingAvgSpec M S C) := by
        change
          (StateT.mk (fun s =>
            OracleComp.liftComp
              ((hidingImplCountAll (M := M) (S := S) (C := C) t).run s)
              (HidingAvgSpec M S C))).run st =
            OracleComp.liftComp
              ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
              (HidingAvgSpec M S C)
        rfl
      exact OracleComp.bind_congr' hstep (fun p => by
        simpa using ih p.1 p.2)

private lemma run_simulateQ_hidingAvgComp_eq_bind {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0) =
      (liftM (query (spec := Unit →ₒ S) ()) >>= fun s =>
        Prod.map (fun b => (s, b)) id <$>
          OracleComp.liftComp
            ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
            (HidingAvgSpec M S C)) := by
  have hleftrun :
      (simulateQ hidingAvgQueryImpl
          (query (spec := HidingAvgSpec M S C) (Sum.inl ()) : OracleComp (HidingAvgSpec M S C) S)).run
          (∅, fun _ => 0) =
        (liftM (query (spec := Unit →ₒ S) ()) >>= fun s => pure (s, (∅, fun _ => 0))) := by
    simp [hidingAvgQueryImpl, hidingAvgLeftImpl, simulateQ_query]
  rw [hidingAvgComp, simulateQ_bind, StateT.run_bind, hleftrun]
  simp only [bind_assoc, pure_bind]
  refine OracleComp.bind_congr' rfl ?_
  intro s
  rw [simulateQ_bind, StateT.run_bind]
  rw [show simulateQ hidingAvgQueryImpl
      ((hidingOa A s : OracleComp (CMOracle M S C) Bool).liftComp (HidingAvgSpec M S C)) =
        simulateQ hidingAvgRightImpl (hidingOa A s) by
        simpa [hidingAvgQueryImpl, OracleComp.liftComp_eq_liftM] using
          (QueryImpl.simulateQ_add_liftComp_right
            (impl₁' := hidingAvgLeftImpl) (impl₂' := hidingAvgRightImpl)
            (hidingOa A s))]
  rw [run_simulateQ_hidingAvgRightImpl_eq_liftComp]
  change
    ((fun a : Bool × HidingCountState M S C => ((s, a.1), a.2)) <$>
      (liftM ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)) :
        OracleComp (HidingAvgSpec M S C) (Bool × HidingCountState M S C))) =
    ((fun a : Bool × HidingCountState M S C => ((s, a.1), a.2)) <$>
      (liftM ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)) :
        OracleComp (HidingAvgSpec M S C) (Bool × HidingCountState M S C)))
  rfl

/-- Averaged-mass bridge for hiding.

This packages the per-salt bad probabilities into the shared `hidingAvgComp`
run, where the salt is sampled once up front and then the shared count-all
simulation is reused for the rest of the game. -/
theorem sum_probEvent_hidingBad_eq_avg_bad_mass {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) =
    (Fintype.card S : ℝ≥0∞) *
      Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
        (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] := by
  classical
  let P : S → ℝ≥0∞ := fun s =>
    Pr[fun z : Bool × HidingCountState M S C => 2 ≤ z.2.2 s |
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)]
  have hrun := run_simulateQ_hidingAvgComp_eq_bind (M := M) (S := S) (C := C) A
  have hprob :
      Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
          (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] =
        ∑ s : S, Pr[= s | (query (spec := Unit →ₒ S) () : OracleComp (Unit →ₒ S) S)] * P s := by
    rw [hrun, probEvent_bind_eq_tsum, tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hsprob :
        Pr[= s | (query (spec := Unit →ₒ S) () : OracleComp (Unit →ₒ S) S)] =
          (Fintype.card S : ℝ≥0∞)⁻¹ := by
      simpa using (probOutput_query (spec := Unit →ₒ S) () s)
    rw [probEvent_map, probEvent_liftComp, hsprob]
    congr 1
  have hcard0 : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp
  have hcard_top : (Fintype.card S : ℝ≥0∞) ≠ ∞ := by simp
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
        = ∑ s : S, P s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simpa [P] using
              probEvent_hidingBad_eq_countAll (M := M) (S := S) (C := C) A s
    _ = ∑ s : S, (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * P s) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          calc
            P s = 1 * P s := by rw [one_mul]
            _ = ((Fintype.card S : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹) * P s := by
                  rw [ENNReal.mul_inv_cancel hcard0 hcard_top]
            _ = (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * P s) := by
                  rw [mul_assoc]
    _ = (Fintype.card S : ℝ≥0∞) * ∑ s : S, (Fintype.card S : ℝ≥0∞)⁻¹ * P s := by
          rw [Finset.mul_sum]
    _ = (Fintype.card S : ℝ≥0∞) * ∑ s : S,
          Pr[= s | (query (spec := Unit →ₒ S) () : OracleComp (Unit →ₒ S) S)] * P s := by
          simp_rw [probOutput_query]
    _ = (Fintype.card S : ℝ≥0∞) *
          Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
            (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] := by
          rw [hprob]

private lemma probEvent_hidingAvg_bad_le_wp_selectedCountPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
      (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] ≤
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
      (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) := by
  let oa :=
    (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)
  have h :=
    OracleComp.ProgramLogic.markov_bound
      oa
      (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞))
      1
      (fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1)
      (fun z hz => by
        have hnat : (1 : ℕ) ≤ z.2.2 z.1.1 - 1 := by omega
        have hcast : (1 : ℝ≥0∞) ≤ (z.2.2 z.1.1 - 1 : ℝ≥0∞) := by
          exact_mod_cast hnat
        simpa using hcast)
  simpa [oa] using h

private lemma card_mul_wp_hidingAvg_selectedCountPred_eq_sum_wp_countPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (Fintype.card S : ℝ≥0∞) *
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
        (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) =
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
  classical
  let Q : S → ℝ≥0∞ := fun s =>
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))
  have hwp :
      OracleComp.ProgramLogic.wp
          ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
          (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) =
        ∑ s : S,
          Pr[= s | (query (spec := Unit →ₒ S) () : OracleComp (Unit →ₒ S) S)] * Q s := by
    rw [run_simulateQ_hidingAvgComp_eq_bind, OracleComp.ProgramLogic.wp_bind,
      OracleComp.ProgramLogic.wp_eq_tsum, tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_liftComp]
    rfl
  have hcard0 : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp
  have hcard_top : (Fintype.card S : ℝ≥0∞) ≠ ∞ := by simp
  calc
    (Fintype.card S : ℝ≥0∞) *
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
          (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞))
      = (Fintype.card S : ℝ≥0∞) * ∑ s : S,
          Pr[= s | (query (spec := Unit →ₒ S) () : OracleComp (Unit →ₒ S) S)] * Q s := by
            rw [hwp]
    _ = (Fintype.card S : ℝ≥0∞) * ∑ s : S,
          (Fintype.card S : ℝ≥0∞)⁻¹ * Q s := by
            simp_rw [probOutput_query]
    _ = ∑ s : S, (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * Q s) := by
          rw [Finset.mul_sum]
    _ = ∑ s : S, Q s := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          calc
            (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * Q s)
              = ((Fintype.card S : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹) * Q s := by
                  rw [mul_assoc]
            _ = 1 * Q s := by
                  rw [ENNReal.mul_inv_cancel hcard0 hcard_top]
            _ = Q s := by
                  rw [one_mul]
    _ = ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
            (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
          simp [Q]

/-- Textbook outer bridge: the bad-mass sum is bounded by the per-salt
count-pred expectations from the shared counted implementation. -/
theorem sum_probEvent_hidingBad_le_sum_wp_countPred {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) ≤
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
      =
        (Fintype.card S : ℝ≥0∞) *
          Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
            (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] := by
              simpa using sum_probEvent_hidingBad_eq_avg_bad_mass (M := M) (S := S) (C := C) A
    _ ≤
        (Fintype.card S : ℝ≥0∞) *
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
            (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) := by
              exact mul_le_mul' le_rfl (probEvent_hidingAvg_bad_le_wp_selectedCountPred
                (M := M) (S := S) (C := C) A)
    _ =
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
            (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
              simpa using
                card_mul_wp_hidingAvg_selectedCountPred_eq_sum_wp_countPred
                  (M := M) (S := S) (C := C) A

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

/-- One-step counter growth bound for `hidingImpl₁`:
the salt counter is monotone and increases by at most one. -/
theorem hidingImpl₁_counter_le_succ (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImpl₁ s ms).run st)) :
    st.2 ≤ x.2.2 ∧ x.2.2 ≤ st.2 + 1 := by
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingImpl₁, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨Nat.le_refl _, Nat.le_succ _⟩
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
-- Pointwise arithmetic helper: event indicator is bounded by a natural count.
private theorem indicator_le_natCast_count (P : Prop) [Decidable P] (n : ℕ)
    (h : P → 1 ≤ n) : (if P then (1 : ℝ≥0∞) else 0) ≤ n := by
  by_cases hP : P
  · simp [hP, h hP]
  · simp [hP]

private lemma wp_finset_sum {α : Type}
    (oa : OracleComp (CMOracle M S C) α) (ss : Finset S) (f : S → α → ℝ≥0∞) :
    (ss.sum fun s => OracleComp.ProgramLogic.wp oa (f s)) =
      OracleComp.ProgramLogic.wp oa (fun z => ss.sum fun s => f s z) := by
  refine Finset.induction_on ss ?_ ?_
  · simp
  · intro s ss hs ih
    simp [Finset.sum_insert, hs, ih, OracleComp.ProgramLogic.wp_add]

private lemma sum_wp_hidingOa_eq_wp_choose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    (post : S → Bool × HidingCountState M S C → ℝ≥0∞) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (post s)) =
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × HidingCountState M S C =>
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            (fun qch : C × HidingCountState M S C =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (post s))) := by
  classical
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (post s))
      =
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            (fun qch : C × HidingCountState M S C =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (post s))) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        simp [hidingOa, simulateQ_bind, StateT.run_bind, OracleComp.ProgramLogic.wp_bind]
    _ =
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            OracleComp.ProgramLogic.wp
              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
              (fun qch : C × HidingCountState M S C =>
                OracleComp.ProgramLogic.wp
                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                  (post s))) := by
        simpa using
          (wp_finset_sum
            ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
            Finset.univ
            (fun s qchoose =>
              OracleComp.ProgramLogic.wp
                ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                (fun qch : C × HidingCountState M S C =>
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (post s))))

private lemma sum_wp_countPred_eq_wp_choose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) =
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            OracleComp.ProgramLogic.wp
              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
              (fun qch : C × HidingCountState M S C =>
                OracleComp.ProgramLogic.wp
                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                  (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)))) := by
  simpa using
    sum_wp_hidingOa_eq_wp_choose
      (M := M) (S := S) (C := C) A
      (fun s z => (z.2.2 s - 1 : ℝ≥0∞))

private lemma wp_challenge_countPred_le_initialCount
    (m : M) (s : S) (st : HidingCountState M S C) :
    OracleComp.ProgramLogic.wp
      ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)
      (fun qch : C × HidingCountState M S C => (qch.2.2 s - 1 : ℝ≥0∞)) ≤ st.2 s := by
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qch,
        Pr[= qch |
          (hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st] *
          (qch.2.2 s - 1 : ℝ≥0∞)
      ≤
        ∑' qch,
          Pr[= qch |
            (hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st] * st.2 s := by
            refine ENNReal.tsum_le_tsum fun qch => ?_
            by_cases hqch :
                qch ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)
            · exact mul_le_mul'
                le_rfl
                (by
                  exact_mod_cast
                    (challenge_countPred_le_initialCount_of_mem_support_step_hidingImplCountAll
                      (M := M) (S := S) (C := C) m s st hqch))
            · rw [probOutput_eq_zero_of_not_mem_support hqch]
              simp
    _ = st.2 s := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private lemma sum_wp_challenge_countPred_le_initialCount
    (m : M) (st : HidingCountState M S C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)
        (fun qch : C × HidingCountState M S C => (qch.2.2 s - 1 : ℝ≥0∞))) ≤
      (∑ s : S, st.2 s : ℝ≥0∞) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  exact wp_challenge_countPred_le_initialCount (M := M) (S := S) (C := C) m s st

private lemma sum_wp_distinguish_countPred_le_sum_initialPred_add_residual
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) ≤
      (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)) + (t - ∑ s : S, qchoose.2.2 s) := by
  have hsplit :=
    sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements
      (M := M) (S := S) (C := C)
      (oa := A.distinguish qchoose.1.2 cm)
      (st₀ := qchoose.2)
  have hbound :
      IsTotalQueryBound (A.distinguish qchoose.1.2 cm) (t - ∑ s : S, qchoose.2.2 s) :=
    hiding_distinguish_totalBound_of_choose_count_support
      (M := M) (S := S) (C := C) A hqchoose cm
  have hincr :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
          (fun z : Bool × HidingCountState M S C => (z.2.2 s - qchoose.2.2 s : ℝ≥0∞))) ≤
        (t - ∑ s : S, qchoose.2.2 s) := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C)
        (oa := A.distinguish qchoose.1.2 cm)
        (n := t - ∑ s : S, qchoose.2.2 s)
        hbound qchoose.2)
  exact le_trans hsplit (by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hincr (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)))

private lemma sum_wp_countPred_le_sum_initialPred_add_queryBound_of_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : HidingCountState M S C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) ≤
      (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) + n := by
  have hsplit :=
    sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements
      (M := M) (S := S) (C := C) oa st₀
  have hincr :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll oa).run st₀)
          (fun z : α × HidingCountState M S C => (z.2.2 s - st₀.2 s : ℝ≥0∞))) ≤ n := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C) (oa := oa) (n := n) hbound st₀)
  exact le_trans hsplit (by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hincr (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)))

private lemma sum_wp_distinguish_countPred_le_queryBound_of_choose_count_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) ≤ t := by
  have hsplit :=
    sum_wp_distinguish_countPred_le_sum_initialPred_add_residual
      (M := M) (S := S) (C := C) A hqchoose cm
  rcases
      exists_counting_support_of_mem_support_run_hidingImplCountAll_coord
        (M := M) (S := S) (C := C)
        (oa := A.choose)
        (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
        (z := qchoose)
        hqchoose with
    ⟨qcChoose, hqcChoose, hcoordChoose⟩
  have hchooseCounts :
      (∑ s : S, qchoose.2.2 s) ≤ t := by
    have hcoordSum :
        (∑ s : S, qchoose.2.2 s) ≤ ∑ s : S, ∑ m : M, qcChoose (m, s) := by
      refine Finset.sum_le_sum ?_
      intro s hs
      simpa using hcoordChoose s
    have htotal :
        (∑ ms : M × S, qcChoose ms) ≤ t := by
      exact IsTotalQueryBound.counting_total_le
        (spec := CMOracle M S C)
        (ι := M × S)
        (oa := A.choose)
        (n := t)
        (h := hiding_choose_totalBound (M := M) (S := S) (C := C) A)
        hqcChoose
    have hswap :
        (∑ s : S, ∑ m : M, qcChoose (m, s)) = ∑ ms : M × S, qcChoose ms := by
      calc
        (∑ s : S, ∑ m : M, qcChoose (m, s)) = ∑ m : M, ∑ s : S, qcChoose (m, s) := by
          simpa using (Finset.sum_comm : (∑ s : S, ∑ m : M, qcChoose (m, s)) =
            ∑ m : M, ∑ s : S, qcChoose (m, s))
        _ = ∑ ms : M × S, qcChoose ms := by
          symm
          simpa [Fintype.sum_prod_type]
    exact le_trans hcoordSum (by simpa [hswap] using htotal)
  have hpred :
      (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)) ≤ (∑ s : S, qchoose.2.2 s : ℝ≥0∞) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    exact_mod_cast (Nat.sub_le (qchoose.2.2 s) 1)
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)))
      ≤ (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)) + (t - ∑ s : S, qchoose.2.2 s) := hsplit
    _ ≤ (∑ s : S, qchoose.2.2 s : ℝ≥0∞) + (t - ∑ s : S, qchoose.2.2 s) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_right hpred (t - ∑ s : S, qchoose.2.2 s)
    _ = t := by
        have hcast : (∑ s : S, qchoose.2.2 s : ℝ≥0∞) ≤ t := by
          exact_mod_cast hchooseCounts
        rw [add_comm]
        rw [Nat.cast_sum]
        exact tsub_add_cancel_of_le hcast

private lemma sum_wp_distinguish_incrementIndicators_le_queryResidual_of_choose_count_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C =>
          OracleComp.ProgramLogic.propInd (qchoose.2.2 s < z.2.2 s))) ≤
      (t - ∑ s : S, qchoose.2.2 s) := by
  have hbound :
      IsTotalQueryBound (A.distinguish qchoose.1.2 cm) (t - ∑ s : S, qchoose.2.2 s) :=
    hiding_distinguish_totalBound_of_choose_count_support
      (M := M) (S := S) (C := C) A hqchoose cm
  have hres :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
          (fun z : Bool × HidingCountState M S C => (z.2.2 s - qchoose.2.2 s : ℝ≥0∞))) ≤
        (t - ∑ s : S, qchoose.2.2 s) := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C)
        (oa := A.distinguish qchoose.1.2 cm)
        (n := t - ∑ s : S, qchoose.2.2 s)
        hbound qchoose.2)
  have hmono :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
          (fun z : Bool × HidingCountState M S C =>
            OracleComp.ProgramLogic.propInd (qchoose.2.2 s < z.2.2 s))) ≤
        (∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
            (fun z : Bool × HidingCountState M S C => (z.2.2 s - qchoose.2.2 s : ℝ≥0∞))) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    refine OracleComp.ProgramLogic.wp_mono
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2) ?_
    intro z
    by_cases hslt : qchoose.2.2 s < z.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hslt]
      exact_mod_cast (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hslt))
    · simp [OracleComp.ProgramLogic.propInd, hslt]
  exact le_trans hmono hres

private lemma sum_wp_badIndicator_eq_wp_choose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) =
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × HidingCountState M S C =>
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            (fun qch : C × HidingCountState M S C =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) := by
  classical
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
      =
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C =>
          OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        rw [probEvent_hidingBad_eq_countAll (M := M) (S := S) (C := C) A s,
          OracleComp.ProgramLogic.probEvent_eq_wp_propInd]
    _ =
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            OracleComp.ProgramLogic.wp
              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
              (fun qch : C × HidingCountState M S C =>
                OracleComp.ProgramLogic.wp
                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                  (fun z : Bool × HidingCountState M S C =>
                    OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) := by
        simpa using
          sum_wp_hidingOa_eq_wp_choose
            (M := M) (S := S) (C := C) A
            (fun s z => OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))

private lemma wp_badIndicator_le_chooseHit_add_distinguishIncrement_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) ≤
    ∑ s : S,
      (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s)))) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qch,
        Pr[= qch |
          (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
      ≤
        ∑' qch,
          Pr[= qch |
            (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
            (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) := by
            refine ENNReal.tsum_le_tsum ?_
            intro qch
            by_cases hqch :
                qch ∈ support
                  ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            · have hinner :
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
                  ≤
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      OracleComp.ProgramLogic.wp
                        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                        (fun z : Bool × HidingCountState M S C =>
                          OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s)) := by
                rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
                calc
                  ∑' z,
                      Pr[= z |
                        (simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                        OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)
                    ≤
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                            OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s)) := by
                              refine ENNReal.tsum_le_tsum ?_
                              intro z
                              by_cases hz :
                                  z ∈ support
                                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                              · exact mul_le_mul'
                                  le_rfl
                                  (bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator
                                    (M := M) (S := S) (C := C) A hqchoose s hqch hz)
                              · rw [probOutput_eq_zero_of_not_mem_support hz]
                                simp
                  _ =
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s) := by
                            simp_rw [mul_add]
                            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                              HasEvalPMF.tsum_probOutput_eq_one, one_mul]
              exact mul_le_mul' le_rfl hinner
            · rw [probOutput_eq_zero_of_not_mem_support hqch]
              simp
    _ =
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) := by
        rw [OracleComp.ProgramLogic.wp_eq_tsum]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private lemma wp_badIndicator_le_chooseHit_add_freshDistinguishIncrement_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) ≤
    ∑ s : S,
      (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd
                  (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qch,
        Pr[= qch |
          (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
      ≤
        ∑' qch,
          Pr[= qch |
            (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
            (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd
                    (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) := by
            refine ENNReal.tsum_le_tsum ?_
            intro qch
            by_cases hqch :
                qch ∈ support
                  ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            · have hinner :
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
                  ≤
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      OracleComp.ProgramLogic.wp
                        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                        (fun z : Bool × HidingCountState M S C =>
                          OracleComp.ProgramLogic.propInd
                            (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)) := by
                rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
                calc
                  ∑' z,
                      Pr[= z |
                        (simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                        OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)
                    ≤
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                            OracleComp.ProgramLogic.propInd
                              (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)) := by
                              refine ENNReal.tsum_le_tsum ?_
                              intro z
                              by_cases hz :
                                  z ∈ support
                                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                              · exact mul_le_mul'
                                  le_rfl
                                  (bad_indicator_le_chooseHitIndicator_add_freshDistinguishIncrementIndicator
                                    (M := M) (S := S) (C := C) A hqchoose s hqch hz)
                              · rw [probOutput_eq_zero_of_not_mem_support hz]
                                simp
                  _ =
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          OracleComp.ProgramLogic.propInd
                            (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s) := by
                            simp_rw [mul_add]
                            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                              HasEvalPMF.tsum_probOutput_eq_one, one_mul]
              exact mul_le_mul' le_rfl hinner
            · rw [probOutput_eq_zero_of_not_mem_support hqch]
              simp
    _ =
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd
                  (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) := by
        rw [OracleComp.ProgramLogic.wp_eq_tsum]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private lemma sum_chooseHitIndicators_le_sumCounts
    (counts : S → ℕ) :
    (∑ s : S, OracleComp.ProgramLogic.propInd (0 < counts s)) ≤
      (∑ s : S, counts s : ℝ≥0∞) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  by_cases hpos : 0 < counts s
  · simp [OracleComp.ProgramLogic.propInd, hpos]
    exact_mod_cast hpos
  · simp [OracleComp.ProgramLogic.propInd, hpos]

private lemma sum_wp_freshDistinguishIncrement_eq_query
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) =
      ∑ s : S,
        OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
          OracleComp.ProgramLogic.wp
            (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
              OracleComp (CMOracle M S C) C)
            (fun cm =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
                  (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                    Function.update qchoose.2.2 s 1))
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd (1 < z.2.2 s))) := by
  refine Finset.sum_congr rfl ?_
  intro s hs
  exact wp_freshDistinguishIncrement_eq
    (M := M) (S := S) (C := C) A hqchoose s

private lemma wp_choose_sumHitIndicators_le_queryBound
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × HidingCountState M S C =>
        ∑ s : S, OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s)) ≤ t := by
  refine le_trans
    (OracleComp.ProgramLogic.wp_mono
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose =>
        sum_chooseHitIndicators_le_sumCounts qchoose.2.2))
    (wp_choose_sumCounts_le_queryBound (M := M) (S := S) (C := C) A)

private lemma run_simulateQ_loggingOracle_query_bind {α : Type}
    (t : (CMOracle M S C).Domain) (mx : (CMOracle M S C).Range t → OracleComp (CMOracle M S C) α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp (CMOracle M S C) _) >>= fun u =>
        (fun p : α × QueryLog (CMOracle M S C) =>
          (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def, Function.comp]

private lemma sum_querySaltCounts_eq_length
    (log : QueryLog (CMOracle M S C)) :
    (∑ s : S,
      QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) = log.length := by
  classical
  induction log with
  | nil =>
      simp [QueryLog.countQ]
  | cons entry log ih =>
      have hcount : ∀ s : S,
          QueryLog.countQ (entry :: log) (fun t : (CMOracle M S C).Domain => t.2 = s) =
            (if s = entry.1.2 then 1 else 0) +
              QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s) := by
        intro s
        by_cases h : s = entry.1.2
        · simpa [h, Nat.add_comm] using
            (show
              QueryLog.countQ (entry :: log) (fun t : (CMOracle M S C).Domain => t.2 = s) =
                (QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s) + 1) by
              simp [QueryLog.countQ, QueryLog.getQ_cons, h])
        · have h' : ¬ entry.1.2 = s := by simpa [eq_comm] using h
          simp [QueryLog.countQ, QueryLog.getQ_cons, h, h']
      calc
        (∑ s : S,
          QueryLog.countQ (entry :: log) (fun t : (CMOracle M S C).Domain => t.2 = s))
            = ∑ s : S,
                ((if s = entry.1.2 then 1 else 0) +
                  QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) := by
                refine Finset.sum_congr rfl ?_
                intro s hs
                exact hcount s
        _ = (∑ s : S, (if s = entry.1.2 then 1 else 0)) +
              (∑ s : S, QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) := by
                rw [Finset.sum_add_distrib]
        _ = (1 : ℕ) + (∑ s : S, QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) := by
              have hsingle : (∑ s : S, (if s = entry.1.2 then 1 else 0 : ℕ)) = 1 := by
                simp
              rw [hsingle]
        _ = log.length + 1 := by rw [ih, Nat.add_comm]

private lemma sum_querySaltIndicators_le_logLength
    (log : QueryLog (CMOracle M S C)) :
    (∑ s : S,
      OracleComp.ProgramLogic.propInd
        (0 < QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s))) ≤ log.length := by
  have hcounts :
      (∑ s : S,
        QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s) : ℝ≥0∞) = log.length := by
    exact_mod_cast sum_querySaltCounts_eq_length (M := M) (S := S) (C := C) log
  refine le_trans
    (sum_chooseHitIndicators_le_sumCounts
      (counts := fun s => QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s))) ?_
  exact le_of_eq hcounts

private lemma log_length_le_of_mem_support_counting_simulate_run_logging
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {z : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S)}
    (hz : z ∈ support (countingOracle.simulate ((simulateQ loggingOracle oa).run) 0)) :
    z.1.2.length ≤ ∑ ms : M × S, z.2 ms := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x =>
      have hz' :
          z ∈ support
            (countingOracle.simulate (spec := CMOracle M S C) (ι := M × S)
              (pure (x, ([] : QueryLog (CMOracle M S C)))) 0) := by
        simpa [simulateQ_pure] using hz
      rw [countingOracle.mem_support_simulate_pure_iff
        (spec := CMOracle M S C) (ι := M × S)] at hz'
      subst z
      simp
  | query_bind t mx ih =>
      rw [run_simulateQ_loggingOracle_query_bind] at hz
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz⟩ := hz
      have hmap :
          countingOracle.simulate
            (((fun p : α × QueryLog (CMOracle M S C) =>
                (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) ::
                  p.2)) <$> (simulateQ loggingOracle (mx u)).run)) 0 =
            (fun zz : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S) =>
              ((zz.1.1,
                  (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) ::
                    zz.1.2), zz.2)) <$>
              countingOracle.simulate ((simulateQ loggingOracle (mx u)).run) 0 := by
        simp [countingOracle.simulate, Prod.map, simulateQ_map]
      rw [hmap, support_map] at hz
      obtain ⟨w, hzu, hzEq⟩ := hz
      rcases w with ⟨⟨zu, logu⟩, qcu⟩
      have hz1 :
          (zu,
            (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: logu) = z.1 := by
        simpa using congrArg Prod.fst hzEq
      have hzlog :
          (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: logu = z.1.2 := by
        simpa using congrArg Prod.snd hz1
      have hzqc : qcu = Function.update z.2 t (z.2 t - 1) := by
        simpa using congrArg Prod.snd hzEq
      have hlen : logu.length ≤ ∑ ms : M × S, qcu ms :=
        ih u (z := ((zu, logu), qcu)) hzu
      have hsum :
          ∑ ms : M × S, Function.update z.2 t (z.2 t - 1) ms = (∑ ms : M × S, z.2 ms) - 1 := by
        let qpred : QueryCount (M × S) := Function.update z.2 t (z.2 t - 1)
        have hpredsucc : Function.update qpred t (qpred t + 1) = z.2 := by
          funext j
          by_cases hj : j = t
          · subst hj
            simp [qpred]
            omega
          · simp [qpred, Function.update, hj]
        have hsumsucc := sum_update_succ_count (counts := qpred) t
        rw [hpredsucc] at hsumsucc
        dsimp [qpred] at hsumsucc
        omega
      rw [hzqc, hsum] at hlen
      have hsumpos : 0 < ∑ ms : M × S, z.2 ms := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      have hcons :
          ((⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: logu).length
            ≤ ∑ ms : M × S, z.2 ms := by
        have hlt : logu.length < ∑ ms : M × S, z.2 ms := by
          exact lt_of_le_of_lt hlen (Nat.sub_lt hsumpos (by simp))
        simpa using Nat.succ_le_of_lt hlt
      simpa [hzlog] using hcons

private lemma log_length_le_of_mem_support_run_cached_logging
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (cache₀ : QueryCache (CMOracle M S C))
    {z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)) :
    z.1.2.length ≤ n := by
  let cost : QueryCache (CMOracle M S C) → ℕ := fun _ => 0
  have hstep :
      ∀ t : (CMOracle M S C).Domain, ∀ st : QueryCache (CMOracle M S C),
        ∀ x : (CMOracle M S C).Range t × QueryCache (CMOracle M S C),
          x ∈ support ((cachingOracle (spec := CMOracle M S C) t).run st) →
            cost x.2 ≤ cost st + 1 := by
    intro t st x hx
    simp [cost]
  rcases countingOracle.exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
      (spec := CMOracle M S C)
      (ι := M × S)
      (impl := cachingOracle)
      cost hstep hz with ⟨qc, hqc, _⟩
  have hlen :
      z.1.2.length ≤ ∑ ms : M × S, qc ms :=
    log_length_le_of_mem_support_counting_simulate_run_logging
      (M := M) (S := S) (C := C) oa hqc
  have hboundLog :
      IsTotalQueryBound ((simulateQ loggingOracle oa).run) n :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff
      (spec := CMOracle M S C) oa n).2 hbound
  have hqc_le : (∑ ms : M × S, qc ms) ≤ n :=
    IsTotalQueryBound.counting_total_le
      (spec := CMOracle M S C)
      (ι := M × S)
      (oa := (simulateQ loggingOracle oa).run)
      (n := n)
      hboundLog hqc
  exact le_trans hlen hqc_le

private lemma sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (cache₀ : QueryCache (CMOracle M S C))
    (hbound : IsTotalQueryBound oa n) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
        (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          OracleComp.ProgramLogic.propInd
            (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))) ≤ n := by
  classical
  have hsum :=
    wp_finset_sum
      (M := M) (S := S) (C := C)
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
      Finset.univ
      (fun s z =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z,
        Pr[= z | (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀] *
          (∑ s : S,
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
      ≤
        ∑' z,
          Pr[= z | (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀] * n := by
            refine ENNReal.tsum_le_tsum ?_
            intro z
            by_cases hz :
                z ∈ support
                  ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
            · exact mul_le_mul'
                le_rfl
                (le_trans
                  (sum_querySaltIndicators_le_logLength (M := M) (S := S) (C := C) z.1.2)
                  (by
                    exact_mod_cast
                      (log_length_le_of_mem_support_run_cached_logging
                        (M := M) (S := S) (C := C)
                        (oa := oa) (n := n) hbound cache₀ hz)))
            · rw [probOutput_eq_zero_of_not_mem_support hz]
              simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private lemma sum_wp_distinguish_incrementIndicators_le_queryResidual_of_choose_count_support_with_state
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) (qch : C × HidingCountState M S C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
        (fun z : Bool × HidingCountState M S C =>
          OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) ≤
      (t - ∑ s : S, qchoose.2.2 s) := by
  have hbound :
      IsTotalQueryBound (A.distinguish qchoose.1.2 cm) (t - ∑ s : S, qchoose.2.2 s) :=
    hiding_distinguish_totalBound_of_choose_count_support
      (M := M) (S := S) (C := C) A hqchoose cm
  have hres :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
          (fun z : Bool × HidingCountState M S C =>
            (z.2.2 s - qch.2.2 s : ℝ≥0∞))) ≤
        (t - ∑ s : S, qchoose.2.2 s) := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C)
        (oa := A.distinguish qchoose.1.2 cm)
        (n := t - ∑ s : S, qchoose.2.2 s)
        hbound qch.2)
  have hmono :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
          (fun z : Bool × HidingCountState M S C =>
            OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) ≤
        (∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              (z.2.2 s - qch.2.2 s : ℝ≥0∞))) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    refine OracleComp.ProgramLogic.wp_mono
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2) ?_
    intro z
    by_cases hslt : qch.2.2 s < z.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hslt]
      have hsub : 1 ≤ (z.2.2 s - qch.2.2 s : ℕ) := by
        omega
      have hcast : (1 : ℝ≥0∞) ≤ (z.2.2 s - qch.2.2 s : ℝ≥0∞) := by
        exact_mod_cast hsub
      simpa using hcast
    · simp [OracleComp.ProgramLogic.propInd, hslt]
  exact le_trans hmono hres

private lemma sum_wp_querySaltIndicators_le_queryBound_of_run_logging
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ loggingOracle oa).run)
        (fun z : α × QueryLog (CMOracle M S C) =>
          OracleComp.ProgramLogic.propInd
            (0 < QueryLog.countQ z.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))) ≤ n := by
  classical
  have hsum :=
    wp_finset_sum
      (M := M) (S := S) (C := C)
      ((simulateQ loggingOracle oa).run)
      Finset.univ
      (fun s z =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z,
        Pr[= z | (simulateQ loggingOracle oa).run] *
          (∑ s : S,
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
      ≤
        ∑' z, Pr[= z | (simulateQ loggingOracle oa).run] * n := by
          refine ENNReal.tsum_le_tsum ?_
          intro z
          by_cases hz : z ∈ support ((simulateQ loggingOracle oa).run)
          · exact mul_le_mul'
              le_rfl
              (le_trans
                (sum_querySaltIndicators_le_logLength (M := M) (S := S) (C := C) z.2)
                (by
                  exact_mod_cast
                    (log_length_le_of_mem_support_run_simulateQ
                      (spec := CMOracle M S C)
                      (oa := oa) (n := n) hbound hz)))
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private theorem run_cached_logging_proj_eq_cachingOracle
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache₀ : QueryCache (CMOracle M S C)) :
    Prod.map Prod.fst id <$>
        (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀ =
      (simulateQ cachingOracle oa).run cache₀ := by
  induction oa using OracleComp.inductionOn generalizing cache₀ with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [run_simulateQ_loggingOracle_query_bind]
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
      cases ht : cache₀ t with
      | some u =>
          simp [cachingOracle.apply_eq, ht, StateT.run_bind, StateT.run_get, pure_bind]
          simpa [simulateQ_map, StateT.map, StateT.run, Function.comp_def] using ih u cache₀
      | none =>
          simp [cachingOracle.apply_eq, ht, StateT.run_bind, StateT.run_get, pure_bind,
            OracleComp.liftM_run_StateT, StateT.run_modifyGet, MonadLift.monadLift]
          refine bind_congr ?_
          intro u
          simpa [simulateQ_map, StateT.map, StateT.run, Function.comp_def] using
            ih u (cache₀.cacheQuery t u)

private lemma queryLog_countQ_pos_of_mem
    {entry : (t : (CMOracle M S C).Domain) × (CMOracle M S C).Range t}
    {log : QueryLog (CMOracle M S C)}
    {p : (CMOracle M S C).Domain → Prop} [DecidablePred p]
    (hmem : entry ∈ log) (hp : p entry.1) :
    0 < QueryLog.countQ log p := by
  induction log with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      simp [QueryLog.countQ, QueryLog.getQ_cons] at hmem ⊢
      rcases hmem with rfl | hmem
      · simp [hp]
      · by_cases hhd : p hd.1
        · simp [hhd]
        · simp [hhd]
          exact ih hmem

private lemma fresh_incrementIndicator_le_querySaltIndicator_cached_logging
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (cm : C) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
        (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm, Function.update qchoose.2.2 s 1))
      (fun z : Bool × HidingCountState M S C =>
        OracleComp.ProgramLogic.propInd (1 < z.2.2 s))
    ≤
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run
        (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm))
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) := by
  let freshCache : QueryCache (CMOracle M S C) :=
    qchoose.2.1.cacheQuery (qchoose.1.1, s) cm
  let freshState : HidingCountState M S C :=
    (freshCache, Function.update qchoose.2.2 s 1)
  let oa := A.distinguish qchoose.1.2 cm
  let countRun := ((simulateQ hidingImplCountAll oa).run freshState)
  let cacheRun := ((simulateQ cachingOracle oa).run freshCache)
  let cachedLogRun :=
    ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run freshCache)
  let cacheEvent : Bool × QueryCache (CMOracle M S C) → Prop :=
    fun z => ∃ m : M, ∃ v : C, m ≠ qchoose.1.1 ∧ z.2 (m, s) = some v
  rw [← OracleComp.ProgramLogic.probEvent_eq_wp_propInd,
    ← OracleComp.ProgramLogic.probEvent_eq_wp_propInd]
  have hcount_to_cache :
      Pr[fun z : Bool × HidingCountState M S C => 1 < z.2.2 s | countRun] ≤
        Pr[cacheEvent | cacheRun] := by
    dsimp [countRun, cacheRun]
    rw [← run_hidingImplCountAll_proj_eq_cachingOracle
      (M := M) (S := S) (C := C) oa freshState]
    rw [probEvent_map]
    refine probEvent_mono ?_
    intro z hz hgt
    have hcount1 : (Function.update qchoose.2.2 s 1) s = 1 := by
      simp [Function.update]
    have hself1 : ∃ v : C, freshCache (qchoose.1.1, s) = some v := by
      refine ⟨cm, ?_⟩
      simpa [freshCache] using
        (QueryCache.cacheQuery_self qchoose.2.1 (qchoose.1.1, s) cm)
    have hunique1 : ∀ m : M, m ≠ qchoose.1.1 → freshCache (m, s) = none := by
      intro m hm
      have hnone :
          qchoose.2.1 (m, s) = none :=
        cache_none_of_zero_count_of_mem_support_run_hidingChoose
          (M := M) (S := S) (C := C) A hqchoose m s hzero
      have hne : (m, s) ≠ (qchoose.1.1, s) := by
        intro hEq
        exact hm (by simpa using congrArg Prod.fst hEq)
      simpa [freshCache, QueryCache.cacheQuery_of_ne qchoose.2.1 cm hne] using hnone
    rcases exists_new_salt_cacheEntry_of_count_gt_one
        (M := M) (S := S) (C := C) (oa := oa) (m0 := qchoose.1.1) (s := s)
        (cache₀ := freshCache) (counts₀ := Function.update qchoose.2.2 s 1)
        (z := z) hcount1 hself1 hunique1 hz hgt with ⟨m, v, hmne, hcache⟩
    exact ⟨m, v, hmne, hcache⟩
  have hcache_to_log :
      Pr[cacheEvent | cacheRun] ≤
        Pr[fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)
          | cachedLogRun] := by
    dsimp [cacheRun, cachedLogRun]
    rw [← run_cached_logging_proj_eq_cachingOracle
      (M := M) (S := S) (C := C) oa freshCache]
    rw [probEvent_map]
    refine probEvent_mono ?_
    intro z hz hcacheEv
    rcases hcacheEv with ⟨m, v, hmne, hcache⟩
    have hlog :=
      cache_entry_in_log_or_initial oa freshCache z hz (m, s) v hcache
    cases hlog with
    | inl hinit =>
        have hnone :
            qchoose.2.1 (m, s) = none :=
          cache_none_of_zero_count_of_mem_support_run_hidingChoose
            (M := M) (S := S) (C := C) A hqchoose m s hzero
        have hne : (m, s) ≠ (qchoose.1.1, s) := by
          intro hEq
          exact hmne (by simpa using congrArg Prod.fst hEq)
        have hinitnone : freshCache (m, s) = none := by
          simpa [freshCache, QueryCache.cacheQuery_of_ne qchoose.2.1 cm hne] using hnone
        have : some v = none := hinit.symm.trans hinitnone
        cases this
    | inr hentry =>
        rcases hentry with ⟨entry, hmem, hentry_eq, _⟩
        have hsalt : entry.1.2 = s := by
          simpa using congrArg Prod.snd hentry_eq
        exact queryLog_countQ_pos_of_mem
          (M := M) (S := S) (C := C) hmem (by simpa [hsalt])
  exact le_trans hcount_to_cache hcache_to_log

private lemma cacheQuery_swap_of_ne
    (cache : QueryCache (CMOracle M S C))
    {t₀ t₁ : (CMOracle M S C).Domain}
    (u₀ u₁ : C)
    (hne : t₀ ≠ t₁) :
    (cache.cacheQuery t₀ u₀).cacheQuery t₁ u₁ =
      (cache.cacheQuery t₁ u₁).cacheQuery t₀ u₀ := by
  ext t
  by_cases ht₀ : t = t₀
  · subst ht₀
    simp [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne, hne]
  · by_cases ht₁ : t = t₁
    · subst ht₁
      simp [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne, hne.symm]
    · simp [QueryCache.cacheQuery_of_ne, ht₀, ht₁]

private lemma wp_querySaltIndicator_prepend_eq_one
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache : QueryCache (CMOracle M S C))
    (t : (CMOracle M S C).Domain) (u : C) (s : S)
    (hsalt : t.2 = s) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((fun p : α × QueryLog (CMOracle M S C) =>
            (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
          (simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) = 1 := by
  rw [simulateQ_map]
  change OracleComp.ProgramLogic.wp
      (((fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) <$>
        (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache))
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) = 1
  rw [OracleComp.ProgramLogic.wp_map]
  have hpost :
      ((fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) ∘
        fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) =
      fun _ => (1 : ℝ≥0∞) := by
    funext z
    have hpos :
        0 <
          QueryLog.countQ
            ((⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: z.1.2)
            (fun t' : (CMOracle M S C).Domain => t'.2 = s) := by
      simp [QueryLog.countQ, QueryLog.getQ_cons, hsalt]
    simp [OracleComp.ProgramLogic.propInd, hpos]
  rw [hpost, OracleComp.ProgramLogic.wp_const]

private lemma wp_querySaltIndicator_prepend_eq_of_ne
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache : QueryCache (CMOracle M S C))
    (t : (CMOracle M S C).Domain) (u : C) (s : S)
    (hsalt : t.2 ≠ s) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((fun p : α × QueryLog (CMOracle M S C) =>
            (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
          (simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) := by
  rw [simulateQ_map]
  change OracleComp.ProgramLogic.wp
      (((fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) <$>
        (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache))
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s)))
  rw [OracleComp.ProgramLogic.wp_map]
  have hpost :
      ((fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) ∘
        fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) =
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) := by
    funext z
    simp [QueryLog.countQ, QueryLog.getQ_cons, hsalt, OracleComp.ProgramLogic.propInd]
  rw [hpost]

private lemma wp_querySaltIndicator_cached_logging_cacheQuery_eq_of_no_other_salt_entries
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache₀ : QueryCache (CMOracle M S C))
    (m : M) (s : S) (cm : C)
    (hself : cache₀ (m, s) = none)
    (hother : ∀ m' : M, m' ≠ m → cache₀ (m', s) = none) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run
        (cache₀.cacheQuery (m, s) cm))
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) := by
  induction oa using OracleComp.inductionOn generalizing cache₀ with
  | pure x =>
      simp [simulateQ_pure, QueryLog.countQ]
  | query_bind t mx ih =>
      change
        OracleComp.ProgramLogic.wp
          ((simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) t)) >>= fun u =>
              (fun p : α × QueryLog (CMOracle M S C) =>
                (p.1,
                  (⟨t, u⟩ :
                    (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                (simulateQ loggingOracle (mx u)).run)).run
            (cache₀.cacheQuery (m, s) cm))
          (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) =
        OracleComp.ProgramLogic.wp
          ((simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) t)) >>= fun u =>
              (fun p : α × QueryLog (CMOracle M S C) =>
                (p.1,
                  (⟨t, u⟩ :
                    (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                (simulateQ loggingOracle (mx u)).run)).run cache₀)
          (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s)))
      simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
      rw [OracleComp.ProgramLogic.wp_bind, OracleComp.ProgramLogic.wp_bind]
      by_cases hsalt : t.2 = s
      · have hpost :
            (fun qu : C × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.wp
                ((simulateQ cachingOracle
                  ((fun p : α × QueryLog (CMOracle M S C) =>
                      (p.1,
                        (⟨t, (query t).cont qu.1⟩ :
                          (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                    (simulateQ loggingOracle (mx ((query t).cont qu.1))).run)).run qu.2)
                (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                  OracleComp.ProgramLogic.propInd
                    (0 < QueryLog.countQ z.1.2
                      (fun t' : (CMOracle M S C).Domain => t'.2 = s)))) =
            fun _ => (1 : ℝ≥0∞) := by
          funext qu
          exact wp_querySaltIndicator_prepend_eq_one
            (M := M) (S := S) (C := C)
            (oa := mx ((query t).cont qu.1)) (cache := qu.2)
            (t := t) (u := (query t).cont qu.1) (s := s) hsalt
        rw [hpost]
        simp [OracleComp.ProgramLogic.wp_const]
      · have hpost :
            (fun qu : C × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.wp
                ((simulateQ cachingOracle
                  ((fun p : α × QueryLog (CMOracle M S C) =>
                      (p.1,
                        (⟨t, (query t).cont qu.1⟩ :
                          (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                    (simulateQ loggingOracle (mx ((query t).cont qu.1))).run)).run qu.2)
                (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                  OracleComp.ProgramLogic.propInd
                    (0 < QueryLog.countQ z.1.2
                      (fun t' : (CMOracle M S C).Domain => t'.2 = s)))) =
            (fun qu : C × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.wp
                ((simulateQ cachingOracle
                  ((simulateQ loggingOracle (mx ((query t).cont qu.1))).run)).run qu.2)
                (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                  OracleComp.ProgramLogic.propInd
                    (0 < QueryLog.countQ z.1.2
                      (fun t' : (CMOracle M S C).Domain => t'.2 = s)))) := by
          funext qu
          exact wp_querySaltIndicator_prepend_eq_of_ne
            (M := M) (S := S) (C := C)
            (oa := mx ((query t).cont qu.1)) (cache := qu.2)
            (t := t) (u := (query t).cont qu.1) (s := s) hsalt
        rw [hpost]
        have htne : t ≠ (m, s) := by
          intro hEq
          exact hsalt (by simpa using congrArg Prod.snd hEq)
        have hmst_ne_t : (m, s) ≠ t := by
          intro hEq
          exact htne hEq.symm
        have hcache_eq : (cache₀.cacheQuery (m, s) cm) t = cache₀ t := by
          simpa [QueryCache.cacheQuery_of_ne cache₀ cm htne]
        cases ht : cache₀ t with
        | some u =>
            have hcache_hit : (cache₀.cacheQuery (m, s) cm) t = some u := by
              rw [hcache_eq, ht]
            have hcache_fresh_run :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run
                    (cache₀.cacheQuery (m, s) cm) =
                  pure (u, cache₀.cacheQuery (m, s) cm) := by
              simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, hcache_hit, pure_bind, StateT.run_pure]
            have hcache_common_run :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run cache₀ =
                  pure (u, cache₀) := by
              simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, ht, pure_bind, StateT.run_pure]
            rw [hcache_fresh_run, hcache_common_run]
            rw [OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_pure]
            simpa [OracleQuery.cont_query] using ih u cache₀ hself hother
        | none =>
            have hcache_none : (cache₀.cacheQuery (m, s) cm) t = none := by
              rw [hcache_eq, ht]
            have hmiss_fresh :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run
                    (cache₀.cacheQuery (m, s) cm) =
                  (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
                    pure (u, (cache₀.cacheQuery (m, s) cm).cacheQuery t u) :
                      OracleComp (CMOracle M S C) (C × QueryCache (CMOracle M S C))) := by
              simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, pure_bind, hcache_none]
              show (StateT.lift
                  (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t))
                  (cache₀.cacheQuery (m, s) cm) >>= _) = _
              simp only [StateT.lift, bind_assoc, pure_bind,
                modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
                StateT.modifyGet, StateT.run]
            have hmiss_common :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run cache₀ =
                  (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
                    pure (u, cache₀.cacheQuery t u) :
                      OracleComp (CMOracle M S C) (C × QueryCache (CMOracle M S C))) := by
              simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, pure_bind, ht]
              show (StateT.lift (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t)) cache₀ >>= _) = _
              simp only [StateT.lift, bind_assoc, pure_bind,
                modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
                StateT.modifyGet, StateT.run]
            rw [hmiss_fresh, hmiss_common, OracleComp.ProgramLogic.wp_bind,
              OracleComp.ProgramLogic.wp_bind]
            simp_rw [OracleComp.ProgramLogic.wp_pure]
            rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
            refine tsum_congr ?_
            intro u
            congr 1
            have hself' : (cache₀.cacheQuery t u) (m, s) = none := by
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hmst_ne_t] using hself
            have hother' : ∀ m' : M, m' ≠ m → (cache₀.cacheQuery t u) (m', s) = none := by
              intro m' hm'
              have hne' : (m', s) ≠ t := by
                intro hEq
                exact hsalt (by simpa [eq_comm] using congrArg Prod.snd hEq)
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hne'] using hother m' hm'
            simpa [OracleQuery.cont_query,
              cacheQuery_swap_of_ne (M := M) (S := S) (C := C)
              (cache := cache₀) (t₀ := (m, s)) (t₁ := t) cm u hmst_ne_t]
              using ih u (cache₀.cacheQuery t u) hself' hother'

private lemma wp_querySaltIndicator_cached_logging_freshCache_eq_common
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (cm : C) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run
        (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm))
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) := by
  refine wp_querySaltIndicator_cached_logging_cacheQuery_eq_of_no_other_salt_entries
    (M := M) (S := S) (C := C)
    (oa := A.distinguish qchoose.1.2 cm)
    (cache₀ := qchoose.2.1)
    (m := qchoose.1.1) (s := s) (cm := cm) ?_ ?_
  · exact cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  · intro m' hm'
    exact cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose m' s hzero

private lemma sum_wp_freshDistinguishIncrement_le_queryResidual_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) ≤
      (t - ∑ s : S, qchoose.2.2 s) := by
  classical
  rw [sum_wp_freshDistinguishIncrement_eq_query (M := M) (S := S) (C := C) A hqchoose]
  let freshTerm : S → ℝ≥0∞ := fun s =>
    OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
      OracleComp.ProgramLogic.wp
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C)
        (fun cm =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
              (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                Function.update qchoose.2.2 s 1))
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (1 < z.2.2 s)))
  let logTerm : S → ℝ≥0∞ := fun s =>
    OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
      OracleComp.ProgramLogic.wp
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C)
        (fun cm =>
          OracleComp.ProgramLogic.wp
            ((simulateQ cachingOracle
              ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
            (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.propInd
                (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))))
  have hstep : (∑ s : S, freshTerm s) ≤ ∑ s : S, logTerm s := by
    refine Finset.sum_le_sum ?_
    intro s hs
    by_cases hzero : qchoose.2.2 s = 0
    · dsimp [freshTerm, logTerm]
      simp [hzero]
      refine OracleComp.ProgramLogic.wp_mono
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C) ?_
      intro cm
      refine le_trans
        (fresh_incrementIndicator_le_querySaltIndicator_cached_logging
          (M := M) (S := S) (C := C) A hqchoose s hzero cm) ?_
      exact le_of_eq
        (wp_querySaltIndicator_cached_logging_freshCache_eq_common
          (M := M) (S := S) (C := C) A hqchoose s hzero cm)
    · dsimp [freshTerm, logTerm]
      simp [hzero]
  refine le_trans hstep ?_
  have hdrop :
      (∑ s : S, logTerm s)
      ≤
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
            OracleComp (CMOracle M S C) C)
          (fun cm =>
            OracleComp.ProgramLogic.wp
              ((simulateQ cachingOracle
                ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
              (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                OracleComp.ProgramLogic.propInd
                  (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))))) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    by_cases hzero : qchoose.2.2 s = 0
    · dsimp [logTerm]
      simp [hzero]
    · dsimp [logTerm]
      simp [hzero]
  refine le_trans hdrop ?_
  let G : S → C → ℝ≥0∞ := fun s cm =>
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C)
        (fun cm => G s cm))
      = ∑ s : S, ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [OracleComp.ProgramLogic.wp_eq_tsum, tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro cm hcm
          simp [G, probOutput_query]
    _ = ∑ cm : C, ∑ s : S, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm := by
          simpa using (Finset.sum_comm :
            (∑ s : S, ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm) =
              ∑ cm : C, ∑ s : S, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm)
    _ = ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * ∑ s : S, G s cm := by
          refine Finset.sum_congr rfl ?_
          intro cm hcm
          rw [Finset.mul_sum]
    _ ≤ ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * (t - ∑ s : S, qchoose.2.2 s) := by
          refine Finset.sum_le_sum ?_
          intro cm hcm
          exact mul_le_mul' le_rfl
            (by
              simpa [G] using
                (sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging
                  (M := M) (S := S) (C := C)
                  (cache₀ := qchoose.2.1)
                  (oa := A.distinguish qchoose.1.2 cm)
                  (n := t - ∑ s : S, qchoose.2.2 s)
                  (hiding_distinguish_totalBound_of_choose_count_support
                    (M := M) (S := S) (C := C) A hqchoose cm)))
    _ = (t - ∑ s : S, qchoose.2.2 s) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← mul_assoc]
          have hcard0 : (Fintype.card C : ℝ≥0∞) ≠ 0 := by simp
          have hcard_top : (Fintype.card C : ℝ≥0∞) ≠ ∞ := by simp
          rw [ENNReal.mul_inv_cancel hcard0 hcard_top, one_mul]

theorem sum_probEvent_hidingBad_le {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) ≤ t := by
  classical
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
      =
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
          (fun qchoose : (M × AUX) × HidingCountState M S C =>
            ∑ s : S,
              OracleComp.ProgramLogic.wp
                ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                (fun qch : C × HidingCountState M S C =>
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) := by
          simpa using sum_wp_badIndicator_eq_wp_choose (M := M) (S := S) (C := C) A
    _ ≤
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
              OracleComp.ProgramLogic.wp
                ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                (fun qch : C × HidingCountState M S C =>
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd
                        (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))))) := by
          rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
          refine ENNReal.tsum_le_tsum ?_
          intro qchoose
          by_cases hqchoose : qchoose ∈ support
              ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
          · exact mul_le_mul'
              le_rfl
              (wp_badIndicator_le_chooseHit_add_freshDistinguishIncrement_of_choose_support
                (M := M) (S := S) (C := C) A hqchoose)
          · rw [probOutput_eq_zero_of_not_mem_support hqchoose]
            simp
    _ ≤ t := by
      rw [OracleComp.ProgramLogic.wp_eq_tsum]
      calc
        ∑' qchoose,
            Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] *
              (∑ s : S,
                (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                  OracleComp.ProgramLogic.wp
                    ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                    (fun qch : C × HidingCountState M S C =>
                      OracleComp.ProgramLogic.wp
                        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                        (fun z : Bool × HidingCountState M S C =>
                          OracleComp.ProgramLogic.propInd
                            (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))))
          ≤
            ∑' qchoose,
              Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] * t := by
                refine ENNReal.tsum_le_tsum ?_
                intro qchoose
                by_cases hqchoose :
                    qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
                · refine mul_le_mul' le_rfl ?_
                  have hhit :
                      (∑ s : S, OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s)) ≤
                        (∑ s : S, qchoose.2.2 s : ℝ≥0∞) :=
                    sum_chooseHitIndicators_le_sumCounts qchoose.2.2
                  have hfresh :
                      (∑ s : S,
                        OracleComp.ProgramLogic.wp
                          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                          (fun qch : C × HidingCountState M S C =>
                            OracleComp.ProgramLogic.wp
                              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                              (fun z : Bool × HidingCountState M S C =>
                                OracleComp.ProgramLogic.propInd
                                  (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) ≤
                        (t - ∑ s : S, qchoose.2.2 s) :=
                    sum_wp_freshDistinguishIncrement_le_queryResidual_of_choose_support
                      (M := M) (S := S) (C := C) A hqchoose
                  have hcounts :
                      (∑ s : S, qchoose.2.2 s) ≤ t :=
                    sum_counts_le_queryBound_of_mem_support_run_hidingChoose
                      (M := M) (S := S) (C := C) A hqchoose
                  calc
                    (∑ s : S,
                      (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                        OracleComp.ProgramLogic.wp
                          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                          (fun qch : C × HidingCountState M S C =>
                            OracleComp.ProgramLogic.wp
                              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                              (fun z : Bool × HidingCountState M S C =>
                                OracleComp.ProgramLogic.propInd
                                  (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))))
                      = (∑ s : S, OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s)) +
                          (∑ s : S,
                            OracleComp.ProgramLogic.wp
                              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                              (fun qch : C × HidingCountState M S C =>
                                OracleComp.ProgramLogic.wp
                                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                                  (fun z : Bool × HidingCountState M S C =>
                                    OracleComp.ProgramLogic.propInd
                                      (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) := by
                          rw [Finset.sum_add_distrib]
                    _ ≤ (∑ s : S, qchoose.2.2 s : ℝ≥0∞) + (t - ∑ s : S, qchoose.2.2 s) := by
                          exact add_le_add hhit hfresh
                    _ = t := by
                          have hcast : (∑ s : S, qchoose.2.2 s : ℝ≥0∞) ≤ t := by
                            exact_mod_cast hcounts
                          rw [add_comm, Nat.cast_sum]
                          exact tsub_add_cancel_of_le hcast
                · rw [probOutput_eq_zero_of_not_mem_support hqchoose]
                  simp
    _ = t := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

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
