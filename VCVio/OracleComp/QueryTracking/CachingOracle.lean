/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# Caching Queries Made by a Computation

This file defines a modifier `QueryImpl.withCaching` that modifies a query implementation to
cache results to return to the same query in the future.

We also define `cachingOracle`, which caches queries to the oracles in `spec`,
querying fresh values from `spec` if no cached value exists.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a query implementation to cache previous call and return that output in the future. -/
def withCaching (so : QueryImpl spec m) : QueryImpl spec (StateT spec.QueryCache m) :=
  fun t => do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)

@[simp] lemma withCaching_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCaching t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

section CacheMonotonicity

variable [spec.DecidableEq]

omit [spec.DecidableEq] in
/-- Running `withCaching` at state `cache` produces a result whose cache is `≥ cache`.
On a cache hit the state is unchanged; on a miss a single entry is added. -/
lemma withCaching_cache_le [LawfulMonad m] [HasEvalSet m]
    (so : QueryImpl spec m) (t : spec.Domain) (cache₀ : QueryCache spec)
    (z) (hz : z ∈ support ((so.withCaching t).run cache₀)) :
    cache₀ ≤ z.2 := by
  simp only [withCaching_apply, StateT.run_bind] at hz
  have hget : (get : StateT spec.QueryCache m spec.QueryCache).run cache₀ =
      pure (cache₀, cache₀) := rfl
  rw [hget, pure_bind] at hz
  cases ht : cache₀ t with
  | some u =>
    simp only [ht] at hz
    have hrun : (pure u : StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        pure (u, cache₀) := rfl
    rw [hrun] at hz
    simp at hz; rw [hz]
  | none =>
    simp only [ht, StateT.run_bind] at hz
    have hlift : (liftM (so t) : StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        so t >>= fun v => pure (v, cache₀) := by
      show StateT.lift (so t) cache₀ = _; rfl
    rw [hlift, bind_assoc] at hz
    simp only [pure_bind] at hz
    rcases (mem_support_bind_iff _ _ _).1 hz with ⟨v, _, hmod⟩
    have : (modifyGet fun c => (v, QueryCache.cacheQuery c t v) :
        StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        pure (v, cache₀.cacheQuery t v) := rfl
    rw [this] at hmod
    simp at hmod
    rw [hmod]
    exact QueryCache.le_cacheQuery cache₀ ht

/-- `withCaching` preserves the invariant `(cache₀ ≤ ·)` (the cache only grows). -/
lemma PreservesInv.withCaching_le {ι₀ : Type} {spec₀ : OracleSpec.{0,0} ι₀}
    [DecidableEq ι₀] [spec₀.DecidableEq]
    (so : QueryImpl spec₀ ProbComp) (cache₀ : QueryCache spec₀) :
    QueryImpl.PreservesInv (so.withCaching) (cache₀ ≤ ·) :=
  fun t cache hle z hz => le_trans hle (withCaching_cache_le so t cache z hz)

end CacheMonotonicity

end QueryImpl

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCaching

namespace cachingOracle

lemma apply_eq (t : spec.Domain) : cachingOracle t =
    (do match (← get) t with
      | Option.some u => return u
      | Option.none =>
          let u ← query t
          modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

/-- On a cache hit, `cachingOracle` is deterministic: it returns the cached value
and leaves the cache unchanged. -/
@[simp] lemma run_apply_hit (t : spec.Domain) (cache : QueryCache spec)
    (u : spec.Range t) (h : cache t = some u) :
    (cachingOracle t).run cache = pure (u, cache) := by
  simp [apply_eq, h]

/-- Any support point of `cachingOracle` preserves the initial cache by monotonicity. -/
lemma cache_le_of_mem_support_run_apply (t : spec.Domain) (cache : QueryCache spec)
    (z : spec.Range t × QueryCache spec)
    (hz : z ∈ support ((cachingOracle t).run cache)) :
    cache ≤ z.2 :=
  QueryImpl.withCaching_cache_le (m := OracleComp spec)
    (QueryImpl.ofLift spec (OracleComp spec)) t cache z hz

theorem isTotalQueryBound_run_simulateQ {α : Type u} {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) (cache : QueryCache spec) :
    IsTotalQueryBound ((simulateQ (cachingOracle (spec := spec)) oa).run cache) n := by
  induction oa using OracleComp.inductionOn generalizing n cache with
  | pure x =>
      simpa [simulateQ_pure] using
        (show IsTotalQueryBound (pure (x, cache) : OracleComp spec (α × QueryCache spec)) n
          from trivial)
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      cases ht : cache t with
      | some u =>
          simpa [cachingOracle.apply_eq, ht, StateT.run_bind, StateT.run_get, pure_bind] using
            IsTotalQueryBound.mono (ih u (h.2 u) cache) (Nat.sub_le _ _)
      | none =>
          have hq : IsTotalQueryBound
              (liftM (query t) : OracleComp spec (spec.Range t)) 1 := by
            rw [show (liftM (query t) : OracleComp spec (spec.Range t)) =
              (liftM (query t) >>= pure) by simp]
            rw [isTotalQueryBound_query_bind_iff]
            exact ⟨Nat.one_pos, fun _ => trivial⟩
          have hrest : ∀ u : spec.Range t,
              IsTotalQueryBound
                ((simulateQ (cachingOracle (spec := spec)) (mx u)).run (cache.cacheQuery t u))
                (n - 1) :=
            fun u => ih u (h.2 u) (cache.cacheQuery t u)
          have hn : 1 + (n - 1) = n := by omega
          simpa [cachingOracle.apply_eq, ht, hn, StateT.run_bind, StateT.run_get, pure_bind,
            OracleComp.liftM_run_StateT, StateT.run_modifyGet, MonadLift.monadLift] using
            isTotalQueryBound_bind hq hrest

@[simp]
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0,0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    Pr[⊥ | (simulateQ (cachingOracle (spec := spec₀)) oa).run cache] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0,0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    NeverFail ((simulateQ (cachingOracle (spec := spec₀)) oa).run cache) ↔ NeverFail oa := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    HasEvalPMF.probFailure_eq_zero, HasEvalPMF.probFailure_eq_zero]

end cachingOracle
