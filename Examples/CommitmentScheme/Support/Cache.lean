/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, jpwaters
-/

import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.EvalDist

/-!
# Commitment Scheme generic cache support

Cache predicates and monotonicity facts used by random-oracle security proofs.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-- A cache has a collision: two distinct inputs map to the same output. -/
def CacheHasCollision (cache : QueryCache spec) : Prop :=
  ∃ (t₁ t₂ : spec.Domain) (u₁ : spec.Range t₁) (u₂ : spec.Range t₂),
    t₁ ≠ t₂ ∧ cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ HEq u₁ u₂

/-- A later cache contains a fresh entry whose output matches an entry already
present in the initial cache.

Lean event/game: this is the generic fresh-hit event used by origin-aware
Merkle binding to separate adversary-cache hits from verifier-rest collisions.

Scope note: excluding or bounding this event is what permits a separate
`(depth + 1)^2 / |C|` verifier-rest term. -/
def FreshHitInitialCache (cache₀ cache₁ : QueryCache spec) : Prop :=
  ∃ (tNew tOld : spec.Domain) (uNew : spec.Range tNew) (uOld : spec.Range tOld),
    cache₀ tNew = none ∧ cache₁ tNew = some uNew ∧
      cache₀ tOld = some uOld ∧ tNew ≠ tOld ∧ HEq uNew uOld

/-- In a collision-free cache, a value determines at most one query input. -/
lemma cache_lookup_eq_of_noCollision
    {cache : QueryCache spec}
    {t₀ t₁ : spec.Domain} {v : spec.Range t₀}
    (hno : ¬ CacheHasCollision cache)
    (h₀ : cache t₀ = some v)
    (h₁ : ∃ v' : spec.Range t₁, cache t₁ = some v' ∧ HEq v' v) :
    t₀ = t₁ := by
  rcases h₁ with ⟨v', hcache₁, hv'⟩
  by_contra hne
  exact hno ⟨t₀, t₁, v, v', hne, h₀, hcache₁, hv'.symm⟩

/-- `simulateQ cachingOracle` only grows the cache: for any `oa`, if
`z ∈ support ((simulateQ cachingOracle oa).run cache₀)` then `cache₀ ≤ z.2`. -/
theorem simulateQ_cachingOracle_cache_le {α : Type}
    (oa : OracleComp spec α) (cache₀ : QueryCache spec)
    (z : α × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle oa).run cache₀)) :
    cache₀ ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    simp [simulateQ_pure, StateT.run] at hmem
    rw [hmem]
  | query_bind t mx ih =>
    simp only [simulateQ_query_bind, StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hmid, hrest⟩ := hmem
    have hle_mid : cache₀ ≤ cache_mid := by
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.run_bind, StateT.run_get, pure_bind] at hmid
      unfold cachingOracle at hmid
      exact QueryImpl.withCaching_cache_le _ _ cache₀ _ hmid
    exact le_trans hle_mid (ih _ cache_mid z hrest)

end OracleComp
