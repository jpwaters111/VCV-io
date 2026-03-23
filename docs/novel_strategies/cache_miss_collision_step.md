# Novel Proof Strategy: Cache-Miss Collision Step

**Randomization Seed**: `0xA7F3B2D1E9C4` (for reproducible exploration)

## The Problem

Prove: when drawing `u` uniformly from `spec.Range t` and adding to a cache with `s` entries at distinct inputs, `Pr[new collision] ≤ s/|C|`.

A "new collision" means: ∃ t' ≠ t in cache with `cache t' = some u'` and `HEq u u'`.

## Why It's Hard

`HEq u u'` where `u : spec.Range t` and `u' : spec.Range t'` — the types may differ. In standard probability, this is trivial (uniform sample matches a fixed target with prob 1/N). But Lean's dependent types make "matches" require `HEq` across potentially different types.

## Novel Strategy 1: Type-Erased Collision via Finset Injection

**Idea**: Don't reason about `HEq` directly. Instead, show that the set of "bad" values `{u | CacheHasCollision (cache.cacheQuery t u)}` injects into the set of cached keys.

**Why it works**: For each bad `u`, there exists a unique `t'` in the cache such that `HEq u (cache t')`. The uniqueness comes from: if `HEq u₁ u'` and `HEq u₂ u'` for the same `u'`, then `HEq u₁ u₂`, and since `u₁, u₂ : spec.Range t` (same type), `u₁ = u₂`.

**Formalization**: `|bad_set| ≤ |cached_keys| ≤ s`. Then `Pr[u ∈ bad_set] = |bad_set|/|spec.Range t| ≤ s/|C|`.

**Status**: Proof logic is correct but Lean typeclass synthesis fails on `Finset.filter` with `CacheHasCollision` (not decidable). Fix: use `open Classical` or define a decidable approximation.

## Novel Strategy 2: Constant-Range Specialization

**Idea**: Prove the lemma first for specs where `∀ t₁ t₂, spec.Range t₁ = spec.Range t₂` (constant range). Then `HEq` reduces to `Eq` via `heq_iff_eq`. The general case follows because collision across different-cardinality ranges has probability 0.

**Formalization**:
```lean
-- For constant-range specs (like CMOracle):
lemma pr_collision_constant_range [h : ∀ t, spec.Range t = C] : ...
-- General case: split by whether Range t₁ = Range t₂
```

**Advantage**: Avoids all `HEq` headaches. Sufficient for the commitment scheme application (CMOracle has constant range `C`).

## Novel Strategy 3: Via Fintype.card and Counting

**Idea**: Instead of reasoning about `HEq` values, count how many elements of `spec.Range t` can possibly be `HEq` to elements of `spec.Range t'`.

For any `u' : spec.Range t'`:
- If `spec.Range t` and `spec.Range t'` are not definitionally equal, then `{u : spec.Range t | HEq u u'} = ∅` (no u is HEq to u')
- If they ARE equal, then `{u : spec.Range t | HEq u u'} = {cast eq u'}` (exactly one element)

Either way, `|{u | HEq u u'}| ≤ 1`. Union over `s` cached entries: `|bad_set| ≤ s`.

**Key lemma needed**:
```lean
lemma card_heq_singleton (u' : spec.Range t') :
    Finset.card (Finset.filter (fun u : spec.Range t => HEq u u') Finset.univ) ≤ 1
```

## Novel Strategy 4: Seeded Oracle Detour

**Idea**: Instead of reasoning about cachingOracle's cache state, use the seeded oracle equivalence:
1. `simulateQ cachingOracle oa` ≈ `simulateQ (seededOracle seed) oa` averaged over random seeds
2. Under seeded oracle, the "cache" is pre-determined by the seed
3. Collision in the cache = collision among pre-sampled seed values
4. Birthday bound on pre-sampled values is purely combinatorial (no HEq needed for constant specs)

**Advantage**: Completely avoids the cache-miss step by reformulating the problem.

**Challenge**: Need `evalDist_simulateQ_run'_eq_evalDist`-style equivalence between caching and seeded oracles. The `eagerRandomOracle` in `RandomOracle.lean` partially does this but has a sorry.

## Novel Strategy 5: Probabilistic Indicator Function

**Idea**: Express `Pr[collision]` as an expectation of an indicator:
```
Pr[CacheHasCollision (cache.cacheQuery t u)]
= E_u[𝟙{CacheHasCollision (cache.cacheQuery t u)}]
= ∑ u, (1/|C|) * 𝟙{CacheHasCollision (cache.cacheQuery t u)}
= |bad_set| / |C|
≤ s / |C|
```

This uses `probEvent_eq_sum_fintype_ite` to convert the probability to a sum, then bounds the sum by counting the indicator's support.

**Formalization**: Needs `Pr[p | uniform_sample] = |{x | p x}| / |total|` which should follow from `probOutput_query` + `probEvent_eq_tsum_ite`.

## Recommended Next Step

**Strategy 5** is the most Lean-idiomatic: express probability as a normalized count, then bound the count via **Strategy 1** (injection). The `open Classical` fix resolves decidability. The `HEq` injection argument in Strategy 1 is mathematically correct — it just needs careful Lean 4 encoding with `Subtype.ext` and `eq_of_heq`.
