# Novel Proof Strategy: Hiding Game Redesign

**Randomization Seed**: `0x5E8D1A3F7B02` (for reproducible exploration)

## The Problem

The current hiding game formulation has two design issues:
1. Bad flag triggers on the challenge query `(m, s)` itself → `Pr[bad] = 1`
2. Intermediate game caches at `(m, s)` while sim caches at `(default, default)` → observable difference

## Novel Strategy 1: Split the Computation into Three Phases

**Idea**: Restructure `hidingOa` to explicitly separate three phases:
1. **Choose phase**: `A.choose` runs with bad-tracking oracle
2. **Challenge phase**: A single query `(m, s)` — NOT tracked by bad
3. **Distinguish phase**: `A.distinguish aux cm` runs with bad-tracking oracle

The bad event only captures: "the adversary queried a point with salt = s during choose or distinguish, NOT the challenge query."

```lean
def hidingOa (A : HidingAdversary ...) (s : S) : OracleComp (CMOracle M S C) Bool := do
  let (m, aux) ← A.choose          -- phase 1: bad-tracked
  let cm ← query (m, s)             -- phase 2: NOT bad-tracked
  A.distinguish aux cm              -- phase 3: bad-tracked
```

The implementations differ only in phase 2:
- `impl₁` (real): query `(m, s)` normally (cache + return)
- `impl₂` (sim): query `(m, s)` but return a FRESH uniform value (don't use cache for this specific query)

**How to formalize**: Use a 3-element enum in the state to track which phase we're in. The bad flag is only set during phases 1 and 3.

## Novel Strategy 2: External Salt Sampling

**Idea**: Sample the salt OUTSIDE the caching oracle, as a separate random draw. The game becomes:

```lean
def hidingReal (A : ...) : ProbComp Bool := do
  let s ← $ᵗ S                      -- sample salt externally
  (simulateQ cachingOracle (do
    let (m, aux) ← A.choose
    let cm ← query (m, s)
    A.distinguish aux cm)).run' ∅

def hidingSim (A : ...) : ProbComp Bool := do
  let s ← $ᵗ S                      -- sample salt (unused)
  (simulateQ cachingOracle (do
    let (m, aux) ← A.choose
    let cm ← query (default, default)  -- independent of m
    A.distinguish aux cm)).run' ∅
```

Now `Pr[bad]` is averaged over random `s`. For each adversary execution path with ≤ t queries, the set of queried salts has size ≤ t. So `Pr[s ∈ queried_salts] ≤ t/|S|`.

**Advantage**: The standard textbook argument works directly. The salt is random, so the bound follows from a counting argument.

**Challenge**: Moves from `OracleComp` to `ProbComp` (needs `$ᵗ S`), which changes the type signature of `hiding_bound`.

## Novel Strategy 3: Bijection Argument (Pedersen-style)

**Idea**: Instead of identical-until-bad, prove that the challenge commitment's distribution is uniform REGARDLESS of the adversary's queries.

In the caching oracle model, if `(m, s)` was NOT previously queried, then `query (m, s)` returns uniform over C (cache miss). If it WAS queried, it returns the cached value — but this is still uniform (it was sampled uniformly on first query).

So in BOTH cases, `cm` is uniform over C! The real and sim games are actually PERFECTLY hiding in the caching model too, not just statistically.

Wait — that's not right. If the adversary queried `(m, s)` during choose, it KNOWS the value `H(m, s)`. So when it receives `cm = H(m, s)`, it can check if `cm` matches its cached value. In the sim game, `cm` is independent. So the adversary CAN distinguish.

The statistical gap is exactly `Pr[adversary queried (m, s)] ≤ t/|S|`.

## Novel Strategy 4: Lazy-to-Eager via Program Refinement

**Idea**: Use `evalDist_simulateQ_run'_eq_evalDist` to show that the caching oracle preserves output distribution. Then:
1. `hidingReal` under caching = `hidingReal` under evalDist (for the OUTPUT, ignoring cache state)
2. `hidingSim` under caching = `hidingSim` under evalDist
3. In evalDist, both games have the same output distribution (proven in `basic_commitment_scheme_hiding.lean`)
4. Therefore the caching versions also agree on output distribution

**Wait**: This would prove PERFECT hiding, which is too strong (the adversary CAN distinguish in the caching model). The issue: `evalDist_simulateQ_run'_eq_evalDist` preserves the OUTPUT distribution but not the JOINT distribution of (output, cache_state). The adversary's distinguish phase depends on the cache state (its queries get cached responses), not just the challenge commitment.

So this approach would only work if we could separate the choose+distinguish oracle from the challenge oracle, which brings us back to Strategy 1.

## Novel Strategy 5: Two-Oracle Decomposition

**Idea**: Use TWO oracle specs: one for the adversary's queries, one for the challenge. The adversary interacts with `spec₁`, the challenge uses `spec₂`. These are independent.

```lean
-- Adversary oracle: CMOracle M S C
-- Challenge oracle: a separate single-query oracle returning C
def challengeSpec : OracleSpec Unit := fun _ => C
```

The real game queries the challenge oracle at `()` and returns the result. The sim game does the same. But the challenge oracle is INDEPENDENT of the adversary's oracle.

**Advantage**: Independence is baked into the type. The challenge commitment is uniform regardless of adversary queries.

**Challenge**: The adversary might query `(m, s)` to its OWN oracle, getting a value that's INDEPENDENT of the challenge commitment. This is the wrong model — in the real scheme, the challenge commitment IS `H(m, s)` from the SAME oracle.

So we need a correlation between the two oracles at point `(m, s)`. This brings back the full complexity.

## Recommended Path

**Strategy 2** (external salt sampling) is the most aligned with the textbook. It changes the theorem signature slightly but gives a clean `Pr[bad] ≤ t/|S|` via counting. Combined with **Strategy 1** (three-phase separation) for the by_upto setup, this should yield a complete proof.

The key insight: sample `s ← $ᵗ S` OUTSIDE the caching oracle. Then for any fixed adversary execution (which determines a set of ≤ t queried salts), `Pr[s ∈ queried_salts | s uniform] ≤ t/|S|`.
