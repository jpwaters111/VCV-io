# Knowledge: Hiding Theorem & Library Improvements for Random Oracle Commitment Scheme

## Goal

Prove statistical hiding for the random oracle commitment scheme:
```
|Pr[= true | hiding_real A] - Pr[= true | hiding_sim A]| ≤ t / 2^s
```

And identify library improvements needed to support this proof.

---

## Hiding Theorem Structure

### Games

- **Real game**: Adversary chooses `m`, challenger samples `s ←$ S`, computes `cm = H(m,s)`,
  adversary distinguishes with oracle access
- **Simulated game**: Adversary chooses `m`, challenger samples `cm ←$ C` uniformly,
  adversary distinguishes with oracle access
- **Bad event**: Adversary has already queried `(m, s)` before `s` is sampled

### Key Insight

`H` is a random oracle. For a fresh query `(m,s)` not in the cache, the response is
uniform over `C`. So `H(m,s)` for fresh `s` is indistinguishable from a uniform sample
of `C` — UNLESS the adversary already queried `(m,s)`.

Since `s` is uniform over `S` (size `2^s`) and the adversary made ≤ `t` queries,
`Pr[bad] ≤ t / 2^s`.

---

## Core Framework: Identical-Until-Bad

### Main Theorem (VCVio/ProgramLogic/Relational/SimulateQ.lean)

```lean
theorem tvDist_simulateQ_le_probEvent_bad
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (oa : OracleComp spec α) (s₀ : σ)
    (h_init : ¬bad s₀)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal
```

### The `by_upto` Tactic

```lean
by_upto bad
```

Applies `tvDist_simulateQ_le_probEvent_bad` automatically. Leaves 4 subgoals:
1. `¬bad s₀` — initial state is not bad
2. Agreement off bad — implementations agree when state is not bad
3. Monotonicity for impl₁ — bad is absorbing
4. Monotonicity for impl₂ — bad is absorbing

---

## TV Distance Infrastructure (VCVio/EvalDist/TVDist.lean)

```lean
def tvDist (mx my : m α) : ℝ := SPMF.tvDist (evalDist mx) (evalDist my)
```

Key lemmas:
- `tvDist_self`, `tvDist_comm`, `tvDist_triangle`, `tvDist_le_one`
- `tvDist_map_le` — data processing inequality
- `tvDist_bind_right_le` — post-processing inequality
- `tvDist_le_probEvent_of_probOutput_eq_of_not` — **critical**: if outputs agree on ¬bad
  and bad-event probability is equal, then `tvDist ≤ Pr[bad].toReal`

---

## Uniform Sampling (VCVio/OracleComp/Constructions/SampleableType.lean)

```lean
class SampleableType (β : Type) where
  selectElem : ProbComp β
  mem_support_selectElem (x : β) : x ∈ support selectElem
  probOutput_selectElem_eq (x y : β) : Pr[= x | selectElem] = Pr[= y | selectElem]

def uniformSample (β : Type) [SampleableType β] : ProbComp β := selectElem
prefix : 90 "$ᵗ" => uniformSample
```

Key lemma:
```lean
probOutput_uniformSample [Fintype α] (x : α) :
    Pr[= x | $ᵗ α] = (Fintype.card α : ℝ≥0∞)⁻¹
```

For bijection-based arguments:
```lean
probOutput_bind_bijective_uniform_cross : -- uniform composed with bijection = uniform
```

---

## Caching Oracle for Lazy Sampling

```lean
cachingOracle : QueryImpl spec (StateT spec.QueryCache (OracleComp spec))
```

- `spec.QueryCache = (t : spec.Domain) → Option (spec.Range t)`
- Cache miss → fresh uniform query + cache update
- Cache hit → return cached value
- Cache is monotone (only grows)

### Why This Matters for Hiding

The real game uses `cachingOracle` (lazy sampling). The simulated game uses a modified
oracle that returns uniform values even on cache hits for the challenge query. The two
agree UNLESS the adversary has already cached `(m, s)`, which is the bad event.

---

## Game-Hopping Tactics

### `by_equiv` — Enter Relational Mode

Transforms `g₁ ≡ₚ g₂` into `RelTriple g₁ g₂ (EqRel α)`.

### `game_trans g₂` — Split Game Hop

Splits `g₁ ≡ₚ g₃` into `g₁ ≡ₚ g₂` and `g₂ ≡ₚ g₃`.

### `rvcgen_step` / `rvcgen` — Relational VCGen

Decompose relational goals step by step. `rvcgen_step using R` provides
explicit intermediate relations.

### `relTriple_simulateQ_run` — Relational simulateQ

Lifts per-query relational invariants to full computation:
if each query step preserves `R_state s₁ s₂` and produces equal outputs,
then the full `simulateQ` preserves the same invariant.

---

## Proof Outline for Hiding

### Step 1: Restructure Games

Define both games as `simulateQ` with different oracle implementations over a shared
adversary computation:

```lean
-- Real: caching oracle + challenge commitment via query
def realImpl : QueryImpl (CMOracle M S C) (StateT QueryCache (OracleComp ...)) :=
  cachingOracle

-- Sim: caching oracle but challenge commitment is fresh uniform
def simImpl : QueryImpl (CMOracle M S C) (StateT QueryCache (OracleComp ...)) :=
  -- Same as cachingOracle, but for the challenge query (m, s_challenge),
  -- always return fresh uniform regardless of cache
```

### Step 2: Define Bad Event

```lean
def bad (m_challenge : M) (s_challenge : S) (cache : QueryCache) : Prop :=
  cache (m_challenge, s_challenge) ≠ none
```

Bad = the adversary has already queried `(m, s)` before the challenge is issued.

### Step 3: Apply `by_upto`

```lean
by_upto (bad m s)
-- Subgoal 1: ¬bad on empty cache → trivial
-- Subgoal 2: agreement when ¬bad → both return same fresh uniform value
-- Subgoal 3-4: monotonicity → cache only grows, so bad is absorbing
```

### Step 4: Bound Pr[bad]

After `by_upto`, remaining goal: `Pr[bad | ...].toReal ≤ t / 2^s`

- Adversary makes ≤ `t` queries (from `IsQueryBound`)
- Each query caches one `(m_i, s_i)` pair
- `s_challenge` is uniform over `S` of size `2^s`, independent of queries
- `Pr[s_challenge ∈ {s₁, ..., s_t}] ≤ t / |S| = t / 2^s`

Use `probEvent_bind_eq_tsum` + `IsPerIndexQueryBound.counting_bounded` to formalize.

---

## Library Improvements Needed

### 1. Missing: Birthday Bound Lemma (High Priority)

**Current state**: `SumSquares.lean` has the algebraic inequalities, but there is no
dedicated birthday bound lemma connecting query count to collision probability for
random oracles.

**Needed**:
```lean
theorem birthday_bound [Fintype C] (oa : OracleComp spec α) (t : ℕ)
    (ht : IsPerIndexQueryBound oa t) :
    Pr[collision in trace | simulateQ loggingOracle oa] ≤ t * (t-1) / (2 * Fintype.card C)
```

**Where**: `VCVio/OracleComp/QueryTracking/` or `VCVio/CryptoFoundations/`

### 2. Missing: Lazy Sampling ↔ Eager Sampling Equivalence

**Current state**: `cachingOracle` exists but there's no formal proof that
`simulateQ cachingOracle oa` has the same distribution as the eager (standard) semantics
for computations that don't re-query.

**Needed**: A lemma showing that for a random oracle, lazy sampling (cache on first query)
and eager sampling (pre-sample all values) are distributionally equivalent.

### 3. Missing: Query Count → Bad Event Probability

**Current state**: `IsQueryBound` provides structural bounds, `counting_bounded` connects
to dynamic counts, but there's no direct lemma:

**Needed**:
```lean
theorem probEvent_cache_hit_le_queryCount_div_card
    [Fintype S] (oa : OracleComp spec α) (t : ℕ)
    (ht : IsPerIndexQueryBound oa t) (s : S) :
    Pr[s ∈ queried_salts | simulateQ loggingOracle oa] ≤ t / Fintype.card S
```

### 4. Improvement: HidingAdversary Structure

**Current state**: `HidingAdversary` in `basic_commitment_scheme.lean` is incomplete
(lines 129-132 don't compile). The commented-out version (lines 135-140) is better:

**Recommended**:
```lean
structure HidingAdversary (σ : OracleSpec ι') (t : QueryCount ι') where
  chooseMessage : OracleComp σ (M × AUX)
  distinguish : AUX → C → OracleComp σ Bool
  t_Query_choose : IsQueryBound chooseMessage t
  t_Query_distinguish : ∀ aux cm, IsQueryBound (distinguish aux cm) t
```

### 5. Improvement: Connecting tvDist to Pr Difference

**Current state**: `tvDist` is defined on distributions but the hiding theorem uses
`|Pr[= true | g₁] - Pr[= true | g₂]|`.

**Needed**:
```lean
theorem abs_probOutput_sub_le_tvDist (mx my : m α) (x : α) :
    |Pr[= x | mx].toReal - Pr[= x | my].toReal| ≤ tvDist mx my
```

This may already exist in the SPMF/PMF TV distance theory — check
`ToMathlib/Probability/ProbabilityMassFunction/TotalVariation.lean`.

### 6. Improvement: Pedersen-Style Hiding via Bijection

For **perfect** hiding (Pedersen-style, `Examples/Pedersen.lean:97`), the argument is:
the map `s ↦ H(m, s)` is a bijection (since H is a random permutation), so the
pushforward of uniform is uniform regardless of `m`. This uses
`evalDist_map_bijective_uniform_cross`.

For the random oracle scheme, hiding is statistical (not perfect), so we need
the `by_upto` path instead. But the Pedersen pattern is useful for any future
scheme with perfect hiding.

---

## File References

| Component | File |
|-----------|------|
| TV distance | `VCVio/EvalDist/TVDist.lean` |
| Identical-until-bad | `VCVio/ProgramLogic/Relational/SimulateQ.lean` |
| Relational tactics | `VCVio/ProgramLogic/Tactics/Relational.lean` |
| Caching oracle | `VCVio/OracleComp/QueryTracking/CachingOracle.lean` |
| Uniform sampling | `VCVio/OracleComp/Constructions/SampleableType.lean` |
| SubSpec / coercions | `VCVio/OracleComp/Coercions/SubSpec.lean` |
| GameEquiv notation | `VCVio/ProgramLogic/Notation.lean` |
| Pedersen hiding | `Examples/Pedersen.lean` (lines 61-105) |
| ElGamal IND-CPA | `Examples/ElGamal/Basic.lean` |
| Proof workflows | `docs/agents/proof-workflows.md` |
| Program logic guide | `docs/agents/program-logic.md` |
| PMF TV distance | `ToMathlib/Probability/ProbabilityMassFunction/TotalVariation.lean` |
