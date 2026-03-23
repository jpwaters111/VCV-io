# Knowledge: Commitment Scheme Proof Walkthrough

Complete walkthrough of the three proven security properties for the random oracle
commitment scheme, connecting the formal Lean proofs to the knowledge base.

---

## Overview

| Property | File | Theorem | Bound |
|----------|------|---------|-------|
| Binding | `Examples/basic_commitment_scheme_proofs.lean` | `binding_bound` | `Pr[win] ≤ (Fintype.card C)⁻¹` |
| Extractability | `Examples/basic_commitment_scheme_proofs.lean` | `extractability_bound` | `Pr[win] ≤ (Fintype.card C)⁻¹` |
| Hiding | `Examples/basic_commitment_scheme_hiding.lean` | `hiding_perfect` | `Pr[real] = Pr[sim]` (perfect) |

All proofs are complete with no `sorry`.

---

## Model: evalDist (Independent Sampling)

**Critical distinction** (from `docs/knowledge_binding_extractability.md`):

The proofs use the `evalDist` model where every `query` call returns an **independent
uniform sample**. This is NOT the random function model (where same input → same output).

- **evalDist model**: `query (m,s)` → fresh uniform over C, always
- **Random function model** (cachingOracle): `query (m,s)` → cached if seen before

Consequences:
- Binding/extractability bounds are **stronger** (1/|C| vs birthday bound t²/2|C|)
  because verification queries are independent of the adversary's queries
- Hiding is **perfect** (advantage 0) because `query` output is uniform regardless of input

For the random function model, use `simulateQ cachingOracle` and the
`by_upto` / `tvDist_simulateQ_le_probEvent_bad` infrastructure
(see `docs/knowledge_hiding_theorem.md`).

---

## Proof 1: Binding

### Statement
```lean
theorem binding_bound (A : BindingAdversary M S C) :
    Pr[= true | bindingGame A] ≤ (Fintype.card C : ℝ≥0∞)⁻¹
```

### Game Definition
The adversary outputs `(c, m₀, s₀, m₁, s₁)`, then we make two fresh verification
queries `c₀ ← query (m₀,s₀)` and `c₁ ← query (m₁,s₁)`. Win requires
`c₀ = c ∧ c₁ = c ∧ (m₀,s₀) ≠ (m₁,s₁)`.

### Proof Strategy (from `docs/knowledge_binding_extractability.md`)
1. **Peel off adversary**: `probOutput_bind_le` — for any adversary output,
   bound the verification probability
2. **Peel off first query**: `probOutput_bind_le` again — for any `c₀`,
   bound the second query probability
3. **Fresh query bound**: The second query `c₁ ← query (m₁,s₁)` returns
   uniform over C. Win requires `c₁ = c`, so probability ≤ `1/|C|`
4. **Tsum collapse**: `tsum_query_weight_le` — the sum has at most one
   nonzero term (at `c₁ = c`), bounded by `(Fintype.card C)⁻¹`

### Key Lemmas Used
| Lemma | From | Purpose |
|-------|------|---------|
| `probOutput_bind_le` | This file | Bound bind by bounding each continuation |
| `probOutput_bind_eq_tsum` | `EvalDist/Monad/Basic.lean` | Decompose bind into tsum |
| `probOutput_query` | `OracleComp/EvalDist.lean` | Each query output has probability `1/\|C\|` |
| `probOutput_pure` | `EvalDist/Defs/Basic.lean` | Pure returns deterministic value |
| `tsum_ite_eq` | Mathlib | `∑' x, if x = a then f a else 0 = f a` |
| `ENNReal.tsum_le_tsum` | Mathlib | Pointwise inequality lifts to tsum |

---

## Proof 2: Extractability

### Statement
```lean
theorem extractability_bound (A : ExtractAdversary M S C AUX) :
    Pr[= true | extractabilityGame A] ≤ (Fintype.card C : ℝ≥0∞)⁻¹
```

### Game Definition
Phase 1: Run `A.commit` with `simulateQ loggingOracle` to capture the query trace.
Phase 2: `A.open_ aux` produces opening `(m, τ)`.
Verification: fresh `c ← query (m, τ)`.
Extractor: `CMExtract cm tr` searches the trace for an entry matching `cm`.
Win: `c = cm` AND (extractor failed OR extractor disagrees with adversary).

### Proof Strategy (from `docs/knowledge_binding_extractability.md`)
Same as binding! The key observation: regardless of the match branch
(extractor found something or not), winning always requires `c = cm`.
Since `c` is a fresh uniform query, `Pr[c = cm] = 1/|C|`.

1. **Peel off commit+log**: `probOutput_bind_le`
2. **Peel off open phase**: `probOutput_bind_le`
3. **Fresh query bound**: `c ← query (m, τ)` is uniform, win requires `c = cm`
4. **Both match branches**: `cases CMExtract cm tr` — in both `none` and `some`,
   `c == cm = false` (from `hc : c ≠ cm`) kills the condition

### Connection to Binding (from knowledge file)
The extractability bound equals the binding bound because both reduce to:
"a fresh oracle query matches a fixed target with probability 1/|C|".
In the random function model, the reduction would be more complex
(see `docs/knowledge_binding_extractability.md` §Proof Strategy: Extractability).

---

## Proof 3: Perfect Hiding

### Statement
```lean
theorem hiding_perfect (A : HidingAdversary M S C AUX) :
    Pr[= true | hidingReal A] = Pr[= true | hidingSim A]
```

### Game Definitions
- **Real**: adversary chooses `m`, commitment is `query (m, default)`
- **Sim**: adversary chooses `m`, commitment is `query (default, default)`

### Proof Strategy (from `docs/knowledge_hiding_theorem.md`)
In the `evalDist` model, `query t` returns uniform over C for ANY input `t`.
So `query (m, default)` and `query (default, default)` have identical distributions.

The proof uses `probOutput_bind_congr'` to peel off shared computation layers:
1. `A.choose` — identical in both games
2. Dummy query — identical
3. Commitment query — different inputs but same distribution (by `probOutput_query`)
4. `A.distinguish` — identical function applied to identically-distributed input

### Why This Is Perfect (Not Just Statistical)
From `docs/knowledge_hiding_theorem.md` §Library Improvements:
- In the **random function model** (cachingOracle), hiding is only **statistical**
  because the adversary might have queried `(m, s)` before
- In the **evalDist model** (independent queries), hiding is **perfect**
  because query results don't depend on inputs at all
- The `by_upto` tactic would be needed for the statistical version

---

## Helper Infrastructure Created

### `probOutput_bind_le` (new, in proofs file)
```lean
lemma probOutput_bind_le
    (h : ∀ x : β, Pr[= y | my x] ≤ r) :
    Pr[= y | mx >>= my] ≤ r
```
**Why**: Standard probability lemma — if every continuation is bounded by `r`,
then the overall bind is bounded by `r`. Uses `probOutput_bind_eq_tsum`,
`ENNReal.tsum_mul_right`, and `tsum_probOutput_le_one`.

### `tsum_query_weight_le` (new, in proofs file)
```lean
private lemma tsum_query_weight_le (target : C)
    (f : C → ℝ≥0∞) (hf : ∀ c, c ≠ target → f c = 0) (hle : f target ≤ 1) :
    ∑' c : C, (Fintype.card C)⁻¹ * f c ≤ (Fintype.card C)⁻¹
```
**Why**: When a weighted sum over uniform query probabilities has at most one
nonzero term, the sum collapses to a single `(Fintype.card C)⁻¹` factor.
Uses `tsum_ite_eq` for the collapse.

---

## Future Work: Random Function Model

To prove these properties in the random function model (stronger, more standard):

1. **Binding**: Use `simulateQ cachingOracle` + birthday bound from
   `ToMathlib/Data/ENNReal/SumSquares.lean`. Bound: `t(t-1)/(2|C|)`.
   See `docs/knowledge_binding_extractability.md` §Birthday / Sum-of-Squares.

2. **Extractability**: Reduce to binding via the `CMExtract` trace search.
   See `docs/knowledge_binding_extractability.md` §Proof Strategy: Extractability.

3. **Hiding**: Use `by_upto bad` where `bad` = adversary queried `(m, s)`.
   Bound: `t/|S|`. See `docs/knowledge_hiding_theorem.md` §Identical-Until-Bad.

---

## File References

| File | Content |
|------|---------|
| `Examples/basic_commitment_scheme.lean` | Original definitions (WIP) |
| `Examples/basic_commitment_scheme_proofs.lean` | Binding + extractability proofs |
| `Examples/basic_commitment_scheme_hiding.lean` | Hiding proof |
| `Examples/basic_commitment_scheme_sketch.lean` | Proof strategy sketches |
| `docs/knowledge_binding_extractability.md` | Knowledge: binding/extract tools |
| `docs/knowledge_hiding_theorem.md` | Knowledge: hiding tools + library gaps |
| `docs/knowledge_commitment_proof_walkthrough.md` | This file |
| `Examples/Pedersen.lean` | Reference: Pedersen commitment proofs |
