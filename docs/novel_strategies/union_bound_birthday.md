# Proof Strategy: Union Bound Birthday (Textbook-Aligned)

**Randomization Seed**: `0xC4E7A1B3D509`

## Textbook Proof (SNARGs, Lemma rom-cr)

Given t-query adversary A with trace q₁,...,qₜ:
1. Define E_{i,j} = "qᵢ ≠ qⱼ AND H(qᵢ) = H(qⱼ)" for each pair i ≠ j
2. Pr[E_{i,j}] ≤ 1/|C| (independent uniform outputs for distinct inputs)
3. Collision = ∨ E_{i,j}
4. Union bound: Pr[collision] ≤ C(t,2)/|C| = t(t-1)/(2|C|)

## Lean Formalization Chain

```
probEvent_pair_collision_le     -- Step 2: Pr[E_{i,j}] ≤ 1/|C|
  ↓
probEvent_logCollision_le_birthday_total  -- Steps 3-4: union bound
  ↓
probEvent_cacheCollision_le_birthday_total  -- cache ← log reduction
  ↓
probEvent_cacheCollision_le_birthday   -- per-index → total bridge
  ↓
probEvent_cacheCollision_le_birthday'  -- single-index specialization
  ↓
probEvent_collision_win_le             -- win ⟹ collision → bounded
```

## Sorry 1: `gauss_sum_inv_le` (Arithmetic)

**Statement**: `∑_{k=0}^{n-1} k * N⁻¹ ≤ n² / (2N)`

**Textbook**: This is `C(n,2)/N = n(n-1)/(2N) ≤ n²/(2N)`.

**Lean strategy**:
```lean
∑ k ∈ range n, (k : ℝ≥0∞) * N⁻¹
= N⁻¹ * ∑ k ∈ range n, (k : ℝ≥0∞)      -- factor out N⁻¹
= N⁻¹ * (n * (n-1) / 2)                  -- Gauss sum formula
≤ N⁻¹ * (n² / 2)                          -- n(n-1) ≤ n²
= n² / (2N)
```

Key Mathlib lemmas:
- `Finset.sum_range_id_eq_sum_range_succ` or `Gauss.sum_range_id`
- For ENNReal: need `∑ k ∈ range n, (k : ℝ≥0∞) = n * (n-1) / 2` — may not exist directly
- Alternative: use `ENNReal.tsum_mul_right` to factor, then bound the sum

**Novel challenge**: ENNReal doesn't have subtraction in the usual sense (`n * (n-1)` for `n : ℕ` cast to ENNReal is fine, but the Gauss formula `n(n-1)/2` needs careful handling with natural number division).

**Approach**: Work in ℕ first: `∑ k in range n, k = n * (n-1) / 2` (Mathlib: `Finset.sum_range_id`). Then cast to ENNReal and multiply by N⁻¹.

## Sorry 2: `IsTotalQueryBound.of_perIndex` (Infrastructure)

**Statement**: If `IsPerIndexQueryBound oa qb`, then `IsTotalQueryBound oa (∑ i, qb i)`.

**Textbook**: Trivial — total queries ≤ sum of per-index budgets.

**Lean strategy**: Induction on `OracleComp` via `construct`:
- Pure: any bound works, `0 ≤ ∑ qb`
- Query t >>= k: per-index says `0 < qb t` and continuation has budget `Function.update qb t (qb t - 1)`. Total says `0 < ∑ qb` and continuation has budget `∑ qb - 1`. Need: `∑ (Function.update qb t (qb t - 1)) = (∑ qb) - 1`.

**Key lemma needed**: `∑ i, Function.update qb t (qb t - 1) i = (∑ i, qb i) - 1` when `0 < qb t` and `ι` is `Fintype`.

## Sorry 3: `probEvent_pair_collision_le` (CORE — Step 2)

**Statement**: For positions i,j in the log with distinct inputs, Pr[same output] ≤ 1/|C|.

**Textbook**: "If qᵢ ≠ qⱼ then H(qᵢ) and H(qⱼ) are independent uniform, so Pr[H(qᵢ) = H(qⱼ)] = 1/|C|."

**Why it's research-level in Lean**: The textbook asserts "independent uniform" as obvious from the ROM definition. In Lean with `loggingOracle`, we need to formally show that outputs at different log positions are independent. This requires:

1. Decomposing `(simulateQ loggingOracle oa).run` into individual query steps
2. Showing each query returns uniform via `probOutput_query`
3. Showing independence: the output at position j doesn't depend on the output at position i (for distinct inputs)

**Approach A (evalDist model)**: In raw `evalDist`, ALL queries are independent uniform (by definition). So the pair collision bound holds trivially. The challenge: connecting `loggingOracle` trace positions to the underlying independent queries.

**Approach B (direct)**: Express `Pr[log[i].2 = log[j].2 | log[i].1 ≠ log[j].1]` using `probEvent_bind_eq_tsum`, decompose over all possible logs, and use `probOutput_query` for the uniform bound.

**Approach C (via probEvent_map)**: The log entries are mapped from independent queries. Use `probEvent_map` + independence to get the bound.

## Sorry 4: `probEvent_logCollision_le_birthday_total` (Steps 3-4)

**Statement**: `Pr[LogHasCollision log] ≤ n²/(2|C|)`

**Textbook**: Union bound over pairs + per-pair bound.

**Lean strategy**:
```lean
Pr[LogHasCollision log]
= Pr[∃ (i,j), i ≠ j ∧ log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2]
≤ ∑ (i,j) with i ≠ j, Pr[E_{i,j}]     -- union bound (probEvent_union_le or similar)
≤ C(n,2) * (1/|C|)                       -- per-pair bound
= n(n-1)/(2|C|)
≤ n²/(2|C|)                              -- gauss_sum_inv_le
```

**Key Mathlib lemma needed**: A union bound for existential events:
`Pr[∃ i ∈ S, p i | mx] ≤ ∑ i ∈ S, Pr[p i | mx]`

Check if `probEvent_iUnion_le` or similar exists in VCV-io.

## Sorry 5: `probEvent_cacheCollision_le_birthday_total` (Cache ← Log)

**Statement**: Cache collision probability ≤ log collision probability.

**Textbook**: Implicit — the cache is a subset of the log (distinct inputs only).

**Lean strategy**: Show `CacheHasCollision cache → LogHasCollision log` when the cache and log come from the same `cachingOracle` + `loggingOracle` run. Or prove the cache version directly from the log version via a simulation argument.

**Alternative**: Prove directly for `cachingOracle` using the same union-bound structure but over cache entries instead of log entries.
