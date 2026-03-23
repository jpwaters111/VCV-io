# Knowledge: Binding & Extractability Proofs for Random Oracle Commitment Scheme

## Goal

Prove `binding_thm` and `extractable_thm` from `Examples/basic_commitment_scheme.lean`:
- **Binding**: `Pr[= True | binding_check] ≤ ½ · t² / 2^n`
- **Extractability**: `Pr[= True | extractability_game A] ≤ ½ · t² / 2^n`

Both use the **birthday bound** on a random oracle with `t` queries and output size `2^n`.

---

## Key Definitions in basic_commitment_scheme.lean

```
CMOracle M S C : OracleSpec (M × S) := fun _ => C
CMCommit (m : M) (s : S) : OracleComp (CMOracle M S C) C     -- query (m, s)
CMCheck (c : C) (m : M) (s : S) : OracleComp (CMOracle M S C) Prop
BindingAdversary.Algorithm : OracleComp σ (C × M × S × M × S)
BindingAdversary.t_Query : IsQueryBound Algorithm t
ExtractAdversary.commit : OracleComp σ (C × AUX)
ExtractAdversary.open_ : AUX → OracleComp σ (M × S)
CMExtract [DecidableEq C] (cm : C) (tr : QueryLog (CMOracle M S C)) : Option (M × S)
```

---

## Available Tools & Lemmas

### Birthday / Sum-of-Squares (ToMathlib/Data/ENNReal/SumSquares.lean)

- `sq_sum_le_card_mul_sum_sq`: `(∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2`
- `sq_tsum_le_tsum_mul_tsum`: `(∑' a, w a * f a) ^ 2 ≤ (∑' a, w a) * ∑' a, w a * f a ^ 2`
- `sq_tsum_le_tsum_sq`: When `∑' a, w a ≤ 1`, get `(∑' a, w a * f a) ^ 2 ≤ ∑' a, w a * f a ^ 2`
- `two_mul_le_add_sq`: `2 * a * b ≤ a ^ 2 + b ^ 2`

These are the core inequalities for deriving birthday-style collision bounds.

### Query Tracking

- **LoggingOracle** (`VCVio/OracleComp/QueryTracking/LoggingOracle.lean`):
  `loggingOracle : QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec))`
  - Captures all queries as `QueryLog spec = List ((t : spec.Domain) × spec.Range t)`
  - Key: `fst_map_run_simulateQ` (strips log), `probEvent_fst_run_simulateQ` (preserves probabilities)

- **CachingOracle** (`VCVio/OracleComp/QueryTracking/CachingOracle.lean`):
  `cachingOracle : QueryImpl spec (StateT spec.QueryCache (OracleComp spec))`
  - Lazy sampling: fresh queries get uniform random values, repeated queries return cached value
  - Cache is monotone (only grows)

- **QueryBound** (`VCVio/OracleComp/QueryTracking/QueryBound.lean`):
  `IsQueryBound oa budget canQuery cost : Prop`
  - `IsPerIndexQueryBound oa qb`: Per-index variant, `qb : ι → ℕ`
  - `IsPerIndexQueryBound.counting_bounded`: Links static bound to dynamic count from `countingOracle`

- **QueryLog** (`VCVio/OracleComp/QueryTracking/Structures.lean`):
  `QueryLog spec = List ((t : spec.Domain) × spec.Range t)`
  - `QueryLog.getQ`, `QueryLog.countQ`, `QueryLog.wasQueried`
  - Standard `List.find?` used for `CMExtract`

### Probability Reasoning

- **Pr notation** (`VCVio/EvalDist/Defs/Basic.lean`):
  - `Pr[= x | mx]` = `probOutput mx x = evalDist mx x`
  - `Pr[p | mx]` = `probEvent mx p`
  - `mem_support_iff`: `x ∈ support mx ↔ Pr[= x | mx] ≠ 0`

- **Bind decomposition** (`VCVio/EvalDist/Monad/Basic.lean`):
  - `probOutput_bind_eq_tsum`: `Pr[= y | mx >>= my] = ∑' x, Pr[= x | mx] * Pr[= y | my x]`
  - `probEvent_bind_eq_tsum`: `Pr[q | mx >>= my] = ∑' x, Pr[= x | mx] * Pr[q | my x]`
  - `probEvent_bind_of_const`: When Pr[p | my x] = r for all x in support, simplifies

- **Event monotonicity** (`probEvent_mono`): If `p ⟹ q` then `Pr[p | mx] ≤ Pr[q | mx]`

- **Markov's inequality** (`VCVio/OracleComp/QueryTracking/CostModel.lean:182`):
  `probEvent_cost_gt_le_expectedCost_div`

### Forking Lemma Connection (VCVio/CryptoFoundations/Fork.lean)

Uses `sq_tsum_le_tsum_mul_tsum` for collision bounds. Similar structure to binding: two
successful outputs sharing a collision point. Can adapt the pattern.

---

## Proof Strategy: Binding

### Setup
1. Run `A.Algorithm` with `simulateQ loggingOracle` to capture query trace
2. The adversary outputs `(cm, m0, s0, m1, s1)` with `(m0,s0) ≠ (m1,s1)`
3. Winning = `H(m0,s0) = H(m1,s1) = cm`

### Case Analysis
- **Case 1 (¬E)**: A wins but didn't query both `(m0,s0)` and `(m1,s1)`.
  At least one output is fresh random → collision probability ≤ `1/|C|`
- **Case 2 (E)**: Both queries appear in trace.
  Among `t` queries, birthday collision probability ≤ `C(t,2) / |C| = t(t-1)/(2|C|) ≤ t²/(2|C|)`

### Key Steps
1. Use `probEvent_bind_eq_tsum` to decompose over adversary outputs
2. Condition on trace via `loggingOracle`
3. Apply `sq_sum_le_card_mul_sum_sq` for birthday bound
4. Use `probEvent_mono` to connect winning to collision

---

## Proof Strategy: Extractability

### Setup
1. Run `A.commit` with `simulateQ loggingOracle` → get `((cm, aux), tr)`
2. `CMExtract cm tr` searches trace for entry with output `cm`
3. Run `A.open_ aux` → get `(m, τ)`
4. Game wins if `H(m,τ) = cm` AND extractor disagrees (or extractor failed)

### Reduction to Binding
- **If extractor finds `(m', τ')` in trace**: Game requires `(m',τ') ≠ (m,τ)` but
  both map to `cm`. This IS a binding collision.
- **If extractor fails (no trace entry maps to `cm`)**: Then `cm` is independent of
  oracle responses, and `Pr[H(m,τ) = cm] = 1/|C|` for each open query.
- Combined bound equals the binding bound.

### Key Steps
1. Use `probEvent_mono` to relate extractability game to collision event
2. Apply birthday bound from binding proof
3. The `QueryLog.find?` in `CMExtract` directly connects trace to collision detection

---

## Canonical Pattern: Pedersen Binding (Examples/Pedersen.lean)

Pedersen uses a different strategy (reduction to DLog), but the proof pattern is instructive:
1. Construct reduction adversary (`dlogReduction`)
2. Unify both games to a common base computation
3. Define win conditions as predicates
4. Use `probEvent_mono` to relate: `bindingWin ⟹ dlogWin ⟹ Pr[binding] ≤ Pr[dlog]`

For our random oracle scheme, replace the DLog reduction with the birthday bound.

---

## Required Instances

```lean
[DecidableEq M] [DecidableEq S] [DecidableEq C]
[Fintype C] [Inhabited C]           -- for probability reasoning
[spec.Fintype] [spec.Inhabited]     -- for evalDist
```

---

## File References

| Component | File |
|-----------|------|
| SumSquares / birthday | `ToMathlib/Data/ENNReal/SumSquares.lean` |
| LoggingOracle | `VCVio/OracleComp/QueryTracking/LoggingOracle.lean` |
| CachingOracle | `VCVio/OracleComp/QueryTracking/CachingOracle.lean` |
| QueryBound | `VCVio/OracleComp/QueryTracking/QueryBound.lean` |
| QueryLog / Structures | `VCVio/OracleComp/QueryTracking/Structures.lean` |
| CostModel / Markov | `VCVio/OracleComp/QueryTracking/CostModel.lean` |
| Probability defs | `VCVio/EvalDist/Defs/Basic.lean` |
| Probability bind | `VCVio/EvalDist/Monad/Basic.lean` |
| Fork lemma (pattern) | `VCVio/CryptoFoundations/Fork.lean` |
| Pedersen binding | `Examples/Pedersen.lean` |
| Commitment scheme | `Examples/basic_commitment_scheme.lean` |
