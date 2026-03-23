# Proof Strategy: Hiding Sorrys 7 & 8

**Source**: SNARGs book, Lemma cm-hiding (`docs/commitment_scheme.tex` line 455)

## Textbook Proof Structure (finite t case)

The proof defines event E = "adversary queries (m, s) in trace₁ or trace₂".

1. **Conditioned on ¬E**: H(m,s) is a cache miss, so `H(m,s)` returns fresh uniform — identical to `Simulator^H` which also returns fresh uniform. Statistical distance = 0 on ¬E paths.
2. **Statistical distance ≤ Pr[E]** by the identical-until-bad technique.
3. **Pr[E] ≤ t/|S|** because salt s is sampled independently of the adversary's queries. Each of the ≤ t queries hits salt s with probability 1/|S|, union bound gives t/|S|.

## Mapping to Lean Sorrys

### Sorry 7: `hidingImpl₂_eq_hidingSim` (tvDist = 0)

**Goal**: `tvDist ((simulateQ (hidingImpl₂ s) (hidingOa A s)).run' (∅, 0)) (hidingSim A s) = 0`

**What this says**: The intermediate game (impl₂) and the simulator produce identical distributions.

**Key insight**: `hidingImpl₂` redirects queries to `(default, default)` when `cnt ≥ 2` (bad) AND salt matches s. But `hidingSim` queries `(default, default)` for the challenge. The claim is these are distributionally equal.

**Approach — Coupling/relational argument**:

Both games run the same adversary code. The difference is only in the challenge query:
- `hidingImpl₂`: queries `(m, s)` — goes through impl₂ which caches at `(m, s)`
- `hidingSim`: queries `(default, default)` — goes through cachingOracle

In BOTH cases, the challenge query is a cache miss (first time that point is queried), so both return fresh uniform from the underlying oracle. The adversary's subsequent queries are answered by the same caching mechanism in both games.

**Formal approach**: Use `by_equiv` to enter coupling mode, then show via `rvcstep`/`rvcgen` that:
1. `A.choose` is identical in both (same oracle, same state projection)
2. The challenge query returns identically-distributed fresh uniform in both
3. `A.distinguish` sees the same distribution of responses

**Alternative**: Use `evalDist_simulateQ_run'_eq_evalDist` to show both games have the same evalDist when projected to output.

**Difficulty**: The main challenge is that the cache STATE differs ((m,s)→cm vs (default,default)→cm), but the adversary only observes responses, not the internal cache. When ¬bad, the adversary never queries (m,s) or (default,default) again (or if it does, gets the same cached value), so the output distribution is the same.

**Potential VCV-io tactics**:
- `by_equiv` to enter `RelTriple` shell
- `rvcstep` / `rvcgen` for stepping through the computation
- `rel_dist` for distributional equivalence steps

### Sorry 8: `probEvent_hidingBad_le` (Pr[bad] ≤ t/|S|)

**Goal**: `Pr[hidingBad ∘ Prod.snd | (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal ≤ t / |S|`

**What this says**: The probability that saltCount ≥ 2 at the end is at most t/|S|.

**Textbook argument** (Claim cm-hiding-hit-query, line 523):
- The challenge query `(m, s)` contributes exactly 1 to the counter
- Bad (cnt ≥ 2) means ≥ 1 adversary query also had salt s
- The adversary makes ≤ t queries total (across choose + distinguish phases)
- Each query has some salt s'. For FIXED adversary execution path, the set of queried salts is determined
- Salt s is sampled uniformly from S, independently of the adversary's strategy
- Pr[s ∈ {queried salts}] ≤ t/|S| by union bound

**CRITICAL ISSUE with current formalization**: In the current code, `s` is a PARAMETER, not randomly sampled. The textbook proof fundamentally requires `s` to be random relative to the adversary's queries. Two possible resolutions:

1. **Strengthen the adversary model**: Require that the adversary's query strategy is independent of s (i.e., the adversary is "salt-oblivious"). This is realistic since in the real scheme, s is chosen after the adversary commits to its strategy.

2. **Reformulate**: Sample s externally as `s ← $ᵗ S` and prove the averaged bound. This matches the textbook more directly but changes the theorem signature.

3. **Use the per-query bound**: For each adversary query `(m_i, s_i)`, since the adversary doesn't know s (it's chosen after the query), `Pr[s_i = s] ≤ 1/|S|`. Sum over ≤ t queries.

**Approach for current formalization (fixed s)**:
The bound `Pr[bad] ≤ t/|S|` for FIXED s requires arguing that the adversary's queries have salt-s probability ≤ t/|S| even for fixed s. This is where the argument gets subtle.

Actually, re-reading the current code: `hidingOa` takes `s` as a parameter, and the game uses `hidingImpl₁ s`. The bound must hold for ALL s, not in expectation. The textbook argument works because:
- The adversary's query distribution is independent of s (the adversary doesn't see s until the challenge query)
- Before the challenge query, A.choose produces queries whose salts are independent of s
- After the challenge query, A.distinguish sees `cm = H(m,s)` — but conditioned on the oracle responses, s only appears through cm

This means we need: for fixed s, Pr[any of A's ≤t queries has salt = s] ≤ t/|S|.

**Formal proof sketch**:
1. Decompose `hidingOa` into choose + challenge + distinguish phases
2. For `A.choose`: queries are independent of s entirely. Each query has some salt. Since we're in the ROM, the adversary's salt choices are determined by its code + previous responses. The probability any specific query has salt = s is at most 1/|S| only if we can argue the adversary "doesn't know s" — but s is fixed!

**Resolution**: The bound holds in EXPECTATION over s. For fixed s, the adversary could trivially always query salt s. The theorem as stated (for fixed s) may need the additional assumption that s is sampled uniformly, OR we need to interpret the probability as being over both the oracle randomness AND the choice of s.

**Recommended approach**: Prove a version where s is sampled uniformly:
```
Pr[hidingBad | s ← uniform S, run game with s] ≤ t/|S|
```
Then the existing `hiding_bound` theorem can average over s.

**Potential VCV-io tactics**:
- `by_hoare` for probability bounding
- `vcstep` / `vcgen` for decomposing the computation
- Query counting lemmas from `QueryBound.lean`

## Priority

- **Sorry 8 first**: The Pr[bad] bound is the load-bearing step. Even a partial proof clarifies the right formalization.
- **Sorry 7 second**: The distributional equivalence may need careful coupling but follows a known pattern.

## Relevant Library Files

- `VCVio/OracleComp/QueryTracking/QueryBound.lean` — IsPerIndexQueryBound, IsTotalQueryBound
- `VCVio/EvalDist/TVDist.lean` — tvDist definitions and lemmas
- `VCVio/ProgramLogic/Relational/SimulateQ.lean` — run'_simulateQ_eq_of_query_map_eq'
- `VCVio/OracleComp/QueryTracking/CachingOracle.lean` — cachingOracle, QueryCache
- `VCVio/ProgramLogic/Tactics.lean` — by_equiv, rvcstep, vcstep, etc.
