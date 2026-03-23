/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Random Oracle Commitment Scheme — Caching Oracle Model

A commitment scheme in the random oracle model: `commit(m, s) = H(m, s)` where
`H : M × S → C` is a random oracle modeled via `cachingOracle`.

Following `docs/commitment_scheme.tex`, we prove three security properties:

1. **Binding** (Lemma cm-binding):
   `Pr[win] ≤ ½ · t² / |C|` where `t` is the query bound.
   The adversary and verification share the **same** random oracle (via `cachingOracle`).

2. **Extractability** (Lemma cm-extractability):
   `Pr[win] ≤ ½ · t² / |C|` with the same structure.
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
  /-- The adversary makes at most `t` queries. -/
  queryBound : IsPerIndexQueryBound run (fun (_ : M × S) => t)

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

/-- **Binding theorem (Lemma cm-binding)**: The probability that any `t`-query
adversary wins the binding game is at most `½ · t² / |C|`.

The proof in the textbook splits into two cases:
- Case 1 (collision): Both `(m₀,s₀)` and `(m₁,s₁)` were queried by A, so
  the trace contains a collision. By ROM collision resistance, this happens
  with probability ≤ ½ · t(t-1) / |C|.
- Case 2 (unpredictability): At least one pair was not queried by A, so
  A "guessed" the oracle output. By ROM unpredictability, this happens
  with probability ≤ 1/|C|.
Together: ½ · (t²-t+2) / |C| ≤ ½ · t² / |C| for t ≥ 2.

This requires ROM-CR and ROM-unpredictability lemmas not yet in the library. -/
theorem binding_bound {t : ℕ} (A : BindingAdversary M S C t) :
    Pr[fun z => z.1 = true | bindingGame A] ≤
    (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card C) := by
  sorry

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
  /-- Query bound for the commit phase. -/
  commitBound : IsPerIndexQueryBound commit (fun (_ : M × S) => t)

/-- The extractor: scan the query-answer trace for a pair whose answer matches `cm`. -/
def CMExtract (cm : C) (tr : QueryLog (CMOracle M S C)) : Option (M × S) :=
  match tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => some entry.1
  | none => none

/-- The extractability game in the random oracle model.

Phase 1 (commit): Run `A.commit` with a logging oracle layered on top
  (to capture the trace), all within `cachingOracle`.
Phase 2 (open): Run `A.open_` with the same oracle (shared cache).
Verification: Query `H(m, s)` and compare to `cm`.
Extraction: Search the commit-phase trace for an entry matching `cm`.

Win: Check passes AND (extractor found nothing OR found a different opening). -/
def extractabilityGame {AUX : Type} {t : ℕ} (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) (Bool × QueryCache (CMOracle M S C)) :=
  (simulateQ cachingOracle (do
    -- Phase 1: commit with logging to get trace
    let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
    -- Phase 2: open
    let (m, s) ← A.open_ aux
    -- Verify: query H(m,s) using the same oracle
    let c ← query (spec := CMOracle M S C) (m, s)
    -- Extract from the commit-phase trace
    let extracted := CMExtract cm tr
    return (match extracted with
      | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
      | none => (c == cm)))).run ∅

variable {AUX : Type}

/-- **Extractability theorem (Lemma cm-extractability)**: The probability that
any `t`-query adversary wins the extractability game is at most `½ · t² / |C|`.

The proof follows the same case analysis as binding, with the same three cases
(collision in trace, inversion of a commitment, and lucky guess). -/
theorem extractability_bound {t : ℕ} (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1 = true | extractabilityGame A] ≤
    (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card C) := by
  sorry

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

/-- A hiding adversary with two phases and query bound `t`. -/
structure HidingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- Phase 1: choose a message and auxiliary state (with oracle access). -/
  choose : OracleComp (CMOracle M S C) (M × AUX)
  /-- Phase 2: given auxiliary state and a commitment, output a guess bit. -/
  distinguish : AUX → C → OracleComp (CMOracle M S C) Bool
  /-- Query bound for the choose phase. -/
  chooseBound : IsPerIndexQueryBound choose (fun (_ : M × S) => t)
  /-- Query bound for the distinguish phase. -/
  distinguishBound : ∀ (aux : AUX) (cm : C),
    IsPerIndexQueryBound (distinguish aux cm) (fun (_ : M × S) => t)

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

/-- `Pr[bad]` bound for **uniformly random** salt.

When `s` is sampled uniformly from `S`, the probability that any of the
adversary's ≤ t queries has salt = s is at most `t / |S|`.

This requires `s` to be independent of the adversary's strategy. For the choose
phase, independence holds because `s` hasn't been revealed. For the distinguish
phase, the textbook applies the ROM one-way entropy lemma (Lemma rom-ow-high-entropy)
which shows that even after seeing `cm = H(m, s)`, the adversary's queries hit
salt `s` with probability ≤ 1/|S| per query.

This bound does NOT hold for fixed `s`: an adversary that always queries salt `s`
has `Pr[bad] = 1` (for `t ≥ 1`). -/
theorem probEvent_hidingBad_le_of_uniform {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal ≤
    (t : ℝ) / (Fintype.card S : ℝ) := by
  -- This bound is correct when averaging over uniform s, but the current
  -- statement is for fixed s. The textbook proof (Claim cm-hiding-hit-query)
  -- relies on s being sampled uniformly and independently.
  --
  -- For the choose phase: adversary queries are independent of s (it hasn't
  -- seen s yet). Each query has Pr[salt = s | s uniform] = 1/|S|.
  -- For the distinguish phase: uses ROM one-way entropy lemma.
  -- Union bound: t₁/|S| + t₂/|S| = t/|S|.
  --
  -- The correct formalization would either:
  -- (a) Sample s uniformly outside and prove 𝔼_s[Pr[bad_s]] ≤ t/|S|, or
  -- (b) Add a hypothesis that the adversary is salt-oblivious.
  sorry

/-- **Hiding theorem (Lemma cm-hiding)**: For every salt `s`, the statistical distance
between the real and simulated hiding games is at most `t / |S|`.

The proof combines:
1. `tvDist(real, sim) ≤ Pr[bad]` (identical-until-bad, sorry 7)
2. `Pr[bad] ≤ t/|S|` (union bound with random salt, sorry 8) -/
theorem hiding_bound {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    tvDist (hidingReal A s) (hidingSim A s) ≤ (t : ℝ) / (Fintype.card S : ℝ) := by
  calc tvDist (hidingReal A s) (hidingSim A s)
      ≤ Pr[hidingBad ∘ Prod.snd |
          (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal :=
        tvDist_hidingReal_hidingSim_le_probBad A s
    _ ≤ (t : ℝ) / (Fintype.card S : ℝ) :=
        probEvent_hidingBad_le_of_uniform A s
