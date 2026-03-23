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

The proof uses identical-until-bad: the "bad" event is that the adversary
queries any `(_, s)` during the whole game, where `s` is the challenge salt.
When `¬bad`, `hidingImpl₁` and `hidingImpl₂` behave identically (the redirect
condition `bad && (ms.2 == s)` is `false`), so the fundamental lemma gives
`tvDist(real, intermediate) ≤ Pr[bad]`.

The intermediate game (`hidingImpl₂`) always queries `(m, s)` for the
commitment (same as `hidingImpl₁`) when `¬bad`. The `tvDist(intermediate,
sim) = 0` step therefore requires a separate distributional argument showing
the intermediate game's output matches the simulator.

**Note on the `Pr[bad]` bound**: The `Pr[bad]` bound `t / |S|` holds when
reasoning that (1) the adversary makes at most `t` queries total, (2) each
query's salt component is chosen by the adversary (possibly adaptively), and
(3) the bad event `∃ query with salt = s` has probability bounded by `t / |S|`
**when `s` is uniformly random and independent of the adversary's oracle
responses**. For a *fixed* `s`, the bound requires that `s` is independent
of the adversary's strategy, which is ensured by the ROM model where oracle
responses (which the adversary's adaptive queries depend on) are independent
of which input maps to a given salt. -/

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

/-- The simulated hiding game, parametrized by salt `s` (unused by simulator).

The adversary chooses `m`, then receives a commitment that is a fresh uniform
value from the oracle (at a dummy input unrelated to `m`). The simulator
simply queries a fresh oracle point. -/
def hidingSim {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (_s : S) :
    OracleComp (CMOracle M S C) Bool :=
  (simulateQ cachingOracle (do
    let (_m, aux) ← A.choose
    -- Simulator: query at a default point to get a uniform commitment.
    -- This is independent of the adversary's message.
    let cm ← query (spec := CMOracle M S C) (default, default)
    A.distinguish aux cm)).run' ∅

/-! ### Identical-until-bad infrastructure for hiding

The proof uses `tvDist_simulateQ_le_probEvent_bad` for the step
`tvDist(hidingReal, intermediate) ≤ Pr[bad]`, where bad tracks whether
any query had salt `s`.

**`hidingImpl₁`** (real): standard caching + bad flag tracking on salt `s`.
**`hidingImpl₂`** (intermediate): same as `hidingImpl₁` EXCEPT when `bad = true`
and cache miss with salt `s`, queries the underlying oracle at `(default, default)`.

When `¬bad`, both implementations are literally identical (the condition
`bad && (ms.2 == s)` is `false`), so `h_agree` holds.

The remaining steps:
- `tvDist(intermediate, hidingSim) = 0`: distributional argument (see `h_step2`).
- `Pr[bad] ≤ t / |S|`: query-counting argument (see `probEvent_hidingBad_le`).
-/

/-- The "bad" predicate on the hiding game state:
bad holds when the flag has been set, indicating a previous query had salt `s`. -/
def hidingBad : QueryCache (CMOracle M S C) × Bool → Prop := fun p => p.2 = true

instance : DecidablePred (hidingBad (M := M) (S := S) (C := C)) :=
  fun p => decEq p.2 true

/-- Real oracle implementation for the hiding game.
Standard caching + sets bad flag when any query with salt `s` is processed. -/
def hidingImpl₁ (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × Bool) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, bad) ← get
    match cache ms with
    | some u => return u
    | none => do
      let u ← (liftM (query (spec := CMOracle M S C) ms) :
        StateT (QueryCache (CMOracle M S C) × Bool) (OracleComp (CMOracle M S C)) C)
      set (cache.cacheQuery ms u, bad || (ms.2 == s))
      return u

/-- Intermediate oracle implementation for the hiding game.
Same as `hidingImpl₁`, except when `bad = true` and cache miss with salt `s`,
queries the underlying oracle at `(default, default)` instead. -/
def hidingImpl₂ (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × Bool) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, bad) ← get
    match cache ms with
    | some u => return u
    | none => do
      -- When bad is already set and salt matches, redirect query
      let queryPoint := if bad && (ms.2 == s) then (default, default) else ms
      let u ← (liftM (query (spec := CMOracle M S C) queryPoint) :
        StateT (QueryCache (CMOracle M S C) × Bool) (OracleComp (CMOracle M S C)) C)
      set (cache.cacheQuery ms u, bad || (ms.2 == s))
      return u

/-- The shared adversary computation for the hiding game.
Both `hidingReal` and the intermediate game use this computation. -/
def hidingOa {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool := do
  let (m, aux) ← A.choose
  let cm ← query (spec := CMOracle M S C) (m, s)
  A.distinguish aux cm

/-- The real hiding game is `simulateQ cachingOracle` applied to the shared computation. -/
theorem hidingReal_eq {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingReal A s = (simulateQ cachingOracle (hidingOa A s)).run' ∅ := by
  simp only [hidingReal, hidingOa]

/-- The real hiding game equals `simulateQ hidingImpl₁` projected to discard the bad flag.
This lifts cachingOracle's state by pairing it with the bad tracker. -/
theorem hidingReal_eq_impl₁ {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingReal A s = (simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, false) := by
  rw [hidingReal_eq A s]
  -- Use the generalized state-projection theorem with proj = Prod.fst
  exact (OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq'
    (hidingImpl₁ s) cachingOracle Prod.fst (fun ms st => by
      -- Need: Prod.map id Prod.fst <$> (hidingImpl₁ s ms).run st = (cachingOracle ms).run st.1
      obtain ⟨cache, bad⟩ := st
      simp only [hidingImpl₁, cachingOracle, QueryImpl.withCaching_apply,
        QueryImpl.ofLift, StateT.run_bind, StateT.run_get, pure_bind]
      cases hc : cache ms with
      | some u =>
        simp [hc, StateT.run_pure, Prod.map]
      | none =>
        simp only [hc, StateT.run_bind, OracleComp.liftM_run_StateT]
        simp only [bind_assoc, pure_bind, Prod.map]
        simp [StateT.run_set, StateT.run_pure, Prod.map, StateT.run_modifyGet]
    ) (hidingOa A s) (∅, false)).symm

/-- The implementations agree when `¬bad`: when the bad flag is `false`,
`hidingImpl₁` and `hidingImpl₂` produce the same monadic computation. -/
theorem hidingImpl_agree (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × Bool) (h : ¬hidingBad st) :
    (hidingImpl₁ s ms).run st = (hidingImpl₂ s ms).run st := by
  simp only [hidingBad, Bool.not_eq_true] at h
  obtain ⟨cache, bad⟩ := st
  simp only at h
  -- Since bad = false, `bad && (ms.2 == s) = false`, so queryPoint = ms in impl₂.
  subst h
  simp only [hidingImpl₁, hidingImpl₂, StateT.run_bind, StateT.run_get, pure_bind]
  -- Now both sides have `match cache ms with ...`. The `none` branch differs only
  -- in `query (if (false && ms.2 == s) = true then (default, default) else ms)` vs `query ms`.
  -- Since `(false && _) = true` is `False`, the if reduces to `ms`.
  cases cache ms with
  | some u => rfl
  | none => simp [Bool.false_and]

/-- Bad is monotone for `hidingImpl₁`: once set, it stays set. -/
theorem hidingImpl₁_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × Bool) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × Bool))
    (hx : x ∈ support ((hidingImpl₁ s ms).run st)) :
    hidingBad x.2 := by
  simp only [hidingBad] at h ⊢
  obtain ⟨cache, bad⟩ := st
  simp only at h
  subst h
  simp only [hidingImpl₁, StateT.run_bind, StateT.run_get, pure_bind] at hx
  -- Case split on cache hit/miss
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    -- After the query, set is called with bad' = true || (ms.2 == s) = true
    -- We need to extract the state from the support
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp [Bool.true_or]

/-- Bad is monotone for `hidingImpl₂`: once set, it stays set. -/
theorem hidingImpl₂_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × Bool) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × Bool))
    (hx : x ∈ support ((hidingImpl₂ s ms).run st)) :
    hidingBad x.2 := by
  simp only [hidingBad] at h ⊢
  obtain ⟨cache, bad⟩ := st
  simp only at h
  subst h
  simp only [hidingImpl₂, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp [Bool.true_or]

/-! ### Step 2b: Distributional equivalence of intermediate and simulator

The intermediate game (`simulateQ hidingImpl₂ hidingOa`) differs from `hidingSim`
because:
- `hidingOa` queries `(m, s)` for the challenge, while `hidingSim` queries
  `(default, default)`.
- Under `hidingImpl₂`, once `bad = true`, salt-`s` cache misses redirect to
  `(default, default)`. But the *first* salt-`s` query enters with `bad = false`
  and is NOT redirected.

The distributional argument proceeds per-execution-path: when bad was set by some
query *before* the challenge (during `A.choose`), the challenge query `(m, s)` may
already be cached, and subsequent salt-`s` queries are redirected. When bad was NOT
set before the challenge, the challenge query `(m, s)` is a fresh cache miss
querying the underlying oracle at `(m, s)` — producing a uniform `C` value, the
same distribution as querying `(default, default)`. However the caches diverge
thereafter (the intermediate caches `(m, s) → cm` while the sim caches
`(default, default) → cm`), so `A.distinguish` sees different oracle behaviour.

This means `tvDist(intermediate, sim) ≠ 0` in general. The correct resolution is
to redesign `hidingImpl₂` to redirect ALL salt-`s` queries (including the first),
but this breaks `h_agree` with `hidingImpl₁`. The standard textbook proof resolves
this by applying the identical-until-bad argument at the level of the *full* oracle
transcript (not per-query), which requires infrastructure beyond
`tvDist_simulateQ_le_probEvent_bad`.

Below, we reduce `h_step2` to `hidingImpl₂_eq_hidingSim`, which captures the
precise distributional claim needed. This is left as sorry with a detailed
explanation of the gap. -/

/-- The distributional equivalence between the intermediate game and the simulator.

**Status**: This is the core technical gap. The intermediate game
(`simulateQ hidingImpl₂ hidingOa`) does NOT exactly equal `hidingSim` because the
oracle implementations differ after bad is set. Closing this sorry requires either:
1. Redesigning `hidingImpl₂` to redirect ALL salt-`s` queries (making it exactly
   equal `hidingSim` after projection), then using a modified identical-until-bad
   lemma that allows disagreement on the bad-setting query itself, OR
2. A direct coupling argument at the probability level showing that, for each output
   `b : Bool`, `Pr[= b | intermediate] = Pr[= b | hidingSim]`.

Approach (2) would require showing that the divergent cache entries (from redirected
vs non-redirected salt-`s` queries after bad is set) cancel out in expectation. -/
theorem hidingImpl₂_eq_hidingSim {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    tvDist ((simulateQ (hidingImpl₂ s) (hidingOa A s)).run' (∅, false))
      (hidingSim A s) = 0 := by
  sorry

/-- Bound `Pr[bad]` by `t / |S|`.

The bad event is: some query during `hidingOa` (which includes `A.choose`, the
challenge commitment, and `A.distinguish`) had salt component equal to `s`.

Since the challenge query `(m, s)` ALWAYS has salt `s`, bad is ALWAYS set to `true`
after the challenge query. Therefore `Pr[bad] = 1` for any adversary and any `s`.

This means the bound `Pr[bad] ≤ t / |S|` holds only when `t ≥ |S|`, which is
vacuously true but not useful.

**Root cause**: The bad event should track adversary queries only (during `A.choose`),
NOT the challenge commitment query. The current `hidingOa` includes the challenge
query `(m, s)` in the computation run under `hidingImpl₁`, causing bad to always
be set.

**Fix needed**: Restructure the proof to either:
1. Track bad only during `A.choose` (requires separating the simulation into
   phases), OR
2. Average over `s` (sample `s` uniformly inside the game and use the fact that
   for random `s`, each of the adversary's ≤ t queries has probability 1/|S|
   of hitting salt `s`). -/
theorem probEvent_hidingBad_le {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, false)].toReal ≤
    (t : ℝ) / (Fintype.card S : ℝ) := by
  sorry

/-- **Hiding theorem (Lemma cm-hiding)**: For every salt `s`, the statistical distance
between the real and simulated hiding games is at most `t / |S|`.

**Proof structure** (identical-until-bad via game chain):

1. Reformulate `hidingReal` as `simulateQ hidingImpl₁` over augmented state.
2. Apply `tvDist_simulateQ_le_probEvent_bad` with `hidingImpl₁` and `hidingImpl₂`:
   - `h_agree`: when `¬bad`, the condition `bad && (ms.2 == s)` is false,
     so `hidingImpl₂` queries at `ms` (same as `hidingImpl₁`).
   - `h_mono`: bad flag uses `||`, so once true it stays true.
3. Show the intermediate game `(simulateQ hidingImpl₂ ...)` has TV distance 0 to `hidingSim`.
4. Bound `Pr[bad] ≤ t / |S|` using the adversary's query bound.

**Known issues**: Steps 3 and 4 have fundamental gaps — see the documentation on
`hidingImpl₂_eq_hidingSim` and `probEvent_hidingBad_le` for details and proposed fixes. -/
theorem hiding_bound {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    tvDist (hidingReal A s) (hidingSim A s) ≤ (t : ℝ) / (Fintype.card S : ℝ) := by
  -- Step 1: Rewrite hidingReal in simulateQ form with augmented state
  rw [hidingReal_eq_impl₁ A s]
  -- Step 2: Triangle inequality via intermediate game
  have h_triangle := tvDist_triangle
    ((simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, false))
    ((simulateQ (hidingImpl₂ s) (hidingOa A s)).run' (∅, false))
    (hidingSim A s)
  -- Step 2a: TV distance between real and intermediate via by_upto
  have h_step1 : tvDist
      ((simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, false))
      ((simulateQ (hidingImpl₂ s) (hidingOa A s)).run' (∅, false))
    ≤ Pr[hidingBad ∘ Prod.snd |
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, false)].toReal := by
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
    · -- ¬bad on initial state
      simp [hidingBad]
    · -- Implementations agree when ¬bad
      exact hidingImpl_agree s
    · -- Bad monotonicity for impl₁
      exact hidingImpl₁_bad_mono s
    · -- Bad monotonicity for impl₂
      exact hidingImpl₂_bad_mono s
  -- Step 2b: intermediate game equals hidingSim (distributional equivalence)
  have h_step2 : tvDist
      ((simulateQ (hidingImpl₂ s) (hidingOa A s)).run' (∅, false))
      (hidingSim A s) = 0 :=
    hidingImpl₂_eq_hidingSim A s
  -- Step 3: Combine
  have h_step3 : Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, false)].toReal ≤
      (t : ℝ) / (Fintype.card S : ℝ) :=
    probEvent_hidingBad_le A s
  linarith [tvDist_nonneg
    ((simulateQ (hidingImpl₂ s) (hidingOa A s)).run' (∅, false))
    (hidingSim A s)]
