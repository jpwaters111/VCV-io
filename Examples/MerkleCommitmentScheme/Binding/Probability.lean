/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Binding.QueryBound
import Examples.MerkleCommitmentScheme.Support.ROM
import Examples.CommitmentScheme.Support.Probability

/-!
# Merkle Commitment Scheme — Binding Probability Bounds

This file connects the deterministic Merkle collision theorem to reusable ROM
probability support from `Examples.CommitmentScheme.Support`. The generic
support supplies cache/log collision events, cache monotonicity, birthday
bounds, fresh-hit bounds, and probability bind/union lemmas. The Merkle-specific
inputs are the selected `checkSingle` computations and their query bound
`depth + 1`.

Quantitative map:
* ordinary witness fallback:
  `(t + 2 * (depth + 1))^2 / (2 * |C|)`;
* origin-aware conditioned split:
  `t * (t - 1) / (2 * |C|) + (depth + 1)^2 / |C|`.

The helper theorems below identify which generic event a Merkle binding failure
creates. They are intentionally explicit about cache origins because the
`(depth + 1)^2 / |C|` verifier term only applies after excluding fresh hits
into the adversary's commit cache.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- A second selected verifier path creates a fresh cache entry whose answer is
one of the first selected verifier path's logged answers.

This is the concrete Merkle event charged to the verifier term
`(depth + 1)^2 / |C|`: the second path has at most `depth + 1` queries and the
first path contributes at most `depth + 1` target answers. -/
private def SecondVerifierFreshHit [DecidableEq C]
    (targets : Finset C)
    (cache₁ : QueryCache (Oracle M S C))
    (z : (Bool × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)) :
    Prop :=
  ∃ target ∈ targets, ∃ t₀ : (Oracle M S C).Domain,
    ∃ v : (Oracle M S C).Range t₀,
      z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v target

/-- Monotonicity for the excluded fresh-hit side condition: if a later cache
extends an intermediate cache, a hit into the initial cache remains visible.

This lets rest-phase proofs reason with the final cache produced by both
selected verifier paths while applying local no-fresh-hit hypotheses. -/
private theorem freshHitInitialCache_mono_final
    {cache₀ cache₁ cache₂ : QueryCache (Oracle M S C)}
    (hle : cache₁ ≤ cache₂) :
    OracleComp.FreshHitInitialCache cache₀ cache₁ →
      OracleComp.FreshHitInitialCache cache₀ cache₂ := by
  rintro ⟨tNew, tOld, uNew, uOld, hnone, hnew, hold, hne, heq⟩
  exact ⟨tNew, tOld, uNew, uOld, hnone, hle hnew, hold, hne, heq⟩

/-- Convert two concrete colliding log entries into the generic
`OracleComp.LogHasCollision` event.

The theorem has no probability content; it is the structural bridge used when a
cache collision is traced back to two entries in the same selected verifier
log. -/
private theorem logHasCollision_of_mem
    {log : QueryLog (Oracle M S C)}
    {entry₀ entry₁ :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t}
    (hentry₀ : entry₀ ∈ log) (hentry₁ : entry₁ ∈ log)
    (hne : entry₀.1 ≠ entry₁.1) (heq : HEq entry₀.2 entry₁.2) :
    OracleComp.LogHasCollision log := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hentry₀
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hentry₁
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_, heq⟩
  · intro hij
    have hval : i = j := congrArg Fin.val hij
    subst j
    exact hne rfl
  · exact hne

/-- If a cached/logged computation starts from a collision-free cache, produces
no local log collision, and does not create a fresh value hitting the initial
cache, then the resulting cache is still collision-free.

This is the cache-origin invariant behind the conditioned textbook binding
split: adversary collisions are paid by the birthday term, while rest-created
collisions are charged only to selected verifier queries. -/
private theorem cacheNoCollision_after_cached_logging_of_no_initial_collision
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {α : Type}
    (oa : OracleComp (Oracle M S C) α)
    {cache₀ cache₁ cacheFinal : QueryCache (Oracle M S C)}
    {z : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀))
    (hcache₁ : z.2 = cache₁)
    (hcache₁Final : cache₁ ≤ cacheFinal)
    (hnoInitial : ¬ CacheHasCollision cache₀)
    (hnoFreshInitial : ¬ OracleComp.FreshHitInitialCache cache₀ cacheFinal)
    (hnoLog : ¬ OracleComp.LogHasCollision z.1.2) :
    ¬ CacheHasCollision cache₁ := by
  classical
  subst cache₁
  intro hcollision
  rcases hcollision with ⟨t₀, t₁, u₀, u₁, hne, hcache₀', hcache₁', heq⟩
  have hentries :=
    OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) oa cache₀ z hz
  have horigin₀ :=
    OracleComp.cache_entry_in_log_or_initial
      (spec := Oracle M S C) oa cache₀ z hz t₀ u₀ hcache₀'
  have horigin₁ :=
    OracleComp.cache_entry_in_log_or_initial
      (spec := Oracle M S C) oa cache₀ z hz t₁ u₁ hcache₁'
  rcases horigin₀ with hinit₀ | hlog₀
  · rcases horigin₁ with hinit₁ | hlog₁
    · exact hnoInitial ⟨t₀, t₁, u₀, u₁, hne, hinit₀, hinit₁, heq⟩
    · rcases hlog₁ with ⟨entry₁, hentry₁, hentry₁_input, hentry₁_answer⟩
      by_cases hcached₁ : ∃ old₁ : (Oracle M S C).Range entry₁.1,
          cache₀ entry₁.1 = some old₁
      · rcases hcached₁ with ⟨old₁, hold₁⟩
        have hentry_cache : z.2 entry₁.1 = some entry₁.2 :=
          hentries.1 entry₁ hentry₁
        have hold₁_z : z.2 entry₁.1 = some old₁ := hentries.2 hold₁
        have hold₁_eq : HEq old₁ entry₁.2 := by
          have hsome : (some old₁ : Option ((Oracle M S C).Range entry₁.1)) =
              some entry₁.2 := by
            rw [← hold₁_z, hentry_cache]
          exact heq_of_eq (Option.some.inj hsome)
        have hentry_ne : t₀ ≠ entry₁.1 := by
          intro hsame
          exact hne (by rw [← hentry₁_input, ← hsame])
        exact hnoInitial
          ⟨t₀, entry₁.1, u₀, old₁, hentry_ne, hinit₀, hold₁,
            heq.trans (hentry₁_answer.symm.trans hold₁_eq.symm)⟩
      · push_neg at hcached₁
        have hentry_none : cache₀ entry₁.1 = none := by
          cases h : cache₀ entry₁.1 with
          | none => rfl
          | some old => exact False.elim (hcached₁ old h)
        have hentry_cache_final : cacheFinal entry₁.1 = some entry₁.2 :=
          hcache₁Final (hentries.1 entry₁ hentry₁)
        have hentry_ne : entry₁.1 ≠ t₀ := by
          intro hsame
          exact hne (by rw [← hentry₁_input, hsame])
        exact hnoFreshInitial
          ⟨entry₁.1, t₀, entry₁.2, u₀, hentry_none, hentry_cache_final,
            hinit₀, hentry_ne, hentry₁_answer.trans heq.symm⟩
  · rcases hlog₀ with ⟨entry₀, hentry₀, hentry₀_input, hentry₀_answer⟩
    rcases horigin₁ with hinit₁ | hlog₁
    · by_cases hcached₀ : ∃ old₀ : (Oracle M S C).Range entry₀.1,
          cache₀ entry₀.1 = some old₀
      · rcases hcached₀ with ⟨old₀, hold₀⟩
        have hentry_cache : z.2 entry₀.1 = some entry₀.2 :=
          hentries.1 entry₀ hentry₀
        have hold₀_z : z.2 entry₀.1 = some old₀ := hentries.2 hold₀
        have hold₀_eq : HEq old₀ entry₀.2 := by
          have hsome : (some old₀ : Option ((Oracle M S C).Range entry₀.1)) =
              some entry₀.2 := by
            rw [← hold₀_z, hentry_cache]
          exact heq_of_eq (Option.some.inj hsome)
        have hentry_ne : entry₀.1 ≠ t₁ := by
          intro hsame
          exact hne (by rw [← hentry₀_input, hsame])
        exact hnoInitial
          ⟨entry₀.1, t₁, old₀, u₁, hentry_ne, hold₀, hinit₁,
            hold₀_eq.trans (hentry₀_answer.trans heq)⟩
      · push_neg at hcached₀
        have hentry_none : cache₀ entry₀.1 = none := by
          cases h : cache₀ entry₀.1 with
          | none => rfl
          | some old => exact False.elim (hcached₀ old h)
        have hentry_cache_final : cacheFinal entry₀.1 = some entry₀.2 :=
          hcache₁Final (hentries.1 entry₀ hentry₀)
        have hentry_ne : entry₀.1 ≠ t₁ := by
          intro hsame
          exact hne (by rw [← hentry₀_input, hsame])
        exact hnoFreshInitial
          ⟨entry₀.1, t₁, entry₀.2, u₁, hentry_none, hentry_cache_final,
            hinit₁, hentry_ne, hentry₀_answer.trans heq⟩
    · rcases hlog₁ with ⟨entry₁, hentry₁, hentry₁_input, hentry₁_answer⟩
      have hentry_ne : entry₀.1 ≠ entry₁.1 := by
        intro hsame
        exact hne (by rw [← hentry₀_input, ← hentry₁_input, hsame])
      exact hnoLog
        (logHasCollision_of_mem
          (M := M) (S := S) (C := C)
          hentry₀ hentry₁ hentry_ne
          (hentry₀_answer.trans (heq.trans hentry₁_answer.symm)))

/-- A rest-created cross-log collision between the two selected verifier logs
forces the second verifier run to sample a fresh answer that hits the first
verifier log's answer set.

The no-first-log-collision hypothesis rules out the case where the second log
only reuses a value already created twice by the first verifier path. -/
private theorem restCreatedLogCrossCollision_implies_secondVerifierFreshHit
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (check₀ check₁ : OracleComp (Oracle M S C) Bool)
    {commitCache cache₁ cache₂ : QueryCache (Oracle M S C)}
    {single₀ single₁ : Bool × QueryLog (Oracle M S C)}
    (hsupport₀ : (single₀, cache₁) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₀).run)).run commitCache))
    (hsupport₁ : (single₁, cache₂) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁))
    (hrest :
      OracleComp.RestCreatedLogCrossCollision commitCache single₀.2 single₁.2)
    (hnoFirst : ¬ OracleComp.LogHasCollision single₀.2) :
    SecondVerifierFreshHit (M := M) (S := S) (C := C)
      (merkleLogAnswerTargets (M := M) (S := S) (C := C) single₀.2)
      cache₁ (single₁, cache₂) := by
  classical
  rcases hrest with
    ⟨entry₀, hentry₀, entry₁, hentry₁, _hfresh₀, hfresh₁, hne, heq⟩
  have hentries₀ :=
    OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) check₀ commitCache (single₀, cache₁) hsupport₀
  have hentries₁ :=
    OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) check₁ cache₁ (single₁, cache₂) hsupport₁
  have hentry₁_cache₂ : cache₂ entry₁.1 = some entry₁.2 :=
    hentries₁.1 entry₁ hentry₁
  have hentry₁_cache₁_none : cache₁ entry₁.1 = none := by
    unfold OracleComp.LogEntryFresh at hfresh₁
    cases hcache₁ : cache₁ entry₁.1 with
    | none => rfl
    | some old =>
        have horigin :=
          OracleComp.cache_entry_in_log_or_initial
            (spec := Oracle M S C) check₀ commitCache (single₀, cache₁)
            hsupport₀ entry₁.1 old hcache₁
        rcases horigin with hinit | hlog
        · rw [hfresh₁] at hinit
          contradiction
        · rcases hlog with ⟨entry₀', hentry₀', hentry₀'_input, hentry₀'_answer⟩
          have hold_cache₂ : cache₂ entry₁.1 = some old := hentries₁.2 hcache₁
          have hold_eq : HEq old entry₁.2 := by
            have hsome : (some old : Option ((Oracle M S C).Range entry₁.1)) =
                some entry₁.2 := by
              rw [← hold_cache₂, hentry₁_cache₂]
            exact heq_of_eq (Option.some.inj hsome)
          have hentry_ne : entry₀.1 ≠ entry₀'.1 := by
            intro hsame
            exact hne (hsame.trans hentry₀'_input)
          have heq_first : HEq entry₀.2 entry₀'.2 :=
            heq.trans (hold_eq.symm.trans hentry₀'_answer.symm)
          exact False.elim <| hnoFirst
            (logHasCollision_of_mem
              (M := M) (S := S) (C := C)
              hentry₀ hentry₀' hentry_ne heq_first)
  refine ⟨traceEntryAnswer (M := M) (S := S) (C := C) entry₀,
    traceEntryAnswer_mem_merkleLogAnswerTargets
      (M := M) (S := S) (C := C) hentry₀,
    entry₁.1, entry₁.2, hentry₁_cache₂, hentry₁_cache₁_none, ?_⟩
  exact heq.symm.trans (traceEntryAnswer_heq_of_entry (M := M) (S := S) (C := C) entry₀)

/-- Bound the second-verifier fresh-hit event by the selected-path verifier
term `bindingVerifierErrorTerm C depth = (depth + 1)^2 / |C|`.

The proof is a direct application of the generic fresh-cache-hit bound to the
target finset formed from the first selected verifier log. -/
private theorem secondVerifierFreshHit_bound_of_first_log
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (check₀ check₁ : OracleComp (Oracle M S C) Bool)
    {commitCache cache₁ : QueryCache (Oracle M S C)}
    {single₀ : Bool × QueryLog (Oracle M S C)}
    (hsupport₀ : (single₀, cache₁) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₀).run)).run commitCache))
    (hbound₀ : IsTotalQueryBound check₀ (depth + 1))
    (hbound₁ : IsTotalQueryBound check₁ (depth + 1))
    (hnoCache₁ : ¬ CacheHasCollision cache₁) :
    Pr[fun z =>
      SecondVerifierFreshHit (M := M) (S := S) (C := C)
        (merkleLogAnswerTargets (M := M) (S := S) (C := C) single₀.2)
        cache₁ z |
      (simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁] ≤
      bindingVerifierErrorTerm C depth := by
  classical
  let targets := merkleLogAnswerTargets (M := M) (S := S) (C := C) single₀.2
  have hlogBound₁ :
      IsTotalQueryBound ((simulateQ loggingOracle check₁).run) (depth + 1) :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff check₁ (depth + 1)).mpr
      hbound₁
  have hfresh :
      Pr[fun z =>
        SecondVerifierFreshHit (M := M) (S := S) (C := C) targets cache₁ z |
        (simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁] ≤
        ((((depth + 1) * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
    simpa [SecondVerifierFreshHit, targets] using
      (probEvent_merkle_cache_has_value_mem_finset_le
        (M := M) (S := S) (C := C)
        ((simulateQ loggingOracle check₁).run) (depth + 1) hlogBound₁
        targets cache₁ hnoCache₁)
  have hlen : single₀.2.length ≤ depth + 1 :=
    OracleComp.log_length_le_of_mem_support_run_cached_logging
      (spec := Oracle M S C) (oa := check₀) hbound₀ commitCache
      (z := (single₀, cache₁)) hsupport₀
  have htargets : targets.card ≤ depth + 1 :=
    le_trans (merkleLogAnswerTargets_card_le (M := M) (S := S) (C := C) single₀.2) hlen
  calc
    Pr[fun z =>
      SecondVerifierFreshHit (M := M) (S := S) (C := C) targets cache₁ z |
      (simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁]
        ≤ ((((depth + 1) * targets.card : ℕ) : ℝ≥0∞) *
            (Fintype.card C : ℝ≥0∞)⁻¹) := hfresh
    _ ≤ ((((depth + 1) * (depth + 1) : ℕ) : ℝ≥0∞) *
            (Fintype.card C : ℝ≥0∞)⁻¹) := by
          gcongr
    _ = bindingVerifierErrorTerm C depth := by
          simp [bindingVerifierErrorTerm, Nat.pow_two, ENNReal.div_eq_inv_mul,
            bindingVerifierPathQueryCount, mul_comm]

/-- Conditional bound for the second selected verifier path after the first
path has been logged.

If the intermediate cache is collision-free, the event is bounded as a fresh
hit into the first log's at-most-`depth + 1` answers. If it is not collision-free,
the local no-collision/no-fresh-hit hypotheses in `BindingTextbookRestCreatedEvent`
make the event impossible. -/
private theorem bindingTextbookRestCreatedEvent_second_bound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (commitCache : QueryCache (Oracle M S C))
    (w : BindingMismatchWitness (M := M) (S := S) (C := C) out)
    (check₀ check₁ : OracleComp (Oracle M S C) Bool)
    {single₀ : Bool × QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    (hsupport₀ : (single₀, cache₁) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₀).run)).run commitCache))
    (hbound₀ : IsTotalQueryBound check₀ (depth + 1))
    (hbound₁ : IsTotalQueryBound check₁ (depth + 1))
    (hnoCommit : ¬ CacheHasCollision commitCache) :
    Pr[fun z =>
      BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        ((simulateQ loggingOracle check₁).run >>= fun single₁ =>
          pure
            ({ out := out
               commitCache := commitCache
               witness? := some w
               single₀? := some single₀
               single₁? := some single₁ } :
              BindingTextbookWitnessTranscript M S C depth))).run cache₁] ≤
      bindingVerifierErrorTerm C depth := by
  classical
  by_cases hnoCache₁ : ¬ CacheHasCollision cache₁
  · have hrun :
        (simulateQ cachingOracle
          ((simulateQ loggingOracle check₁).run >>= fun single₁ =>
            pure
              ({ out := out
                 commitCache := commitCache
                 witness? := some w
                 single₀? := some single₀
                 single₁? := some single₁ } :
                BindingTextbookWitnessTranscript M S C depth))).run cache₁ =
          (fun z : (Bool × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C) =>
            (({ out := out
                commitCache := commitCache
                witness? := some w
                single₀? := some single₀
                single₁? := some z.1 } :
              BindingTextbookWitnessTranscript M S C depth), z.2)) <$>
            ((simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁) := by
      rw [simulateQ_bind, StateT.run_bind]
      simp [simulateQ_pure, StateT.run, map_eq_bind_pure_comp]
      rfl
    rw [hrun, probEvent_map]
    refine le_trans
      (probEvent_mono
        (q := fun z =>
          SecondVerifierFreshHit (M := M) (S := S) (C := C)
            (merkleLogAnswerTargets (M := M) (S := S) (C := C) single₀.2)
            cache₁ z) ?_) ?_
    · intro z hz hevent
      rcases hevent with
        ⟨single₀Event, single₁Event, hsingle₀, hsingle₁, hrest, hnoFirst, _hnoFresh⟩
      have hsingle₀Eq : single₀Event = single₀ := by
        simpa using (Option.some.inj hsingle₀).symm
      subst single₀Event
      have hsingle₁Eq : single₁Event = z.1 := by
        simpa using (Option.some.inj hsingle₁).symm
      subst single₁Event
      exact
        restCreatedLogCrossCollision_implies_secondVerifierFreshHit
          (M := M) (S := S) (C := C)
          check₀ check₁ hsupport₀ hz hrest hnoFirst
    · exact
        secondVerifierFreshHit_bound_of_first_log
          (M := M) (S := S) (C := C)
          check₀ check₁ hsupport₀ hbound₀ hbound₁ hnoCache₁
  · have hzero :
        Pr[fun z =>
          BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            ((simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   commitCache := commitCache
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingTextbookWitnessTranscript M S C depth))).run cache₁] = 0 := by
      apply probEvent_eq_zero
      intro z hz hevent
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₂⟩, hsupport₁, hpure⟩
      simp [simulateQ_pure, StateT.run] at hpure
      subst z
      rcases hevent with
        ⟨single₀Event, single₁Event, hsingle₀, hsingle₁, _hrest, hnoFirst, hnoFresh⟩
      have hsingle₀Eq : single₀Event = single₀ := by
        simpa using (Option.some.inj hsingle₀).symm
      subst single₀Event
      have hsingle₁Eq : single₁Event = single₁ := by
        simpa using (Option.some.inj hsingle₁).symm
      subst single₁Event
      have hcache₁Final : cache₁ ≤ cache₂ :=
        OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C) ((simulateQ loggingOracle check₁).run)
          cache₁ (single₁, cache₂) hsupport₁
      exact hnoCache₁
        (cacheNoCollision_after_cached_logging_of_no_initial_collision
          (M := M) (S := S) (C := C)
          check₀ hsupport₀ rfl hcache₁Final hnoCommit hnoFresh hnoFirst)
    rw [hzero]
    exact zero_le _

/-- Bound the entire selected-verifier rest phase of the conditioned textbook
binding game by `(depth + 1)^2 / |C|`.

The no-witness branch has probability zero. In the selected branch, both
`checkSingle` computations have query bound `depth + 1`, and the previous
lemma charges all rest-created cross-log collisions to the second verifier
fresh-hit event. -/
private theorem bindingTextbookWitnessRest_restCreatedEvent_bound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (commitCache : QueryCache (Oracle M S C))
    (hnoCommit : ¬ CacheHasCollision commitCache) :
    Pr[fun z =>
      BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
          commitCache out)).run commitCache] ≤
      bindingVerifierErrorTerm C depth := by
  classical
  unfold bindingTextbookWitnessRest bindingWitnessRest
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      have hzero :
          Pr[fun z =>
            BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (pure
                ({ out := out
                   commitCache := commitCache
                   witness? := none
                   single₀? := none
                   single₁? := none } :
                  BindingTextbookWitnessTranscript M S C depth))).run commitCache] = 0 := by
        apply probEvent_eq_zero
        intro z hz hevent
        simp [simulateQ_pure, StateT.run] at hz
        subst z
        rcases hevent with ⟨single₀, _single₁, hsingle₀, _hsingle₁, _⟩
        simp at hsingle₀
      simpa [hsel] using le_of_eq_of_le hzero (zero_le _)
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      have hbound₀ : IsTotalQueryBound check₀ (depth + 1) := by
        dsimp [check₀]
        exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      have hbound₁ : IsTotalQueryBound check₁ (depth + 1) := by
        dsimp [check₁]
        exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel]
      have hcomp :
          ((do
            let base ←
              ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
                (simulateQ loggingOracle check₁).run >>= fun single₁ =>
                  pure
                    ({ out := out
                       witness? := some w
                       single₀? := some single₀
                       single₁? := some single₁ } :
                      BindingWitnessTranscript M S C depth))
            pure
              ({ out := base.out
                 commitCache := commitCache
                 witness? := base.witness?
                 single₀? := base.single₀?
                 single₁? := base.single₁? } :
                BindingTextbookWitnessTranscript M S C depth)) :
            OracleComp (Oracle M S C)
              (BindingTextbookWitnessTranscript M S C depth)) =
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   commitCache := commitCache
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingTextbookWitnessTranscript M S C depth)) := by
        simp [bind_assoc]
      rw [hcomp]
      change
        Pr[fun z =>
          BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
              (simulateQ loggingOracle check₁).run >>= fun single₁ =>
                pure
                  ({ out := out
                     commitCache := commitCache
                     witness? := some w
                     single₀? := some single₀
                     single₁? := some single₁ } :
                    BindingTextbookWitnessTranscript M S C depth))).run commitCache] ≤
          bindingVerifierErrorTerm C depth
      rw [simulateQ_bind, StateT.run_bind]
      refine OracleComp.probEvent_bind_le_of_forall_support ?_
      intro z hz
      rcases z with ⟨single₀, cache₁⟩
      exact
        bindingTextbookRestCreatedEvent_second_bound
          (M := M) (S := S) (C := C)
          out commitCache w check₀ check₁ hz hbound₀ hbound₁ hnoCommit

/-- A successful selected binding rest phase gives a generic cross-log
collision between the two stored selected `checkSingle` logs.

This is the deterministic-to-ROM bridge for the conservative fallback bound:
the Merkle theorem `checkSingle_crossLogCollision` supplies the collision, and
generic cache-collision support supplies the probability estimate. -/
private theorem bindingWitnessRest_win_implies_logCrossEvent_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    {cache₀ : QueryCache (Oracle M S C)}
    {z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀))
    (hwin : BindingWitnessWinROM (M := M) (S := S) (C := C) z) :
    BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z := by
  classical
  unfold bindingWitnessRest at hz
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      simp [hsel] at hz
      subst z
      rcases hwin with ⟨w, single₀, single₁, hw, hsingle₀, hsingle₁, _, _⟩
      simp at hw
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel] at hz
      change z ∈ support
        ((simulateQ cachingOracle
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))).run cache₀) at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₀, cache₁⟩, hsingle₀Support, hz⟩
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₂⟩, hsingle₁Support, hz⟩
      simp at hz
      subst z
      rcases hwin with
        ⟨wWin, single₀Win, single₁Win, hw, hsingle₀, hsingle₁, hok₀, hok₁⟩
      cases hw
      cases hsingle₀
      cases hsingle₁
      let f := oracleFnOfCache (M := M) (S := S) (C := C) cache₂
      have hmono₁₂ : cache₁ ≤ cache₂ := by
        exact OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C) ((simulateQ loggingOracle check₁).run)
          cache₁ (single₁, cache₂) hsingle₁Support
      have hlog₀ : logEval (M := M) (S := S) (C := C) f check₀ = single₀ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₀
          (cache₀ := cache₀) (cacheFinal := cache₂)
          (z := (single₀, cache₁)) hsingle₀Support hmono₁₂
      have hlog₁ : logEval (M := M) (S := S) (C := C) f check₁ = single₁ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₁
          (cache₀ := cache₁) (cacheFinal := cache₂)
          (z := (single₁, cache₂)) hsingle₁Support (le_refl cache₂)
      have hcheck₀ : eval (M := M) (S := S) (C := C) f check₀ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₀).1 = true := by
          simpa [hlog₀] using hok₀.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₀] using hfst
      have hcheck₁ : eval (M := M) (S := S) (C := C) f check₁ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₁).1 = true := by
          simpa [hlog₁] using hok₁.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₁] using hfst
      have hcollision :
          CrossLogCollision
            (logEval (M := M) (S := S) (C := C) f check₀).2
            (logEval (M := M) (S := S) (C := C) f check₁).2 := by
        dsimp [check₀, check₁] at hcheck₀ hcheck₁
        exact checkSingle_crossLogCollision (M := M) (S := S) (C := C)
          f out.commitment w.idx (out.message₀ i₀) (out.message₁ i₁)
          (out.proof₀ i₀) (out.proof₁ i₁) hcheck₀ hcheck₁
          (Or.inl w.mismatch)
      have hcollisionStored :
          OracleComp.LogCrossCollision single₀.2 single₁.2 := by
        exact
          (crossLogCollision_iff_oracleComp_logCrossCollision
            (M := M) (S := S) (C := C)).mp
            (by simpa [hlog₀, hlog₁] using hcollision)
      exact ⟨single₀, single₁, rfl, rfl, hcollisionStored⟩

/-- Lift a bound on selected-rest cross-log collisions to a bound on selected
binding wins.

There is no new arithmetic here: the theorem only packages the deterministic
implication from accepted conflicting paths to `BindingWitnessRestLogCrossEvent`
so the probability proof can reuse any supplied `ε`. -/
private theorem bindingWitnessRest_win_bound_of_logCrossEvent_bound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (cache₀ : QueryCache (Oracle M S C))
    (ε : ℝ≥0∞)
    (hlog :
      Pr[ fun z => BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z |
        (simulateQ cachingOracle
          (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀] ≤ ε) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀] ≤ ε :=
  le_trans
    (probEvent_mono fun _ hz hwin =>
      bindingWitnessRest_win_implies_logCrossEvent_of_support
        (M := M) (S := S) (C := C) out hz hwin)
    hlog

/-- Convert a generic selected-rest cross-log collision into an origin-aware
`RestCreatedLogCrossCollision` when the starting cache is collision-free and no
fresh rest query hits an initial-cache value.

This is the event-strengthening step needed for the conditioned textbook split:
only collisions whose two answers are created during the selected verifier rest
phase can be charged to the `(depth + 1)^2 / |C|` term. -/
private theorem bindingWitnessRest_logCrossEvent_implies_restCreatedEvent_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    {cache₀ : QueryCache (Oracle M S C)}
    {z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀))
    (hlog : BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z)
    (hnoCollision : ¬ CacheHasCollision cache₀)
    (hnoFreshHit : ¬ OracleComp.FreshHitInitialCache cache₀ z.2) :
    ∃ (single₀ single₁ : Bool × QueryLog (Oracle M S C)),
      z.1.single₀? = some single₀ ∧
      z.1.single₁? = some single₁ ∧
      OracleComp.RestCreatedLogCrossCollision cache₀ single₀.2 single₁.2 := by
  classical
  unfold bindingWitnessRest at hz
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      simp [hsel] at hz
      subst z
      rcases hlog with ⟨single₀, single₁, hsingle₀, _hsingle₁, _hcross⟩
      simp at hsingle₀
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel] at hz
      change z ∈ support
        ((simulateQ cachingOracle
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))).run cache₀) at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₀, cache₁⟩, hsingle₀Support, hz⟩
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₂⟩, hsingle₁Support, hz⟩
      simp at hz
      subst z
      rcases hlog with ⟨single₀Log, single₁Log, hsingle₀, hsingle₁, hcross⟩
      have hsingle₀Eq : single₀Log = single₀ := by
        simpa using (Option.some.inj hsingle₀).symm
      have hsingle₁Eq : single₁Log = single₁ := by
        simpa using (Option.some.inj hsingle₁).symm
      subst single₀Log
      subst single₁Log
      have h₀ :=
        OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₀ cache₀ (single₀, cache₁)
          hsingle₀Support
      have h₁ :=
        OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₁ cache₁ (single₁, cache₂)
          hsingle₁Support
      have hrest :
          OracleComp.RestCreatedLogCrossCollision cache₀ single₀.2 single₁.2 :=
        OracleComp.LogCrossCollision.to_restCreated_of_no_initial_collision_no_freshHit
          (spec := Oracle M S C)
          (cache₀ := cache₀) (cache₁ := cache₂)
          (log₀ := single₀.2) (log₁ := single₁.2)
          (le_trans h₀.2 h₁.2)
          (fun entry hentry => h₁.2 (h₀.1 entry hentry))
          (fun entry hentry => h₁.1 entry hentry)
          hnoCollision hnoFreshHit hcross
      exact ⟨single₀, single₁, rfl, rfl, hrest⟩

/-- A conditioned selected binding win implies the precise rest-created event
bounded by the verifier term.

The theorem combines the deterministic Merkle collision theorem with the
origin-aware no-fresh-hit side conditions stored in `BindingTextbookWinROM`. -/
private theorem bindingTextbookWitnessRest_win_implies_restCreatedEvent_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (commitCache : QueryCache (Oracle M S C))
    {z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
          commitCache out)).run commitCache))
    (hnoCollision : ¬ CacheHasCollision commitCache)
    (hwin : BindingTextbookWinROM (M := M) (S := S) (C := C) z) :
    BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z := by
  classical
  unfold bindingTextbookWitnessRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨baseZ, hbase, hz⟩
  simp [simulateQ_pure, StateT.run] at hz
  subst z
  rcases hwin with ⟨hbaseWin, hnoFreshHit, hnoFirstCollision⟩
  have hlog :
      BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) baseZ :=
    bindingWitnessRest_win_implies_logCrossEvent_of_support
      (M := M) (S := S) (C := C) out hbase hbaseWin
  rcases
      bindingWitnessRest_logCrossEvent_implies_restCreatedEvent_of_support
        (M := M) (S := S) (C := C) out hbase hlog hnoCollision hnoFreshHit
    with ⟨single₀, single₁, hsingle₀, hsingle₁, hrest⟩
  exact ⟨single₀, single₁, by simpa using hsingle₀, by simpa using hsingle₁,
    hrest, hnoFirstCollision single₀ (by simpa using hsingle₀), hnoFreshHit⟩

/-- A ROM witness binding win implies a whole-cache collision in the final
cache.

This is the conservative fallback path: it does not classify origins, so the
probability bound charges the adversary and the two selected verifier paths to
one birthday term `(t + 2 * (depth + 1))^2 / (2 * |C|)`. -/
private theorem bindingWitnessWinROM_implies_badEventROM_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t)
    {z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support (bindingWitnessGame (M := M) (S := S) (C := C) A))
    (hwin : BindingWitnessWinROM (M := M) (S := S) (C := C) z) :
    BindingWitnessBadEventROM (M := M) (S := S) (C := C) z := by
  classical
  unfold bindingWitnessGame bindingWitnessInner at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨⟨out, cache₁⟩, hout, hz⟩
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      simp [hsel] at hz
      subst z
      rcases hwin with ⟨w, single₀, single₁, hw, hsingle₀, hsingle₁, hok₀, hok₁⟩
      simp at hw
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel, Prod.fst, Prod.snd] at hz
      change z ∈ support
        ((simulateQ cachingOracle
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))).run cache₁) at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₀, cache₂⟩, hsingle₀Support, hz⟩
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₃⟩, hsingle₁Support, hz⟩
      simp at hz
      subst z
      rcases hwin with
        ⟨wWin, single₀Win, single₁Win, hw, hsingle₀, hsingle₁, hok₀, hok₁⟩
      cases hw
      cases hsingle₀
      cases hsingle₁
      let f := oracleFnOfCache (M := M) (S := S) (C := C) cache₃
      have hmono₂₃ : cache₂ ≤ cache₃ := by
        exact OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C) ((simulateQ loggingOracle check₁).run)
          cache₂ (single₁, cache₃) hsingle₁Support
      have hlog₀ : logEval (M := M) (S := S) (C := C) f check₀ = single₀ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₀
          (cache₀ := cache₁) (cacheFinal := cache₃)
          (z := (single₀, cache₂)) hsingle₀Support hmono₂₃
      have hlog₁ : logEval (M := M) (S := S) (C := C) f check₁ = single₁ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₁
          (cache₀ := cache₂) (cacheFinal := cache₃)
          (z := (single₁, cache₃)) hsingle₁Support (le_refl cache₃)
      have hcheck₀ : eval (M := M) (S := S) (C := C) f check₀ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₀).1 = true := by
          simpa [hlog₀] using hok₀.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₀] using hfst
      have hcheck₁ : eval (M := M) (S := S) (C := C) f check₁ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₁).1 = true := by
          simpa [hlog₁] using hok₁.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₁] using hfst
      have hcollision :
          CrossLogCollision
            (logEval (M := M) (S := S) (C := C) f check₀).2
            (logEval (M := M) (S := S) (C := C) f check₁).2 := by
        dsimp [check₀, check₁] at hcheck₀ hcheck₁
        exact checkSingle_crossLogCollision (M := M) (S := S) (C := C)
          f out.commitment w.idx (out.message₀ i₀) (out.message₁ i₁)
          (out.proof₀ i₀) (out.proof₁ i₁) hcheck₀ hcheck₁
          (Or.inl w.mismatch)
      have hcollisionStored : CrossLogCollision single₀.2 single₁.2 := by
        simpa [hlog₀, hlog₁] using hcollision
      rcases hcollisionStored with ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
      have hentry₀Cache₂ : cache₂ entry₀.1 = some entry₀.2 :=
        (OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₀ cache₁ (single₀, cache₂)
          hsingle₀Support).1 entry₀ hentry₀
      have hentry₀Cache₃ : cache₃ entry₀.1 = some entry₀.2 :=
        hmono₂₃ hentry₀Cache₂
      have hentry₁Cache₃ : cache₃ entry₁.1 = some entry₁.2 :=
        (OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₁ cache₂ (single₁, cache₃)
          hsingle₁Support).1 entry₁ hentry₁
      exact
        ⟨entry₀.1, entry₁.1, entry₀.2, entry₁.2,
          hne, hentry₀Cache₃, hentry₁Cache₃, heq⟩

/-- A fixed-oracle binding win produces the cross-log collision from
`check_crossLogCollision`. -/
theorem bindingWin_implies_crossLogCollision [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (out : BindingOutput M S C depth) :
    BindingWin (M := M) (S := S) (C := C) f out →
      BindingCollisionEvent (M := M) (S := S) (C := C) f out := by
  intro hwin
  exact
    check_crossLogCollision (M := M) (S := S) (C := C)
      f out.commitment out.I₀ out.I₁ out.message₀ out.message₁
      out.proof₀ out.proof₁ hwin.2.1 hwin.2.2 (.inl hwin.1)

/-- Any probability bound for the induced cross-log collision event immediately
bounds fixed-oracle Merkle binding wins. This is the conditional combiner used
before the final ROM binding theorem bounds the collision event directly. -/
theorem binding_bound_of_collision_bound [DecidableEq C]
    [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) (BindingOutput M S C depth))
    (ε : ℝ≥0∞)
    (hcollision :
      Pr[ fun out =>
        BindingCollisionEvent (M := M) (S := S) (C := C) f out | oa] ≤ ε) :
    Pr[ fun out => BindingWin (M := M) (S := S) (C := C) f out | oa] ≤ ε :=
  le_trans
    (probEvent_mono fun out _ hout =>
      bindingWin_implies_crossLogCollision (M := M) (S := S) (C := C) f out hout)
    hcollision

/-- Conservative ROM binding bound for the witness-index Merkle binding game.

This theorem uses the generic whole-cache birthday bound for the adversary plus
the two selected single-check traces. It is intentionally looser than the
textbook split bound, but it is unconditional and applies to the witness game
that checks only one mismatching shared index. -/
theorem binding_bound_wholeCache {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t := by
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [merkleOracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hbirthday :=
    probEvent_cacheCollision_le_birthday_total
      (spec := Oracle M S C)
      (oa := bindingWitnessInner (M := M) (S := S) (C := C) A)
      (t + bindingWitnessVerifierQueryCount depth)
      (bindingWitnessInner_totalQueryBound (M := M) (S := S) (C := C) A)
      hCdefault
      (merkleOracleRange_card_le (M := M) (S := S) (C := C))
  calc
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A]
        ≤ Pr[fun z => BindingWitnessBadEventROM (M := M) (S := S) (C := C) z |
            bindingWitnessGame (M := M) (S := S) (C := C) A] :=
          probEvent_mono fun z hz hwin =>
            bindingWitnessWinROM_implies_badEventROM_of_support
              (M := M) (S := S) (C := C) A hz hwin
    _ ≤ bindingWitnessErrorTerm C depth t := by
          simpa [bindingWitnessGame, BindingWitnessBadEventROM, bindingWitnessErrorTerm,
            bindingWitnessVerifierQueryCount, bindingVerifierPathQueryCount,
            merkleOracleRange_card_eq (M := M) (S := S) (C := C) default] using hbirthday

/-- Generic two-phase combiner for the ordinary witness game.

The commit phase contributes the adversary birthday term
`t * (t - 1) / (2 * |C|)`. The hypothesis supplies the rest-phase verifier
term, usually `(depth + 1)^2 / |C|`, after conditioning on a collision-free
post-commit cache. -/
private theorem bindingWitnessGame_bound_of_rest_logCrossEvent_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hrest :
      ∀ (out : BindingOutput M S C depth)
        (cache₁ : QueryCache (Oracle M S C)),
        (out, cache₁) ∈ support
          ((simulateQ cachingOracle
            (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅) →
        ¬ CacheHasCollision cache₁ →
          Pr[ fun z =>
            BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₁] ≤
            bindingVerifierErrorTerm C depth) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  classical
  let commitPart :=
    bindingWitnessCommitPart (M := M) (S := S) (C := C) A
  let restPart :=
    fun x : BindingOutput M S C depth × QueryCache (Oracle M S C) =>
      (simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) x.1)).run x.2
  let ε₁ : ℝ≥0∞ := bindingBirthdayTerm C t
  let ε₂ : ℝ≥0∞ := bindingVerifierErrorTerm C depth
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [merkleOracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hcommit :
      Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
        (simulateQ cachingOracle commitPart).run ∅] ≤ ε₁ := by
    have hbirthday :=
      probEvent_cacheCollision_le_birthday_total_tight
        (spec := Oracle M S C)
        (oa := commitPart)
        t
        (by
          simpa [commitPart, bindingWitnessCommitPart] using A.queryBound)
        hCdefault
        (merkleOracleRange_card_le (M := M) (S := S) (C := C))
    simpa [ε₁, bindingBirthdayTerm,
      merkleOracleRange_card_eq (M := M) (S := S) (C := C) default,
      not_not] using hbirthday
  have hrestWin :
      ∀ x ∈ support ((simulateQ cachingOracle commitPart).run ∅),
        ¬ CacheHasCollision x.2 →
          Pr[fun z => ¬
              (¬ BindingWitnessWinROM (M := M) (S := S) (C := C) z) |
            restPart x] ≤ ε₂ := by
    intro x hx hno
    rcases x with ⟨out, cache₁⟩
    have hlog :
        Pr[fun z =>
          BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₁] ≤
          ε₂ := by
      simpa [commitPart, ε₂] using hrest out cache₁ (by simpa [commitPart] using hx) hno
    have hwin :=
      bindingWitnessRest_win_bound_of_logCrossEvent_bound
        (M := M) (S := S) (C := C) out cache₁ ε₂ hlog
    simpa [restPart, ε₂, not_not] using hwin
  have hcombine :=
    probEvent_bind_le_add
      (mx := (simulateQ cachingOracle commitPart).run ∅)
      (my := restPart)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => ¬ BindingWitnessWinROM (M := M) (S := S) (C := C) z)
      (ε₁ := ε₁)
      (ε₂ := ε₂)
      hcommit hrestWin
  rw [bindingWitnessGame, bindingWitnessInner_eq_bind (M := M) (S := S) (C := C) A,
    simulateQ_bind, StateT.run_bind]
  simpa [commitPart, restPart, ε₁, ε₂, bindingWitnessCommitPart,
    bindingErrorTerm, bindingBirthdayTerm, bindingVerifierErrorTerm,
    not_not] using hcombine

/-- Conditional textbook combiner for the origin-aware witness game.

The hypothesis is the rest-phase estimate: once the adversary cache is
collision-free, the conditioned selected-check win is bounded by the
single-pair verifier term. -/
theorem bindingTextbookWitnessGame_bound_of_rest_win_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hrest :
      ∀ (out : BindingOutput M S C depth)
        (cache₁ : QueryCache (Oracle M S C)),
        (out, cache₁) ∈ support
          ((simulateQ cachingOracle
            (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅) →
        ¬ CacheHasCollision cache₁ →
          Pr[ fun z =>
            BindingTextbookWinROM (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
                cache₁ out)).run cache₁] ≤
            bindingVerifierErrorTerm C depth) :
    Pr[ fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  classical
  let commitPart :=
    bindingWitnessCommitPart (M := M) (S := S) (C := C) A
  let restPart :=
    fun x : BindingOutput M S C depth × QueryCache (Oracle M S C) =>
      (simulateQ cachingOracle
        (bindingTextbookWitnessRest (M := M) (S := S) (C := C) x.2 x.1)).run x.2
  let ε₁ : ℝ≥0∞ := bindingBirthdayTerm C t
  let ε₂ : ℝ≥0∞ := bindingVerifierErrorTerm C depth
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [merkleOracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hcommit :
      Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
        (simulateQ cachingOracle commitPart).run ∅] ≤ ε₁ := by
    have hbirthday :=
      probEvent_cacheCollision_le_birthday_total_tight
        (spec := Oracle M S C)
        (oa := commitPart)
        t
        (by
          simpa [commitPart, bindingWitnessCommitPart] using A.queryBound)
        hCdefault
        (merkleOracleRange_card_le (M := M) (S := S) (C := C))
    simpa [ε₁, bindingBirthdayTerm,
      merkleOracleRange_card_eq (M := M) (S := S) (C := C) default,
      not_not] using hbirthday
  have hrestWin :
      ∀ x ∈ support ((simulateQ cachingOracle commitPart).run ∅),
        ¬ CacheHasCollision x.2 →
          Pr[fun z => ¬
              (¬ BindingTextbookWinROM (M := M) (S := S) (C := C) z) |
            restPart x] ≤ ε₂ := by
    intro x hx hno
    rcases x with ⟨out, cache₁⟩
    have hwin :
        Pr[fun z =>
          BindingTextbookWinROM (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
              cache₁ out)).run cache₁] ≤ ε₂ := by
      simpa [commitPart, ε₂] using hrest out cache₁ (by simpa [commitPart] using hx) hno
    simpa [restPart, ε₂, not_not] using hwin
  have hcombine :=
    probEvent_bind_le_add
      (mx := (simulateQ cachingOracle commitPart).run ∅)
      (my := restPart)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => ¬ BindingTextbookWinROM (M := M) (S := S) (C := C) z)
      (ε₁ := ε₁)
      (ε₂ := ε₂)
      hcommit hrestWin
  rw [bindingTextbookWitnessGame]
  simpa [commitPart, restPart, ε₁, ε₂, bindingWitnessCommitPart,
    bindingErrorTerm, bindingBirthdayTerm, bindingVerifierErrorTerm,
    not_not] using hcombine

/-- Conditional textbook combiner using the precise rest-created cross-collision
event. This is the form consumed by the final product-bound ROM lemma. -/
theorem bindingTextbookWitnessGame_bound_of_restCreatedEvent_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hrest :
      ∀ (out : BindingOutput M S C depth)
        (cache₁ : QueryCache (Oracle M S C)),
        (out, cache₁) ∈ support
          ((simulateQ cachingOracle
            (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅) →
        ¬ CacheHasCollision cache₁ →
          Pr[ fun z =>
            BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
                cache₁ out)).run cache₁] ≤
            bindingVerifierErrorTerm C depth) :
    Pr[ fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  refine
    bindingTextbookWitnessGame_bound_of_rest_win_bound
      (M := M) (S := S) (C := C) A hC ?_
  intro out cache₁ hsupport hnoCollision
  exact le_trans
    (probEvent_mono fun z hz hwin =>
      bindingTextbookWitnessRest_win_implies_restCreatedEvent_of_support
        (M := M) (S := S) (C := C) out cache₁ hz hnoCollision hwin)
    (hrest out cache₁ hsupport hnoCollision)

/-- Conditional combiner for the ordinary witness game.

Use this when a separate proof already establishes the exact textbook split
error for `bindingWitnessGame`. The theorem is intentionally just a named
identity wrapper, mirroring the basic commitment-scheme style where a
collision-event estimate is converted into a game bound. -/
theorem binding_bound_of_witnessGame_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hbound :
      Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
        bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
        bindingErrorTerm C depth t) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t :=
  hbound

/-- Compact textbook-expression wrapper for the ordinary witness game.

If the ordinary witness game has already been bounded by `bindingErrorTerm`,
then the named dominance condition
`bindingTextbookDominanceThreshold depth ≤ t` gives the documented
`t^2 / (2 * |C|)` expression. Expanded, the condition is
`2 * (depth + 1)^2 ≤ t`. -/
theorem binding_bound_textbook_of_witnessGame_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hbudget : bindingTextbookDominanceThreshold depth ≤ t)
    (hbound :
      Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
        bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
        bindingErrorTerm C depth t) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingTextbookErrorTerm C t :=
  le_trans
    (binding_bound_of_witnessGame_bound (M := M) (S := S) (C := C) A hbound)
    (bindingErrorTerm_le_textbook (C := C) depth t hbudget)

/-- Textbook split ROM binding bound for the origin-aware witness game.

Textbook statement: selected-index Merkle binding, with the adversary phase and
the selected verifier paths charged separately.

Lean event/game: `BindingTextbookWinROM` in `bindingTextbookWitnessGame`.

Bound expression, with `d = depth` and `|C| = 2^λ`:

`t * (t - 1) / (2 * |C|) + (d + 1)^2 / |C|`.

The corresponding compact textbook macro is
`MTBindingExpression(λ, t) = 1/2 * t^2 / 2^λ`.

Scope note: `BindingTextbookWinROM` includes origin-aware side conditions
needed to charge only rest-created verifier collisions. Use `binding_bound` for
the unconditional ordinary witness game. -/
theorem binding_bound_conditioned {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t :=
  bindingTextbookWitnessGame_bound_of_restCreatedEvent_bound
    (M := M) (S := S) (C := C) A hC
    (fun out cache₁ _hsupport hnoCollision =>
      bindingTextbookWitnessRest_restCreatedEvent_bound
        (M := M) (S := S) (C := C) out cache₁ hnoCollision)

/-- Compact textbook arithmetic corollary for the origin-aware witness game.

Textbook statement: the split binding expression is dominated by the compact
`t^2 / (2 * |C|)` form once the adversary budget dominates the verifier
cross term.

Lean event/game: same conditioned event as `binding_bound_conditioned`.

Bound expression: `bindingTextbookErrorTerm C t = t^2 / (2 * |C|)` under
`bindingTextbookDominanceThreshold depth <= t`, i.e.
`2 * (depth + 1)^2 <= t`. In textbook notation this is
`MTBindingExpression(λ, t) = 1/2 * t^2 / 2^λ`. -/
theorem binding_bound_textbook_conditioned {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hbudget : bindingTextbookDominanceThreshold depth ≤ t) :
    Pr[fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingTextbookErrorTerm C t :=
  le_trans
    (binding_bound_conditioned (M := M) (S := S) (C := C) A hC)
    (bindingErrorTerm_le_textbook (C := C) depth t hbudget)

/-- Public unconditional ROM binding bound for the ordinary witness game.

Textbook statement: selected-index Merkle binding in the ROM.

Lean event/game: `BindingWitnessWinROM` in `bindingWitnessGame`.

Bound expression: the conservative whole-cache birthday term
`(t + 2 * (depth + 1))^2 / (2 * |C|)`.

Scope note: this theorem is unconditional for the ordinary witness game. Its
term is intentionally looser than the origin-aware split theorem
`binding_bound_conditioned`, and it is not the textbook macro
`MTBindingExpression(λ, t) = 1/2 * t^2 / 2^λ`. -/
theorem binding_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t :=
  binding_bound_wholeCache (M := M) (S := S) (C := C) A hC

/-- Conditional honest-binding combiner once the honest game has been reduced
to a two-opening binding output distribution. -/
theorem honest_binding_bound_of_collision_bound [DecidableEq C]
    [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) (BindingOutput M S C depth))
    (ε : ℝ≥0∞)
    (hcollision :
      Pr[ fun out =>
        BindingCollisionEvent (M := M) (S := S) (C := C) f out | oa] ≤ ε) :
    Pr[ fun out => BindingWin (M := M) (S := S) (C := C) f out | oa] ≤ ε :=
  binding_bound_of_collision_bound (M := M) (S := S) (C := C) f oa ε hcollision

end MerkleTree
