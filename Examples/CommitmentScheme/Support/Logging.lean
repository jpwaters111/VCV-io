/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, jpwaters
-/

import Examples.CommitmentScheme.Support.Cache
import Examples.CommitmentScheme.Support.QueryBound
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.EvalDist

/-!
# Commitment Scheme generic logging support

Log predicates and logging/cached-logging structural facts used by ROM proofs.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-- A query log has a collision: two entries at distinct positions with
distinct inputs but HEq-equal outputs. -/
def LogHasCollision (log : QueryLog spec) : Prop :=
  ∃ (i j : Fin log.length), i ≠ j ∧
    log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2

/-- Two query logs have a cross-collision: one entry from each log has distinct
inputs but HEq-equal outputs.

Lean event/game: this is the generic log-level event used by Merkle binding
after reducing two accepted openings to two accepted verifier traces. -/
def LogCrossCollision (log₀ log₁ : QueryLog spec) : Prop :=
  ∃ entry₀ ∈ log₀, ∃ entry₁ ∈ log₁, entry₀.1 ≠ entry₁.1 ∧ HEq entry₀.2 entry₁.2

/-- A log entry is fresh relative to an initial cache when its query was not
already cached in that initial cache. -/
def LogEntryFresh (cache : QueryCache spec)
    (entry : (t : spec.Domain) × spec.Range t) : Prop :=
  cache entry.1 = none

/-- A cross-log collision where both colliding log entries are fresh relative to
the same initial cache.

Lean event/game: this is the rest-created collision charged to the verifier
part of the conditioned Merkle binding theorem. -/
def RestCreatedLogCrossCollision (cache : QueryCache spec)
    (log₀ log₁ : QueryLog spec) : Prop :=
  ∃ entry₀ ∈ log₀, ∃ entry₁ ∈ log₁,
    LogEntryFresh cache entry₀ ∧ LogEntryFresh cache entry₁ ∧
      entry₀.1 ≠ entry₁.1 ∧ HEq entry₀.2 entry₁.2

namespace LogCrossCollision

/-- Cross-collisions are monotone under log containment on both sides. -/
theorem mono {log₀ log₀' log₁ log₁' : QueryLog spec}
    (h₀ : ∀ entry, entry ∈ log₀ → entry ∈ log₀')
    (h₁ : ∀ entry, entry ∈ log₁ → entry ∈ log₁') :
    LogCrossCollision log₀ log₁ → LogCrossCollision log₀' log₁' := by
  rintro ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
  exact ⟨entry₀, h₀ _ hentry₀, entry₁, h₁ _ hentry₁, hne, heq⟩

/-- If every entry from both logs is present in the same cache, any cross-log
collision gives a cache collision. -/
theorem to_cacheCollision {cache : QueryCache spec} {log₀ log₁ : QueryLog spec}
    (h₀ : ∀ entry ∈ log₀, cache entry.1 = some entry.2)
    (h₁ : ∀ entry ∈ log₁, cache entry.1 = some entry.2)
    (hcross : LogCrossCollision log₀ log₁) :
    CacheHasCollision cache := by
  rcases hcross with ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
  exact ⟨entry₀.1, entry₁.1, entry₀.2, entry₁.2, hne,
    h₀ entry₀ hentry₀, h₁ entry₁ hentry₁, heq⟩

/-- A cross-collision between logs bounded by `n₀` and `n₁` is witnessed by
some pair of bounded positions. -/
theorem exists_fin_pair_of_length_le {log₀ log₁ : QueryLog spec} {n₀ n₁ : ℕ}
    (hlen₀ : log₀.length ≤ n₀) (hlen₁ : log₁.length ≤ n₁)
    (hcross : LogCrossCollision log₀ log₁) :
    ∃ (i : Fin n₀) (j : Fin n₁),
      log₀.length > i.val ∧ log₁.length > j.val ∧
        log₀[i]?.bind (fun entry₀ =>
          log₁[j]?.map (fun entry₁ => entry₀.1 ≠ entry₁.1 ∧ HEq entry₀.2 entry₁.2)) =
          some true := by
  rcases hcross with ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hentry₀
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hentry₁
  have hi' : i < n₀ := Nat.lt_of_lt_of_le hi hlen₀
  have hj' : j < n₁ := Nat.lt_of_lt_of_le hj hlen₁
  refine ⟨⟨i, hi'⟩, ⟨j, hj'⟩, hi, hj, ?_⟩
  have hget₀ : log₀[(⟨i, hi'⟩ : Fin n₀)]? = some log₀[i] := by
    simp [List.getElem?_eq_getElem, hi]
  have hget₁ : log₁[(⟨j, hj'⟩ : Fin n₁)]? = some log₁[j] := by
    simp [List.getElem?_eq_getElem, hj]
  rw [hget₀, hget₁]
  simp [hne, heq]

end LogCrossCollision

namespace RestCreatedLogCrossCollision

/-- Forgetting freshness gives an ordinary cross-log collision. -/
theorem to_logCrossCollision {cache : QueryCache spec} {log₀ log₁ : QueryLog spec}
    (hcross : RestCreatedLogCrossCollision cache log₀ log₁) :
    LogCrossCollision log₀ log₁ := by
  rcases hcross with
    ⟨entry₀, hentry₀, entry₁, hentry₁, _hfresh₀, _hfresh₁, hne, heq⟩
  exact ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩

/-- Rest-created cross-collisions are monotone under log containment. -/
theorem mono {cache : QueryCache spec} {log₀ log₀' log₁ log₁' : QueryLog spec}
    (h₀ : ∀ entry, entry ∈ log₀ → entry ∈ log₀')
    (h₁ : ∀ entry, entry ∈ log₁ → entry ∈ log₁') :
    RestCreatedLogCrossCollision cache log₀ log₁ →
      RestCreatedLogCrossCollision cache log₀' log₁' := by
  rintro ⟨entry₀, hentry₀, entry₁, hentry₁, hfresh₀, hfresh₁, hne, heq⟩
  exact ⟨entry₀, h₀ _ hentry₀, entry₁, h₁ _ hentry₁, hfresh₀, hfresh₁, hne, heq⟩

/-- A rest-created cross-collision between bounded logs is witnessed by bounded
positions. -/
theorem exists_fin_pair_of_length_le {cache : QueryCache spec}
    {log₀ log₁ : QueryLog spec} {n₀ n₁ : ℕ}
    (hlen₀ : log₀.length ≤ n₀) (hlen₁ : log₁.length ≤ n₁)
    (hcross : RestCreatedLogCrossCollision cache log₀ log₁) :
    ∃ (i : Fin n₀) (j : Fin n₁),
      log₀.length > i.val ∧ log₁.length > j.val ∧
        log₀[i]?.bind (fun entry₀ =>
          log₁[j]?.map (fun entry₁ =>
            LogEntryFresh cache entry₀ ∧ LogEntryFresh cache entry₁ ∧
              entry₀.1 ≠ entry₁.1 ∧ HEq entry₀.2 entry₁.2)) =
          some true := by
  rcases hcross with
    ⟨entry₀, hentry₀, entry₁, hentry₁, hfresh₀, hfresh₁, hne, heq⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hentry₀
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hentry₁
  have hi' : i < n₀ := Nat.lt_of_lt_of_le hi hlen₀
  have hj' : j < n₁ := Nat.lt_of_lt_of_le hj hlen₁
  refine ⟨⟨i, hi'⟩, ⟨j, hj'⟩, hi, hj, ?_⟩
  have hget₀ : log₀[(⟨i, hi'⟩ : Fin n₀)]? = some log₀[i] := by
    simp [List.getElem?_eq_getElem, hi]
  have hget₁ : log₁[(⟨j, hj'⟩ : Fin n₁)]? = some log₁[j] := by
    simp [List.getElem?_eq_getElem, hj]
  rw [hget₀, hget₁]
  simp [hfresh₀, hfresh₁, hne, heq]

end RestCreatedLogCrossCollision

namespace LogCrossCollision

/-- If a cross-collision is present in two logs whose entries are all present in
the same final cache, then it is rest-created relative to an initial cache when
the initial cache has no collision and the final cache has no fresh hit into the
initial cache. -/
theorem to_restCreated_of_no_initial_collision_no_freshHit
    {cache₀ cache₁ : QueryCache spec} {log₀ log₁ : QueryLog spec}
    (hcache : cache₀ ≤ cache₁)
    (hlog₀ : ∀ entry ∈ log₀, cache₁ entry.1 = some entry.2)
    (hlog₁ : ∀ entry ∈ log₁, cache₁ entry.1 = some entry.2)
    (hnoCollision : ¬ CacheHasCollision cache₀)
    (hnoFreshHit : ¬ FreshHitInitialCache cache₀ cache₁)
    (hcross : LogCrossCollision log₀ log₁) :
    RestCreatedLogCrossCollision cache₀ log₀ log₁ := by
  rcases hcross with ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
  have hentry₀_cache₁ : cache₁ entry₀.1 = some entry₀.2 :=
    hlog₀ entry₀ hentry₀
  have hentry₁_cache₁ : cache₁ entry₁.1 = some entry₁.2 :=
    hlog₁ entry₁ hentry₁
  have hfresh₀ : LogEntryFresh cache₀ entry₀ := by
    unfold LogEntryFresh
    cases hcache₀_entry₀ : cache₀ entry₀.1 with
    | none => rfl
    | some old₀ =>
        have hold₀_cache₁ : cache₁ entry₀.1 = some old₀ :=
          hcache hcache₀_entry₀
        have hold₀_eq : HEq old₀ entry₀.2 := by
          have hsome : (some old₀ : Option (spec.Range entry₀.1)) = some entry₀.2 := by
            rw [← hold₀_cache₁, hentry₀_cache₁]
          exact heq_of_eq (Option.some.inj hsome)
        cases hcache₀_entry₁ : cache₀ entry₁.1 with
        | none =>
            exact False.elim <| hnoFreshHit
              ⟨entry₁.1, entry₀.1, entry₁.2, old₀, hcache₀_entry₁,
                hentry₁_cache₁, hcache₀_entry₀, hne.symm,
                heq.symm.trans hold₀_eq.symm⟩
        | some old₁ =>
            have hold₁_cache₁ : cache₁ entry₁.1 = some old₁ :=
              hcache hcache₀_entry₁
            have hold₁_eq : HEq old₁ entry₁.2 := by
              have hsome : (some old₁ : Option (spec.Range entry₁.1)) = some entry₁.2 := by
                rw [← hold₁_cache₁, hentry₁_cache₁]
              exact heq_of_eq (Option.some.inj hsome)
            exact False.elim <| hnoCollision
              ⟨entry₀.1, entry₁.1, old₀, old₁, hne, hcache₀_entry₀,
                hcache₀_entry₁, hold₀_eq.trans (heq.trans hold₁_eq.symm)⟩
  have hfresh₁ : LogEntryFresh cache₀ entry₁ := by
    unfold LogEntryFresh
    cases hcache₀_entry₁ : cache₀ entry₁.1 with
    | none => rfl
    | some old₁ =>
        have hold₁_cache₁ : cache₁ entry₁.1 = some old₁ :=
          hcache hcache₀_entry₁
        have hold₁_eq : HEq old₁ entry₁.2 := by
          have hsome : (some old₁ : Option (spec.Range entry₁.1)) = some entry₁.2 := by
            rw [← hold₁_cache₁, hentry₁_cache₁]
          exact heq_of_eq (Option.some.inj hsome)
        exact False.elim <| hnoFreshHit
          ⟨entry₀.1, entry₁.1, entry₀.2, old₁, hfresh₀,
            hentry₀_cache₁, hcache₀_entry₁, hne, heq.trans hold₁_eq.symm⟩
  exact ⟨entry₀, hentry₀, entry₁, hentry₁, hfresh₀, hfresh₁, hne, heq⟩

end LogCrossCollision

/-! ## Logging Oracle Run Decomposition -/

/-- When running `loggingOracle` on `query t >>= mx`, the result decomposes as:
a uniform draw `u` from `Range t`, followed by prepending `⟨t, u⟩` to the sub-log. -/
theorem run_simulateQ_loggingOracle_query_bind {α : Type}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp spec _) >>= fun u =>
        (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def, Function.comp]

/-! ## IsTotalQueryBound preservation through loggingOracle -/

/-- `loggingOracle` preserves `IsTotalQueryBound`: the query structure of
`(simulateQ loggingOracle oa).run` is identical to that of `oa`. -/
theorem isTotalQueryBound_run_simulateQ_loggingOracle_iff {α : Type}
    (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ loggingOracle oa).run) n ↔
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
    constructor <;> intro _ <;> trivial
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    rw [isTotalQueryBound_query_bind_iff, isTotalQueryBound_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun u =>
      (isQueryBound_map_iff _ _ _ _ _).trans (ih u (n - 1))

/-- A total query bound controls the length of every `loggingOracle` trace in support:
if `oa` makes at most `n` queries, then every support point of
`(simulateQ loggingOracle oa).run` has log length at most `n`. -/
theorem log_length_le_of_mem_support_run_simulateQ {α : Type}
    {oa : OracleComp spec α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    {z : α × QueryLog spec}
    (hz : z ∈ support ((simulateQ loggingOracle oa).run)) :
    z.2.length ≤ n := by
  suffices h : ∀ (β : Type) (ob : OracleComp spec β) (m : ℕ),
      IsTotalQueryBound ob m → ∀ z ∈ support ((simulateQ loggingOracle ob).run),
      z.2.length ≤ m from
    h α oa n hbound z hz
  intro β ob m hm
  induction ob using OracleComp.inductionOn generalizing m with
  | pure x =>
      intro z hz
      simp [simulateQ_pure] at hz
      subst hz
      simp
  | query_bind t mx ih =>
      intro z hz
      rw [isTotalQueryBound_query_bind_iff] at hm
      obtain ⟨hpos, hrest⟩ := hm
      simp only [simulateQ_bind, simulateQ_query] at hz
      rw [show ((query t).cont <$> loggingOracle (query t).input >>=
        fun x => simulateQ loggingOracle (mx x) :
        WriterT (QueryLog spec) (OracleComp spec) β).run =
        ((query t).cont <$> loggingOracle (query t).input).run >>=
        fun p => Prod.map id (p.2 ++ ·) <$>
          (simulateQ loggingOracle (mx p.1)).run
        from WriterT.run_bind' _ _] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hqu_log : qu.2.length = 1 := by
        simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query] at hqu
        have hrun : (loggingOracle (spec := spec) t).run =
            (query t : OracleComp spec _) >>= fun u =>
              pure (u, [⟨t, u⟩]) := by
          simp [loggingOracle, QueryImpl.withLogging_apply,
            WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
            map_pure, Prod.map]
        rw [hrun] at hqu
        simp only [support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff] at hqu
        obtain ⟨u, _, rfl⟩ := hqu
        simp
      have hz'_len : z'.2.length ≤ m - 1 :=
        ih qu.1 (m - 1) (hrest qu.1) z' hz'
      have hm : 1 + (m - 1) = m := by omega
      simpa [List.length_append, hqu_log, hm] using Nat.add_le_add_left hz'_len 1

/-- When running `loggingOracle` inside `cachingOracle`, every log entry ends up in the cache.

The theorem also returns cache monotonicity from the initial cache to the final cache. -/
theorem log_entry_in_cache_and_mono {α : Type}
    (oa : OracleComp spec α)
    (cache₀ : QueryCache spec)
    (z : (α × QueryLog spec) × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle
        ((simulateQ loggingOracle oa).run)).run cache₀)) :
    (∀ entry ∈ z.1.2, z.2 entry.1 = some entry.2) ∧ cache₀ ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    simp only [simulateQ_pure] at hmem
    change z ∈ support (pure ((a, ([] : QueryLog spec)), cache₀)) at hmem
    rw [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨fun _ h => ?_, le_refl _⟩; simp at h
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at hmem
    rw [show simulateQ cachingOracle
          ((query t : OracleComp spec _) >>= fun u =>
            (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              <$> (simulateQ loggingOracle (mx u)).run) =
          ((cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) :
            StateT (QueryCache spec) (OracleComp spec) _)
        from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query]] at hmem
    have hbind_rw : (cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run) :
            StateT (QueryCache spec) (OracleComp spec) _) =
          (cachingOracle t >>= fun u =>
            StateT.map
              (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
      congr 1; ext u s
      simp only [StateT.map, StateT.run, StateT.bind, map_eq_bind_pure_comp,
        simulateQ_bind, simulateQ_pure, Function.comp_def, bind_assoc, pure_bind]
      rfl
    rw [hbind_rw] at hmem
    rw [StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hu_mem, hmem⟩ := hmem
    have hu_mem' : (u, cache_mid) ∈ support ((cachingOracle (spec := spec) t).run cache₀) := by
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem ⊢
      exact hu_mem
    have hcache_mid_entry : cache_mid t = some u := by
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem
      cases hc : cache₀ t with
      | some v =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hu_mem; exact hc
      | none =>
        simp only [hc, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet] at hu_mem
        rw [support_bind] at hu_mem; simp only [Set.mem_iUnion] at hu_mem
        obtain ⟨w, _, hmem_w⟩ := hu_mem
        rw [support_pure, Set.mem_singleton_iff] at hmem_w
        have h1 : u = w.1 := congr_arg Prod.fst hmem_w
        have h2 : cache_mid = w.2.cacheQuery t w.1 := congr_arg Prod.snd hmem_w
        subst h1; rw [h2]
        exact QueryCache.cacheQuery_self w.2 t w.1
    have hcache₀_le_mid : cache₀ ≤ cache_mid := by
      unfold cachingOracle at hu_mem'
      exact QueryImpl.withCaching_cache_le
        (QueryImpl.ofLift spec (OracleComp spec)) t cache₀ (u, cache_mid) hu_mem'
    change z ∈ support ((StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid) at hmem
    rw [show (StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid =
      (fun zz : (α × QueryLog spec) × QueryCache spec =>
        ((zz.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zz.1.2), zz.2)) <$>
      ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache_mid)
      from by simp only [StateT.map, StateT.run, map_eq_bind_pure_comp,
        Function.comp_def]] at hmem
    rw [support_map] at hmem
    obtain ⟨⟨⟨x', log'⟩, cache_final⟩, hmem_cont, heq⟩ := hmem
    have hz : z = ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'), cache_final) := heq.symm
    rw [hz]
    have ⟨ih_entries, ih_mono⟩ := ih u cache_mid ((x', log'), cache_final) hmem_cont
    exact ⟨fun entry hentry => by
      cases hentry with
      | head => exact ih_mono hcache_mid_entry
      | tail _ hentry' => exact ih_entries entry hentry',
      le_trans hcache₀_le_mid ih_mono⟩

/-- A total query bound controls the log length even when the logged computation
is run through `cachingOracle`. -/
theorem log_length_le_of_mem_support_run_cached_logging {α : Type}
    {oa : OracleComp spec α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (cache₀ : QueryCache spec)
    {z : (α × QueryLog spec) × QueryCache spec}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)) :
    z.1.2.length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n cache₀ z with
  | pure x =>
      simp only [simulateQ_pure] at hz
      change z ∈ support (pure ((x, ([] : QueryLog spec)), cache₀)) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at hbound
      obtain ⟨hpos, hrest⟩ := hbound
      rw [run_simulateQ_loggingOracle_query_bind] at hz
      rw [show simulateQ cachingOracle
            ((query t : OracleComp spec _) >>= fun u =>
              (fun p : α × QueryLog spec =>
                (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2)) <$>
                (simulateQ loggingOracle (mx u)).run) =
            ((cachingOracle t >>= fun u =>
              simulateQ cachingOracle
                ((fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2)) <$>
                  (simulateQ loggingOracle (mx u)).run)) :
              StateT (QueryCache spec) (OracleComp spec) _)
          from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query]] at hz
      have hbind_rw : (cachingOracle t >>= fun u =>
              simulateQ cachingOracle
                ((fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2)) <$>
                  (simulateQ loggingOracle (mx u)).run) :
              StateT (QueryCache spec) (OracleComp spec) _) =
            (cachingOracle t >>= fun u =>
              StateT.map
                (fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
        congr 1
        ext u s
        simp only [StateT.map, StateT.run, map_eq_bind_pure_comp,
          simulateQ_bind, simulateQ_pure, Function.comp_def]
        rfl
      rw [hbind_rw, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨⟨u, cache_mid⟩, _, hz⟩ := hz
      change z ∈ support ((StateT.map
        (fun p : α × QueryLog spec =>
          (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
        (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid) at hz
      rw [show (StateT.map
        (fun p : α × QueryLog spec =>
          (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
        (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid =
        (fun zz : (α × QueryLog spec) × QueryCache spec =>
          ((zz.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zz.1.2), zz.2)) <$>
        ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache_mid)
        from by simp only [StateT.map, StateT.run, map_eq_bind_pure_comp,
          Function.comp_def]] at hz
      rw [support_map] at hz
      obtain ⟨⟨⟨x', log'⟩, cache_final⟩, hz_cont, heq⟩ := hz
      have hz_eq :
          z = ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'), cache_final) :=
        heq.symm
      rw [hz_eq]
      have hlen : log'.length ≤ n - 1 :=
        ih u (hrest u) cache_mid hz_cont
      simpa using Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hlen (Nat.sub_lt hpos (by simp)))

/-- For two cached logged computations run sequentially, a cross-collision
between their two logs is always present as a collision in the final cache. -/
theorem logCrossCollision_implies_cacheCollision_cached_two {α β : Type}
    (oa₀ : OracleComp spec α) (oa₁ : OracleComp spec β)
    (cache₀ : QueryCache spec)
    {z : ((α × QueryLog spec) × (β × QueryLog spec)) × QueryCache spec}
    (hz : z ∈ support ((simulateQ cachingOracle
        ((simulateQ loggingOracle oa₀).run >>= fun out₀ =>
          (simulateQ loggingOracle oa₁).run >>= fun out₁ =>
            pure (out₀, out₁))).run cache₀))
    (hcross : LogCrossCollision z.1.1.2 z.1.2.2) :
    CacheHasCollision z.2 := by
  rw [simulateQ_bind, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨z₀, hz₀, hzrest⟩ := hz
  rw [simulateQ_bind, StateT.run_bind] at hzrest
  rw [support_bind] at hzrest
  simp only [Set.mem_iUnion] at hzrest
  obtain ⟨z₁, hz₁, hzpure⟩ := hzrest
  simp [simulateQ_pure, StateT.run] at hzpure
  subst z
  have h₀ := log_entry_in_cache_and_mono oa₀ cache₀ z₀ hz₀
  have h₁ := log_entry_in_cache_and_mono oa₁ z₀.2 z₁ hz₁
  exact LogCrossCollision.to_cacheCollision
    (fun entry hentry => h₁.2 (h₀.1 entry hentry))
    (fun entry hentry => h₁.1 entry hentry)
    hcross

/-- Converse of `log_entry_in_cache_and_mono`: every cache entry that was not in
the initial cache has a corresponding log entry. -/
theorem cache_entry_in_log_or_initial {α : Type}
    (oa : OracleComp spec α)
    (cache₀ : QueryCache spec)
    (z : (α × QueryLog spec) × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle
        ((simulateQ loggingOracle oa).run)).run cache₀)) :
    ∀ (t₀ : spec.Domain) (v : spec.Range t₀),
      z.2 t₀ = some v → cache₀ t₀ = some v ∨
        ∃ entry ∈ z.1.2, entry.1 = t₀ ∧ HEq entry.2 v := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    simp only [simulateQ_pure] at hmem
    change z ∈ support (pure ((a, ([] : QueryLog spec)), cache₀)) at hmem
    rw [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    intro t₀ v hcache
    exact Or.inl hcache
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at hmem
    rw [show simulateQ cachingOracle
          ((query t : OracleComp spec _) >>= fun u =>
            (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              <$> (simulateQ loggingOracle (mx u)).run) =
          ((cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) :
            StateT (QueryCache spec) (OracleComp spec) _)
        from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query]] at hmem
    have hbind_rw : (cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run) :
            StateT (QueryCache spec) (OracleComp spec) _) =
          (cachingOracle t >>= fun u =>
            StateT.map
              (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
      congr 1; ext u s
      simp only [StateT.map, StateT.run, StateT.bind, map_eq_bind_pure_comp,
        simulateQ_bind, simulateQ_pure, Function.comp_def, bind_assoc, pure_bind]
      rfl
    rw [hbind_rw] at hmem
    rw [StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hu_mem, hmem⟩ := hmem
    have hcache_mid_entry : cache_mid t = some u := by
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem
      cases hc : cache₀ t with
      | some v =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hu_mem; exact hc
      | none =>
        simp only [hc, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet] at hu_mem
        rw [support_bind] at hu_mem; simp only [Set.mem_iUnion] at hu_mem
        obtain ⟨w, _, hmem_w⟩ := hu_mem
        rw [support_pure, Set.mem_singleton_iff] at hmem_w
        have h1 : u = w.1 := congr_arg Prod.fst hmem_w
        have h2 : cache_mid = w.2.cacheQuery t w.1 := congr_arg Prod.snd hmem_w
        subst h1; rw [h2]
        exact QueryCache.cacheQuery_self w.2 t w.1
    have hcache_mid_eq : ∀ t₀ : spec.Domain, t₀ ≠ t → cache_mid t₀ = cache₀ t₀ := by
      intro t₀ hne
      have hu_mem' : (u, cache_mid) ∈ support ((cachingOracle (spec := spec) t).run cache₀) := by
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem ⊢
        exact hu_mem
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem'
      cases hc : cache₀ t with
      | some w =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem'
        have := (Prod.mk.inj hu_mem').2; rw [this]
      | none =>
        simp only [hc, StateT.run_bind] at hu_mem'
        change (u, cache_mid) ∈ support
          ((liftM (query t) : StateT _ (OracleComp spec) _).run cache₀ >>= fun p =>
            ((modifyGet fun cache => (p.1, QueryCache.cacheQuery cache t p.1) :
              StateT (QueryCache spec) (OracleComp spec) _).run p.2)) at hu_mem'
        rw [support_bind] at hu_mem'; simp only [Set.mem_iUnion] at hu_mem'
        obtain ⟨⟨r, s⟩, hrs, hfinal⟩ := hu_mem'
        simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hfinal
        have hru : u = r := congr_arg Prod.fst hfinal
        have hcm : cache_mid = s.cacheQuery t r := congr_arg Prod.snd hfinal
        simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
          StateT.run, StateT.lift] at hrs
        rw [support_bind] at hrs; simp only [Set.mem_iUnion] at hrs
        obtain ⟨q, _, hq⟩ := hrs
        rw [support_pure, Set.mem_singleton_iff] at hq
        have hs : s = cache₀ := congr_arg Prod.snd hq
        rw [hcm, hs, QueryCache.cacheQuery_of_ne _ _ hne]
    change z ∈ support ((StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid) at hmem
    rw [show (StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid =
      (fun zz : (α × QueryLog spec) × QueryCache spec =>
        ((zz.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zz.1.2), zz.2)) <$>
      ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache_mid)
      from by simp only [StateT.map, StateT.run, map_eq_bind_pure_comp,
        Function.comp_def]] at hmem
    rw [support_map] at hmem
    obtain ⟨⟨⟨x', log'⟩, cache_final⟩, hmem_cont, heq⟩ := hmem
    have hz : z = ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'), cache_final) := heq.symm
    rw [hz]
    intro t₀ v hcache_final
    have ih_result := ih u cache_mid ((x', log'), cache_final) hmem_cont t₀ v hcache_final
    rcases ih_result with h_in_mid | ⟨entry, hentry, hentry_eq, hentry_heq⟩
    · by_cases ht₀ : t₀ = t
      · subst ht₀
        rw [hcache_mid_entry] at h_in_mid; cases h_in_mid
        exact Or.inr ⟨⟨t₀, _⟩, List.Mem.head _, rfl, HEq.rfl⟩
      · rw [hcache_mid_eq t₀ ht₀] at h_in_mid
        exact Or.inl h_in_mid
    · exact Or.inr ⟨entry, List.Mem.tail _ hentry, hentry_eq, hentry_heq⟩

end OracleComp
