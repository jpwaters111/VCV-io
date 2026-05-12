/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Extractability.Reconstruction
import Examples.MerkleCommitmentScheme.Extractability.QueryBound
import Examples.MerkleCommitmentScheme.Support.ROM
import Examples.CommitmentScheme.Support.Probability

/-!
# Merkle Commitment Scheme — Extractability Probability Bounds

This file proves the selected-witness ROM extractability bound by reusing the
generic basic commitment support for cache/log collisions and fresh-cache-hit
probabilities. The Merkle layer supplies only the tree-specific target set and
query counts.

Quantitative map:
* commit trace collision: `A.t₁^2 / (2 * |C|)`;
* rest-phase fresh hit into an extractor-known tree label:
  `(A.t₂ + depth + 1) *
    min (2 * A.t₁ + 1, 2^(depth + 1)) / |C|`.

Here `|C|` is `Fintype.card C`, corresponding to `2^λ` in the textbook. The
selected witness accounts for one verifier path, so its verifier cost is
`depth + 1`; full-batch bounds are handled by separate conditional combiners.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- A collision visible in the commit-phase log is already present in the
post-commit cache.

This is the bridge from `CommitCollisionEvent` to the generic birthday bound,
which contributes the `A.t₁^2 / (2 * |C|)` summand. -/
private theorem commitLogCollision_implies_cacheCollision {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (z : ((C × AUX) × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C))
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hcoll : LogHasCollision z.1.2) :
    CacheHasCollision z.2 := by
  rcases hcoll with ⟨i, j, hij, hdomain, hanswer⟩
  have hcache :=
    (OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) A.commit ∅ z (by
        simpa [extractabilityWitnessCommitPart] using hz)).1
  have hiMem : z.1.2[i] ∈ z.1.2 := by
    simpa using (List.getElem_mem i.2)
  have hjMem : z.1.2[j] ∈ z.1.2 := by
    simpa using (List.getElem_mem j.2)
  exact ⟨z.1.2[i].1, z.1.2[j].1, z.1.2[i].2, z.1.2[j].2,
    hdomain, hcache z.1.2[i] hiMem,
    hcache z.1.2[j] hjMem, hanswer⟩

/-- A rest-phase computation creates a fresh cache entry whose random-oracle
answer is one of the labels already known from the commit trace.

This is the single target event used for both extractor-state changes and
selected-check trace escapes. If the rest phase has query bound `q` and the
known-label set has size `N`, the generic fresh-hit estimate charges it by
`q * N / |C|`. -/
private def FreshTraceKnownLabelHit {depth : ℕ} [DecidableEq C]
    (commitment : C) (commitTrace : QueryLog (Oracle M S C))
    (cache₁ : QueryCache (Oracle M S C))
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  ∃ target ∈ traceKnownLabels (M := M) (S := S) (C := C)
      (depth := depth) commitment commitTrace,
    ∃ t₀ : (Oracle M S C).Domain, ∃ v : (Oracle M S C).Range t₀,
      z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v target

/-- Definitional bridge between the extractor-state notation used by this file
and the state construction exported from the deterministic reconstruction
layer. -/
private theorem extractedStateOfTrace_eq_extractedStateFromTrace {depth : ℕ}
    [DecidableEq C] (commitment : C) (trace : QueryLog (Oracle M S C)) :
    extractedStateOfTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment trace =
      extractedStateFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment trace := rfl

/-- Equality for dependent query-log entries from equal domains and HEq answers.

This is used when a cache entry is traced back to a commit-log entry: once the
domain and random-oracle answer match, the dependent sigma entries are equal. -/
private theorem queryLogEntry_eq_of_fst_eq_heq
    {entry₀ entry₁ :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t}
    (hfst : entry₀.1 = entry₁.1) (hval : HEq entry₀.2 entry₁.2) :
    entry₀ = entry₁ := by
  cases entry₀ with
  | mk domain₀ answer₀ =>
      cases entry₁ with
      | mk domain₁ answer₁ =>
          dsimp at hfst
          subst hfst
          have hanswer : answer₀ = answer₁ := eq_of_heq hval
          subst hanswer
          rfl

/-- If a final cache entry has a known-label answer but is not in the commit
trace, then it is a fresh hit relative to the post-commit cache.

The lemma rules out the alternative that the entry was already created during
commit by using the cached-log origin theorem from generic support. -/
private theorem freshTraceKnownLabelHit_of_final_cache_entry_not_mem {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hx : (((commitment, aux), commitTrace), cache₁) ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hmono : cache₁ ≤ z.2)
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t)
    (hfinal : z.2 entry.1 = some entry.2)
    (hnotCommit : entry ∉ commitTrace)
    (htarget :
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace) :
    FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
      commitment commitTrace cache₁ z := by
  have hcache₁_none : cache₁ entry.1 = none := by
    cases hcache : cache₁ entry.1 with
    | none => rfl
    | some oldValue =>
        have hfinalOld : z.2 entry.1 = some oldValue := hmono hcache
        have holdEntry : HEq oldValue entry.2 := by
          rw [hfinal] at hfinalOld
          cases hfinalOld
          exact HEq.rfl
        let commitZ :
            ((C × AUX) × QueryLog (Oracle M S C)) ×
              QueryCache (Oracle M S C) :=
          (Prod.mk (Prod.mk (Prod.mk commitment aux) commitTrace) cache₁)
        have hfromCommit :=
          OracleComp.cache_entry_in_log_or_initial
            (spec := Oracle M S C)
            A.commit
            ∅ commitZ (by simpa [commitZ] using hx)
            entry.1 oldValue hcache
        cases hfromCommit with
        | inl hinit =>
            simp at hinit
        | inr hlog =>
            rcases hlog with ⟨entry', hmem, hfst, hheq⟩
            have hentry' : entry' = entry :=
              queryLogEntry_eq_of_fst_eq_heq
                (M := M) (S := S) (C := C)
                hfst (hheq.trans holdEntry)
            exact False.elim (hnotCommit (by simpa [hentry'] using hmem))
  exact
    ⟨traceEntryAnswer (M := M) (S := S) (C := C) entry, htarget,
      entry.1, entry.2, hfinal, hcache₁_none,
      traceEntryAnswer_heq_of_entry (M := M) (S := S) (C := C) entry⟩

/-- Entries logged by the adversary open phase are present in the final rest
cache.

This is a pure replay/cache-monotonicity fact: it has no probability content,
but it lets extractor-state changes be charged to actual fresh cache entries. -/
private theorem openTrace_entry_in_final_cache_of_rest_support {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (commitment : C) (aux : AUX) (commitTrace : QueryLog (Oracle M S C))
    (cache₁ : QueryCache (Oracle M S C))
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁))
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t)
    (hmem : entry ∈ z.1.base.openTrace) :
    z.2 entry.1 = some entry.2 := by
  unfold extractabilityWitnessRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨⟨⟨opening, openTrace⟩, cache₂⟩, hopen, hz⟩
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  have hopenCache :
      ∀ entry ∈ openTrace, cache₂ entry.1 = some entry.2 :=
    (OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) (A.open_ aux) cache₁
      ((opening, openTrace), cache₂) hopen).1
  cases hw : selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      simp [base, hw] at hz
      subst z
      exact hopenCache entry hmem
  | some i =>
      rw [hw] at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single, cache₃⟩, hsingle, hzpure⟩
      simp [base] at hzpure
      subst z
      have hmono :
          cache₂ ≤ cache₃ :=
        OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C)
          ((simulateQ loggingOracle
            (checkSingle (M := M) (S := S) (C := C)
              commitment i.1 (opening.message i) (opening.proof i))).run)
          cache₂ (single, cache₃) hsingle
      exact hmono (hopenCache entry hmem)

/-- If adding the open trace changes the extracted partial tree, then the rest
phase produced a fresh answer equal to a label already known from the commit
trace.

This is the extractor-state-change contribution to the fresh-hit summand
`(A.t₂ + depth + 1) * knownLabels / |C|`. -/
private theorem extractorStateChangedEvent_implies_freshTraceKnownLabelHit_of_rest_support
    {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hx : (((commitment, aux), commitTrace), cache₁) ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁))
    (hchange :
      ExtractorStateChangedEvent (M := M) (S := S) (C := C) z.1.base) :
    FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
      commitment commitTrace cache₁ z := by
  have hzOrig := hz
  have hmono :
      cache₁ ≤ z.2 :=
    OracleComp.simulateQ_cachingOracle_cache_le
      (spec := Oracle M S C)
      (extractabilityWitnessRest (M := M) (S := S) (C := C)
        A commitment aux commitTrace)
      cache₁ z hzOrig
  unfold extractabilityWitnessRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨⟨⟨opening, openTrace⟩, cache₂⟩, hopen, hz⟩
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  have hzBase : z.1.base = base := by
    cases hw : selectWitness? (M := M) (S := S) (C := C) base with
    | none =>
        simp [base, hw] at hz
        subst z
        rfl
    | some i =>
        rw [hw] at hz
        rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
        simp only [Set.mem_iUnion] at hz
        rcases hz with ⟨⟨single, cache₃⟩, hsingle, hzpure⟩
        simp [base] at hzpure
        subst z
        rfl
  have hchangeBase :
      ExtractorStateChangedEvent (M := M) (S := S) (C := C) base := by
    simpa [hzBase] using hchange
  have hchangeCommon :
      extractedStateFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment (commitTrace ++ openTrace) ≠
        extractedStateFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace := by
    intro heq
    exact hchangeBase (by
      simpa [ExtractorStateChangedEvent, extractedStateOfTrace_eq_extractedStateFromTrace,
        base] using heq.symm)
  rcases
    exists_open_answer_mem_traceKnownLabels_and_not_mem_commitTrace_of_extractedStateFromTrace_append_ne
      (M := M) (S := S) (C := C) (depth := depth)
      commitment commitTrace openTrace hchangeCommon with
  ⟨entry, hmemOpen, hnotCommit, htarget⟩
  have hfinal :
      z.2 entry.1 = some entry.2 :=
    openTrace_entry_in_final_cache_of_rest_support
      (M := M) (S := S) (C := C)
      A commitment aux commitTrace cache₁ hzOrig entry
      (by simpa [hzBase, base] using hmemOpen)
  exact
    freshTraceKnownLabelHit_of_final_cache_entry_not_mem
      (M := M) (S := S) (C := C)
      A hx hmono entry hfinal hnotCommit htarget

/-- Entries in the selected `checkSingle` log are present in the final rest
cache.

The selected witness branch logs exactly one verifier path, so this helper
connects trace escape to a concrete cache entry created or replayed during the
rest phase. -/
private theorem singleTrace_entry_in_final_cache_of_rest_support {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (commitment : C) (aux : AUX) (commitTrace : QueryLog (Oracle M S C))
    (cache₁ : QueryCache (Oracle M S C))
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁))
    (i : {j // j ∈ z.1.base.opening.I})
    (hw : z.1.witness? = some i)
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t)
    (hmem :
      entry ∈
        (logEval (M := M) (S := S) (C := C)
          (oracleFnOfCache (M := M) (S := S) (C := C) z.2)
          (checkSingle (M := M) (S := S) (C := C)
            z.1.base.commitment i.1
            (z.1.base.opening.message i) (z.1.base.opening.proof i))).2) :
    z.2 entry.1 = some entry.2 := by
  unfold extractabilityWitnessRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨⟨⟨opening, openTrace⟩, cache₂⟩, hopen, hz⟩
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  cases hselect : selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      simp [base, hselect] at hz
      subst z
      simp at hw
  | some j =>
      rw [hselect] at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single, cache₃⟩, hsingle, hzpure⟩
      simp [base] at hzpure
      subst z
      have hij : j = i := by
        exact Option.some.inj (by simpa using hw)
      cases hij
      have hmonoSelf : cache₃ ≤ cache₃ := by
        intro q answer hq
        exact hq
      have hlog :
          logEval (M := M) (S := S) (C := C)
            (oracleFnOfCache (M := M) (S := S) (C := C) cache₃)
            (checkSingle (M := M) (S := S) (C := C)
              commitment j.1 (opening.message j) (opening.proof j)) =
            single := by
        exact
          logEval_oracleFnOfCache_eq_of_cached_logging
            (M := M) (S := S) (C := C)
            (checkSingle (M := M) (S := S) (C := C)
              commitment j.1 (opening.message j) (opening.proof j))
            hsingle hmonoSelf
      have hmemSingle : entry ∈ single.2 := by
        rw [hlog] at hmem
        exact hmem
      exact
        (OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C)
          (checkSingle (M := M) (S := S) (C := C)
            commitment j.1 (opening.message j) (opening.proof j))
          cache₂ (single, cache₃) hsingle).1 entry hmemSingle

/-- If the leaf query and every internal path query of a selected
`checkSingle` run are already in the commit trace, then the whole selected
verifier log is contained in that commit trace.

This is a fixed-oracle trace-shape helper; it carries no probability term. -/
private theorem logContains_checkSingle_of_leaf_and_internal_mem {depth : ℕ}
    [DecidableEq C]
    (f : OracleFn M S C) (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth)
    (commitTrace : QueryLog (Oracle M S C))
    (hleaf :
      ⟨checkLeafQuery (M := M) (S := S) (C := C) message authPath,
        f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩ ∈
        commitTrace)
    (hinternal :
      ∀ layer : Fin depth,
        ⟨checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer,
          f (checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer)⟩ ∈ commitTrace) :
    LogContains
      (logEval f
        (checkSingle (M := M) (S := S) (C := C)
          commitment idx message authPath)).2
      commitTrace := by
  intro entry hentry
  rcases
      (mem_logEval_checkSingle_iff_leaf_or_internal
        (M := M) (S := S) (C := C)
        f commitment idx message authPath entry).mp hentry with hleafEntry | hinternalEntry
  · simpa [hleafEntry] using hleaf
  · rcases hinternalEntry with ⟨layer, hentryEq⟩
    simpa [hentryEq] using hinternal layer

/-- If a selected verifier path is missing an internal query from the commit
trace, then the missing query's answer is already an extractor-known label.

The proof uses the deterministic reconstruction layer: all earlier internal
queries on the path are present, so closure of the partial tree knows the
parent label. This converts a trace escape into the same fresh-hit target set
used in the probability bound. -/
private theorem exists_known_answer_not_mem_commitTrace_of_missing_internal
    {depth : ℕ} [DecidableEq M] [DecidableEq S] [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true)
    (hmissingInternal :
      ∃ layer : Fin depth,
        (⟨checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer,
          f (checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer)⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) ∉
          x.commitTrace) :
    ∃ entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t,
      entry ∈
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2 ∧
      entry ∉ x.commitTrace ∧
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) x.commitment x.commitTrace := by
  classical
  let internalEntry (layer : Fin depth) :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t :=
    ⟨checkInternalQuery (M := M) (S := S) (C := C)
        f idx message authPath layer,
      f (checkInternalQuery (M := M) (S := S) (C := C)
        f idx message authPath layer)⟩
  let missingSet : Finset (Fin depth) :=
    Finset.univ.filter fun layer => internalEntry layer ∉ x.commitTrace
  have hsetNonempty : missingSet.Nonempty := by
    rcases hmissingInternal with ⟨layer, hmissing⟩
    exact ⟨layer, by simp [missingSet, internalEntry, hmissing]⟩
  let layer : Fin depth := missingSet.min' hsetNonempty
  let n : ℕ := layer.1
  have hlayerMem : layer ∈ missingSet := Finset.min'_mem _ _
  have hmissing : internalEntry layer ∉ x.commitTrace := by
    simpa [missingSet, layer] using (Finset.mem_filter.mp hlayerMem).2
  have hprefix :
      ∀ internalLayer : Fin depth, internalLayer.1 < n →
        internalEntry internalLayer ∈ x.commitTrace := by
    intro internalLayer hlt
    by_contra hnot
    have hmemSet : internalLayer ∈ missingSet := by
      simp [missingSet, hnot]
    have hminLe := Finset.min'_le missingSet internalLayer hmemSet
    have hminLeNat : layer.1 ≤ internalLayer.1 := by
      exact hminLe
    dsimp [n] at hlt
    omega
  let parentLayer : Fin (depth + 1) :=
    ⟨n, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩
  have hknownGet :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) x.commitment x.commitTrace n parentLayer).get
          (pathPos idx parentLayer) =
        some (checkPathLabel f idx message authPath parentLayer) := by
    exact
      path_label_known_after_passes_of_internal_prefix
        (M := M) (S := S) (C := C) (AUX := AUX)
        f x idx message authPath hcoll hcheck n parentLayer.2
        (fun internalLayer hlt => hprefix internalLayer hlt)
  have htarget :
      checkPathLabel f idx message authPath parentLayer ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) x.commitment x.commitTrace := by
    exact knownLabels_after_passes_subset_traceKnownLabels
      (M := M) (S := S) (C := C)
      (depth := depth) x.commitment x.commitTrace n (by omega)
        ((mem_knownLabels_iff (C := C)
          (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
            (depth := depth) x.commitment x.commitTrace n)
          (checkPathLabel f idx message authPath parentLayer)).mpr
          ⟨parentLayer, pathPos idx parentLayer, hknownGet⟩)
  refine ⟨internalEntry layer, ?_, hmissing, ?_⟩
  · exact checkInternalQuery_mem_logEval_checkSingle
      (M := M) (S := S) (C := C)
      f x.commitment idx message authPath layer
  · have hanswer :=
      checkInternalQueryAnswer_eq_checkPathLabel_parent
        (M := M) (S := S) (C := C) f idx message authPath layer
    have htraceAnswer₀ :
        traceEntryAnswer (M := M) (S := S) (C := C) (internalEntry layer) =
          checkInternalQueryAnswer (M := M) (S := S) (C := C)
            f idx message authPath layer := by
      simpa [internalEntry] using
        traceEntryAnswer_checkInternalQuery
          (M := M) (S := S) (C := C) f idx message authPath layer
    have htraceAnswer :
        traceEntryAnswer (M := M) (S := S) (C := C) (internalEntry layer) =
          checkPathLabel f idx message authPath parentLayer := by
      rw [htraceAnswer₀, hanswer]
    rw [htraceAnswer]
    exact htarget

/-- If all selected internal queries are present but the selected verifier log
still escapes the commit trace, then the missing entry is the leaf query and
its answer is the known leaf label.

This is the leaf analogue of the missing-internal helper and handles the
`depth = 0` case directly. -/
private theorem exists_known_answer_not_mem_commitTrace_of_missing_leaf
    {depth : ℕ} [DecidableEq M] [DecidableEq S] [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true)
    (hallInternal :
      ∀ layer : Fin depth,
        (⟨checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer,
          f (checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer)⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) ∈
          x.commitTrace)
    (hescape :
      ¬ LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace) :
    ∃ entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t,
      entry ∈
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2 ∧
      entry ∉ x.commitTrace ∧
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) x.commitment x.commitTrace := by
  classical
  let leafEntry :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t :=
    ⟨checkLeafQuery (M := M) (S := S) (C := C) message authPath,
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩
  let internalEntry (layer : Fin depth) :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t :=
    ⟨checkInternalQuery (M := M) (S := S) (C := C)
        f idx message authPath layer,
      f (checkInternalQuery (M := M) (S := S) (C := C)
        f idx message authPath layer)⟩
  have hleafMissing : leafEntry ∉ x.commitTrace := by
    intro hleaf
    exact hescape
      (logContains_checkSingle_of_leaf_and_internal_mem
        (M := M) (S := S) (C := C)
        f x.commitment idx message authPath x.commitTrace
        (by simpa [leafEntry] using hleaf)
        (fun layer => by simpa [internalEntry] using hallInternal layer))
  have hknownGet :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) x.commitment x.commitTrace depth
        ⟨depth, Nat.lt_succ_self depth⟩).get
          (pathPos idx ⟨depth, Nat.lt_succ_self depth⟩) =
        some (checkPathLabel f idx message authPath
          ⟨depth, Nat.lt_succ_self depth⟩) := by
    exact
      path_label_known_after_passes_of_internal_prefix
        (M := M) (S := S) (C := C) (AUX := AUX)
        f x idx message authPath hcoll hcheck depth (Nat.lt_succ_self depth)
        (fun internalLayer _ => by
          simpa [internalEntry] using hallInternal internalLayer)
  have htarget :
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath) ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) x.commitment x.commitTrace := by
    have htargetPath :
        checkPathLabel f idx message authPath ⟨depth, Nat.lt_succ_self depth⟩ ∈
          traceKnownLabels (M := M) (S := S) (C := C)
            (depth := depth) x.commitment x.commitTrace :=
      knownLabels_after_passes_subset_traceKnownLabels
        (M := M) (S := S) (C := C)
        (depth := depth) x.commitment x.commitTrace depth (by omega)
        ((mem_knownLabels_iff (C := C)
          (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
            (depth := depth) x.commitment x.commitTrace depth)
          (checkPathLabel f idx message authPath
            ⟨depth, Nat.lt_succ_self depth⟩)).mpr
          ⟨⟨depth, Nat.lt_succ_self depth⟩,
            pathPos idx ⟨depth, Nat.lt_succ_self depth⟩, hknownGet⟩)
    have hleafEq :=
      checkPathLabel_leaf_eq_leafQuery
        (M := M) (S := S) (C := C) f idx message authPath
    have htargetLast :
        checkPathLabel f idx message authPath (Fin.last depth) ∈
          traceKnownLabels (M := M) (S := S) (C := C)
            (depth := depth) x.commitment x.commitTrace := by
      simpa [Fin.last] using htargetPath
    rw [hleafEq] at htargetLast
    exact htargetLast
  refine ⟨leafEntry, ?_, hleafMissing, ?_⟩
  · exact checkLeafQuery_mem_logEval_checkSingle
      (M := M) (S := S) (C := C)
      f x.commitment idx message authPath
  · simpa [leafEntry, traceEntryAnswer] using htarget

/-- Any selected-check trace escape exposes a missing entry whose answer is in
the extractor-known label set.

The proof splits on whether the first missing entry is an internal query or the
leaf query. This is the deterministic core behind the witness-trace-escape
fresh-hit bound. -/
private theorem exists_known_answer_not_mem_commitTrace_of_checkSingle_escape
    {depth : ℕ} [DecidableEq M] [DecidableEq S] [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true)
    (hescape :
      ¬ LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace) :
    ∃ entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t,
      entry ∈
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2 ∧
      entry ∉ x.commitTrace ∧
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) x.commitment x.commitTrace := by
  classical
  by_cases hmissingInternal :
      ∃ layer : Fin depth,
        (⟨checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer,
          f (checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer)⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) ∉
          x.commitTrace
  · exact
      exists_known_answer_not_mem_commitTrace_of_missing_internal
        (M := M) (S := S) (C := C) (AUX := AUX)
        f x idx message authPath hcoll hcheck hmissingInternal
  · have hallInternal :
        ∀ layer : Fin depth,
          (⟨checkInternalQuery (M := M) (S := S) (C := C)
              f idx message authPath layer,
            f (checkInternalQuery (M := M) (S := S) (C := C)
              f idx message authPath layer)⟩ :
            (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) ∈
            x.commitTrace := by
      intro layer
      by_contra hnot
      exact hmissingInternal ⟨layer, hnot⟩
    exact
      exists_known_answer_not_mem_commitTrace_of_missing_leaf
        (M := M) (S := S) (C := C) (AUX := AUX)
        f x idx message authPath hcoll hcheck hallInternal hescape

/-- Every rest-phase transcript keeps the commitment, auxiliary value, and
commit trace fixed from the commit phase. This small shape lemma keeps the
later bad-event proofs from repeating the `selectWitness?` case split. -/
private theorem rest_support_base_fields {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁)) :
    z.1.base.commitment = commitment ∧
      z.1.base.aux = aux ∧
      z.1.base.commitTrace = commitTrace := by
  unfold extractabilityWitnessRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨⟨⟨opening, openTrace⟩, cache₂⟩, hopen, hz⟩
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  cases hselect : selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      simp [base, hselect] at hz
      subst z
      simp [base]
  | some i =>
      rw [hselect] at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single, cache₃⟩, hsingle, hzpure⟩
      simp [base] at hzpure
      subst z
      simp [base]

/-- A selected verifier trace can escape the commit trace only by producing a
fresh post-commit random-oracle answer that equals a label already known to the
extractor from the commit trace. This is the selected-witness source of the
`(t₂ + depth + 1) * knownLabels / |C|` summand. -/
private theorem witnessTraceEscapeEvent_implies_freshTraceKnownLabelHit_of_rest_support
    {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hx : (((commitment, aux), commitTrace), cache₁) ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁))
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) z.1.base)
    (hescape :
      WitnessTraceEscapeEvent (M := M) (S := S) (C := C)
        (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1) :
    FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
      commitment commitTrace cache₁ z := by
  rcases hescape with ⟨i, hw, hcheck, hnotContains⟩
  have hfields :=
    rest_support_base_fields (M := M) (S := S) (C := C)
      A hz
  let f := oracleFnOfCache (M := M) (S := S) (C := C) z.2
  rcases
    exists_known_answer_not_mem_commitTrace_of_checkSingle_escape
      (M := M) (S := S) (C := C) (AUX := AUX)
      f z.1.base i.1 (z.1.base.opening.message i)
      (z.1.base.opening.proof i) hcoll hcheck hnotContains with
  ⟨entry, hmemLog, hnotCommitBase, htargetBase⟩
  have hfinal :
      z.2 entry.1 = some entry.2 :=
    singleTrace_entry_in_final_cache_of_rest_support
      (M := M) (S := S) (C := C)
      A commitment aux commitTrace cache₁ hz i hw entry hmemLog
  have hnotCommit : entry ∉ commitTrace := by
    simpa [hfields.2.2] using hnotCommitBase
  have htarget :
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace := by
    simpa [hfields.1, hfields.2.2] using htargetBase
  have hmono :
      cache₁ ≤ z.2 :=
    OracleComp.simulateQ_cachingOracle_cache_le
      (spec := Oracle M S C)
      (extractabilityWitnessRest (M := M) (S := S) (C := C)
        A commitment aux commitTrace)
      cache₁ z hz
  exact
    freshTraceKnownLabelHit_of_final_cache_entry_not_mem
      (M := M) (S := S) (C := C)
      A hx hmono entry hfinal hnotCommit htarget

/-- Once the post-commit cache is collision-free, every selected-witness bad
event is a fresh hit into the known-label target set.

The commit-collision branch is impossible under `hno`; the remaining branches
are extractor-state change and selected verifier trace escape. -/
private theorem witnessBadEventROM_implies_freshTraceKnownLabelHit_of_rest_support
    {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    {z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)}
    (hx : (((commitment, aux), commitTrace), cache₁) ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁))
    (hno : ¬ CacheHasCollision cache₁)
    (hbad : WitnessBadEventROM (M := M) (S := S) (C := C) z) :
    FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
      commitment commitTrace cache₁ z := by
  have hfields :=
    rest_support_base_fields (M := M) (S := S) (C := C)
      A hz
  unfold WitnessBadEventROM WitnessBadEvent at hbad
  rcases hbad with hcommit | hstate | hescape
  · have hcollCommit : LogHasCollision commitTrace := by
      simpa [CommitCollisionEvent, hfields.2.2] using hcommit
    exact False.elim
      (hno (commitLogCollision_implies_cacheCollision
        (M := M) (S := S) (C := C) A
        (((commitment, aux), commitTrace), cache₁) hx hcollCommit))
  · exact
      extractorStateChangedEvent_implies_freshTraceKnownLabelHit_of_rest_support
        (M := M) (S := S) (C := C)
        A hx hz hstate
  · have hnotCollBase :
        ¬ CommitCollisionEvent (M := M) (S := S) (C := C) z.1.base := by
      intro hcollBase
      have hcollCommit : LogHasCollision commitTrace := by
        simpa [CommitCollisionEvent, hfields.2.2] using hcollBase
      exact hno (commitLogCollision_implies_cacheCollision
        (M := M) (S := S) (C := C) A
        (((commitment, aux), commitTrace), cache₁) hx hcollCommit)
    exact
      witnessTraceEscapeEvent_implies_freshTraceKnownLabelHit_of_rest_support
        (M := M) (S := S) (C := C)
        A hx hz hnotCollBase hescape

/-- Bound the number of extractor-known labels after an `A.t₁`-bounded commit
phase by `extractabilityCountingTerm depth A.t₁`.

Quantitatively this is
`min (2 * A.t₁ + 1, 2^(depth + 1))`: each internal query can justify at most two
new children plus the root, and the full perfect tree has `2^(depth + 1)` label
slots. -/
private theorem traceKnownLabels_card_le_extractabilityCountingTerm_of_commit_support
    {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    (hx : (((commitment, aux), commitTrace), cache₁) ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅)) :
    (traceKnownLabels (M := M) (S := S) (C := C)
      (depth := depth) commitment commitTrace).card ≤
      extractabilityCountingTerm depth A.t₁ := by
  have hlen : commitTrace.length ≤ A.t₁ :=
    OracleComp.log_length_le_of_mem_support_run_cached_logging
      (spec := Oracle M S C)
      (oa := A.commit) A.commitBound ∅
      (by simpa [extractabilityWitnessCommitPart] using hx)
  unfold extractabilityCountingTerm
  exact le_trans
    (traceKnownLabels_card_le_min (M := M) (S := S) (C := C)
      (depth := depth) commitment commitTrace)
    (by
      apply min_le_min
      · omega
      · rfl)

/-- Bound all rest-phase witness bad events after a fixed collision-free commit
support point.

The rest phase consists of the adversary open phase plus at most one selected
`checkSingle` path, so its query bound is `A.t₂ + depth + 1`. Multiplying by the
known-label target count gives `extractabilityFreshHitTerm`. -/
private theorem witnessBadEventROM_rest_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {commitment : C} {aux : AUX}
    {commitTrace : QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    (hx : (((commitment, aux), commitTrace), cache₁) ∈ support
      ((simulateQ cachingOracle
        (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hno : ¬ CacheHasCollision cache₁) :
    Pr[fun z => WitnessBadEventROM (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A commitment aux commitTrace)).run cache₁] ≤
      extractabilityFreshHitTerm C depth A.t₁ A.t₂ := by
  classical
  let targets :=
    traceKnownLabels (M := M) (S := S) (C := C)
      (depth := depth) commitment commitTrace
  let rest :=
    extractabilityWitnessRest (M := M) (S := S) (C := C)
      A commitment aux commitTrace
  have hbad_le :
      Pr[fun z => WitnessBadEventROM (M := M) (S := S) (C := C) z |
        (simulateQ cachingOracle rest).run cache₁] ≤
        Pr[fun z =>
          FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
            commitment commitTrace cache₁ z |
          (simulateQ cachingOracle rest).run cache₁] := by
    apply probEvent_mono
    intro z hz hbad
    exact
      witnessBadEventROM_implies_freshTraceKnownLabelHit_of_rest_support
        (M := M) (S := S) (C := C)
        A hx (by simpa [rest] using hz) hno hbad
  have hfresh :
      Pr[fun z =>
        FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
          commitment commitTrace cache₁ z |
        (simulateQ cachingOracle rest).run cache₁] ≤
        (((extractabilityPostCommitQueryCount depth A.t₂ * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
    simpa [FreshTraceKnownLabelHit, targets, rest] using
      probEvent_merkle_cache_has_value_mem_finset_le
        (M := M) (S := S) (C := C)
        (oa := rest) (n := extractabilityPostCommitQueryCount depth A.t₂)
        (extractabilityWitnessRest_totalBound
          (M := M) (S := S) (C := C)
          A commitment aux commitTrace)
        targets cache₁ hno
  have htargets :
      targets.card ≤ extractabilityCountingTerm depth A.t₁ := by
    simpa [targets] using
      traceKnownLabels_card_le_extractabilityCountingTerm_of_commit_support
        (M := M) (S := S) (C := C) A hx
  calc
    Pr[fun z => WitnessBadEventROM (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle rest).run cache₁]
        ≤ Pr[fun z =>
            FreshTraceKnownLabelHit (M := M) (S := S) (C := C)
              commitment commitTrace cache₁ z |
            (simulateQ cachingOracle rest).run cache₁] := hbad_le
    _ ≤ (((extractabilityPostCommitQueryCount depth A.t₂ * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := hfresh
    _ ≤ extractabilityFreshHitTerm C depth A.t₁ A.t₂ := by
        have hnat :
            extractabilityPostCommitQueryCount depth A.t₂ * targets.card ≤
              extractabilityPostCommitQueryCount depth A.t₂ *
                extractabilityCountingTerm depth A.t₁ := by
          exact Nat.mul_le_mul_left _ htargets
        unfold extractabilityFreshHitTerm
        gcongr

/-- Commit-phase component of the selected-witness bad-event game.

This abbreviation lets the final probability proof read as a standard
commit/rest bind split. -/
private noncomputable def witnessBadEventCommitPart {depth t : ℕ}
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) ((C × AUX) × QueryLog (Oracle M S C)) :=
  extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A

/-- Rest-phase component after a concrete commit output and post-commit cache.

It runs the open phase and, if a mismatch witness is selected, one logged
`checkSingle` verifier path. -/
private noncomputable def witnessBadEventRestPart
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth t : ℕ}
    (A : ExtractAdversary M S C AUX depth t)
    (x : ((C × AUX) × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)) :
    OracleComp (Oracle M S C)
      (WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle
    (extractabilityWitnessRest (M := M) (S := S) (C := C)
      A x.1.1.1 x.1.1.2 x.1.2)).run x.2

/-- Birthday bound for commit-phase cache collisions:
`A.t₁^2 / (2 * |C|)`.

This is the generic cache-collision bound specialized to the Merkle oracle
range, whose answer cardinality is `|C|`. -/
private theorem witnessCommitCollision_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
      (simulateQ cachingOracle
        (witnessBadEventCommitPart (M := M) (S := S) (C := C) A)).run ∅] ≤
      extractabilityBirthdayTerm C A.t₁ := by
  classical
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [merkleOracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hbirthday :=
    probEvent_cacheCollision_le_birthday_total
      (spec := Oracle M S C)
      (oa := witnessBadEventCommitPart (M := M) (S := S) (C := C) A)
      A.t₁
      (by
        simpa [witnessBadEventCommitPart] using
          extractabilityWitnessCommitPart_totalBound
            (M := M) (S := S) (C := C) A)
      hCdefault
      (merkleOracleRange_card_le (M := M) (S := S) (C := C))
  simpa [extractabilityBirthdayTerm,
    merkleOracleRange_card_eq (M := M) (S := S) (C := C) default,
    not_not] using hbirthday

/-- Conditional rest-phase bound after a fixed collision-free commit support
point.

This packages `witnessBadEventROM_rest_bound` into the shape required by
`probEvent_bind_le_add`, with the predicate written as the negation form used
by that generic lemma. -/
private theorem witnessRestBadEvent_bound_of_commit_support {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    {x : ((C × AUX) × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)}
    (hx : x ∈ support
      ((simulateQ cachingOracle
        (witnessBadEventCommitPart (M := M) (S := S) (C := C) A)).run ∅))
    (hno : ¬ CacheHasCollision x.2) :
    Pr[fun z => ¬ (¬ WitnessBadEventROM (M := M) (S := S) (C := C) z) |
      witnessBadEventRestPart (M := M) (S := S) (C := C) A x] ≤
      extractabilityFreshHitTerm C depth A.t₁ A.t₂ := by
  rcases x with ⟨⟨⟨commitment, aux⟩, commitTrace⟩, cache₁⟩
  have hbound :=
    witnessBadEventROM_rest_bound
      (M := M) (S := S) (C := C)
      A (commitment := commitment) (aux := aux)
      (commitTrace := commitTrace) (cache₁ := cache₁)
      (by simpa [witnessBadEventCommitPart] using hx) hno
  simpa [witnessBadEventRestPart, not_not] using hbound

/-- ROM bad-event estimate for the selected-witness extractability game.

Textbook statement: the selected-witness bad event is bounded by a commit
birthday term plus a fresh-hit term.

Lean event/game: `WitnessBadEventROM` in `extractabilityWitnessGame`.

Bound expression: `extractabilityErrorTerm C depth A.t₁ A.t₂`.

Proof roadmap: split the cached game after the commit phase. If the commit
cache collides, use the birthday bound. Otherwise, any later bad event creates
a fresh cache entry whose answer hits a known label from the commit partial
tree. -/
private theorem witnessBadEventROM_game_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => WitnessBadEventROM (M := M) (S := S) (C := C) z |
      extractabilityWitnessGame (M := M) (S := S) (C := C) A] ≤
      extractabilityErrorTerm C depth A.t₁ A.t₂ := by
  classical
  let commitPart := witnessBadEventCommitPart (M := M) (S := S) (C := C) A
  let restPart := witnessBadEventRestPart (M := M) (S := S) (C := C) A
  let ε₁ : ℝ≥0∞ := extractabilityBirthdayTerm C A.t₁
  let ε₂ : ℝ≥0∞ := extractabilityFreshHitTerm C depth A.t₁ A.t₂
  have hcommit :
      Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
        (simulateQ cachingOracle commitPart).run ∅] ≤ ε₁ := by
    simpa [commitPart, ε₁] using
      witnessCommitCollision_bound (M := M) (S := S) (C := C) A hC
  have hrest :
      ∀ x ∈ support ((simulateQ cachingOracle commitPart).run ∅),
        ¬ CacheHasCollision x.2 →
          Pr[fun z => ¬
              (¬ WitnessBadEventROM (M := M) (S := S) (C := C) z) |
            restPart x] ≤ ε₂ := by
    intro x hx hno
    simpa [commitPart, restPart, ε₂] using
      witnessRestBadEvent_bound_of_commit_support
        (M := M) (S := S) (C := C) A (by simpa [commitPart] using hx) hno
  have hcombine :=
    probEvent_bind_le_add
      (mx := (simulateQ cachingOracle commitPart).run ∅)
      (my := restPart)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => ¬ WitnessBadEventROM (M := M) (S := S) (C := C) z)
      (ε₁ := ε₁)
      (ε₂ := ε₂)
      hcommit hrest
  rw [extractabilityWitnessGame_eq, extractabilityWitnessInner_eq_bind,
    simulateQ_bind, StateT.run_bind]
  simpa [commitPart, restPart, ε₁, ε₂, extractabilityErrorTerm,
    extractabilityBirthdayTerm, extractabilityFreshHitTerm, not_not] using hcombine

/-- Conditional witness-game extractability combiner specialized to
`extractabilityWitnessGame`. The hypothesis is the bad-event estimate for the
selected-witness ROM experiment, whose verifier phase logs one single path. -/
theorem extractability_bound_of_witnessBadEventROM_game_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (hbad :
      Pr[ fun z => WitnessBadEventROM (M := M) (S := S) (C := C) z |
        extractabilityWitnessGame (M := M) (S := S) (C := C) A] ≤
        extractabilityErrorTerm C depth A.t₁ A.t₂) :
    Pr[ fun z => WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z |
      extractabilityWitnessGame (M := M) (S := S) (C := C) A] ≤
      extractabilityErrorTerm C depth A.t₁ A.t₂ :=
  extractability_bound_of_witnessBadEventROM_bound
    (M := M) (S := S) (C := C)
    (extractabilityWitnessGame (M := M) (S := S) (C := C) A)
    (extractabilityErrorTerm C depth A.t₁ A.t₂) hbad

/-- Final single-commitment Merkle extractability bound for the selected-witness
ROM game.

Textbook statement: extractor failure implies one of the standard
single-commitment bad events.

Lean event/game: `WitnessExtractabilityWinROM` in `extractabilityWitnessGame`.

Bound expression: with `d = depth` and `|C| = 2^λ`,
`extractabilityErrorTerm C d A.t₁ A.t₂` expands to
`A.t₁^2 / (2 * |C|)
 + (A.t₂ + d + 1) * min (2 * A.t₁ + 1, 2^(d + 1)) / |C|`.

Scope note: this is the selected-witness ROM theorem, not the full-batch
verifier theorem. -/
theorem extractability_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z |
      extractabilityWitnessGame (M := M) (S := S) (C := C) A] ≤
      extractabilityErrorTerm C depth A.t₁ A.t₂ :=
  extractability_bound_of_witnessBadEventROM_game_bound
    (M := M) (S := S) (C := C) A
    (witnessBadEventROM_game_bound (M := M) (S := S) (C := C) A hC)

/-- Single-commitment extractability bound obtained from a bad-event estimate
for the full-batch experiment.

Textbook statement: this is the full-batch bad-event-to-win implication.

Lean event/game: `ExtractabilityWin` and `BadEvent` over an arbitrary
full-batch transcript distribution.

Scope note: this is intentionally conditional. A caller must separately prove
the probability estimate for the full-batch bad event. This wrapper is
specialized to `extractabilityErrorTerm C depth A.t₁ A.t₂`; a theorem matching
the full-batch textbook macro should first prove its own bad-event estimate and
then instantiate the more general `extractability_bound_of_badEvent_bound`.
The textbook target for that separate estimate is
`MTExtractabilityExpression(λ, q, L, d) =
  1/2 * (q - 1) * q / 2^λ + (d + 1) * 2L / 2^λ`. -/
theorem extractability_bound_of_textbook_badEvent_bound {depth t : ℕ}
    [DecidableEq C] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth))
    (hbad :
      Pr[ fun x => BadEvent (M := M) (S := S) (C := C) f x | oa] ≤
        extractabilityErrorTerm C depth A.t₁ A.t₂) :
    Pr[ fun x => ExtractabilityWin (M := M) (S := S) (C := C) f x | oa] ≤
      extractabilityErrorTerm C depth A.t₁ A.t₂ :=
  extractability_bound_of_badEvent_bound
    (M := M) (S := S) (C := C) f oa
    (extractabilityErrorTerm C depth A.t₁ A.t₂) hbad

end MerkleTree
