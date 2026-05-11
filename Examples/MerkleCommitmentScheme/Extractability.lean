/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support
import Examples.MerkleCommitmentScheme.Collision
import Examples.CommitmentScheme.Support.Collision
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Merkle Commitment Scheme — Extractability

This module packages the Merkle extractor and the associated two-phase game in a
form suitable for the textbook extractability proof from Section 18.5.

The current file provides the experiment and bad-event surface together with the
basic deterministic unfold lemmas. The remaining probability and same-tree
arguments can be developed against these definitions.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- The opening output of the adversary's second phase. -/
structure OpeningData (M : Type) (S : Type) (C : Type) (depth : ℕ) where
  I : IndexSet depth
  message : Subvector M I
  proof : Proof S C I

/-- A two-phase Merkle extractability adversary with an overall query budget. -/
structure ExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth t : ℕ) where
  commit : OracleComp (Oracle M S C) (C × AUX)
  open_ : AUX → OracleComp (Oracle M S C) (OpeningData M S C depth)
  t₁ : ℕ
  t₂ : ℕ
  totalBound : t₁ + t₂ ≤ t
  commitBound : IsTotalQueryBound commit t₁
  openBound : ∀ aux, IsTotalQueryBound (open_ aux) t₂

/-- The partial extractor state reconstructed from a commit trace. -/
def extractedStateOfTrace {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    ExtractedState M S C depth :=
  let labels := buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
    commitment trace
  let leaves := populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth) trace labels
  ⟨labels, leaves⟩

/-- The extractor output computed from a commit trace. -/
def extractedOutputOfTrace {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    Leaves M depth × Trapdoor S C depth :=
  extract (M := M) (S := S) (C := C) (depth := depth) commitment trace

/-- Transcript of the Merkle extractability experiment. -/
structure ExtractTranscript (M : Type) (S : Type) (C : Type) (AUX : Type) (depth : ℕ) where
  commitment : C
  aux : AUX
  commitTrace : QueryLog (Oracle M S C)
  opening : OpeningData M S C depth
  openTrace : QueryLog (Oracle M S C)

/-- The extractor output induced by the commit trace stored in a transcript. -/
def extractedOutputOfTranscript {depth : ℕ} [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) :
    Leaves M depth × Trapdoor S C depth :=
  extractedOutputOfTrace (M := M) (S := S) (C := C) (depth := depth)
    x.commitment x.commitTrace

private def authPathMismatch [DecidableEq S] [DecidableEq C] {depth : ℕ}
    (p q : AuthPath S C depth) : Prop :=
  p.salt ≠ q.salt ∨ ∃ layer : Fin depth, p.siblings.get layer ≠ q.siblings.get layer

private theorem not_authPathMismatch_of_eq [DecidableEq S] [DecidableEq C] {depth : ℕ}
    {p q : AuthPath S C depth} (h : p = q) :
    ¬ authPathMismatch (S := S) (C := C) p q := by
  rintro (hsalt | hsiblings)
  · exact hsalt (by simp [h])
  · rcases hsiblings with ⟨layer, hsiblings⟩
    exact hsiblings (by simp [h])

/-- A selected witness index for the extractor/opening mismatch. -/
def WitnessMismatch [DecidableEq S] [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) (i : {j // j ∈ x.opening.I}) : Prop :=
  (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get i.1 ≠
      x.opening.message i ∨
    authPathMismatch (S := S) (C := C)
      (openSingle (S := S) (C := C)
        (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 i.1)
      (x.opening.proof i)

/-- Deterministically select the first opened index where the extracted output
differs from the adversary opening. Message mismatches are tested before proof
mismatches at each index. -/
noncomputable def selectWitness? [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) :
    Option {i // i ∈ x.opening.I} :=
  by
    classical
    exact x.opening.I.attach.toList.find? fun i =>
      if (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get i.1 ≠
          x.opening.message i then
        true
      else if authPathMismatch (S := S) (C := C)
          (openSingle (S := S) (C := C)
            (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 i.1)
          (x.opening.proof i) then
        true
      else
        false

theorem selectWitness?_some {depth : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {x : ExtractTranscript M S C AUX depth} {i : {j // j ∈ x.opening.I}}
    (h : selectWitness? (M := M) (S := S) (C := C) x = some i) :
    WitnessMismatch (M := M) (S := S) (C := C) x i := by
  classical
  unfold selectWitness? at h
  have hpred := List.find?_some h
  by_cases hmsg :
      (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get i.1 ≠
        x.opening.message i
  · exact .inl hmsg
  · by_cases hproof :
        authPathMismatch (S := S) (C := C)
          (openSingle (S := S) (C := C)
            (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 i.1)
          (x.opening.proof i)
    · exact .inr hproof
    · simp [hmsg, hproof] at hpred

/-- The honest batch verifier computation induced by a transcript. -/
noncomputable def honestCheckComp [DecidableEq C] {depth : ℕ}
    (x : ExtractTranscript M S C AUX depth) :
    OracleComp (Oracle M S C) Bool :=
  check (M := M) (S := S) (C := C)
    x.commitment x.opening.I x.opening.message x.opening.proof

/-- The honest verifier's query-answer trace induced by a transcript. -/
noncomputable def honestTraceOfTranscript [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) :
    QueryLog (Oracle M S C) :=
  (logEval f (honestCheckComp (M := M) (S := S) (C := C) x)).2

/-- The honest verifier's acceptance bit induced by a transcript. -/
noncomputable def acceptedOfTranscript [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Bool :=
  (logEval f (honestCheckComp (M := M) (S := S) (C := C) x)).1

/-- Transcript for the witness-index extractability experiment. The verifier
log is present exactly when a mismatch witness was selected. -/
structure WitnessExtractTranscript (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth : ℕ) where
  base : ExtractTranscript M S C AUX depth
  witness? : Option {i // i ∈ base.opening.I}
  singleCheck? : Option (Bool × QueryLog (Oracle M S C))

/-- The inner two-phase extractability experiment prior to running under
`cachingOracle`. -/
noncomputable def extractabilityInner {depth t : ℕ} [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth) := do
  let ((commitment, aux), commitTrace) ← (simulateQ loggingOracle A.commit).run
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let _ ←
    (simulateQ loggingOracle
      (check (M := M) (S := S) (C := C)
        commitment opening.I opening.message opening.proof)).run
  pure
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }

/-- The witness-index extractability experiment before running under
`cachingOracle`. It runs only the selected single-leaf verifier path. -/
noncomputable def extractabilityWitnessInner {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (WitnessExtractTranscript M S C AUX depth) := do
  let ((commitment, aux), commitTrace) ← (simulateQ loggingOracle A.commit).run
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  match selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      pure { base := base, witness? := none, singleCheck? := none }
  | some i =>
      let single ←
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))).run
      pure { base := base, witness? := some i, singleCheck? := some single }

/-- The Merkle extractability game run with a shared cache. -/
noncomputable def extractabilityGame {depth t : ℕ} [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle (extractabilityInner (M := M) (S := S) (C := C) A)).run ∅

/-- The witness-index Merkle extractability game in the random-oracle model. -/
noncomputable def extractabilityWitnessGame {depth t : ℕ}
    [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C)
      (WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle
    (extractabilityWitnessInner (M := M) (S := S) (C := C) A)).run ∅

/-- The extractability failure event. -/
def ExtractabilityWin [DecidableEq C] {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Prop :=
  acceptedOfTranscript (M := M) (S := S) (C := C) f x = true ∧
    (Subvector.ofVector (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1 x.opening.I
        ≠ x.opening.message ∨
      «open» (S := S) (C := C)
          (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 x.opening.I
        ≠ x.opening.proof)

/-- The commit trace already contains a random-oracle collision. -/
def CommitCollisionEvent {depth : ℕ} (x : ExtractTranscript M S C AUX depth) : Prop :=
  LogHasCollision x.commitTrace

/-- The extractor's partial tree changes after processing the open-phase trace. -/
def ExtractorStateChangedEvent {depth : ℕ} [DecidableEq C]
    (x : ExtractTranscript M S C AUX depth) : Prop :=
  extractedStateOfTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment x.commitTrace ≠
    extractedStateOfTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment (x.commitTrace ++ x.openTrace)

/-- The honest verifier uses a query outside the commit trace while still
accepting. -/
def HonestTraceEscapeEvent [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Prop :=
  acceptedOfTranscript (M := M) (S := S) (C := C) f x = true ∧
    ¬ LogContains (honestTraceOfTranscript (M := M) (S := S) (C := C) f x) x.commitTrace

/-- The three bad events in the textbook single-commitment extractability proof. -/
def BadEvent {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) : Prop :=
  CommitCollisionEvent (M := M) (S := S) (C := C) x ∨
    ExtractorStateChangedEvent (M := M) (S := S) (C := C) x ∨
    HonestTraceEscapeEvent (M := M) (S := S) (C := C) f x

/-- ROM extractability failure for the cached game output, interpreting the
final cache as a total fixed oracle on sampled points. -/
noncomputable def ExtractabilityWinROM [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (z : ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  ExtractabilityWin (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- Fixed-oracle success for the witness-index extractability experiment. -/
def WitnessExtractabilityWin [DecidableEq S] [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) : Prop :=
  ∃ i : {j // j ∈ x.base.opening.I},
    x.witness? = some i ∧
      WitnessMismatch (M := M) (S := S) (C := C) x.base i ∧
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.base.commitment i.1 (x.base.opening.message i) (x.base.opening.proof i)) = true

/-- ROM witness failure for the cached game output, using the final cache as a
total fixed oracle. -/
noncomputable def WitnessExtractabilityWinROM [DecidableEq S] [DecidableEq C]
    {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  WitnessExtractabilityWin (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- ROM bad event for the cached game output. -/
noncomputable def BadEventROM {depth : ℕ} [DecidableEq C]
    [Inhabited C]
    (z : ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  BadEvent (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- The selected single-check trace escapes the commit trace while accepting. -/
def WitnessTraceEscapeEvent [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) : Prop :=
  ∃ i : {j // j ∈ x.base.opening.I},
    x.witness? = some i ∧
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.base.commitment i.1 (x.base.opening.message i) (x.base.opening.proof i)) = true ∧
      ¬ LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.base.commitment i.1
            (x.base.opening.message i) (x.base.opening.proof i))).2
        x.base.commitTrace

/-- The fixed-oracle bad-event disjunction for the witness-index experiment. -/
def WitnessBadEvent {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) : Prop :=
  CommitCollisionEvent (M := M) (S := S) (C := C) x.base ∨
    ExtractorStateChangedEvent (M := M) (S := S) (C := C) x.base ∨
    WitnessTraceEscapeEvent (M := M) (S := S) (C := C) f x

/-- The ROM bad-event disjunction for the witness-index experiment. -/
noncomputable def WitnessBadEventROM {depth : ℕ} [DecidableEq C]
    [Inhabited C]
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  WitnessBadEvent (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- The number of non-dummy labels used in the textbook extractability bound. -/
def extractabilityCountingTerm (depth t₁ : ℕ) : ℕ :=
  min (2 * t₁ + 1) (2 ^ (depth + 1))

/-- The single-commitment Merkle extractability error expression after the
bad-event decomposition. -/
noncomputable def extractabilityErrorTerm (C : Type) [Fintype C]
    (depth t₁ t₂ : ℕ) : ℝ≥0∞ :=
  ((t₁ ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
    (((t₂ + depth + 1) * extractabilityCountingTerm depth t₁ : ℕ) : ℝ≥0∞) *
      (Fintype.card C : ℝ≥0∞)⁻¹

@[simp] theorem extractabilityGame_eq {depth t : ℕ} [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityGame (M := M) (S := S) (C := C) A =
      (simulateQ cachingOracle (extractabilityInner (M := M) (S := S) (C := C) A)).run ∅ := rfl

@[simp] theorem extractabilityWitnessGame_eq {depth t : ℕ}
    [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityWitnessGame (M := M) (S := S) (C := C) A =
      (simulateQ cachingOracle
        (extractabilityWitnessInner (M := M) (S := S) (C := C) A)).run ∅ := rfl

theorem extractabilityWin_iff [DecidableEq C] {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) :
    ExtractabilityWin (M := M) (S := S) (C := C) f x ↔
      acceptedOfTranscript (M := M) (S := S) (C := C) f x = true ∧
        (Subvector.ofVector (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1
            x.opening.I ≠ x.opening.message ∨
          «open» (S := S) (C := C)
              (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 x.opening.I
            ≠ x.opening.proof) := Iff.rfl

theorem not_extractabilityWin_of_accepted_false [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (hacc : acceptedOfTranscript (M := M) (S := S) (C := C) f x = false) :
    ¬ ExtractabilityWin (M := M) (S := S) (C := C) f x := by
  rintro ⟨htrue, _⟩
  simp [hacc] at htrue

private theorem honestTrace_subset_of_not_escape [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (hsubset : ¬ HonestTraceEscapeEvent (M := M) (S := S) (C := C) f x)
    (hacc : acceptedOfTranscript (M := M) (S := S) (C := C) f x = true) :
    LogContains (honestTraceOfTranscript (M := M) (S := S) (C := C) f x) x.commitTrace := by
  by_contra hnot
  exact hsubset ⟨hacc, hnot⟩

private theorem honestTrace_contains_single {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I) (commitTrace : QueryLog (Oracle M S C))
    (i : {j // j ∈ I})
    (hsubset : LogContains
      (logEval f (check (M := M) (S := S) (C := C) commitment I message proof)).2
      commitTrace) :
    LogContains
      (logEval f
        (checkSingle (M := M) (S := S) (C := C) commitment i.1 (message i) (proof i))).2
      commitTrace := by
  exact LogContains.trans
    (logContains_checkSingle_check (M := M) (S := S) (C := C)
      f commitment I message proof i)
    hsubset

private theorem logEval_fst_eq_eval {α : Type} (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) α) :
    (logEval f oa).1 = eval f oa := by
  unfold logEval eval
  have h :=
    QueryImpl.fst_map_run_withLogging (QueryImpl.ofFn f) oa
  simpa using h

private theorem leaf_query_unique_of_no_commit_collision {depth : ℕ}
    (x : ExtractTranscript M S C AUX depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    {message₀ message₁ : M} {salt₀ salt₁ : S} {answer : C}
    (h₀ : ⟨Sum.inl (message₀, salt₀), answer⟩ ∈ x.commitTrace)
    (h₁ : ⟨Sum.inl (message₁, salt₁), answer⟩ ∈ x.commitTrace) :
    message₀ = message₁ ∧ salt₀ = salt₁ := by
  by_contra hne
  have hpair : (message₀, salt₀) ≠ (message₁, salt₁) := by
    intro hp
    exact hne ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  rcases (List.mem_iff_get.mp h₀) with ⟨i, hi⟩
  rcases (List.mem_iff_get.mp h₁) with ⟨j, hj⟩
  by_cases hij : i = j
  · have hentries : (⟨Sum.inl (message₀, salt₀), answer⟩ :
        (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) =
        ⟨Sum.inl (message₁, salt₁), answer⟩ := by
      rw [← hi, ← hj, hij]
    cases hentries
    exact hpair rfl
  · have hiElem : x.commitTrace[i] =
        (⟨Sum.inl (message₀, salt₀), answer⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) := by
      simpa [List.get_eq_getElem] using hi
    have hjElem : x.commitTrace[j] =
        (⟨Sum.inl (message₁, salt₁), answer⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) := by
      simpa [List.get_eq_getElem] using hj
    have hdomne : x.commitTrace[i].1 ≠ x.commitTrace[j].1 := by
      rw [hiElem, hjElem]
      intro hdom
      exact hpair (Sum.inl.inj hdom)
    have heq : HEq x.commitTrace[i].2 x.commitTrace[j].2 := by
      rw [hiElem, hjElem]
    exact hcoll ⟨i, j, hij, hdomne, heq⟩

private theorem internal_query_unique_of_no_commit_collision {depth : ℕ}
    (x : ExtractTranscript M S C AUX depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    {left₀ left₁ right₀ right₁ answer : C}
    (h₀ : ⟨Sum.inr (left₀, right₀), answer⟩ ∈ x.commitTrace)
    (h₁ : ⟨Sum.inr (left₁, right₁), answer⟩ ∈ x.commitTrace) :
    left₀ = left₁ ∧ right₀ = right₁ := by
  by_contra hne
  have hpair : (left₀, right₀) ≠ (left₁, right₁) := by
    intro hp
    exact hne ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  rcases (List.mem_iff_get.mp h₀) with ⟨i, hi⟩
  rcases (List.mem_iff_get.mp h₁) with ⟨j, hj⟩
  by_cases hij : i = j
  · have hentries : (⟨Sum.inr (left₀, right₀), answer⟩ :
        (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) =
        ⟨Sum.inr (left₁, right₁), answer⟩ := by
      rw [← hi, ← hj, hij]
    cases hentries
    exact hpair rfl
  · have hiElem : x.commitTrace[i] =
        (⟨Sum.inr (left₀, right₀), answer⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) := by
      simpa [List.get_eq_getElem] using hi
    have hjElem : x.commitTrace[j] =
        (⟨Sum.inr (left₁, right₁), answer⟩ :
          (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) := by
      simpa [List.get_eq_getElem] using hj
    have hdomne : x.commitTrace[i].1 ≠ x.commitTrace[j].1 := by
      rw [hiElem, hjElem]
      intro hdom
      exact hpair (Sum.inr.inj hdom)
    have heq : HEq x.commitTrace[i].2 x.commitTrace[j].2 := by
      rw [hiElem, hjElem]
    exact hcoll ⟨i, j, hij, hdomne, heq⟩

private theorem single_trace_leaf_entry_in_commitTrace {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth)
    (commitTrace : QueryLog (Oracle M S C))
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            commitment idx message authPath)).2
        commitTrace) :
    ⟨checkLeafQuery (M := M) (S := S) (C := C) message authPath,
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩ ∈ commitTrace := by
  exact hcontains _
    (checkLeafQuery_mem_logEval_checkSingle (M := M) (S := S) (C := C)
      f commitment idx message authPath)

private theorem single_trace_internal_entry_in_commitTrace {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth)
    (commitTrace : QueryLog (Oracle M S C)) (layer : Fin depth)
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            commitment idx message authPath)).2
        commitTrace) :
    ⟨checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer,
      f (checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer)⟩ ∈
        commitTrace := by
  exact hcontains _
    (checkInternalQuery_mem_logEval_checkSingle (M := M) (S := S) (C := C)
      f commitment idx message authPath layer)

private theorem parentPos_pathPos_succ {depth : ℕ} (idx : Index depth) (layer : Fin depth) :
    parentPos
        (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩) =
      pathPos idx ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩ := by
  apply Fin.ext
  change
    (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).1 / 2 =
      (pathPos idx ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩).1
  rw [
    pathPos_val_eq_div_pow (idx := idx)
      (layer := ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩),
    pathPos_val_eq_div_pow (idx := idx)
      (layer := ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩)]
  rw [Nat.div_div_eq_div_mul]
  congr 1
  have hlt : layer.1 < depth := layer.2
  have hpow :
      2 ^ (depth - layer.1) =
        2 ^ (depth - (layer.1 + 1)) * 2 := by
    rw [show depth - layer.1 = depth - (layer.1 + 1) + 1 by omega, pow_succ]
  simpa [Nat.mul_comm] using hpow.symm

private theorem leftChildPos_pathPos_of_even {depth : ℕ} (idx : Index depth)
    (layer : Fin depth)
    (hparity :
      (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).1 % 2 = 0) :
    leftChildPos
        (pathPos idx ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩) =
      pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ := by
  rw [← parentPos_pathPos_succ (idx := idx) (layer := layer)]
  exact leftChildPos_parentPos_of_even
    (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩) hparity

private theorem rightChildPos_pathPos_of_even {depth : ℕ} (idx : Index depth)
    (layer : Fin depth)
    (hparity :
      (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).1 % 2 = 0) :
    rightChildPos
        (pathPos idx ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩) =
      siblingPos idx layer := by
  rw [← parentPos_pathPos_succ (idx := idx) (layer := layer), siblingPos]
  exact rightChildPos_parentPos_of_even
    (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩) hparity

private theorem leftChildPos_pathPos_of_odd {depth : ℕ} (idx : Index depth)
    (layer : Fin depth)
    (hparity :
      (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).1 % 2 = 1) :
    leftChildPos
        (pathPos idx ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩) =
      siblingPos idx layer := by
  rw [← parentPos_pathPos_succ (idx := idx) (layer := layer), siblingPos]
  exact leftChildPos_parentPos_of_odd
    (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩) hparity

private theorem rightChildPos_pathPos_of_odd {depth : ℕ} (idx : Index depth)
    (layer : Fin depth)
    (hparity :
      (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).1 % 2 = 1) :
    rightChildPos
        (pathPos idx ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩) =
      pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ := by
  rw [← parentPos_pathPos_succ (idx := idx) (layer := layer)]
  exact rightChildPos_parentPos_of_odd
    (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩) hparity

private theorem eval_recomputeRootAux_eq_withHash (f : OracleFn M S C) :
    {depth : ℕ} → (idx : Index depth) → (current : C) → (siblings : Vector C depth) →
      eval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
        recomputeRootAuxWithHash (fun x => f (Sum.inr x)) idx current siblings
  | 0, _, _, _ => by
      simp [recomputeRootAux, recomputeRootAuxWithHash]
  | Nat.succ _, idx, current, siblings => by
      by_cases hparity : idx.1 % 2 = 0
      · simp [recomputeRootAux, recomputeRootAuxWithHash, eval_bind,
          hparity, eval_recomputeRootAux_eq_withHash]
      · simp [recomputeRootAux, recomputeRootAuxWithHash, eval_bind,
          hparity, eval_recomputeRootAux_eq_withHash]

private theorem eval_recomputeRootSingle_eq_withHash (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath) =
      recomputeRootSingleWithHash
        (fun x => f (Sum.inl x))
        (fun x => f (Sum.inr x))
        idx message authPath := by
  rw [recomputeRootSingle, eval_bind]
  simp [recomputeRootSingleWithHash, eval_recomputeRootAux_eq_withHash]

private theorem localIndex_root_eq {depth : ℕ} (idx : Index depth) :
    localIndex idx ⟨0, Nat.succ_pos _⟩ = idx := by
  apply Fin.ext
  simp [localIndex, Nat.mod_eq_of_lt idx.2]

private theorem checkPathLabel_root_eq_of_check [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth)
    (hcheck :
      eval f (checkSingle (M := M) (S := S) (C := C)
        commitment idx message authPath) = true) :
    checkPathLabel f idx message authPath ⟨0, Nat.succ_pos _⟩ = commitment := by
  have hroot :=
    (eval_checkSingle_eq_true_iff (M := M) (S := S) (C := C)
      f commitment idx message authPath).mp hcheck
  rw [eval_recomputeRootSingle_eq_withHash] at hroot
  change
    recomputeRootSingleWithHash
        (fun x : M × S => f (Sum.inl x))
        (fun x : C × C => f (Sum.inr x))
        (localIndex idx ⟨0, Nat.succ_pos _⟩)
        message
        { salt := authPath.salt
          siblings := Vector.cast (by simp) (authPath.siblings.take depth) } =
      commitment
  rw [localIndex_root_eq]
  simpa [recomputeRootSingleWithHash] using hroot

private theorem recomputeRootAuxWithHash_eq_current_of_length_zero {n : ℕ}
    (nodeHash : C × C → C) (idx : Fin (2 ^ n)) (current : C)
    (siblings : Vector C n) (hn : n = 0) :
    recomputeRootAuxWithHash nodeHash idx current siblings = current := by
  subst hn
  simp [recomputeRootAuxWithHash]

private theorem checkPathLabel_leaf_eq_leafQuery (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    checkPathLabel f idx message authPath (Fin.last depth) =
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath) := by
  unfold checkPathLabel recomputeRootSingleWithHash checkLeafQuery
  apply recomputeRootAuxWithHash_eq_current_of_length_zero
  simp

private theorem path_label_known_after_passes_of_internal_prefix {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true) :
    ∀ (layer : ℕ) (hlayer : layer < depth + 1),
      (∀ internalLayer : Fin depth, internalLayer.1 < layer →
        ⟨checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath internalLayer,
          f (checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath internalLayer)⟩ ∈ x.commitTrace) →
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) x.commitment x.commitTrace layer ⟨layer, hlayer⟩).get
          (pathPos idx ⟨layer, hlayer⟩) =
        some (checkPathLabel f idx message authPath ⟨layer, hlayer⟩)
  | 0, hlayer, _ => by
      have hroot := checkPathLabel_root_eq_of_check
        (M := M) (S := S) (C := C) f x.commitment idx message authPath hcheck
      have hknown :
          (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
            (depth := depth) x.commitment x.commitTrace 0 ⟨0, hlayer⟩).get 0 =
            some x.commitment := by
        simpa [Vector.head] using
          buildPartialTreeFromTraceAfterPasses_root
            (M := M) (S := S) (C := C) (depth := depth)
            x.commitment x.commitTrace 0
      rw [pathPos_root, hroot]
      exact hknown
  | Nat.succ layer, hlayer, hprefix => by
      have hlt : layer < depth := by omega
      let parentLayer : Fin (depth + 1) :=
        ⟨layer, Nat.lt_of_lt_of_le hlt (Nat.le_succ depth)⟩
      let childLayer : Fin (depth + 1) := ⟨layer + 1, hlayer⟩
      let internalLayer : Fin depth := ⟨layer, hlt⟩
      have hchildLayerEq :
          (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
            Fin (depth + 1)) = childLayer := by
        apply Fin.ext
        simp [childLayer, internalLayer]
      have hparent :=
        path_label_known_after_passes_of_internal_prefix
          f x idx message authPath hcoll hcheck layer parentLayer.2
          (fun internalLayer hlt => hprefix internalLayer (by omega))
      have hentry :=
        hprefix internalLayer (by simp [internalLayer])
      by_cases hparity : (pathPos idx childLayer).1 % 2 = 0
      · have hmem :
            ⟨Sum.inr
                (checkPathLabel f idx message authPath childLayer,
                  copathLabel authPath internalLayer),
              checkPathLabel f idx message authPath parentLayer⟩ ∈
              x.commitTrace := by
          have hparityRaw :
              (pathPos idx
                (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                  Fin (depth + 1))).1 % 2 = 0 := by
            simpa [hchildLayerEq] using hparity
          have hentryEven :
              ⟨Sum.inr
                  (checkPathLabel f idx message authPath childLayer,
                    copathLabel authPath internalLayer),
                f (Sum.inr
                  (checkPathLabel f idx message authPath childLayer,
                    copathLabel authPath internalLayer))⟩ ∈
                x.commitTrace := by
            have hentry' := hentry
            change
              ⟨(if (pathPos idx
                    (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                      Fin (depth + 1))).1 % 2 = 0 then
                    Sum.inr
                      (checkPathLabel f idx message authPath
                        (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                          Fin (depth + 1)),
                        copathLabel authPath internalLayer)
                  else
                    Sum.inr
                      (copathLabel authPath internalLayer,
                        checkPathLabel f idx message authPath
                          (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                            Fin (depth + 1)))),
                f (if (pathPos idx
                    (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                      Fin (depth + 1))).1 % 2 = 0 then
                    Sum.inr
                      (checkPathLabel f idx message authPath
                        (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                          Fin (depth + 1)),
                        copathLabel authPath internalLayer)
                  else
                    Sum.inr
                      (copathLabel authPath internalLayer,
                        checkPathLabel f idx message authPath
                          (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                            Fin (depth + 1))))⟩ ∈ x.commitTrace at hentry'
            rw [if_pos hparityRaw] at hentry'
            simpa [childLayer, hchildLayerEq] using hentry'
          have hanswerEven :
              f (Sum.inr
                  (checkPathLabel f idx message authPath childLayer,
                    copathLabel authPath internalLayer)) =
                checkPathLabel f idx message authPath parentLayer := by
            simpa [checkInternalQueryAnswer, checkInternalQuery, childLayer,
              parentLayer, internalLayer, hchildLayerEq, hparityRaw] using
              checkInternalQueryAnswer_eq_checkPathLabel_parent
                (M := M) (S := S) (C := C) f idx message authPath internalLayer
          simpa [hanswerEven] using hentryEven
        have hunique :
            ∀ left' right' : C,
              ⟨Sum.inr (left', right'),
                  checkPathLabel f idx message authPath parentLayer⟩ ∈ x.commitTrace →
                left' = checkPathLabel f idx message authPath childLayer ∧
                  right' = copathLabel authPath internalLayer := by
          intro left' right' hmem'
          exact internal_query_unique_of_no_commit_collision
            (M := M) (S := S) (C := C) x hcoll hmem' hmem
        have hchild :=
          buildPartialTreeFromTraceAfterPasses_leftChild_get_of_unique_internal
            (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
            x.commitment x.commitTrace layer hlayer
            (pathPos idx parentLayer)
            (checkPathLabel f idx message authPath childLayer)
            (copathLabel authPath internalLayer)
            (checkPathLabel f idx message authPath parentLayer)
            (by simpa [parentLayer] using hparent)
            hmem hunique
        have hpos := leftChildPos_pathPos_of_even
          (idx := idx) (layer := internalLayer) hparity
        rw [← hpos]
        simpa [childLayer, parentLayer, internalLayer] using hchild
      · have hodd : (pathPos idx childLayer).1 % 2 = 1 := by
          have hltmod := Nat.mod_lt (pathPos idx childLayer).1 (by decide : 0 < 2)
          omega
        have hmem :
            ⟨Sum.inr
                (copathLabel authPath internalLayer,
                  checkPathLabel f idx message authPath childLayer),
              checkPathLabel f idx message authPath parentLayer⟩ ∈
              x.commitTrace := by
          have hparityRaw :
              ¬ (pathPos idx
                (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                  Fin (depth + 1))).1 % 2 = 0 := by
            simpa [hchildLayerEq] using hparity
          have hentryOdd :
              ⟨Sum.inr
                  (copathLabel authPath internalLayer,
                    checkPathLabel f idx message authPath childLayer),
                f (Sum.inr
                  (copathLabel authPath internalLayer,
                    checkPathLabel f idx message authPath childLayer))⟩ ∈
                x.commitTrace := by
            have hentry' := hentry
            change
              ⟨(if (pathPos idx
                    (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                      Fin (depth + 1))).1 % 2 = 0 then
                    Sum.inr
                      (checkPathLabel f idx message authPath
                        (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                          Fin (depth + 1)),
                        copathLabel authPath internalLayer)
                  else
                    Sum.inr
                      (copathLabel authPath internalLayer,
                        checkPathLabel f idx message authPath
                          (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                            Fin (depth + 1)))),
                f (if (pathPos idx
                    (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                      Fin (depth + 1))).1 % 2 = 0 then
                    Sum.inr
                      (checkPathLabel f idx message authPath
                        (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                          Fin (depth + 1)),
                        copathLabel authPath internalLayer)
                  else
                    Sum.inr
                      (copathLabel authPath internalLayer,
                        checkPathLabel f idx message authPath
                          (⟨internalLayer.1 + 1, Nat.succ_lt_succ internalLayer.2⟩ :
                            Fin (depth + 1))))⟩ ∈ x.commitTrace at hentry'
            rw [if_neg hparityRaw] at hentry'
            simpa [childLayer, hchildLayerEq] using hentry'
          have hanswerOdd :
              f (Sum.inr
                  (copathLabel authPath internalLayer,
                    checkPathLabel f idx message authPath childLayer)) =
                checkPathLabel f idx message authPath parentLayer := by
            simpa [checkInternalQueryAnswer, checkInternalQuery, childLayer,
              parentLayer, internalLayer, hchildLayerEq, hparityRaw] using
              checkInternalQueryAnswer_eq_checkPathLabel_parent
                (M := M) (S := S) (C := C) f idx message authPath internalLayer
          simpa [hanswerOdd] using hentryOdd
        have hunique :
            ∀ left' right' : C,
              ⟨Sum.inr (left', right'),
                  checkPathLabel f idx message authPath parentLayer⟩ ∈ x.commitTrace →
                left' = copathLabel authPath internalLayer ∧
                  right' = checkPathLabel f idx message authPath childLayer := by
          intro left' right' hmem'
          exact internal_query_unique_of_no_commit_collision
            (M := M) (S := S) (C := C) x hcoll hmem' hmem
        have hchild :=
          buildPartialTreeFromTraceAfterPasses_rightChild_get_of_unique_internal
            (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
            x.commitment x.commitTrace layer hlayer
            (pathPos idx parentLayer)
            (copathLabel authPath internalLayer)
            (checkPathLabel f idx message authPath childLayer)
            (checkPathLabel f idx message authPath parentLayer)
            (by simpa [parentLayer] using hparent)
            hmem hunique
        have hpos := rightChildPos_pathPos_of_odd
          (idx := idx) (layer := internalLayer) hodd
        rw [← hpos]
        simpa [childLayer, parentLayer, internalLayer] using hchild

private theorem path_label_known_after_passes {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true)
    (layer : ℕ) (hlayer : layer < depth + 1) :
    (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
      (depth := depth) x.commitment x.commitTrace layer ⟨layer, hlayer⟩).get
        (pathPos idx ⟨layer, hlayer⟩) =
      some (checkPathLabel f idx message authPath ⟨layer, hlayer⟩) :=
  path_label_known_after_passes_of_internal_prefix
    (M := M) (S := S) (C := C) (AUX := AUX)
    f x idx message authPath hcoll hcheck layer hlayer
    (fun internalLayer _ =>
      single_trace_internal_entry_in_commitTrace
        (M := M) (S := S) (C := C)
        f x.commitment idx message authPath x.commitTrace internalLayer hcontains)

private theorem copath_label_known_final {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true)
    (layer : Fin depth) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment x.commitTrace ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).get
        (siblingPos idx layer) =
      some (copathLabel authPath layer) := by
  let parentLayer : Fin (depth + 1) :=
    ⟨layer.1, Nat.lt_of_lt_of_le layer.2 (Nat.le_succ depth)⟩
  let childLayer : Fin (depth + 1) := ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩
  have hparent :=
    path_label_known_after_passes
      (M := M) (S := S) (C := C) (AUX := AUX)
      f x idx message authPath hcoll hcontains hcheck layer.1 parentLayer.2
  have hentry :=
    single_trace_internal_entry_in_commitTrace
      (M := M) (S := S) (C := C)
      f x.commitment idx message authPath x.commitTrace layer hcontains
  have hpasses : layer.1 + 1 ≤ depth + 1 := by omega
  by_cases hparity : (pathPos idx childLayer).1 % 2 = 0
  · have hmem :
        ⟨Sum.inr
            (checkPathLabel f idx message authPath childLayer,
              copathLabel authPath layer),
          checkPathLabel f idx message authPath parentLayer⟩ ∈
          x.commitTrace := by
      have hentryEven :
          ⟨Sum.inr
              (checkPathLabel f idx message authPath childLayer,
                copathLabel authPath layer),
            f (Sum.inr
              (checkPathLabel f idx message authPath childLayer,
                copathLabel authPath layer))⟩ ∈
            x.commitTrace := by
        have hparityRaw :
            (pathPos idx
              (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                Fin (depth + 1))).1 % 2 = 0 := by
          simpa [childLayer] using hparity
        have hentry' := hentry
        change
          ⟨(if (pathPos idx
                (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                  Fin (depth + 1))).1 % 2 = 0 then
                Sum.inr
                  (checkPathLabel f idx message authPath
                    (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1)),
                    copathLabel authPath layer)
              else
                Sum.inr
                  (copathLabel authPath layer,
                    checkPathLabel f idx message authPath
                      (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1)))),
            f (if (pathPos idx
                (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                  Fin (depth + 1))).1 % 2 = 0 then
                Sum.inr
                  (checkPathLabel f idx message authPath
                    (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1)),
                    copathLabel authPath layer)
              else
                Sum.inr
                  (copathLabel authPath layer,
                    checkPathLabel f idx message authPath
                      (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1))))⟩ ∈
            x.commitTrace at hentry'
        rw [if_pos hparityRaw] at hentry'
        simpa [childLayer] using hentry'
      have hanswerEven :
          f (Sum.inr
              (checkPathLabel f idx message authPath childLayer,
                copathLabel authPath layer)) =
            checkPathLabel f idx message authPath parentLayer := by
        have hparityRaw :
            (pathPos idx
              (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                Fin (depth + 1))).1 % 2 = 0 := by
          simpa [childLayer] using hparity
        simpa [checkInternalQueryAnswer, checkInternalQuery, childLayer,
          parentLayer, hparityRaw] using
          checkInternalQueryAnswer_eq_checkPathLabel_parent
            (M := M) (S := S) (C := C) f idx message authPath layer
      simpa [hanswerEven] using hentryEven
    have hunique :
        ∀ left' right' : C,
          ⟨Sum.inr (left', right'),
              checkPathLabel f idx message authPath parentLayer⟩ ∈ x.commitTrace →
            left' = checkPathLabel f idx message authPath childLayer ∧
              right' = copathLabel authPath layer := by
      intro left' right' hmem'
      exact internal_query_unique_of_no_commit_collision
        (M := M) (S := S) (C := C) x hcoll hmem' hmem
    have hsib :=
      buildPartialTreeFromTrace_rightChild_get_of_unique_internal_after_passes
        (M := M) (S := S) (C := C) (depth := depth) (layer := layer.1)
        x.commitment x.commitTrace layer.1 (Nat.succ_lt_succ layer.2)
        (pathPos idx parentLayer)
        (checkPathLabel f idx message authPath childLayer)
        (copathLabel authPath layer)
        (checkPathLabel f idx message authPath parentLayer)
        hpasses
        (by simpa [parentLayer] using hparent)
        hmem hunique
    have hpos := rightChildPos_pathPos_of_even
      (idx := idx) (layer := layer) hparity
    rw [← hpos]
    simpa [childLayer, parentLayer] using hsib
  · have hodd : (pathPos idx childLayer).1 % 2 = 1 := by
      have hltmod := Nat.mod_lt (pathPos idx childLayer).1 (by decide : 0 < 2)
      omega
    have hmem :
        ⟨Sum.inr
            (copathLabel authPath layer,
              checkPathLabel f idx message authPath childLayer),
          checkPathLabel f idx message authPath parentLayer⟩ ∈
          x.commitTrace := by
      have hentryOdd :
          ⟨Sum.inr
              (copathLabel authPath layer,
                checkPathLabel f idx message authPath childLayer),
            f (Sum.inr
              (copathLabel authPath layer,
                checkPathLabel f idx message authPath childLayer))⟩ ∈
            x.commitTrace := by
        have hparityRaw :
            ¬ (pathPos idx
              (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                Fin (depth + 1))).1 % 2 = 0 := by
          simpa [childLayer] using hparity
        have hentry' := hentry
        change
          ⟨(if (pathPos idx
                (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                  Fin (depth + 1))).1 % 2 = 0 then
                Sum.inr
                  (checkPathLabel f idx message authPath
                    (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1)),
                    copathLabel authPath layer)
              else
                Sum.inr
                  (copathLabel authPath layer,
                    checkPathLabel f idx message authPath
                      (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1)))),
            f (if (pathPos idx
                (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                  Fin (depth + 1))).1 % 2 = 0 then
                Sum.inr
                  (checkPathLabel f idx message authPath
                    (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1)),
                    copathLabel authPath layer)
              else
                Sum.inr
                  (copathLabel authPath layer,
                    checkPathLabel f idx message authPath
                      (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1))))⟩ ∈
            x.commitTrace at hentry'
        rw [if_neg hparityRaw] at hentry'
        simpa [childLayer] using hentry'
      have hanswerOdd :
          f (Sum.inr
              (copathLabel authPath layer,
                checkPathLabel f idx message authPath childLayer)) =
            checkPathLabel f idx message authPath parentLayer := by
        have hparityRaw :
            ¬ (pathPos idx
              (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ :
                Fin (depth + 1))).1 % 2 = 0 := by
          simpa [childLayer] using hparity
        simpa [checkInternalQueryAnswer, checkInternalQuery, childLayer,
          parentLayer, hparityRaw] using
          checkInternalQueryAnswer_eq_checkPathLabel_parent
            (M := M) (S := S) (C := C) f idx message authPath layer
      simpa [hanswerOdd] using hentryOdd
    have hunique :
        ∀ left' right' : C,
          ⟨Sum.inr (left', right'),
              checkPathLabel f idx message authPath parentLayer⟩ ∈ x.commitTrace →
            left' = copathLabel authPath layer ∧
              right' = checkPathLabel f idx message authPath childLayer := by
      intro left' right' hmem'
      exact internal_query_unique_of_no_commit_collision
        (M := M) (S := S) (C := C) x hcoll hmem' hmem
    have hsib :=
      buildPartialTreeFromTrace_leftChild_get_of_unique_internal_after_passes
        (M := M) (S := S) (C := C) (depth := depth) (layer := layer.1)
        x.commitment x.commitTrace layer.1 (Nat.succ_lt_succ layer.2)
        (pathPos idx parentLayer)
        (copathLabel authPath layer)
        (checkPathLabel f idx message authPath childLayer)
        (checkPathLabel f idx message authPath parentLayer)
        hpasses
        (by simpa [parentLayer] using hparent)
        hmem hunique
    have hpos := leftChildPos_pathPos_of_odd
      (idx := idx) (layer := layer) hodd
    rw [← hpos]
    simpa [childLayer, parentLayer] using hsib

private theorem vector_reverse_get {α : Type} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.reverse.get i = v.get ⟨n - 1 - i.1, by omega⟩ := by
  change v.reverse[i.1] = v[n - 1 - i.1]
  rw [show v.reverse = Vector.mk v.toArray.reverse (by simp) by rfl]
  rw [Vector.getElem_mk]
  rw [Array.getElem_reverse]
  rw [Vector.getElem_toArray]
  simp

private theorem openSiblings_get_from_top {depth : ℕ} (labels : Labels C depth)
    (idx : Index depth) (layer : Fin depth) :
    (openSiblings labels idx).get ⟨depth - 1 - layer.1, by omega⟩ =
      (labels ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).get (siblingPos idx layer) := by
  induction depth with
  | zero => exact Fin.elim0 layer
  | succ d ih =>
      by_cases hlast : layer.1 = d
      · have hlayer : layer = Fin.last d := by
          apply Fin.ext
          simpa using hlast
        subst hlayer
        have hpath :
            pathPos idx
                (⟨d + 1, Nat.succ_lt_succ (Fin.last d).2⟩ : Fin (d + 2)) =
              idx := by
          apply Fin.ext
          simp [pathPos]
        have hidx0 : (⟨d + 1 - 1 - (Fin.last d).1, by omega⟩ : Fin (d + 1)) = 0 := by
          apply Fin.ext
          simp
        rw [hidx0]
        let fhead : Fin (d + 1) → C := fun
          | ⟨0, _⟩ => (labels (Fin.last (d + 1))).get (siblingIndex idx)
          | ⟨Nat.succ i, hi⟩ =>
              (openSiblings (Fin.init labels) (parentPos idx)).get
                ⟨i, Nat.lt_of_succ_lt_succ hi⟩
        change (Vector.ofFn fhead)[0] =
          (labels (⟨d + 1, Nat.succ_lt_succ (Fin.last d).2⟩ : Fin (d + 2))).get
            (siblingIndex
              (pathPos idx
                (⟨d + 1, Nat.succ_lt_succ (Fin.last d).2⟩ : Fin (d + 2))))
        rw [Vector.getElem_ofFn]
        rw [hpath]
        rfl
      · have hlt : layer.1 < d :=
          lt_of_le_of_ne (Nat.le_of_lt_succ layer.2) hlast
        let layer' : Fin d := ⟨layer.1, hlt⟩
        let upper : Labels C d := Fin.init labels
        have hfin :
            (⟨d + 1 - 1 - layer.1, by omega⟩ : Fin (d + 1)) =
              Fin.succ (⟨d - 1 - layer.1, by omega⟩ : Fin d) := by
          apply Fin.ext
          simp
          omega
        rw [hfin]
        simp [openSiblings]
        have hrec := ih upper (parentPos idx) layer'
        simpa [upper, layer', siblingPos, pathPos, hlast] using hrec

private theorem openSiblings_reverse_get {depth : ℕ} (labels : Labels C depth)
    (idx : Index depth) (layer : Fin depth) :
    (openSiblings labels idx).reverse.get layer =
      (labels ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).get (siblingPos idx layer) := by
  rw [vector_reverse_get]
  exact openSiblings_get_from_top labels idx layer

private theorem openSingle_eq_of_salt_and_copath {depth : ℕ}
    (trapdoor : Trapdoor S C depth) (idx : Index depth) (authPath : AuthPath S C depth)
    (hsalt : trapdoor.salts.get idx = authPath.salt)
    (hsib : ∀ layer : Fin depth,
      (trapdoor.labels ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).get
        (siblingPos idx layer) = copathLabel authPath layer) :
    openSingle trapdoor idx = authPath := by
  cases trapdoor with
  | mk salts labels =>
  cases authPath with
  | mk salt siblings =>
      have hrev : (openSiblings labels idx).reverse = siblings.reverse := by
        apply Vector.ext
        intro i hi
        change ((openSiblings labels idx).reverse).get ⟨i, hi⟩ =
          (siblings.reverse).get ⟨i, hi⟩
        rw [openSiblings_reverse_get]
        simpa [copathLabel] using hsib ⟨i, hi⟩
      have hsiblings : openSiblings labels idx = siblings := by
        have := congrArg Vector.reverse hrev
        simpa [List.Vector.reverse_reverse] using this
      cases hsalt
      cases hsiblings
      rfl

private theorem leaf_opening_known_final {depth : ℕ} [DecidableEq C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true) :
    (populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitTrace
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        x.commitment x.commitTrace)).get idx =
      some (message, authPath.salt) := by
  let labels :=
    buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment x.commitTrace
  have hleafPass :=
    path_label_known_after_passes
      (M := M) (S := S) (C := C) (AUX := AUX)
      f x idx message authPath hcoll hcontains hcheck depth (Nat.lt_succ_self depth)
  have hleafLabel :
      (labels ⟨depth, Nat.lt_succ_self depth⟩).get idx =
        some (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)) := by
    have hfinal :=
      buildPartialTreeFromTrace_get_eq_of_after_passes
        (M := M) (S := S) (C := C) (depth := depth)
        x.commitment x.commitTrace depth ⟨depth, Nat.lt_succ_self depth⟩
        (pathPos idx ⟨depth, Nat.lt_succ_self depth⟩)
        (checkPathLabel f idx message authPath ⟨depth, Nat.lt_succ_self depth⟩)
        (by omega) hleafPass
    have hpath :
        pathPos idx ⟨depth, Nat.lt_succ_self depth⟩ = idx := by
      apply Fin.ext
      rw [pathPos_val_eq_div_pow
        (depth := depth) (idx := idx)
        (layer := ⟨depth, Nat.lt_succ_self depth⟩)]
      simp
    have hleaf :
        checkPathLabel f idx message authPath ⟨depth, Nat.lt_succ_self depth⟩ =
          f (checkLeafQuery (M := M) (S := S) (C := C) message authPath) := by
      simpa using
        (checkPathLabel_leaf_eq_leafQuery
          (M := M) (S := S) (C := C) f idx message authPath)
    rw [hpath, hleaf] at hfinal
    simpa [labels] using hfinal
  have hleafMem :=
    single_trace_leaf_entry_in_commitTrace
      (M := M) (S := S) (C := C)
      f x.commitment idx message authPath x.commitTrace hcontains
  have hunique :
      ∀ (message' : M) (salt' : S),
        ⟨Sum.inl (message', salt'),
          f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩ ∈
          x.commitTrace →
          message' = message ∧ salt' = authPath.salt := by
    intro message' salt' hmem'
    exact leaf_query_unique_of_no_commit_collision
      (M := M) (S := S) (C := C) x hcoll hmem' hleafMem
  exact populateLeavesFromTrace_get_eq_some_of_unique_leaf
    (M := M) (S := S) (C := C) (depth := depth)
    x.commitTrace labels idx message authPath.salt
    (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
    hleafLabel hleafMem hunique

private theorem extract_eq_fillMissing_of_contained_singleTrace {depth : ℕ}
    [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true) :
    extract (M := M) (S := S) (C := C) (depth := depth)
        x.commitment x.commitTrace =
      fillMissing (M := M) (S := S) (C := C) (depth := depth)
        ⟨buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
            x.commitment x.commitTrace,
          populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
            x.commitTrace
            (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
              (depth := depth) x.commitment x.commitTrace)⟩ := by
  cases depth with
  | zero =>
      have hleafMem :=
        single_trace_leaf_entry_in_commitTrace
          (M := M) (S := S) (C := C)
          f x.commitment idx message authPath x.commitTrace hcontains
      have hroot :=
        checkPathLabel_root_eq_of_check
          (M := M) (S := S) (C := C) f x.commitment idx message authPath hcheck
      have hanswer :
          f (checkLeafQuery (M := M) (S := S) (C := C) message authPath) =
            x.commitment := by
        simpa [checkPathLabel_leaf_eq_leafQuery] using hroot
      have hmemCommit :
          ⟨Sum.inl (message, authPath.salt), x.commitment⟩ ∈ x.commitTrace := by
        rw [← hanswer]
        simpa [checkLeafQuery] using hleafMem
      exact extract_eq_fillMissing_of_leaf_answer_mem
        (M := M) (S := S) (C := C) (depth := 0)
        x.commitment x.commitTrace message authPath.salt hmemCommit
  | succ d =>
      let top : Fin (d + 1) := 0
      have hentry :=
        single_trace_internal_entry_in_commitTrace
          (M := M) (S := S) (C := C)
          f x.commitment idx message authPath x.commitTrace top hcontains
      have hroot :=
        checkPathLabel_root_eq_of_check
          (M := M) (S := S) (C := C) f x.commitment idx message authPath hcheck
      have hparent :=
        checkInternalQueryAnswer_eq_checkPathLabel_parent
          (M := M) (S := S) (C := C) f idx message authPath top
      have hanswerTop :
          checkInternalQueryAnswer (M := M) (S := S) (C := C)
              f idx message authPath top =
            x.commitment := by
        simpa [top] using hparent.trans hroot
      let q := checkInternalQuery (M := M) (S := S) (C := C)
        f idx message authPath top
      have hdomain : ∃ left right : C, q = Sum.inr (left, right) := by
        unfold q checkInternalQuery
        by_cases hparity :
            (pathPos idx (⟨top.1 + 1, Nat.succ_lt_succ top.2⟩ : Fin (d + 2))).1 % 2 = 0
        · refine ⟨checkPathLabel f idx message authPath
              (⟨top.1 + 1, Nat.succ_lt_succ top.2⟩ : Fin (d + 2)),
            copathLabel authPath top, ?_⟩
          simp [hparity]
        · refine ⟨copathLabel authPath top,
            checkPathLabel f idx message authPath
              (⟨top.1 + 1, Nat.succ_lt_succ top.2⟩ : Fin (d + 2)), ?_⟩
          simp [hparity]
      rcases hdomain with ⟨left, right, hdomain⟩
      have hanswer : f (Sum.inr (left, right)) = x.commitment := by
        simpa [q, checkInternalQueryAnswer, hdomain] using hanswerTop
      have hentryConcrete :
          ⟨Sum.inr (left, right), f (Sum.inr (left, right))⟩ ∈ x.commitTrace := by
        have hentry' := hentry
        change ⟨q, f q⟩ ∈ x.commitTrace at hentry'
        rw [hdomain] at hentry'
        exact hentry'
      have hmemCommit :
          ⟨Sum.inr (left, right), x.commitment⟩ ∈ x.commitTrace := by
        simpa [hanswer] using hentryConcrete
      exact extract_eq_fillMissing_of_internal_answer_mem
        (M := M) (S := S) (C := C) (depth := d + 1)
        x.commitment x.commitTrace left right hmemCommit

private theorem extract_entry_eq_of_contained_singleTrace {depth : ℕ}
    [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.commitment idx message authPath)).2
        x.commitTrace)
    (hcheck :
      eval f
        (checkSingle (M := M) (S := S) (C := C)
          x.commitment idx message authPath) = true) :
    (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get idx = message ∧
      openSingle (S := S) (C := C)
        (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 idx =
        authPath := by
  let labels :=
    buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitment x.commitTrace
  let leaves :=
    populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
      x.commitTrace labels
  let state : ExtractedState M S C depth := ⟨labels, leaves⟩
  have hbranch :=
    extract_eq_fillMissing_of_contained_singleTrace
      (M := M) (S := S) (C := C) (AUX := AUX)
      f x idx message authPath hcontains hcheck
  have hleaf :
      leaves.get idx = some (message, authPath.salt) := by
    simpa [leaves, labels] using
      leaf_opening_known_final
        (M := M) (S := S) (C := C) (AUX := AUX)
        f x idx message authPath hcoll hcontains hcheck
  have hmsg :
      (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1.get idx =
        message := by
    unfold extractedOutputOfTranscript extractedOutputOfTrace
    rw [hbranch]
    exact fillMissing_message_get_eq_of_some_leaf
      (M := M) (S := S) (C := C) state idx message authPath.salt hleaf
  have hsalt :
      ((fillMissing (M := M) (S := S) (C := C) state).2.salts).get idx =
        authPath.salt :=
    fillMissing_salt_get_eq_of_some_leaf
      (M := M) (S := S) (C := C) state idx message authPath.salt hleaf
  have hsib :
      ∀ layer : Fin depth,
        ((fillMissing (M := M) (S := S) (C := C) state).2.labels
            ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).get (siblingPos idx layer) =
          copathLabel authPath layer := by
    intro layer
    exact fillMissing_label_get_eq_of_some_label
      (M := M) (S := S) (C := C) state
      ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ (siblingPos idx layer)
      (copathLabel authPath layer)
      (by
        simpa [state, labels] using
          copath_label_known_final
            (M := M) (S := S) (C := C) (AUX := AUX)
            f x idx message authPath hcoll hcontains hcheck layer)
  have hopenFill :
      openSingle (S := S) (C := C)
        (fillMissing (M := M) (S := S) (C := C) state).2 idx =
        authPath :=
    openSingle_eq_of_salt_and_copath
      (S := S) (C := C)
      (fillMissing (M := M) (S := S) (C := C) state).2 idx authPath
      hsalt hsib
  have hopen :
      openSingle (S := S) (C := C)
        (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 idx =
        authPath := by
    unfold extractedOutputOfTranscript extractedOutputOfTrace
    rw [hbranch]
    exact hopenFill
  exact ⟨hmsg, hopen⟩

/-- Deterministic same-tree claim corresponding to the last case in the
textbook extractability proof. -/
theorem sameTree_success {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x)
    (hchange : ¬ ExtractorStateChangedEvent (M := M) (S := S) (C := C) x)
    (hsubset : ¬ HonestTraceEscapeEvent (M := M) (S := S) (C := C) f x)
    (hacc : acceptedOfTranscript (M := M) (S := S) (C := C) f x = true) :
    Subvector.ofVector (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1
        x.opening.I = x.opening.message ∧
      «open» (S := S) (C := C)
          (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 x.opening.I
        = x.opening.proof := by
  have _ : ¬ ExtractorStateChangedEvent (M := M) (S := S) (C := C) x := hchange
  have hhonestContains :=
    honestTrace_subset_of_not_escape
      (M := M) (S := S) (C := C) f x hsubset hacc
  have hcheck :
      eval f
        (check (M := M) (S := S) (C := C)
          x.commitment x.opening.I x.opening.message x.opening.proof) = true := by
    simpa [acceptedOfTranscript, honestCheckComp, logEval_fst_eq_eval] using hacc
  have hcontainsBatch :
      LogContains
        (logEval f
          (check (M := M) (S := S) (C := C)
            x.commitment x.opening.I x.opening.message x.opening.proof)).2
        x.commitTrace := by
    simpa [honestTraceOfTranscript, honestCheckComp] using hhonestContains
  constructor
  · funext i
    have hsingleContains :=
      honestTrace_contains_single
        (M := M) (S := S) (C := C)
        f x.commitment x.opening.I x.opening.message x.opening.proof
        x.commitTrace i hcontainsBatch
    have hsingleCheck :=
      check_eval_eq_true_implies_single
        (M := M) (S := S) (C := C)
        f x.commitment x.opening.I x.opening.message x.opening.proof i hcheck
    have hentry :=
      extract_entry_eq_of_contained_singleTrace
        (M := M) (S := S) (C := C) (AUX := AUX)
        f x i.1 (x.opening.message i) (x.opening.proof i)
        hcoll hsingleContains hsingleCheck
    simpa [Subvector.ofVector] using hentry.1
  · funext i
    have hsingleContains :=
      honestTrace_contains_single
        (M := M) (S := S) (C := C)
        f x.commitment x.opening.I x.opening.message x.opening.proof
        x.commitTrace i hcontainsBatch
    have hsingleCheck :=
      check_eval_eq_true_implies_single
        (M := M) (S := S) (C := C)
        f x.commitment x.opening.I x.opening.message x.opening.proof i hcheck
    exact (extract_entry_eq_of_contained_singleTrace
      (M := M) (S := S) (C := C) (AUX := AUX)
      f x i.1 (x.opening.message i) (x.opening.proof i)
      hcoll hsingleContains hsingleCheck).2

/-- Under the deterministic same-tree argument, any extractability failure must
occur in one of the three bad events. -/
theorem extractabilityWin_implies_badEvent {depth : ℕ} [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    : ExtractabilityWin (M := M) (S := S) (C := C) f x →
      BadEvent (M := M) (S := S) (C := C) f x := by
  intro hwin
  by_contra hbad
  have hacc : acceptedOfTranscript (M := M) (S := S) (C := C) f x = true := hwin.1
  have hsame :=
    sameTree_success (M := M) (S := S) (C := C) f x
      (by intro h; exact hbad (.inl h))
      (by intro h; exact hbad (.inr (.inl h)))
      (by intro h; exact hbad (.inr (.inr h)))
      hacc
  rcases hwin.2 with hmsg | hproof
  · exact hmsg hsame.1
  · exact hproof hsame.2

/-- Cached ROM failures imply the cached ROM bad event by applying the
deterministic same-tree theorem to the oracle induced by the final cache. -/
theorem extractabilityWinROM_implies_badEventROM {depth : ℕ} [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (z : ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :
    ExtractabilityWinROM (M := M) (S := S) (C := C) z →
      BadEventROM (M := M) (S := S) (C := C) z := by
  exact extractabilityWin_implies_badEvent
    (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- The selected-witness residual case is impossible unless one of the witness
bad events occurs. -/
theorem witnessExtractabilityWin_implies_badEvent {depth : ℕ}
    [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : WitnessExtractTranscript M S C AUX depth) :
    WitnessExtractabilityWin (M := M) (S := S) (C := C) f x →
      WitnessBadEvent (M := M) (S := S) (C := C) f x := by
  intro hwin
  by_contra hbad
  have hcoll : ¬ CommitCollisionEvent (M := M) (S := S) (C := C) x.base := by
    intro h
    exact hbad (.inl h)
  rcases hwin with ⟨i, hwi, hmismatch, hcheck⟩
  have hcontains :
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            x.base.commitment i.1
            (x.base.opening.message i) (x.base.opening.proof i))).2
        x.base.commitTrace := by
    by_contra hnot
    exact hbad (.inr (.inr ⟨i, hwi, hcheck, hnot⟩))
  have hentry :=
    extract_entry_eq_of_contained_singleTrace
      (M := M) (S := S) (C := C) (AUX := AUX)
      f x.base i.1 (x.base.opening.message i) (x.base.opening.proof i)
      hcoll hcontains hcheck
  rcases hmismatch with hmsg | hproof
  · exact hmsg hentry.1
  · exact (not_authPathMismatch_of_eq (S := S) (C := C) hentry.2) hproof

/-- Cached ROM witness failures imply the corresponding witness bad event. -/
theorem witnessExtractabilityWinROM_implies_badEventROM {depth : ℕ}
    [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :
    WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z →
      WitnessBadEventROM (M := M) (S := S) (C := C) z := by
  exact witnessExtractabilityWin_implies_badEvent
    (M := M) (S := S) (C := C)
    (oracleFnOfCache (M := M) (S := S) (C := C) z.2) z.1

/-- Any probability bound for the textbook bad-event disjunction immediately
bounds the Merkle extractability failure event. This is the probability-level
combiner for the deterministic same-tree theorem. -/
theorem extractability_bound_of_badEvent_bound {depth : ℕ}
    [DecidableEq C] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth))
    (ε : ℝ≥0∞)
    (hbad :
      Pr[ fun x => BadEvent (M := M) (S := S) (C := C) f x | oa] ≤ ε) :
    Pr[ fun x => ExtractabilityWin (M := M) (S := S) (C := C) f x | oa] ≤ ε :=
  le_trans
    (probEvent_mono fun x _ hx =>
      extractabilityWin_implies_badEvent (M := M) (S := S) (C := C) f x hx)
    hbad

/-- Cached ROM combiner: any probability bound for the cached bad event
immediately bounds cached Merkle extractability failures. -/
theorem extractability_bound_of_badEventROM_bound {depth : ℕ}
    [DecidableEq C] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (oa : OracleComp (Oracle M S C)
      (ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)))
    (ε : ℝ≥0∞)
    (hbad :
      Pr[ fun z => BadEventROM (M := M) (S := S) (C := C) z | oa] ≤ ε) :
    Pr[ fun z => ExtractabilityWinROM (M := M) (S := S) (C := C) z | oa] ≤ ε :=
  le_trans
    (probEvent_mono fun z _ hz =>
      extractabilityWinROM_implies_badEventROM (M := M) (S := S) (C := C) z hz)
    hbad

/-- Witness-game ROM combiner: any probability bound for the witness bad event
immediately bounds selected-witness extractability failures. -/
theorem extractability_bound_of_witnessBadEventROM_bound {depth : ℕ}
    [DecidableEq S] [DecidableEq C] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (oa : OracleComp (Oracle M S C)
      (WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)))
    (ε : ℝ≥0∞)
    (hbad :
      Pr[ fun z => WitnessBadEventROM (M := M) (S := S) (C := C) z | oa] ≤ ε) :
    Pr[ fun z => WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z | oa] ≤ ε :=
  le_trans
    (probEvent_mono fun z _ hz =>
      witnessExtractabilityWinROM_implies_badEventROM (M := M) (S := S) (C := C) z hz)
    hbad

/-! ## Witness-game ROM decomposition -/

private noncomputable def extractabilityWitnessCommitPart
    {depth t : ℕ} (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) ((C × AUX) × QueryLog (Oracle M S C)) :=
  (simulateQ loggingOracle A.commit).run

private noncomputable def extractabilityWitnessRest {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (commitment : C) (aux : AUX) (commitTrace : QueryLog (Oracle M S C)) :
    OracleComp (Oracle M S C) (WitnessExtractTranscript M S C AUX depth) := do
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  match selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      pure { base := base, witness? := none, singleCheck? := none }
  | some i =>
      let single ←
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))).run
      pure { base := base, witness? := some i, singleCheck? := some single }

private theorem extractabilityWitnessInner_eq_bind {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityWitnessInner (M := M) (S := S) (C := C) A =
      extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun x =>
        extractabilityWitnessRest (M := M) (S := S) (C := C) A x.1.1 x.1.2 x.2 := by
  rfl

private theorem extractabilityWitnessCommitPart_totalBound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    IsTotalQueryBound
      (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A) A.t₁ := by
  simpa [extractabilityWitnessCommitPart] using
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff A.commit A.t₁).mpr A.commitBound

private theorem extractabilityWitnessRest_totalBound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (commitment : C) (aux : AUX) (commitTrace : QueryLog (Oracle M S C)) :
    IsTotalQueryBound
      (extractabilityWitnessRest (M := M) (S := S) (C := C)
        A commitment aux commitTrace)
      (A.t₂ + (depth + 1)) := by
  unfold extractabilityWitnessRest
  have hopen :
      IsTotalQueryBound ((simulateQ loggingOracle (A.open_ aux)).run) A.t₂ :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff (A.open_ aux) A.t₂).mpr
      (A.openBound aux)
  apply isTotalQueryBound_bind hopen
  intro ⟨opening, openTrace⟩
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  dsimp only
  cases hw : selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      trivial
  | some i =>
      have hsingle :
          IsTotalQueryBound
            ((simulateQ loggingOracle
              (checkSingle (M := M) (S := S) (C := C)
                commitment i.1 (opening.message i) (opening.proof i))).run)
            (depth + 1) :=
        (isTotalQueryBound_run_simulateQ_loggingOracle_iff
          (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))
          (depth + 1)).mpr
          (checkSingle_totalQueryBound (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))
      exact isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 0)
        hsingle (fun _ => trivial)

private theorem oracleRange_card_eq [Fintype C]
    (q : (Oracle M S C).Domain) :
    Fintype.card ((Oracle M S C).Range q) = Fintype.card C := by
  cases q with
  | inl _ => rfl
  | inr _ => rfl

private theorem oracleRange_card_le [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (q : (Oracle M S C).Domain) :
    Fintype.card ((Oracle M S C).Range default) ≤
      Fintype.card ((Oracle M S C).Range q) := by
  rw [oracleRange_card_eq (M := M) (S := S) (C := C) default,
    oracleRange_card_eq (M := M) (S := S) (C := C) q]

private theorem probEvent_cache_has_value_mem_finset_le {α : Type}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (oa : OracleComp (Oracle M S C) α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (targets : Finset C) (cache₀ : QueryCache (Oracle M S C))
    (hno : ¬ CacheHasCollision cache₀) :
    Pr[fun z =>
      ∃ target ∈ targets, ∃ t₀ : (Oracle M S C).Domain,
        ∃ v : (Oracle M S C).Range t₀,
          z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target |
      (simulateQ cachingOracle oa).run cache₀] ≤
      (((n * targets.card : ℕ) : ℝ≥0∞) *
        (Fintype.card C : ℝ≥0∞)⁻¹) := by
  classical
  calc
    Pr[fun z =>
      ∃ target ∈ targets, ∃ t₀ : (Oracle M S C).Domain,
        ∃ v : (Oracle M S C).Range t₀,
          z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target |
      (simulateQ cachingOracle oa).run cache₀]
        ≤ ∑ target ∈ targets,
            Pr[fun z => ∃ t₀ : (Oracle M S C).Domain,
              ∃ v : (Oracle M S C).Range t₀,
                z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target |
              (simulateQ cachingOracle oa).run cache₀] :=
          probEvent_exists_finset_le_sum targets
            ((simulateQ cachingOracle oa).run cache₀)
            (fun target z => ∃ t₀ : (Oracle M S C).Domain,
              ∃ v : (Oracle M S C).Range t₀,
                z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target)
    _ ≤ ∑ target ∈ targets,
            ((n : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) := by
          apply Finset.sum_le_sum
          intro target htarget
          simpa [oracleRange_card_eq (M := M) (S := S) (C := C) default] using
            (OracleComp.probEvent_cache_has_value_le_of_noCollision
              (spec := Oracle M S C) (oa := oa) (n := n) hbound
              (oracleRange_card_le (M := M) (S := S) (C := C))
              target cache₀ hno)
    _ = (((n * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]

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

private def FreshTraceKnownLabelHit {depth : ℕ} [DecidableEq C]
    (commitment : C) (commitTrace : QueryLog (Oracle M S C))
    (cache₁ : QueryCache (Oracle M S C))
    (z : WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) : Prop :=
  ∃ target ∈ traceKnownLabels (M := M) (S := S) (C := C)
      (depth := depth) commitment commitTrace,
    ∃ t₀ : (Oracle M S C).Domain, ∃ v : (Oracle M S C).Range t₀,
      z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v target

private theorem extractedStateOfTrace_eq_extractedStateFromTrace {depth : ℕ}
    [DecidableEq C] (commitment : C) (trace : QueryLog (Oracle M S C)) :
    extractedStateOfTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment trace =
      extractedStateFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment trace := rfl

private theorem traceEntryAnswer_heq
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    HEq entry.2 (traceEntryAnswer (M := M) (S := S) (C := C) entry) := by
  cases entry with
  | mk domain answer =>
      cases domain <;> rfl

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
      traceEntryAnswer_heq (M := M) (S := S) (C := C) entry⟩

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

private lemma run_simulateQ_loggingOracle_query_bind_merkle {α : Type}
    (t : (Oracle M S C).Domain) (mx : (Oracle M S C).Range t → OracleComp (Oracle M S C) α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp (Oracle M S C) _) >>= fun u =>
        (fun p : α × QueryLog (Oracle M S C) =>
          (p.1, (⟨t, u⟩ : (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def, Function.comp]

private theorem logEval_oracleFnOfCache_eq_of_cached_logging {α : Type}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    (oa : OracleComp (Oracle M S C) α)
    {cache₀ cacheFinal : QueryCache (Oracle M S C)}
    {z : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀))
    (hmono : z.2 ≤ cacheFinal) :
    logEval (M := M) (S := S) (C := C)
      (oracleFnOfCache (M := M) (S := S) (C := C) cacheFinal) oa = z.1 := by
  induction oa using OracleComp.inductionOn generalizing z cache₀ cacheFinal with
  | pure x =>
      simp [logEval] at hz
      subst z
      rfl
  | query_bind t mx ih =>
      have hzWhole := hz
      rw [run_simulateQ_loggingOracle_query_bind_merkle] at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨u, cache₁⟩, hquery, hcont⟩
      rw [simulateQ_map] at hcont
      change z ∈ support
        ((fun p : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C) =>
            ((p.1.1,
              (⟨t, u⟩ :
                (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: p.1.2),
              p.2)) <$>
          ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache₁))
        at hcont
      rw [support_map] at hcont
      rcases hcont with ⟨w, hw, hzw⟩
      rcases w with ⟨⟨value, tailLog⟩, cache₂⟩
      have hzEq :
          z = ((value, (⟨t, u⟩ :
              (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: tailLog),
            cache₂) := by
        simpa using hzw.symm
      subst z
      have hmonoTail : cache₂ ≤ cacheFinal := by
        simpa using hmono
      have hentryInCache : cache₂ t = some u := by
        exact
          (OracleComp.log_entry_in_cache_and_mono
            (spec := Oracle M S C) (liftM (query t) >>= mx) cache₀
            ((value,
              (⟨t, u⟩ :
                (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: tailLog),
              cache₂)
            hzWhole).1
            (⟨t, u⟩ :
              (i : (Oracle M S C).Domain) × (Oracle M S C).Range i)
            (by simp)
      have hcacheFinal : cacheFinal t = some u := hmono
        hentryInCache
      have htail :
          logEval (M := M) (S := S) (C := C)
            (oracleFnOfCache (M := M) (S := S) (C := C) cacheFinal) (mx u) =
            (value, tailLog) := by
        exact ih u (z := ((value, tailLog), cache₂)) (cache₀ := cache₁)
          (cacheFinal := cacheFinal) hw hmonoTail
      have hu :
          oracleFnOfCache (M := M) (S := S) (C := C) cacheFinal t = u := by
        simpa using
          oracleFnOfCache_apply_of_some (M := M) (S := S) (C := C)
            (cache := cacheFinal) (t := t) (v := u) hcacheFinal
      simp [logEval_bind, logEval_query, hu, htail]

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
  by_cases hmissingInternal :
      ∃ layer : Fin depth, internalEntry layer ∉ x.commitTrace
  · let missingSet : Finset (Fin depth) :=
      Finset.univ.filter fun layer => internalEntry layer ∉ x.commitTrace
    have hsetNonempty : missingSet.Nonempty := by
      rcases hmissingInternal with ⟨layer, hmissing⟩
      exact ⟨layer, by simp [missingSet, hmissing]⟩
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
  · have hallInternal :
        ∀ layer : Fin depth, internalEntry layer ∈ x.commitTrace := by
      intro layer
      by_contra hnot
      exact hmissingInternal ⟨layer, hnot⟩
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
  have hzBaseCommitment : z.1.base.commitment = commitment := by
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
        rfl
    | some j =>
        rw [hselect] at hz
        rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
        simp only [Set.mem_iUnion] at hz
        rcases hz with ⟨⟨single, cache₃⟩, hsingle, hzpure⟩
        simp [base] at hzpure
        subst z
        rfl
  have hzBaseTrace : z.1.base.commitTrace = commitTrace := by
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
        rfl
    | some j =>
        rw [hselect] at hz
        rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
        simp only [Set.mem_iUnion] at hz
        rcases hz with ⟨⟨single, cache₃⟩, hsingle, hzpure⟩
        simp [base] at hzpure
        subst z
        rfl
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
    simpa [hzBaseTrace] using hnotCommitBase
  have htarget :
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace := by
    simpa [hzBaseCommitment, hzBaseTrace] using htargetBase
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

private theorem rest_support_base_fields {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
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

private lemma sum_update_succ_count {ι : Type} [Fintype ι] [DecidableEq ι]
    (counts : ι → ℕ) (i : ι) :
    ∑ j : ι, Function.update counts i (counts i + 1) j =
      (∑ j : ι, counts j) + 1 := by
  classical
  calc
    ∑ j : ι, Function.update counts i (counts i + 1) j =
        Function.update counts i (counts i + 1) i +
          Finset.sum (Finset.univ.erase i)
            (fun j : ι => Function.update counts i (counts i + 1) j) := by
          symm
          exact Finset.univ.add_sum_erase
            (f := fun j : ι => Function.update counts i (counts i + 1) j)
            (Finset.mem_univ i)
    _ = counts i + 1 + Finset.sum (Finset.univ.erase i) (fun j : ι => counts j) := by
          simp only [Function.update_self]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    _ = counts i + Finset.sum (Finset.univ.erase i) (fun j : ι => counts j) + 1 := by
          omega
    _ = (∑ j : ι, counts j) + 1 := by
          rw [← Finset.univ.add_sum_erase (f := fun j : ι => counts j) (Finset.mem_univ i)]

private lemma log_length_le_of_mem_support_counting_simulate_run_logging
    {α : Type} [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (oa : OracleComp (Oracle M S C) α)
    {z : (α × QueryLog (Oracle M S C)) × QueryCount (Oracle M S C).Domain}
    (hz : z ∈ support (countingOracle.simulate
      (spec := Oracle M S C) ((simulateQ loggingOracle oa).run) 0)) :
    z.1.2.length ≤ ∑ q : (Oracle M S C).Domain, z.2 q := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x =>
      have hz' :
          z ∈ support
            (countingOracle.simulate (spec := Oracle M S C)
              (ι := (Oracle M S C).Domain)
              (pure (x, ([] : QueryLog (Oracle M S C)))) 0) := by
        simpa [simulateQ_pure] using hz
      rw [countingOracle.mem_support_simulate_pure_iff
        (spec := Oracle M S C) (ι := (Oracle M S C).Domain)] at hz'
      subst z
      simp
  | query_bind t mx ih =>
      rw [run_simulateQ_loggingOracle_query_bind_merkle] at hz
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz⟩ := hz
      have hmap :
          countingOracle.simulate
            (((fun p : α × QueryLog (Oracle M S C) =>
                (p.1,
                  (⟨t, u⟩ :
                    (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) 0 =
            (fun zz : (α × QueryLog (Oracle M S C)) × QueryCount (Oracle M S C).Domain =>
              ((zz.1.1,
                  (⟨t, u⟩ :
                    (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: zz.1.2),
                zz.2)) <$>
              countingOracle.simulate
                (spec := Oracle M S C) ((simulateQ loggingOracle (mx u)).run) 0 := by
        simp [countingOracle.simulate, Prod.map, simulateQ_map]
      rw [hmap, support_map] at hz
      obtain ⟨w, hzu, hzEq⟩ := hz
      rcases w with ⟨⟨zu, logu⟩, qcu⟩
      have hz1 :
          (zu,
            (⟨t, u⟩ :
              (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: logu) = z.1 := by
        simpa using congrArg Prod.fst hzEq
      have hzlog :
          (⟨t, u⟩ :
            (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: logu = z.1.2 := by
        simpa using congrArg Prod.snd hz1
      have hzqc : qcu = Function.update z.2 t (z.2 t - 1) := by
        simpa using congrArg Prod.snd hzEq
      have hlen : logu.length ≤ ∑ q : (Oracle M S C).Domain, qcu q :=
        ih u (z := ((zu, logu), qcu)) hzu
      have hsum :
          ∑ q : (Oracle M S C).Domain, Function.update z.2 t (z.2 t - 1) q =
            (∑ q : (Oracle M S C).Domain, z.2 q) - 1 := by
        let qpred : QueryCount (Oracle M S C).Domain :=
          Function.update z.2 t (z.2 t - 1)
        have hpredsucc : Function.update qpred t (qpred t + 1) = z.2 := by
          funext j
          by_cases hj : j = t
          · subst hj
            simp [qpred]
            omega
          · simp [qpred, Function.update, hj]
        have hsumsucc := sum_update_succ_count (counts := qpred) t
        rw [hpredsucc] at hsumsucc
        dsimp [qpred] at hsumsucc
        omega
      rw [hzqc, hsum] at hlen
      have hsumpos : 0 < ∑ q : (Oracle M S C).Domain, z.2 q := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      have hcons :
          ((⟨t, u⟩ :
            (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: logu).length
              ≤ ∑ q : (Oracle M S C).Domain, z.2 q := by
        have hlt : logu.length < ∑ q : (Oracle M S C).Domain, z.2 q :=
          lt_of_le_of_lt hlen (Nat.sub_lt hsumpos (by simp))
        simpa using Nat.succ_le_of_lt hlt
      simpa [hzlog] using hcons

private lemma log_length_le_of_mem_support_run_cached_logging
    {α : Type} [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {oa : OracleComp (Oracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (cache₀ : QueryCache (Oracle M S C))
    {z : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)) :
    z.1.2.length ≤ n := by
  let cost : QueryCache (Oracle M S C) → ℕ := fun _ => 0
  have hstep :
      ∀ t : (Oracle M S C).Domain, ∀ st : QueryCache (Oracle M S C),
        ∀ x : (Oracle M S C).Range t × QueryCache (Oracle M S C),
          x ∈ support ((cachingOracle (spec := Oracle M S C) t).run st) →
            cost x.2 ≤ cost st + 1 := by
    intro t st x hx
    simp [cost]
  rcases countingOracle.exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
      (spec := Oracle M S C)
      (ι := (Oracle M S C).Domain)
      (impl := cachingOracle)
      cost hstep hz with ⟨qc, hqc, _⟩
  have hlen :
      z.1.2.length ≤ ∑ q : (Oracle M S C).Domain, qc q :=
    log_length_le_of_mem_support_counting_simulate_run_logging
      (M := M) (S := S) (C := C) oa hqc
  have hboundLog :
      IsTotalQueryBound ((simulateQ loggingOracle oa).run) n :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff
      (spec := Oracle M S C) oa n).2 hbound
  have hqc_le : (∑ q : (Oracle M S C).Domain, qc q) ≤ n :=
    IsTotalQueryBound.counting_total_le
      (spec := Oracle M S C)
      (ι := (Oracle M S C).Domain)
      (oa := (simulateQ loggingOracle oa).run)
      (n := n)
      hboundLog hqc
  exact le_trans hlen hqc_le

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
    log_length_le_of_mem_support_run_cached_logging
      (M := M) (S := S) (C := C)
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
      ((((A.t₂ + depth + 1) * extractabilityCountingTerm depth A.t₁ : ℕ) : ℝ≥0∞) *
        (Fintype.card C : ℝ≥0∞)⁻¹) := by
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
        ((((A.t₂ + (depth + 1)) * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
    simpa [FreshTraceKnownLabelHit, targets, rest] using
      probEvent_cache_has_value_mem_finset_le
        (M := M) (S := S) (C := C)
        (oa := rest) (n := A.t₂ + (depth + 1))
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
    _ ≤ ((((A.t₂ + (depth + 1)) * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := hfresh
    _ ≤ ((((A.t₂ + depth + 1) * extractabilityCountingTerm depth A.t₁ : ℕ) :
          ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
        have hnat :
            (A.t₂ + (depth + 1)) * targets.card ≤
              (A.t₂ + depth + 1) * extractabilityCountingTerm depth A.t₁ := by
          have hsum : A.t₂ + (depth + 1) = A.t₂ + depth + 1 := by omega
          rw [hsum]
          exact Nat.mul_le_mul_left _ htargets
        exact mul_le_mul_right' (by exact_mod_cast hnat) _

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
  let commitPart :=
    extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A
  let restPart :=
    fun x : ((C × AUX) × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C) =>
      (simulateQ cachingOracle
        (extractabilityWitnessRest (M := M) (S := S) (C := C)
          A x.1.1.1 x.1.1.2 x.1.2)).run x.2
  let ε₁ : ℝ≥0∞ :=
    ((A.t₁ ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)
  let ε₂ : ℝ≥0∞ :=
    ((((A.t₂ + depth + 1) * extractabilityCountingTerm depth A.t₁ : ℕ) :
      ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹)
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [oracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hcommit :
      Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
        (simulateQ cachingOracle commitPart).run ∅] ≤ ε₁ := by
    have hbirthday :=
      probEvent_cacheCollision_le_birthday_total
        (spec := Oracle M S C)
        (oa := commitPart)
        A.t₁
        (by
          simpa [commitPart] using
            extractabilityWitnessCommitPart_totalBound
              (M := M) (S := S) (C := C) A)
        hCdefault
        (oracleRange_card_le (M := M) (S := S) (C := C))
    simpa [ε₁, oracleRange_card_eq (M := M) (S := S) (C := C) default,
      not_not] using hbirthday
  have hrest :
      ∀ x ∈ support ((simulateQ cachingOracle commitPart).run ∅),
        ¬ CacheHasCollision x.2 →
          Pr[fun z => ¬
              (¬ WitnessBadEventROM (M := M) (S := S) (C := C) z) |
            restPart x] ≤ ε₂ := by
    intro x hx hno
    rcases x with ⟨⟨⟨commitment, aux⟩, commitTrace⟩, cache₁⟩
    have hbound :=
      witnessBadEventROM_rest_bound
        (M := M) (S := S) (C := C)
        A (commitment := commitment) (aux := aux)
        (commitTrace := commitTrace) (cache₁ := cache₁)
        (by simpa [commitPart] using hx) hno
    simpa [restPart, ε₂, not_not] using hbound
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
  simpa [commitPart, restPart, ε₁, ε₂, extractabilityErrorTerm, not_not] using hcombine

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
ROM game. The verifier contribution is one single authentication path, hence the
`depth + 1` term in `extractabilityErrorTerm`. -/
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

This is intentionally named as a conditional helper: the final ROM theorem
should prove the bad-event estimate for `extractabilityGame` directly. -/
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
