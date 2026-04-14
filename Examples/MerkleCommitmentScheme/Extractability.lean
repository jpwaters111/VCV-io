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
def extractedOutputOfTranscript {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (x : ExtractTranscript M S C AUX depth) :
    Leaves M depth × Trapdoor S C depth :=
  extractedOutputOfTrace (M := M) (S := S) (C := C) (depth := depth)
    x.commitment x.commitTrace

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

/-- The inner two-phase extractability experiment prior to running under
`cachingOracle`. -/
noncomputable def extractabilityInner {depth t : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
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

/-- The Merkle extractability game run with a shared cache. -/
noncomputable def extractabilityGame {depth t : ℕ} [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (ExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle (extractabilityInner (M := M) (S := S) (C := C) A)).run ∅

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

@[simp] theorem extractabilityGame_eq {depth t : ℕ} [DecidableEq C] [DecidableEq M] [DecidableEq S]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityGame (M := M) (S := S) (C := C) A =
      (simulateQ cachingOracle (extractabilityInner (M := M) (S := S) (C := C) A)).run ∅ := rfl

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
  sorry

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

end MerkleTree
