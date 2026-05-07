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
          x.commitment idx message authPath) = true) :
    ∀ (layer : ℕ) (hlayer : layer < depth + 1),
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) x.commitment x.commitTrace layer ⟨layer, hlayer⟩).get
          (pathPos idx ⟨layer, hlayer⟩) =
        some (checkPathLabel f idx message authPath ⟨layer, hlayer⟩)
  | 0, hlayer => by
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
  | Nat.succ layer, hlayer => by
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
        path_label_known_after_passes
          f x idx message authPath hcoll hcontains hcheck layer parentLayer.2
      have hentry :=
        single_trace_internal_entry_in_commitTrace
          (M := M) (S := S) (C := C)
          f x.commitment idx message authPath x.commitTrace internalLayer hcontains
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

end MerkleTree
