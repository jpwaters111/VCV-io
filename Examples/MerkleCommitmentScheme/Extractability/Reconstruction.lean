/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Extractability.Basic

/-!
# Merkle Commitment Scheme — Extractability Reconstruction

Deterministic reconstruction layer for Merkle extractability.

This file proves the "same-tree" part of the textbook argument: if an accepted
honest verifier trace is contained in the commit trace and the commit trace has
no random-oracle collision, then the extractor's filled tree agrees with the
later accepted opening on every opened index.

The proofs here are fixed-oracle/state facts, not probability bounds. The
probability layer shows that the assumptions fail only with the advertised ROM
error terms.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- Expand the extractability win predicate into acceptance plus mismatch of
the extracted batch opening.

This is an `Iff.rfl` theorem so later proofs can rewrite the game event without
unfolding all surrounding definitions manually. -/
theorem extractabilityWin_iff [DecidableEq C] {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth) :
    ExtractabilityWin (M := M) (S := S) (C := C) f x ↔
      acceptedOfTranscript (M := M) (S := S) (C := C) f x = true ∧
        (Subvector.ofVector (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).1
            x.opening.I ≠ x.opening.message ∨
          «open» (S := S) (C := C)
              (extractedOutputOfTranscript (M := M) (S := S) (C := C) x).2 x.opening.I
            ≠ x.opening.proof) := Iff.rfl

/-- If the honest verifier rejects, the transcript cannot be an extractability
win. -/
theorem not_extractabilityWin_of_accepted_false [DecidableEq C] {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (hacc : acceptedOfTranscript (M := M) (S := S) (C := C) f x = false) :
    ¬ ExtractabilityWin (M := M) (S := S) (C := C) f x := by
  rintro ⟨htrue, _⟩
  simp [hacc] at htrue

/-- No honest-trace escape plus acceptance means the honest verifier log is
contained in the commit trace. -/
private theorem honestTrace_subset_of_not_escape [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (x : ExtractTranscript M S C AUX depth)
    (hsubset : ¬ HonestTraceEscapeEvent (M := M) (S := S) (C := C) f x)
    (hacc : acceptedOfTranscript (M := M) (S := S) (C := C) f x = true) :
    LogContains (honestTraceOfTranscript (M := M) (S := S) (C := C) f x) x.commitTrace := by
  by_contra hnot
  exact hsubset ⟨hacc, hnot⟩

/-- Batch-log containment gives containment of each constituent selected
`checkSingle` trace. -/
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

/-- In a collision-free commit trace, two leaf queries with the same answer
must have the same `(message, salt)` input. -/
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

/-- In a collision-free commit trace, two internal-node queries with the same
answer must have the same `(left, right)` input pair. -/
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

/-- A contained accepted single-check trace contributes its leaf-query entry to
the commit trace. -/
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

/-- A contained accepted single-check trace contributes each internal-query
entry on the checked path to the commit trace. -/
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

/-
The following path-position lemmas connect the verifier's top-down path view
with the extractor's partial tree coordinates. They are arithmetic only: a path
node at layer `layer + 1` has parent `pathPos idx layer`, and its sibling is
the corresponding `siblingPos`.
-/

/-- The parent of the path position at layer `layer + 1` is the path position
at layer `layer`. -/
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

/-- If the child path position is even, it is the left child of the parent path
position. -/
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

/-- If the child path position is even, its sibling is the right child of the
same parent. -/
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

/-- If the child path position is odd, its sibling is the left child of the
same parent. -/
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

/-- If the child path position is odd, it is the right child of the parent path
position. -/
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

/-- Fixed-oracle evaluation of `recomputeRootAux` as pure hashing. -/
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

/-- Fixed-oracle evaluation of `recomputeRootSingle` as pure leaf-plus-path
hashing. -/
private theorem eval_recomputeRootSingle_eq_withHash (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath) =
      recomputeRootSingleWithHash
        (fun x => f (Sum.inl x))
        (fun x => f (Sum.inr x))
        idx message authPath := by
  rw [recomputeRootSingle, eval_bind]
  simp [recomputeRootSingleWithHash, eval_recomputeRootAux_eq_withHash]

/-- At the root layer, the local index is the original leaf index modulo the
whole tree width, hence exactly `idx`. -/
private theorem localIndex_root_eq {depth : ℕ} (idx : Index depth) :
    localIndex idx ⟨0, Nat.succ_pos _⟩ = idx := by
  apply Fin.ext
  simp [localIndex, Nat.mod_eq_of_lt idx.2]

/-- If a single check accepts, the verifier's computed root path label equals
the commitment. -/
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

/-- Recomputing with an empty sibling vector returns the current label. -/
private theorem recomputeRootAuxWithHash_eq_current_of_length_zero {n : ℕ}
    (nodeHash : C × C → C) (idx : Fin (2 ^ n)) (current : C)
    (siblings : Vector C n) (hn : n = 0) :
    recomputeRootAuxWithHash nodeHash idx current siblings = current := by
  subst hn
  simp [recomputeRootAuxWithHash]

/-- The verifier's leaf-layer path label is the leaf-query answer. -/
theorem checkPathLabel_leaf_eq_leafQuery (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    checkPathLabel f idx message authPath (Fin.last depth) =
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath) := by
  unfold checkPathLabel recomputeRootSingleWithHash checkLeafQuery
  apply recomputeRootAuxWithHash_eq_current_of_length_zero
  simp

/-- Prefix reconstruction theorem for path labels.

If the commit trace contains all internal verifier queries above a layer, then
after that many closure passes the partial tree knows the path label at the
layer. This is the induction engine behind `sameTree_success`. -/
theorem path_label_known_after_passes_of_internal_prefix {depth : ℕ} [DecidableEq C]
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

/-- Final path-label reconstruction from a contained single-check trace.

The prefix theorem needs explicit internal-query membership assumptions; this
wrapper obtains those memberships from log containment of the whole
`checkSingle` trace. -/
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

/-- Final copath-label reconstruction from a contained single-check trace.

For every layer, the extractor's closed partial tree knows the sibling label
used by the accepted authentication path. -/
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

/-
The next three lemmas reconcile ordering conventions. `AuthPath.siblings` is
bottom-up, while `copathLabel` addresses layers top-down. Reversing
`openSiblings` gives the top-down copath order used by the extractor proof.
-/

/-- Indexing formula for a reversed vector. -/
private theorem vector_reverse_get {α : Type} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.reverse.get i = v.get ⟨n - 1 - i.1, by omega⟩ := by
  change v.reverse[i.1] = v[n - 1 - i.1]
  rw [show v.reverse = Vector.mk v.toArray.reverse (by simp) by rfl]
  rw [Vector.getElem_mk]
  rw [Array.getElem_reverse]
  rw [Vector.getElem_toArray]
  simp

/-- Top-down view of `openSiblings`: the sibling for layer `layer` is stored at
bottom-up position `depth - 1 - layer`. -/
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

/-- Reversing `openSiblings` aligns it exactly with top-down copath labels. -/
private theorem openSiblings_reverse_get {depth : ℕ} (labels : Labels C depth)
    (idx : Index depth) (layer : Fin depth) :
    (openSiblings labels idx).reverse.get layer =
      (labels ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).get (siblingPos idx layer) := by
  rw [vector_reverse_get]
  exact openSiblings_get_from_top labels idx layer

/-- Reconstruct an `openSingle` authentication path from its salt and all
top-down copath labels. -/
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

/-- Final leaf-opening reconstruction.

If a contained accepted single-check trace is collision-free with respect to
the commit trace, then `populateLeavesFromTrace` records the exact
`(message, salt)` pair at the checked leaf. -/
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

/-- A contained accepted single-check trace forces `extract` to take the real
`fillMissing` branch rather than the default fallback branch.

For depth `0`, the contained leaf query supplies the commitment answer. For
positive depth, the top internal query supplies the commitment answer. -/
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

/-- Pointwise extraction correctness for one contained accepted single-check
trace.

The extracted message at `idx` equals the adversary's opened message, and
opening the extracted trapdoor at `idx` reproduces the adversary's auth path.
This is the local statement used twice by `sameTree_success`, once for messages
and once for proofs. -/
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
textbook extractability proof.

Assumptions:
* no commit-trace collision;
* no extractor-state change;
* no honest-trace escape;
* the honest verifier accepted.

Conclusion: the extractor's restricted message vector and reopened proof family
match the accepted adversary opening. The proof is pointwise: each opened index
has a contained accepted `checkSingle` trace, so `extract_entry_eq_of_contained_singleTrace`
reconstructs that one leaf and auth path. -/
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

end MerkleTree
