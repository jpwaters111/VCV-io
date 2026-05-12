/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support
import Mathlib.Data.Array.Extract

/-!
# Merkle Commitment Scheme — Completeness

Fixed-oracle completeness for the `MerkleTree` construction.

This file proves the deterministic theorem chain used before any probability
reasoning:

* the executable oracle computations agree with the functional
  `WithHash` shadows under a fixed oracle `f`;
* an honest `openSingle` path recomputes the root stored by `buildTree`;
* if every selected single opening verifies, then the batch verifier accepts;
* therefore `commitWithSalts`, `open`, and `check` compose correctly for every
  fixed oracle.

There are no security bounds here. These lemmas justify the honest branch used
by binding and extractability games.
-/

open OracleComp OracleSpec

namespace MerkleTree

variable {M S C α : Type}

/-
Simulation lemmas: replace each executable `OracleComp` Merkle algorithm by its
pure functional shadow after fixing the oracle function `f`. This lets the
main completeness proof reason about vectors and labels instead of monadic
binds.
-/

/-- Tail indexing for the vector recursion used by `mapFinM` and
`openSiblings`. -/
private theorem vector_tail_get {α : Type} {n : ℕ} (v : Vector α (n + 1)) (i : Fin n) :
    v.tail.get i = v.get i.succ := by
  have hsize : (v.toArray.extract 1 (n + 1)).size = n := by
    simp [Array.size_extract]
  change (Vector.mk (v.toArray.extract 1 (n + 1)) hsize).get i = v.get i.succ
  change (v.toArray.extract 1 (n + 1))[i.1] = v.toArray[i.1 + 1]
  rw [Array.getElem_extract]
  · rw [Vector.getElem_toArray, Vector.getElem_toArray]
    simp [Nat.add_comm]

/-- Fixed-oracle simulation of proof-oriented indexed vector traversal. -/
private theorem simulate_mapFinM_eq {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec Id) :
    {n : ℕ} → (f : Fin n → OracleComp spec α) →
      simulateQ impl (mapFinM f) = Vector.ofFn (fun i => simulateQ impl (f i))
  | 0, _ => by
      apply Vector.ext
      intro i hi
      omega
  | Nat.succ n, f => by
      rw [mapFinM, simulateQ_bind]
      simp [simulateQ_bind]
      rw [simulate_mapFinM_eq (impl := impl) (f := fun i => f i.succ)]
      change
        Id.run
            (do
              let x ← simulateQ impl (f 0)
              (fun a =>
                    Vector.ofFn fun x_1 =>
                      match x_1 with
                      | ⟨0, _⟩ => x
                      | ⟨Nat.succ i, hi⟩ => a.get ⟨i, Nat.lt_of_succ_lt_succ hi⟩) <$>
                  Vector.ofFn (fun i => simulateQ impl (f i.succ))) =
          Vector.ofFn (fun i => simulateQ impl (f i))
      apply Vector.ext
      intro i hi
      cases i with
      | zero =>
          simp [Id.run, Id.instMonad, Functor.map, Vector.getElem_ofFn]
      | succ j =>
          simp [Id.run, Id.instMonad, Functor.map, Vector.getElem_ofFn]

/-- `buildLeafLayer` under oracle `f` is the pure leaf-hash layer. -/
private theorem simulate_buildLeafLayer_eq (f : OracleFn M S C) :
    {depth : ℕ} → (messages : Leaves M depth) → (salts : Leaves S depth) →
      eval f (buildLeafLayer (M := M) (S := S) (C := C) messages salts) =
        buildLeafLayerWithHash (fun x => f (Sum.inl x)) messages salts
  | _, messages, salts => by
      simpa [buildLeafLayer, buildLeafLayerWithHash, eval] using
        simulate_mapFinM_eq (α := C) (spec := Oracle M S C) (impl := QueryImpl.ofFn f)
          (f := fun i =>
            leafCommit (M := M) (S := S) (C := C) (messages.get i) (salts.get i))

/-- `buildLayer` under oracle `f` is the pure internal-node hash layer. -/
private theorem simulate_buildLayer_eq (f : OracleFn M S C) :
    {depth : ℕ} → (children : LayerVector C (depth + 1)) →
      eval f (buildLayer (M := M) (S := S) (C := C) children) =
        buildLayerWithHash (fun x => f (Sum.inr x)) children
  | _, children => by
      simpa [buildLayer, buildLayerWithHash, eval] using
        simulate_mapFinM_eq (α := C) (spec := Oracle M S C) (impl := QueryImpl.ofFn f)
          (f := fun i =>
            nodeCommit (C := C)
              (children.get (leftChildPos i))
              (children.get (rightChildPos i)))

/-- `buildLabels` under oracle `f` is the pure bottom-up label tree. -/
private theorem simulate_buildLabels_eq (f : OracleFn M S C) :
    {depth : ℕ} → (leaves : LayerVector C depth) →
      eval f (buildLabels (M := M) (S := S) (C := C) leaves) =
        buildLabelsWithHash (fun x => f (Sum.inr x)) leaves
  | 0, _ => by
      rfl
  | Nat.succ _, leaves => by
      simp [buildLabels, buildLabelsWithHash, eval_bind,
        simulate_buildLayer_eq, simulate_buildLabels_eq]

/-- `buildTree` under oracle `f` is the pure tree built from leaf and node
hashes derived from `f`. -/
private theorem simulate_buildTree_eq (f : OracleFn M S C) :
    {depth : ℕ} → (messages : Leaves M depth) → (salts : Leaves S depth) →
      eval f (buildTree (M := M) (S := S) (C := C) messages salts) =
        buildTreeWithHash (fun x => f (Sum.inl x)) (fun x => f (Sum.inr x)) messages salts
  | _, messages, salts => by
      simp [buildTree, buildTreeWithHash, eval_bind,
        simulate_buildLeafLayer_eq, simulate_buildLabels_eq]

/-- `recomputeRootAux` under oracle `f` is the pure bottom-up recomputation
using the internal-node hash derived from `f`. -/
private theorem simulate_recomputeRootAux_eq (f : OracleFn M S C) :
    {depth : ℕ} → (idx : Index depth) → (current : C) → (siblings : Vector C depth) →
      eval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
        recomputeRootAuxWithHash (fun x => f (Sum.inr x)) idx current siblings
  | 0, _, _, _ => by
      simp [recomputeRootAux, recomputeRootAuxWithHash]
  | Nat.succ _, idx, current, siblings => by
      by_cases hparity : idx.1 % 2 = 0
      · simp [recomputeRootAux, recomputeRootAuxWithHash, eval_bind,
          hparity, simulate_recomputeRootAux_eq]
      · simp [recomputeRootAux, recomputeRootAuxWithHash, eval_bind,
          hparity, simulate_recomputeRootAux_eq]

/-- `recomputeRootSingle` under oracle `f` is the pure leaf-plus-path
recomputation. -/
private theorem simulate_recomputeRootSingle_eq (f : OracleFn M S C) :
    {depth : ℕ} → (idx : Index depth) → (message : M) → (authPath : AuthPath S C depth) →
      eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath) =
        recomputeRootSingleWithHash
          (fun x => f (Sum.inl x))
          (fun x => f (Sum.inr x))
          idx message authPath
  | _, idx, message, authPath => by
      rw [recomputeRootSingle, eval_bind]
      simp [recomputeRootSingleWithHash, simulate_recomputeRootAux_eq]

/-
Functional path correctness. `openSiblings` returns siblings from leaf to root,
which is exactly the order consumed by `recomputeRootAuxWithHash`.
-/

/-- The first opened sibling is the sibling of the leaf-level index. -/
private theorem openSiblings_head_eq {depth : ℕ} (nodeHash : C × C → C)
    (leaves : LayerVector C (depth + 1)) (idx : Index (depth + 1)) :
    (openSiblings (buildLabelsWithHash nodeHash leaves) idx).head = leaves.get (siblingIndex idx) := by
  simp [openSiblings, buildLabelsWithHash, Vector.head]

/-- After removing the first sibling, the remaining path is the parent path in
the parent label tree. -/
private theorem openSiblings_tail_eq {depth : ℕ} (nodeHash : C × C → C)
    (leaves : LayerVector C (depth + 1)) (idx : Index (depth + 1)) :
    Vector.cast (by omega) ((openSiblings (buildLabelsWithHash nodeHash leaves) idx).extract 1) =
      openSiblings (buildLabelsWithHash nodeHash (buildLayerWithHash nodeHash leaves)) (parentPos idx) := by
  apply Vector.ext
  intro i hi
  change (Vector.cast (by omega) ((openSiblings (buildLabelsWithHash nodeHash leaves) idx).extract 1)).get
      ⟨i, hi⟩ =
    (openSiblings (buildLabelsWithHash nodeHash (buildLayerWithHash nodeHash leaves)) (parentPos idx)).get
      ⟨i, hi⟩
  rw [show Vector.cast (by omega) ((openSiblings (buildLabelsWithHash nodeHash leaves) idx).extract 1) =
      (openSiblings (buildLabelsWithHash nodeHash leaves) idx).tail by rfl]
  rw [vector_tail_get]
  simp [openSiblings, buildLabelsWithHash]

/-- Pure functional correctness of Merkle authentication paths.

Starting at a leaf label and consuming the siblings returned by `openSiblings`
reconstructs the root of the labels tree. -/
private theorem recomputeRootAuxWithHash_buildLabels_eq (nodeHash : C × C → C) :
    {depth : ℕ} → (leaves : LayerVector C depth) → (idx : Index depth) →
      recomputeRootAuxWithHash nodeHash idx (leaves.get idx)
        (openSiblings (buildLabelsWithHash nodeHash leaves) idx) =
          (buildLabelsWithHash nodeHash leaves).root
  | 0, leaves, idx => by
      have hidx : idx = 0 := by
        apply Fin.ext
        omega
      subst hidx
      change leaves.get 0 = leaves[0]
      rfl
  | Nat.succ _, leaves, idx => by
      let parents := buildLayerWithHash nodeHash leaves
      have hhead := openSiblings_head_eq nodeHash leaves idx
      have htail := openSiblings_tail_eq nodeHash leaves idx
      by_cases hparity : idx.1 % 2 = 0
      · have hparent :
            parents.get (parentPos idx) =
              nodeHash (leaves.get idx, leaves.get (siblingIndex idx)) := by
          simpa [parents, buildLayerWithHash, hparity,
            leftChildPos_parentPos_of_even, rightChildPos_parentPos_of_even]
        rw [recomputeRootAuxWithHash]
        simp [hparity, hhead]
        change
          recomputeRootAuxWithHash nodeHash (parentPos idx)
              (nodeHash (leaves.get idx, leaves.get (siblingIndex idx)))
              (Vector.cast (by omega) ((openSiblings (buildLabelsWithHash nodeHash leaves) idx).extract 1)) =
            (buildLabelsWithHash nodeHash leaves).root
        rw [htail, ← hparent]
        simpa [parents] using
          recomputeRootAuxWithHash_buildLabels_eq nodeHash parents (parentPos idx)
      · have hodd : idx.1 % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one idx.1 with h0 | h1
          · contradiction
          · exact h1
        have hparent :
            parents.get (parentPos idx) =
              nodeHash (leaves.get (siblingIndex idx), leaves.get idx) := by
          simpa [parents, buildLayerWithHash, hodd,
            leftChildPos_parentPos_of_odd, rightChildPos_parentPos_of_odd]
        rw [recomputeRootAuxWithHash]
        simp [hparity, hhead]
        change
          recomputeRootAuxWithHash nodeHash (parentPos idx)
              (nodeHash (leaves.get (siblingIndex idx), leaves.get idx))
              (Vector.cast (by omega) ((openSiblings (buildLabelsWithHash nodeHash leaves) idx).extract 1)) =
            (buildLabelsWithHash nodeHash leaves).root
        rw [htail, ← hparent]
        simpa [parents] using
          recomputeRootAuxWithHash_buildLabels_eq nodeHash parents (parentPos idx)

/-- Fixed-oracle simulation of honest deterministic commitment with supplied
salts. -/
private theorem simulate_commitWithSalts_eq (f : OracleFn M S C) {depth : ℕ}
    (messages : Leaves M depth) (salts : Leaves S depth) :
    eval f (commitWithSalts (M := M) (S := S) (C := C) messages salts) =
      let labels := buildTreeWithHash
        (fun x => f (Sum.inl x))
        (fun x => f (Sum.inr x))
        messages salts
      (labels.root, ⟨salts, labels⟩) := by
  simp [commitWithSalts, eval_bind, eval_pure, simulate_buildTree_eq]

/-- Pure honest single-opening completeness.

For the functional `WithHash` tree, opening one leaf and recomputing its root
returns exactly the tree root. -/
theorem recomputeRootSingleWithHash_openSingle_eq_root {depth : ℕ}
    (leafHash : M × S → C) (nodeHash : C × C → C)
    (messages : Leaves M depth) (salts : Leaves S depth) (idx : Index depth) :
    let labels := buildTreeWithHash leafHash nodeHash messages salts
    recomputeRootSingleWithHash leafHash nodeHash idx (messages.get idx)
      (openSingle ⟨salts, labels⟩ idx) = labels.root := by
  simpa [buildTreeWithHash, recomputeRootSingleWithHash, buildLeafLayerWithHash, openSingle] using
    recomputeRootAuxWithHash_buildLabels_eq (C := C) nodeHash
      (buildLeafLayerWithHash leafHash messages salts) idx

/-- Fixed-oracle honest single-opening completeness for the executable
recomputation. -/
theorem recomputeRootSingle_openSingle_eq_root {depth : ℕ} (f : OracleFn M S C)
    (messages : Leaves M depth) (salts : Leaves S depth) (idx : Index depth) :
    let labels := eval f (buildTree (M := M) (S := S) (C := C) messages salts)
    eval f
      (recomputeRootSingle (M := M) (S := S) (C := C)
        idx (messages.get idx) (openSingle ⟨salts, labels⟩ idx)) = labels.root := by
  dsimp
  rw [simulate_recomputeRootSingle_eq, simulate_buildTree_eq]
  simpa using
    recomputeRootSingleWithHash_openSingle_eq_root
      (M := M) (S := S) (C := C)
      (fun x => f (Sum.inl x))
      (fun x => f (Sum.inr x))
      messages salts idx

/-- Honest `openSingle` is accepted by `checkSingle` under any fixed oracle. -/
theorem checkSingle_openSingle_eq_true [DecidableEq C] {depth : ℕ} (f : OracleFn M S C)
    (messages : Leaves M depth) (salts : Leaves S depth) (idx : Index depth) :
    let labels := eval f (buildTree (M := M) (S := S) (C := C) messages salts)
    eval f
      (checkSingle (M := M) (S := S) (C := C)
        labels.root idx (messages.get idx) (openSingle ⟨salts, labels⟩ idx)) = true := by
  rw [eval_checkSingle_eq_true_iff]
  simpa using
    recomputeRootSingle_openSingle_eq_root (M := M) (S := S) (C := C) f messages salts idx

/-- If every listed single check accepts, the auxiliary batch checker returns
a list of `true` values of the same length. -/
theorem checkEntriesAux_eq_replicate_true_of_all_single [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) {I : IndexSet depth} (commitment : C)
    (message : Subvector M I) (proof : Proof S C I) :
    ∀ xs : List {i // i ∈ I},
      (∀ i, i ∈ xs →
        eval f (checkSingle (M := M) (S := S) (C := C)
          commitment i.1 (message i) (proof i)) = true) →
      eval f (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs) =
        List.replicate xs.length true
  | [], _ => by
      simp [checkEntriesAux]
  | i :: xs, hsingle => by
      rw [checkEntriesAux, eval_bind, eval_bind]
      have hi :
          eval f (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (message i) (proof i)) = true :=
        hsingle i (by simp)
      rw [hi]
      have hrest :
          eval f (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs) =
            List.replicate xs.length true := by
        apply checkEntriesAux_eq_replicate_true_of_all_single
        intro j hj
        exact hsingle j (List.mem_cons_of_mem _ hj)
      rw [hrest]
      simp [List.replicate]

/-- If every selected single check accepts, `checkEntries` returns
`I.card` copies of `true`. -/
theorem checkEntries_eq_replicate_true_of_all_single [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I)
    (hsingle : ∀ i,
      eval f (checkSingle (M := M) (S := S) (C := C)
        commitment i.1 (message i) (proof i)) = true) :
    eval f (checkEntries (M := M) (S := S) (C := C) commitment I message proof) =
      List.replicate I.card true := by
  classical
  simpa [checkEntries] using
    checkEntriesAux_eq_replicate_true_of_all_single (M := M) (S := S) (C := C)
      f commitment message proof I.attach.toList
      (fun i _ => hsingle i)

/-- If every selected single check accepts, the public batch verifier accepts. -/
theorem check_eq_true_of_all_single [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I)
    (hsingle : ∀ i,
      eval f (checkSingle (M := M) (S := S) (C := C)
        commitment i.1 (message i) (proof i)) = true) :
    eval f (check (M := M) (S := S) (C := C) commitment I message proof) = true := by
  rw [check, eval_bind, eval_pure]
  rw [checkEntries_eq_replicate_true_of_all_single (M := M) (S := S) (C := C)
    f commitment I message proof hsingle]
  simp

/-- Honest batch openings make the auxiliary checker return all true values for
any supplied list of requested indices. -/
theorem checkEntriesAux_open_eq_replicate_true [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (messages : Leaves M depth) (salts : Leaves S depth)
    {I : IndexSet depth} :
    ∀ xs : List {i // i ∈ I},
      let labels := eval f (buildTree (M := M) (S := S) (C := C) messages salts)
      eval f
        (checkEntriesAux (M := M) (S := S) (C := C) labels.root
          (Subvector.ofVector messages I) («open» ⟨salts, labels⟩ I) xs) =
            List.replicate xs.length true
  | xs => by
      dsimp
      apply checkEntriesAux_eq_replicate_true_of_all_single
      intro i hi
      simpa [Subvector.ofVector, «open»] using
        checkSingle_openSingle_eq_true (M := M) (S := S) (C := C) f messages salts i.1

/-- Honest batch openings make `checkEntries` return all true values. -/
theorem checkEntries_open_eq_replicate_true [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (messages : Leaves M depth) (salts : Leaves S depth)
    (I : IndexSet depth) :
    let labels := eval f (buildTree (M := M) (S := S) (C := C) messages salts)
    eval f
      (checkEntries (M := M) (S := S) (C := C)
        labels.root I (Subvector.ofVector messages I) («open» ⟨salts, labels⟩ I)) =
          List.replicate I.card true := by
  dsimp
  simpa [checkEntries] using
    checkEntriesAux_open_eq_replicate_true (M := M) (S := S) (C := C)
      f messages salts (I := I) I.attach.toList

/-- Honest batch openings are accepted by the public verifier under any fixed
oracle. -/
theorem check_open_eq_true [DecidableEq C] {depth : ℕ} (f : OracleFn M S C)
    (messages : Leaves M depth) (salts : Leaves S depth) (I : IndexSet depth) :
    let labels := eval f (buildTree (M := M) (S := S) (C := C) messages salts)
    eval f
      (check (M := M) (S := S) (C := C)
        labels.root I (Subvector.ofVector messages I) («open» ⟨salts, labels⟩ I)) = true := by
  dsimp
  rw [check, eval_bind, eval_pure]
  rw [checkEntries_open_eq_replicate_true (M := M) (S := S) (C := C) f messages salts I]
  simp

/-- End-to-end deterministic completeness for `commitWithSalts`.

Building a commitment/trapdoor with supplied salts, opening any fixed index set,
and checking that opening under the same fixed oracle returns `true`. -/
theorem commitWithSalts_complete [DecidableEq C] {depth : ℕ} (f : OracleFn M S C)
    (messages : Leaves M depth) (salts : Leaves S depth) (I : IndexSet depth) :
    let out := eval f (commitWithSalts (M := M) (S := S) (C := C) messages salts)
    eval f (check (M := M) (S := S) (C := C) out.1 I (Subvector.ofVector messages I) («open» out.2 I)) =
      true := by
  rw [simulate_commitWithSalts_eq]
  simpa [simulate_buildTree_eq] using
    check_open_eq_true (M := M) (S := S) (C := C) f messages salts I

end MerkleTree
