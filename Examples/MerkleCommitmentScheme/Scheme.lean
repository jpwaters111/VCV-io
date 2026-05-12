/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Tuple.Basic
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Merkle Commitment Scheme — Scheme Definition And Algorithms

This file models the textbook Merkle commitment scheme from
`docs/merklecommitment.tex` in a proof-oriented way.

The honest Merkle data is flattened into `Vector`s indexed by tree layer. A
message of length `2^depth` is represented as a `Vector` of that length, and
the trapdoor stores the full table of labels together with the sampled leaf
salts. Single-leaf opening and checking are the primitive algorithms; the
textbook batch-opening interface is then indexed by a fixed finite set of leaf
positions. The same layer/index view is also used by the partial-tree extractor
state built from query traces.

Relation to the basic commitment scheme: Merkle leaf labels use the same random
oracle shape as the basic fixed-salt commitment, namely `Sum.inl (message,
salt)`. Internal Merkle nodes add the tree-specific query form `Sum.inr (left,
right)`. The Merkle proofs therefore reuse the basic commitment scheme's
generic ROM/cache/logging support for probability bounds, while this file
defines the independent tree algorithms and extractor state used by those
proofs.

This is the main API file for the Merkle construction: the public definitions
`MerkleTree.commitWithSalts`, `MerkleTree.commit`, `MerkleTree.open`,
`MerkleTree.check`, `MerkleTree.extract`, and the bundled
`MerkleTree.scheme` are all defined here.
-/

open OracleComp OracleSpec

namespace MerkleTree

open OracleComp OracleSpec

variable {M S C : Type}

/-! ## Public Types -/

/-- A fixed-length array-style vector. -/
abbrev VectorN (α : Type) (n : ℕ) := Vector α n

/-- Leaf values or salts for a perfect Merkle tree of depth `depth`. -/
abbrev Leaves (α : Type) (depth : ℕ) := Vector α (2 ^ depth)

/-- Leaf indices in a perfect Merkle tree of depth `depth`. -/
abbrev Index (depth : ℕ) := Fin (2 ^ depth)

/-- A finite set of leaf indices. -/
abbrev IndexSet (depth : ℕ) := Finset (Index depth)

/-- Commitment labels stored at a fixed layer. Layer `0` is the root. -/
abbrev LayerVector (α : Type) (layer : ℕ) := Vector α (2 ^ layer)

/-- Full Merkle labels, indexed by tree layer from root to leaves. -/
abbrev Labels (C : Type) (depth : ℕ) :=
  (layer : Fin (depth + 1)) → LayerVector C layer.1

namespace Labels

variable {depth : ℕ}

/-- The root label of a Merkle tree. -/
def root (labels : Labels C depth) : C :=
  (labels ⟨0, Nat.succ_pos _⟩).head

end Labels

/-- Honest opening trapdoor: all salts and all labels. -/
structure Trapdoor (S C : Type) (depth : ℕ) where
  salts : Leaves S depth
  labels : Labels C depth

/-- Authentication path for a single leaf. Siblings are ordered bottom-up:
the head is the sibling of the leaf hash. -/
structure AuthPath (S C : Type) (depth : ℕ) where
  salt : S
  siblings : Vector C depth

/-- Opened values for a fixed leaf index set. -/
abbrev Subvector (M : Type) {depth : ℕ} (I : IndexSet depth) :=
  { i // i ∈ I } → M

/-- Authentication paths for a fixed leaf index set. -/
abbrev Proof (S C : Type) {depth : ℕ} (I : IndexSet depth) :=
  { i // i ∈ I } → AuthPath S C depth

namespace Subvector

variable {M : Type} {depth : ℕ}

/-- Restrict a full leaf vector to a fixed index set. -/
def ofVector (messages : Leaves M depth) (I : IndexSet depth) : Subvector M I :=
  fun i => messages.get i.1

/-- Transport a subvector across an equality of index sets. -/
def cast {I J : IndexSet depth} (h : I = J) (values : Subvector M I) : Subvector M J :=
  fun j => values ⟨j.1, by subst h; exact j.2⟩

@[simp] theorem cast_rfl {I : IndexSet depth} (values : Subvector M I) :
    cast rfl values = values := by
  funext i
  rfl

end Subvector

namespace Proof

variable {depth : ℕ}

/-- Transport a proof family across an equality of index sets. -/
def cast {I J : IndexSet depth} (h : I = J) (proof : Proof S C I) : Proof S C J :=
  fun j => proof ⟨j.1, by subst h; exact j.2⟩

@[simp] theorem cast_rfl {I : IndexSet depth} (proof : Proof S C I) :
    cast rfl proof = proof := by
  funext i
  rfl

end Proof

/-! ## Oracle Specification -/

/-- Leaf-query oracle. -/
abbrev LeafOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

/-- Internal-node oracle. -/
abbrev NodeOracle (C : Type) : OracleSpec (C × C) := fun _ => C

/-- The typed Merkle oracle: leaf queries and internal-node queries. -/
abbrev Oracle (M : Type) (S : Type) (C : Type) :
    OracleSpec ((M × S) ⊕ (C × C)) :=
  LeafOracle M S C + NodeOracle C

/-- Commit a leaf with the Merkle leaf oracle. -/
def leafCommit (message : M) (salt : S) : OracleComp (LeafOracle M S C) C :=
  query (spec := LeafOracle M S C) (message, salt)

/-- Hash an internal node with the Merkle node oracle. -/
def nodeCommit (left right : C) : OracleComp (NodeOracle C) C :=
  query (spec := NodeOracle C) (left, right)

/-! ## Index Arithmetic -/

/-- The left child position of a parent position. -/
def leftChildPos {layer : ℕ} (i : Fin (2 ^ layer)) : Fin (2 ^ (layer + 1)) :=
  ⟨2 * i.1, by
    have hi : i.1 < 2 ^ layer := i.2
    rw [pow_succ, Nat.mul_comm]
    omega⟩

/-- The right child position of a parent position. -/
def rightChildPos {layer : ℕ} (i : Fin (2 ^ layer)) : Fin (2 ^ (layer + 1)) :=
  ⟨2 * i.1 + 1, by
    have hi : i.1 < 2 ^ layer := i.2
    rw [pow_succ, Nat.mul_comm]
    omega⟩

/-- The parent position of a child position. -/
def parentPos {layer : ℕ} (i : Fin (2 ^ (layer + 1))) : Fin (2 ^ layer) :=
  ⟨i.1 / 2, by
    rw [Nat.div_lt_iff_lt_mul (Nat.zero_lt_two)]
    simpa [pow_succ, Nat.mul_comm] using i.2⟩

/-- The sibling position of a non-root vertex. -/
def siblingIndex {layer : ℕ} (i : Fin (2 ^ (layer + 1))) : Fin (2 ^ (layer + 1)) :=
  if h : i.1 % 2 = 0 then
    ⟨i.1 + 1, by
      have hi : i.1 < 2 ^ (layer + 1) := i.2
      have hEven : Even (2 ^ (layer + 1)) := by
        exact (Nat.even_pow).2 ⟨even_two, Nat.succ_ne_zero _⟩
      have hmod : (2 ^ (layer + 1)) % 2 = 0 := (Nat.even_iff).1 hEven
      have hle : i.1 + 1 ≤ 2 ^ (layer + 1) := Nat.succ_le_of_lt hi
      have hne : i.1 + 1 ≠ 2 ^ (layer + 1) := by
        intro hEq
        have hiVal : i.1 = 2 ^ (layer + 1) - 1 := by omega
        have hpos : 0 < 2 ^ (layer + 1) := by
          exact pow_pos (by decide : 0 < (2 : ℕ)) _
        have hmodPred : (2 ^ (layer + 1) - 1) % 2 = 1 := by
          have hle1 : 1 ≤ 2 ^ (layer + 1) := Nat.succ_le_of_lt hpos
          have : (2 ^ (layer + 1) - 1 + 1) % 2 = 0 := by
            simp [Nat.sub_add_cancel hle1, hmod]
          exact (Nat.succ_mod_two_eq_zero_iff (m := 2 ^ (layer + 1) - 1)).1 this
        have : i.1 % 2 = 1 := by simpa [hiVal] using hmodPred
        omega
      exact lt_of_le_of_ne hle hne⟩
  else
    ⟨i.1 - 1, by
      have hi : i.1 < 2 ^ (layer + 1) := i.2
      omega⟩

/-- The path position of `idx` at a given tree layer. -/
def pathPos : {depth : ℕ} → Index depth → (layer : Fin (depth + 1)) → Fin (2 ^ layer.1)
  | 0, _, _ => 0
  | depth + 1, idx, layer =>
      if hlast : layer.1 = depth + 1 then by
        have hlayer : layer = Fin.last (depth + 1) := by
          apply Fin.ext
          simpa using hlast
        subst hlayer
        exact idx
      else
        pathPos (depth := depth) (parentPos idx) ⟨layer.1, by
          exact lt_of_le_of_ne (Nat.le_of_lt_succ layer.2) hlast⟩

/-- The sibling position of `idx` at a non-root tree layer indexed from the
root downward. -/
def siblingPos {depth : ℕ} (idx : Index depth) (layer : Fin depth) :
    Fin (2 ^ (layer.1 + 1)) :=
  siblingIndex (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩)

/-- The label on the path from `idx` at tree layer `layer`. -/
def pathLabel {depth : ℕ} (labels : Labels C depth) (idx : Index depth)
    (layer : Fin (depth + 1)) : C :=
  (labels layer).get (pathPos idx layer)

/-- The sibling label stored in an authentication path at the given tree layer,
indexed from the root downward. -/
def copathLabel {depth : ℕ} (authPath : AuthPath S C depth) (layer : Fin depth) : C :=
  authPath.siblings.reverse.get layer

/-! ## Honest Merkle Algorithms -/

/-- Proof-oriented monadic traversal over `Fin n`, returning a `Vector`. -/
def mapFinM {ι : Type} {spec : OracleSpec ι} {α : Type} :
    {n : ℕ} → (Fin n → OracleComp spec α) → OracleComp spec (Vector α n)
  | 0, _ => pure (Vector.ofFn fun i => nomatch i)
  | depth + 1, f => do
      let head ← f 0
      let tail ← mapFinM (fun i => f i.succ)
      pure <| Vector.ofFn fun
        | ⟨0, _⟩ => head
        | ⟨Nat.succ i, hi⟩ => tail.get ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Hash the leaf layer using an explicit leaf hash function. -/
def buildLeafLayerWithHash {depth : ℕ} (leafHash : M × S → C)
    (messages : Leaves M depth) (salts : Leaves S depth) : LayerVector C depth :=
  Vector.ofFn fun i => leafHash (messages.get i, salts.get i)

/-- Hash one internal layer using an explicit node hash function. -/
def buildLayerWithHash {depth : ℕ} (nodeHash : C × C → C)
    (children : LayerVector C (depth + 1)) : LayerVector C depth :=
  Vector.ofFn fun i => nodeHash (children.get (leftChildPos i), children.get (rightChildPos i))

/-- Build all labels from a leaf layer using an explicit node hash function. -/
def buildLabelsWithHash (nodeHash : C × C → C) :
    {depth : ℕ} → LayerVector C depth → Labels C depth
  | 0, leaves => fun layer => by
      have hlayer : layer = 0 := by
        apply Fin.ext
        omega
      subst hlayer
      exact leaves
  | depth + 1, leaves =>
      let upper := buildLabelsWithHash nodeHash (buildLayerWithHash nodeHash leaves)
      Fin.snoc upper leaves

/-- Build a full honest label table using explicit hash functions. -/
def buildTreeWithHash {depth : ℕ} (leafHash : M × S → C) (nodeHash : C × C → C)
    (messages : Leaves M depth) (salts : Leaves S depth) : Labels C depth :=
  buildLabelsWithHash nodeHash (buildLeafLayerWithHash leafHash messages salts)

/-- Extract the bottom-up sibling labels for a single path from a full label
table. -/
def openSiblings : {depth : ℕ} → Labels C depth → Index depth → Vector C depth
  | 0, _, _ => Vector.ofFn fun i => nomatch i
  | depth + 1, labels, idx =>
      let upper : Labels C depth := Fin.init labels
      let leaves : LayerVector C (depth + 1) := labels (Fin.last (depth + 1))
      Vector.ofFn fun
        | ⟨0, _⟩ => leaves.get (siblingIndex idx)
        | ⟨Nat.succ i, hi⟩ =>
            (openSiblings upper (parentPos idx)).get ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Hash the leaf layer with the Merkle oracle. -/
def buildLeafLayer : {depth : ℕ} → Leaves M depth → Leaves S depth →
    OracleComp (Oracle M S C) (LayerVector C depth)
  | _, messages, salts =>
      mapFinM (spec := Oracle M S C)
        (fun i =>
          leafCommit (M := M) (S := S) (C := C) (messages.get i) (salts.get i))

/-- Hash one internal layer with the Merkle oracle. -/
def buildLayer : {depth : ℕ} → LayerVector C (depth + 1) →
    OracleComp (Oracle M S C) (LayerVector C depth)
  | _, children =>
      mapFinM (spec := Oracle M S C)
        (fun i =>
          nodeCommit (C := C)
            (children.get (leftChildPos i))
            (children.get (rightChildPos i)))

/-- Build all labels from a leaf layer with the Merkle oracle. -/
def buildLabels : {depth : ℕ} → LayerVector C depth →
    OracleComp (Oracle M S C) (Labels C depth)
  | 0, leaves => pure (fun layer => by
      have hlayer : layer = 0 := by
        apply Fin.ext
        omega
      subst hlayer
      exact leaves)
  | depth + 1, leaves => do
      let upperLayer ← buildLayer (C := C) leaves
      let upper ← buildLabels upperLayer
      pure (Fin.snoc upper leaves)

/-- Build the full honest Merkle tree. -/
def buildTree : {depth : ℕ} → Leaves M depth → Leaves S depth →
    OracleComp (Oracle M S C) (Labels C depth)
  | _, messages, salts => do
      let leafLayer ← buildLeafLayer (M := M) (S := S) (C := C) messages salts
      buildLabels (C := C) leafLayer

/-- Deterministic Merkle commitment with fixed salts. -/
def commitWithSalts {depth : ℕ} (messages : Leaves M depth) (salts : Leaves S depth) :
    OracleComp (Oracle M S C) (C × Trapdoor S C depth) := do
  let labels ← buildTree (M := M) (S := S) (C := C) messages salts
  pure (labels.root, ⟨salts, labels⟩)

/-- Probabilistic Merkle commitment. -/
def commit {depth : ℕ} [SampleableType S] (messages : Leaves M depth) :
    OracleComp (unifSpec + Oracle M S C) (C × Trapdoor S C depth) := do
  let salts ← OracleComp.liftComp (spec := unifSpec)
    (superSpec := unifSpec + Oracle M S C) ($ᵗ Leaves S depth)
  commitWithSalts (M := M) (S := S) (C := C) messages salts

/-- Extract the bottom-up authentication path for a single leaf. -/
def openSingle {depth : ℕ} (trapdoor : Trapdoor S C depth) (idx : Index depth) :
    AuthPath S C depth :=
  ⟨trapdoor.salts.get idx, openSiblings trapdoor.labels idx⟩

/-- Batch opening for a fixed index set. -/
def «open» {depth : ℕ} (trapdoor : Trapdoor S C depth) (I : IndexSet depth) :
    Proof S C I :=
  fun i => openSingle trapdoor i.1

/-- Functional root recomputation from an already-computed leaf label.

The sibling vector is ordered bottom-up. At each step the parity of the current
index decides whether the current label is the left or right input to
`nodeHash`, and the recursion moves to the parent index. -/
def recomputeRootAuxWithHash (nodeHash : C × C → C) :
    {depth : ℕ} → Index depth → C → Vector C depth → C
  | 0, _, current, _ => current
  | depth + 1, idx, current, siblings =>
      let parent :=
        if idx.1 % 2 = 0 then
          nodeHash (current, siblings.head)
        else
          nodeHash (siblings.head, current)
      recomputeRootAuxWithHash nodeHash (parentPos idx) parent siblings.tail

/-- Recompute the root with explicit hash functions. -/
def recomputeRootSingleWithHash {depth : ℕ} (leafHash : M × S → C) (nodeHash : C × C → C)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) : C :=
  recomputeRootAuxWithHash nodeHash idx (leafHash (message, authPath.salt)) authPath.siblings

/-- Oracle-based root recomputation from an already-computed leaf label.

This is the verifier-side internal-node computation. Its trace contains
exactly `depth` internal queries; the leaf query is added by
`recomputeRootSingle`. -/
def recomputeRootAux :
    {depth : ℕ} → Index depth → C → Vector C depth → OracleComp (Oracle M S C) C
  | 0, _, current, _ => pure current
  | depth + 1, idx, current, siblings => do
      let parent ←
        if idx.1 % 2 = 0 then
          (nodeCommit (C := C) current siblings.head : OracleComp (Oracle M S C) C)
        else
          (nodeCommit (C := C) siblings.head current : OracleComp (Oracle M S C) C)
      recomputeRootAux (parentPos idx) parent siblings.tail

/-- Recompute the Merkle root for a single opening. -/
def recomputeRootSingle {depth : ℕ} (idx : Index depth) (message : M)
    (authPath : AuthPath S C depth) : OracleComp (Oracle M S C) C := do
  let leaf ←
    (leafCommit (M := M) (S := S) (C := C) message authPath.salt :
      OracleComp (Oracle M S C) C)
  recomputeRootAux idx leaf authPath.siblings

/-- Check a single Merkle opening. -/
def checkSingle [DecidableEq C] {depth : ℕ} (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) :
    OracleComp (Oracle M S C) Bool := do
  let root ← recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath
  pure (commitment == root)

/-- Internal list-based evaluator for batch checking. -/
def checkEntriesAux [DecidableEq C] {depth : ℕ} {I : IndexSet depth} (commitment : C)
    (message : Subvector M I) (proof : Proof S C I) :
    List { i // i ∈ I } → OracleComp (Oracle M S C) (List Bool)
  | [] => pure []
  | i :: rest => do
      let ok ← checkSingle (M := M) (S := S) (C := C) commitment i.1 (message i) (proof i)
      let restChecks ← checkEntriesAux commitment message proof rest
      pure (ok :: restChecks)

/-- Evaluate all single-leaf checks for a fixed index set. -/
noncomputable def checkEntries [DecidableEq C] {depth : ℕ} (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I) :
    OracleComp (Oracle M S C) (List Bool) :=
  checkEntriesAux (M := M) (S := S) (C := C) commitment message proof I.attach.toList

/-- Batch verification. -/
noncomputable def check [DecidableEq C] {depth : ℕ} (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I) :
    OracleComp (Oracle M S C) Bool := do
  let oks ← checkEntries (M := M) (S := S) (C := C) commitment I message proof
  pure (oks.all fun b => b)

/-! ## Extractor-Facing Partial Tree Model -/

/-- Partially-labeled Merkle nodes extracted from a commit-phase trace. -/
abbrev PartialLabels (C : Type) (depth : ℕ) :=
  (layer : Fin (depth + 1)) → Vector (Option C) (2 ^ layer.1)

/-- Partially-known leaves extracted from a commit-phase trace. -/
abbrev PartialLeaves (M S : Type) (depth : ℕ) :=
  Vector (Option (M × S)) (2 ^ depth)

/-- Extractor state: a partial label tree and partial leaf openings. -/
structure ExtractedState (M S C : Type) (depth : ℕ) where
  labels : PartialLabels C depth
  leaves : PartialLeaves M S depth

/-- Partition a commit-phase trace into the query types of 18.5. For the typed
oracle used here, the `other` component is always empty. -/
structure TracePartition (M S C : Type) where
  leafQueries : QueryLog (Oracle M S C)
  internalQueries : QueryLog (Oracle M S C)
  otherQueries : QueryLog (Oracle M S C)

/-- Empty partial label table before seeding the commitment root. -/
private def emptyPartialLabels {depth : ℕ} : PartialLabels C depth :=
  fun layer => Vector.ofFn fun _ => none

/-- Empty partial leaf table before processing any leaf-opening queries. -/
private def emptyPartialLeaves {depth : ℕ} : PartialLeaves M S depth :=
  Vector.ofFn fun _ => none

/-- Initial partial label tree seeded only with the claimed commitment at the
root. -/
private def seedRoot {depth : ℕ} (commitment : C) : PartialLabels C depth :=
  fun
    | ⟨0, _⟩ => Vector.ofFn fun _ => some commitment
    | ⟨Nat.succ layer, _⟩ => Vector.ofFn fun _ => none

/-- The 18.5 partition of a commit-phase trace. -/
def partitionTrace (trace : QueryLog (Oracle M S C)) : TracePartition M S C :=
  trace.foldr
    (fun entry acc =>
      match entry.1 with
      | Sum.inl _ =>
          { acc with leafQueries := entry :: acc.leafQueries }
      | Sum.inr _ =>
          { acc with internalQueries := entry :: acc.internalQueries })
    { leafQueries := [], internalQueries := [], otherQueries := [] }

/-- Membership characterization for the leaf-query part of `partitionTrace`.

A trace entry appears in `leafQueries` exactly when it appeared in the original
trace and its typed Merkle query is `Sum.inl (message, salt)`. -/
theorem mem_partitionTrace_leafQueries_iff (trace : QueryLog (Oracle M S C))
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    entry ∈ (partitionTrace (M := M) (S := S) (C := C) trace).leafQueries ↔
      entry ∈ trace ∧ ∃ ms : M × S, entry.1 = Sum.inl ms := by
  induction trace with
  | nil =>
      simp [partitionTrace]
  | cons hd tl ih =>
      cases hd with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              constructor
              · intro h
                rcases List.mem_cons.mp h with h | h
                · subst h
                  exact ⟨by simp, ⟨ms, rfl⟩⟩
                · rcases ih.mp h with ⟨htl, hdom⟩
                  exact ⟨List.mem_cons_of_mem _ htl, hdom⟩
              · rintro ⟨hmem, hdom⟩
                rcases List.mem_cons.mp hmem with h | htl
                · subst h
                  simpa [partitionTrace]
                · exact List.mem_cons_of_mem _ (ih.mpr ⟨htl, hdom⟩)
          | inr cs =>
              constructor
              · intro h
                rcases ih.mp h with ⟨htl, hdom⟩
                exact ⟨List.mem_cons_of_mem _ htl, hdom⟩
              · rintro ⟨hmem, hdom⟩
                rcases List.mem_cons.mp hmem with h | htl
                · rcases hdom with ⟨ms, hdomEq⟩
                  cases h
                  simp at hdomEq
                · exact ih.mpr ⟨htl, hdom⟩

/-- Membership characterization for the internal-query part of `partitionTrace`.

A trace entry appears in `internalQueries` exactly when it appeared in the
original trace and its typed Merkle query is `Sum.inr (left, right)`. -/
theorem mem_partitionTrace_internalQueries_iff (trace : QueryLog (Oracle M S C))
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    entry ∈ (partitionTrace (M := M) (S := S) (C := C) trace).internalQueries ↔
      entry ∈ trace ∧ ∃ cs : C × C, entry.1 = Sum.inr cs := by
  induction trace with
  | nil =>
      simp [partitionTrace]
  | cons hd tl ih =>
      cases hd with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              constructor
              · intro h
                rcases ih.mp h with ⟨htl, hdom⟩
                exact ⟨List.mem_cons_of_mem _ htl, hdom⟩
              · rintro ⟨hmem, hdom⟩
                rcases List.mem_cons.mp hmem with h | htl
                · rcases hdom with ⟨cs, hdomEq⟩
                  cases h
                  simp at hdomEq
                · exact ih.mpr ⟨htl, hdom⟩
          | inr cs =>
              constructor
              · intro h
                rcases List.mem_cons.mp h with h | h
                · subst h
                  exact ⟨by simp, ⟨cs, rfl⟩⟩
                · rcases ih.mp h with ⟨htl, hdom⟩
                  exact ⟨List.mem_cons_of_mem _ htl, hdom⟩
              · rintro ⟨hmem, hdom⟩
                rcases List.mem_cons.mp hmem with h | htl
                · subst h
                  simpa [partitionTrace]
                · exact List.mem_cons_of_mem _ (ih.mpr ⟨htl, hdom⟩)

/-
Partial-tree closure for the extractor.

The extractor starts with only the root commitment known. An internal query
`H(left, right) = answer` can reveal `left` and `right` at a child layer only
when the parent slot is already known to be `answer`. One pass can unlock one
additional layer in the worst case, so `buildPartialTreeFromTrace` below runs
`depth + 1` passes.

The private lemmas in this block prove three invariants:
* known labels are monotone across propagation;
* roots remain seeded by the commitment;
* when a unique internal query justifies a parent, the corresponding child
  labels become known.
-/

/-- Apply one internal query to one child layer, using already-known parent
labels to reveal missing children. -/
private def propagateInternalQueryAtLayer {layer : ℕ} [DecidableEq C]
    (left right answer : C) (oldChildren : Vector (Option C) (2 ^ (layer + 1)))
    (parents : Vector (Option C) (2 ^ layer)) :
    Vector (Option C) (2 ^ (layer + 1)) :=
  Vector.ofFn fun pos =>
    match oldChildren.get pos with
    | some value => some value
    | none =>
        match parents.get (parentPos pos) with
        | some parent =>
            if parent = answer then
              if pos.1 % 2 = 0 then some left else some right
            else none
        | none => none

/-- Apply one internal query simultaneously to every non-root layer, reading
parents from the fixed base state and writing children into the current state. -/
private def propagateInternalQueryUsingBase {depth : ℕ} [DecidableEq C]
    (left right answer : C) (baseLabels currentLabels : PartialLabels C depth) :
    PartialLabels C depth :=
  fun
    | ⟨0, _⟩ => currentLabels ⟨0, Nat.succ_pos _⟩
    | ⟨Nat.succ layer, hlayer⟩ =>
        propagateInternalQueryAtLayer left right answer
          (currentLabels ⟨Nat.succ layer, hlayer⟩)
          (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩)

/-- One closure pass over all internal queries in the trace. -/
private def propagateInternalQueriesOnce {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth) :
    PartialLabels C depth :=
  let internal := (partitionTrace (M := M) (S := S) (C := C) trace).internalQueries
  internal.foldl
    (fun current entry =>
      match entry with
      | ⟨Sum.inr (left, right), answer⟩ =>
          propagateInternalQueryUsingBase (depth := depth) left right answer labels current
      | ⟨Sum.inl _, _⟩ => current)
    labels

private theorem propagateInternalQueryUsingBase_root {depth : ℕ} [DecidableEq C]
    (left right answer : C) (baseLabels currentLabels : PartialLabels C depth) :
    (propagateInternalQueryUsingBase (depth := depth) left right answer baseLabels currentLabels
      ⟨0, Nat.succ_pos _⟩).head =
      (currentLabels ⟨0, Nat.succ_pos _⟩).head := by
  simp [propagateInternalQueryUsingBase]

private theorem propagateInternalQueriesFold_root {depth : ℕ} [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth),
      (entries.foldl
          (fun current entry =>
            match entry with
            | ⟨Sum.inr (left, right), answer⟩ =>
                propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels current
            | ⟨Sum.inl _, _⟩ => current)
          currentLabels
          ⟨0, Nat.succ_pos _⟩).head =
        (currentLabels ⟨0, Nat.succ_pos _⟩).head
  | [], _, currentLabels => by
      simp
  | entry :: entries, baseLabels, currentLabels => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl leaf =>
              simpa using
                propagateInternalQueriesFold_root (depth := depth) entries baseLabels currentLabels
          | inr pair =>
              rcases pair with ⟨left, right⟩
              have hroot :=
                propagateInternalQueryUsingBase_root (depth := depth)
                  left right answer baseLabels currentLabels
              calc
                (entries.foldl
                    (fun current entry =>
                      match entry with
                      | ⟨Sum.inr (left, right), answer⟩ =>
                          propagateInternalQueryUsingBase (depth := depth)
                            left right answer baseLabels current
                      | ⟨Sum.inl _, _⟩ => current)
                    (propagateInternalQueryUsingBase (depth := depth)
                      left right answer baseLabels currentLabels)
                    ⟨0, Nat.succ_pos _⟩).head
                    = (propagateInternalQueryUsingBase (depth := depth)
                        left right answer baseLabels currentLabels
                        ⟨0, Nat.succ_pos _⟩).head :=
                  propagateInternalQueriesFold_root (depth := depth) entries baseLabels
                    (propagateInternalQueryUsingBase (depth := depth)
                      left right answer baseLabels currentLabels)
                _ = (currentLabels ⟨0, Nat.succ_pos _⟩).head := hroot

private theorem propagateInternalQueriesOnce_root {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth) :
    (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth) trace labels
      ⟨0, Nat.succ_pos _⟩).head =
      (labels ⟨0, Nat.succ_pos _⟩).head := by
  unfold propagateInternalQueriesOnce
  simpa using propagateInternalQueriesFold_root (M := M) (S := S) (C := C)
    (depth := depth)
    ((partitionTrace (M := M) (S := S) (C := C) trace).internalQueries) labels labels

private theorem parentPos_leftChildPos_local {layer : ℕ} (i : Fin (2 ^ layer)) :
    parentPos (leftChildPos i) = i := by
  apply Fin.ext
  simp [parentPos, leftChildPos]

private theorem parentPos_rightChildPos_local {layer : ℕ} (i : Fin (2 ^ layer)) :
    parentPos (rightChildPos i) = i := by
  apply Fin.ext
  rw [parentPos, rightChildPos]
  simp
  omega

private theorem leftChildPos_mod_two {layer : ℕ} (i : Fin (2 ^ layer)) :
    (leftChildPos i).1 % 2 = 0 := by
  simp [leftChildPos]

private theorem rightChildPos_mod_two {layer : ℕ} (i : Fin (2 ^ layer)) :
    (rightChildPos i).1 % 2 = 1 := by
  simp [rightChildPos]

private theorem propagateInternalQueryAtLayer_get_eq_of_some {layer : ℕ} [DecidableEq C]
    (left right answer : C) (oldChildren : Vector (Option C) (2 ^ (layer + 1)))
    (parents : Vector (Option C) (2 ^ layer)) (pos : Fin (2 ^ (layer + 1)))
    (value : C) (hvalue : oldChildren.get pos = some value) :
    (propagateInternalQueryAtLayer left right answer oldChildren parents).get pos =
      some value := by
  simp [propagateInternalQueryAtLayer, hvalue]

private theorem propagateInternalQueryUsingBase_get_eq_of_some {depth : ℕ} [DecidableEq C]
    (left right answer : C) (baseLabels currentLabels : PartialLabels C depth)
    (layer : Fin (depth + 1)) (idx : Fin (2 ^ layer.1)) (value : C)
    (hvalue : (currentLabels layer).get idx = some value) :
    (propagateInternalQueryUsingBase (depth := depth) left right answer baseLabels currentLabels
      layer).get idx = some value := by
  rcases layer with ⟨(_ | layer), hlayer⟩
  · simpa [propagateInternalQueryUsingBase] using hvalue
  · exact propagateInternalQueryAtLayer_get_eq_of_some
      (left := left) (right := right) (answer := answer)
      (oldChildren := currentLabels ⟨Nat.succ layer, hlayer⟩)
      (parents := baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩)
      (pos := idx) (value := value) hvalue

private theorem propagateInternalQueriesFold_get_eq_of_some {depth : ℕ} [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth)
      (layer : Fin (depth + 1)) (idx : Fin (2 ^ layer.1)) (value : C),
      (currentLabels layer).get idx = some value →
        (entries.foldl
            (fun current entry =>
              match entry with
              | ⟨Sum.inr (left, right), answer⟩ =>
                  propagateInternalQueryUsingBase (depth := depth)
                    left right answer baseLabels current
              | ⟨Sum.inl _, _⟩ => current)
            currentLabels
            layer).get idx = some value
  | [], _, currentLabels, _, _, _, hvalue => by
      simpa using hvalue
  | entry :: entries, baseLabels, currentLabels, layer, idx, value, hvalue => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl leaf =>
              exact propagateInternalQueriesFold_get_eq_of_some
                (depth := depth) entries baseLabels currentLabels layer idx value hvalue
          | inr pair =>
              rcases pair with ⟨left, right⟩
              exact propagateInternalQueriesFold_get_eq_of_some
                (depth := depth) entries baseLabels
                (propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels currentLabels)
                layer idx value
                (propagateInternalQueryUsingBase_get_eq_of_some
                  (depth := depth) left right answer baseLabels currentLabels
                  layer idx value hvalue)

private theorem propagateInternalQueriesOnce_get_eq_of_some {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (layer : Fin (depth + 1)) (idx : Fin (2 ^ layer.1)) (value : C)
    (hvalue : (labels layer).get idx = some value) :
    (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
      trace labels layer).get idx = some value := by
  unfold propagateInternalQueriesOnce
  exact propagateInternalQueriesFold_get_eq_of_some (M := M) (S := S) (C := C)
    (depth := depth)
    ((partitionTrace (M := M) (S := S) (C := C) trace).internalQueries)
    labels labels layer idx value hvalue

/-- Iterate internal-query propagation for a fixed number of closure passes. -/
private def closeInternalQueries {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) :
    ℕ → PartialLabels C depth → PartialLabels C depth
  | 0, labels => labels
  | Nat.succ n, labels =>
      closeInternalQueries trace n <|
        propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth) trace labels

private theorem closeInternalQueries_get_eq_of_some {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) :
    ∀ (n : ℕ) (labels : PartialLabels C depth)
      (layer : Fin (depth + 1)) (idx : Fin (2 ^ layer.1)) (value : C),
      (labels layer).get idx = some value →
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace n labels layer).get idx = some value
  | 0, _, _, _, _, hvalue => by
      simpa [closeInternalQueries] using hvalue
  | Nat.succ n, labels, layer, idx, value, hvalue => by
      rw [closeInternalQueries]
      exact closeInternalQueries_get_eq_of_some trace n
        (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
          trace labels)
        layer idx value
        (propagateInternalQueriesOnce_get_eq_of_some (M := M) (S := S) (C := C)
          (depth := depth) trace labels layer idx value hvalue)

private theorem propagateInternalQueryUsingBase_leftChild_origin {depth layer : ℕ}
    [DecidableEq C] (left right answer : C) (baseLabels currentLabels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C)
    (hget :
      (propagateInternalQueryUsingBase (depth := depth)
        left right answer baseLabels currentLabels ⟨layer + 1, hlayer⟩).get
        (leftChildPos parent) = some value) :
    (currentLabels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value ∨
      value = left ∧
        (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
  have hget' :
      (match (currentLabels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) with
        | some oldValue => some oldValue
        | none =>
            match (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent with
            | some parentValue =>
                if parentValue = answer then some left else none
            | none => none) = some value := by
    simpa [propagateInternalQueryUsingBase, propagateInternalQueryAtLayer,
      parentPos_leftChildPos_local, leftChildPos_mod_two] using hget
  cases hchild :
      (currentLabels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) with
  | some oldValue =>
      have hold : some oldValue = some value := by
        simpa [hchild] using hget'
      exact Or.inl (by simpa [Option.some.inj hold] using hchild)
  | none =>
    cases hparent :
        (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent with
    | none =>
        have hnone : none = some value := by
          simpa [hchild, hparent] using hget'
        cases hnone
    | some parentValue =>
        by_cases hanswer : parentValue = answer
        · have hleft : some left = some value := by
            simpa [hchild, hparent, hanswer] using hget'
          exact Or.inr ⟨(Option.some.inj hleft).symm, by simpa [hanswer] using hparent⟩
        · have hnone : none = some value := by
            simpa [hchild, hparent, hanswer] using hget'
          cases hnone

private theorem propagateInternalQueryUsingBase_rightChild_origin {depth layer : ℕ}
    [DecidableEq C] (left right answer : C) (baseLabels currentLabels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C)
    (hget :
      (propagateInternalQueryUsingBase (depth := depth)
        left right answer baseLabels currentLabels ⟨layer + 1, hlayer⟩).get
        (rightChildPos parent) = some value) :
    (currentLabels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value ∨
      value = right ∧
        (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
  have hget' :
      (match (currentLabels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) with
        | some oldValue => some oldValue
        | none =>
            match (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent with
            | some parentValue =>
                if parentValue = answer then some right else none
            | none => none) = some value := by
    simpa [propagateInternalQueryUsingBase, propagateInternalQueryAtLayer,
      parentPos_rightChildPos_local, rightChildPos_mod_two] using hget
  cases hchild :
      (currentLabels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) with
  | some oldValue =>
      have hold : some oldValue = some value := by
        simpa [hchild] using hget'
      exact Or.inl (by simpa [Option.some.inj hold] using hchild)
  | none =>
    cases hparent :
        (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent with
    | none =>
        have hnone : none = some value := by
          simpa [hchild, hparent] using hget'
        cases hnone
    | some parentValue =>
        by_cases hanswer : parentValue = answer
        · have hright : some right = some value := by
            simpa [hchild, hparent, hanswer] using hget'
          exact Or.inr ⟨(Option.some.inj hright).symm, by simpa [hanswer] using hparent⟩
        · have hnone : none = some value := by
            simpa [hchild, hparent, hanswer] using hget'
          cases hnone

private theorem propagateInternalQueriesFold_leftChild_origin {depth layer : ℕ}
    [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth)
      (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C),
      (entries.foldl
          (fun current entry =>
            match entry with
            | ⟨Sum.inr (left, right), answer⟩ =>
                propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels current
            | ⟨Sum.inl _, _⟩ => current)
          currentLabels
          ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value →
        (currentLabels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value ∨
          ∃ right answer,
            ⟨Sum.inr (value, right), answer⟩ ∈ entries ∧
              (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer
  | [], _, currentLabels, _, _, _, hget => by
      exact Or.inl hget
  | entry :: entries, baseLabels, currentLabels, hlayer, parent, value, hget => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl leaf =>
              have horigin := propagateInternalQueriesFold_leftChild_origin
                (depth := depth) (layer := layer) entries baseLabels currentLabels
                hlayer parent value hget
              cases horigin with
              | inl hcurrent =>
                  exact Or.inl hcurrent
              | inr horigin =>
                  rcases horigin with ⟨originRight, originAnswer, hmem, hparent⟩
                  exact Or.inr
                    ⟨originRight, originAnswer, List.mem_cons_of_mem _ hmem, hparent⟩
          | inr pair =>
              rcases pair with ⟨left, right⟩
              have htail :=
                propagateInternalQueriesFold_leftChild_origin
                  (depth := depth) (layer := layer) entries baseLabels
                  (propagateInternalQueryUsingBase (depth := depth)
                    left right answer baseLabels currentLabels)
                  hlayer parent value hget
              cases htail with
              | inl hhead =>
                  have horigin :=
                    propagateInternalQueryUsingBase_leftChild_origin
                      (depth := depth) (layer := layer)
                      left right answer baseLabels currentLabels hlayer parent value hhead
                  cases horigin with
                  | inl hcurrent =>
                      exact Or.inl hcurrent
                  | inr hnew =>
                      rcases hnew with ⟨hvalue, hparent⟩
                      subst hvalue
                      exact Or.inr ⟨right, answer, by simp, hparent⟩
              | inr horigin =>
                  rcases horigin with ⟨originRight, originAnswer, hmem, hparent⟩
                  exact Or.inr
                    ⟨originRight, originAnswer, List.mem_cons_of_mem _ hmem, hparent⟩

private theorem propagateInternalQueriesFold_rightChild_origin {depth layer : ℕ}
    [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth)
      (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C),
      (entries.foldl
          (fun current entry =>
            match entry with
            | ⟨Sum.inr (left, right), answer⟩ =>
                propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels current
            | ⟨Sum.inl _, _⟩ => current)
          currentLabels
          ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value →
        (currentLabels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value ∨
          ∃ left answer,
            ⟨Sum.inr (left, value), answer⟩ ∈ entries ∧
              (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer
  | [], _, currentLabels, _, _, _, hget => by
      exact Or.inl hget
  | entry :: entries, baseLabels, currentLabels, hlayer, parent, value, hget => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl leaf =>
              have horigin := propagateInternalQueriesFold_rightChild_origin
                (depth := depth) (layer := layer) entries baseLabels currentLabels
                hlayer parent value hget
              cases horigin with
              | inl hcurrent =>
                  exact Or.inl hcurrent
              | inr horigin =>
                  rcases horigin with ⟨originLeft, originAnswer, hmem, hparent⟩
                  exact Or.inr
                    ⟨originLeft, originAnswer, List.mem_cons_of_mem _ hmem, hparent⟩
          | inr pair =>
              rcases pair with ⟨left, right⟩
              have htail :=
                propagateInternalQueriesFold_rightChild_origin
                  (depth := depth) (layer := layer) entries baseLabels
                  (propagateInternalQueryUsingBase (depth := depth)
                    left right answer baseLabels currentLabels)
                  hlayer parent value hget
              cases htail with
              | inl hhead =>
                  have horigin :=
                    propagateInternalQueryUsingBase_rightChild_origin
                      (depth := depth) (layer := layer)
                      left right answer baseLabels currentLabels hlayer parent value hhead
                  cases horigin with
                  | inl hcurrent =>
                      exact Or.inl hcurrent
                  | inr hnew =>
                      rcases hnew with ⟨hvalue, hparent⟩
                      subst hvalue
                      exact Or.inr ⟨left, answer, by simp, hparent⟩
              | inr horigin =>
                  rcases horigin with ⟨originLeft, originAnswer, hmem, hparent⟩
                  exact Or.inr
                    ⟨originLeft, originAnswer, List.mem_cons_of_mem _ hmem, hparent⟩

private theorem propagateInternalQueriesOnce_leftChild_origin {depth layer : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C)
    (hget :
      (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
        trace labels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value) :
    (labels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value ∨
      ∃ right answer,
        ⟨Sum.inr (value, right), answer⟩ ∈ trace ∧
          (labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
  unfold propagateInternalQueriesOnce at hget
  have horigin :=
    propagateInternalQueriesFold_leftChild_origin (M := M) (S := S) (C := C)
      (depth := depth) (layer := layer)
      ((partitionTrace (M := M) (S := S) (C := C) trace).internalQueries)
      labels labels hlayer parent value hget
  cases horigin with
  | inl hcurrent =>
      exact Or.inl hcurrent
  | inr hnew =>
      rcases hnew with ⟨right, answer, hmemInternal, hparent⟩
      have hmemTrace :
          ⟨Sum.inr (value, right), answer⟩ ∈ trace := by
        exact (mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
          trace ⟨Sum.inr (value, right), answer⟩).mp hmemInternal |>.1
      exact Or.inr ⟨right, answer, hmemTrace, hparent⟩

private theorem propagateInternalQueriesOnce_rightChild_origin {depth layer : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C)
    (hget :
      (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
        trace labels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value) :
    (labels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value ∨
      ∃ left answer,
        ⟨Sum.inr (left, value), answer⟩ ∈ trace ∧
          (labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
  unfold propagateInternalQueriesOnce at hget
  have horigin :=
    propagateInternalQueriesFold_rightChild_origin (M := M) (S := S) (C := C)
      (depth := depth) (layer := layer)
      ((partitionTrace (M := M) (S := S) (C := C) trace).internalQueries)
      labels labels hlayer parent value hget
  cases horigin with
  | inl hcurrent =>
      exact Or.inl hcurrent
  | inr hnew =>
      rcases hnew with ⟨left, answer, hmemInternal, hparent⟩
      have hmemTrace :
          ⟨Sum.inr (left, value), answer⟩ ∈ trace := by
        exact (mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
          trace ⟨Sum.inr (left, value), answer⟩).mp hmemInternal |>.1
      exact Or.inr ⟨left, answer, hmemTrace, hparent⟩

private theorem propagateInternalQueryUsingBase_leftChild_exists {depth layer : ℕ}
    [DecidableEq C] (left right answer : C) (baseLabels currentLabels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (hparent : (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer) :
    ∃ value : C,
      (propagateInternalQueryUsingBase (depth := depth)
        left right answer baseLabels currentLabels ⟨layer + 1, hlayer⟩).get
        (leftChildPos parent) = some value := by
  cases hchild : (currentLabels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) with
  | some oldValue =>
      exact ⟨oldValue, propagateInternalQueryUsingBase_get_eq_of_some
        (depth := depth) left right answer baseLabels currentLabels
        ⟨layer + 1, hlayer⟩ (leftChildPos parent) oldValue hchild⟩
  | none =>
      refine ⟨left, ?_⟩
      simp [propagateInternalQueryUsingBase, propagateInternalQueryAtLayer, hchild, hparent,
        parentPos_leftChildPos_local, leftChildPos_mod_two]

private theorem propagateInternalQueryUsingBase_rightChild_exists {depth layer : ℕ}
    [DecidableEq C] (left right answer : C) (baseLabels currentLabels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (hparent : (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer) :
    ∃ value : C,
      (propagateInternalQueryUsingBase (depth := depth)
        left right answer baseLabels currentLabels ⟨layer + 1, hlayer⟩).get
        (rightChildPos parent) = some value := by
  cases hchild : (currentLabels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) with
  | some oldValue =>
      exact ⟨oldValue, propagateInternalQueryUsingBase_get_eq_of_some
        (depth := depth) left right answer baseLabels currentLabels
        ⟨layer + 1, hlayer⟩ (rightChildPos parent) oldValue hchild⟩
  | none =>
      refine ⟨right, ?_⟩
      simp [propagateInternalQueryUsingBase, propagateInternalQueryAtLayer, hchild, hparent,
        parentPos_rightChildPos_local, rightChildPos_mod_two]

private theorem propagateInternalQueriesFold_leftChild_exists_of_mem {depth layer : ℕ}
    [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth)
      (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
      (left right answer : C),
      (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer →
        ⟨Sum.inr (left, right), answer⟩ ∈ entries →
          ∃ value : C,
            (entries.foldl
                (fun current entry =>
                  match entry with
                  | ⟨Sum.inr (left, right), answer⟩ =>
                      propagateInternalQueryUsingBase (depth := depth)
                        left right answer baseLabels current
                  | ⟨Sum.inl _, _⟩ => current)
                currentLabels
                ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value
  | [], _, _, _, _, _, _, _, _, hmem => by
      cases hmem
  | entry :: entries, baseLabels, currentLabels, hlayer, parent, left, right, answer,
      hparent, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        rcases propagateInternalQueryUsingBase_leftChild_exists
            (depth := depth) (layer := layer)
            left right answer baseLabels currentLabels hlayer parent hparent with
          ⟨value, hvalue⟩
        exact ⟨value, propagateInternalQueriesFold_get_eq_of_some
          (M := M) (S := S) (C := C) (depth := depth) entries baseLabels
          (propagateInternalQueryUsingBase (depth := depth)
            left right answer baseLabels currentLabels)
          ⟨layer + 1, hlayer⟩ (leftChildPos parent) value hvalue⟩
      · cases entry with
        | mk domain queryAnswer =>
            cases domain with
            | inl ms =>
                exact propagateInternalQueriesFold_leftChild_exists_of_mem
                  (depth := depth) (layer := layer) entries baseLabels currentLabels
                  hlayer parent left right answer hparent htail
            | inr pair =>
                rcases pair with ⟨queryLeft, queryRight⟩
                exact propagateInternalQueriesFold_leftChild_exists_of_mem
                  (depth := depth) (layer := layer) entries baseLabels
                  (propagateInternalQueryUsingBase (depth := depth)
                    queryLeft queryRight queryAnswer baseLabels currentLabels)
                  hlayer parent left right answer hparent htail

private theorem propagateInternalQueriesFold_rightChild_exists_of_mem {depth layer : ℕ}
    [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth)
      (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
      (left right answer : C),
      (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer →
        ⟨Sum.inr (left, right), answer⟩ ∈ entries →
          ∃ value : C,
            (entries.foldl
                (fun current entry =>
                  match entry with
                  | ⟨Sum.inr (left, right), answer⟩ =>
                      propagateInternalQueryUsingBase (depth := depth)
                        left right answer baseLabels current
                  | ⟨Sum.inl _, _⟩ => current)
                currentLabels
                ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value
  | [], _, _, _, _, _, _, _, _, hmem => by
      cases hmem
  | entry :: entries, baseLabels, currentLabels, hlayer, parent, left, right, answer,
      hparent, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        rcases propagateInternalQueryUsingBase_rightChild_exists
            (depth := depth) (layer := layer)
            left right answer baseLabels currentLabels hlayer parent hparent with
          ⟨value, hvalue⟩
        exact ⟨value, propagateInternalQueriesFold_get_eq_of_some
          (M := M) (S := S) (C := C) (depth := depth) entries baseLabels
          (propagateInternalQueryUsingBase (depth := depth)
            left right answer baseLabels currentLabels)
          ⟨layer + 1, hlayer⟩ (rightChildPos parent) value hvalue⟩
      · cases entry with
        | mk domain queryAnswer =>
            cases domain with
            | inl ms =>
                exact propagateInternalQueriesFold_rightChild_exists_of_mem
                  (depth := depth) (layer := layer) entries baseLabels currentLabels
                  hlayer parent left right answer hparent htail
            | inr pair =>
                rcases pair with ⟨queryLeft, queryRight⟩
                exact propagateInternalQueriesFold_rightChild_exists_of_mem
                  (depth := depth) (layer := layer) entries baseLabels
                  (propagateInternalQueryUsingBase (depth := depth)
                    queryLeft queryRight queryAnswer baseLabels currentLabels)
                  hlayer parent left right answer hparent htail

private theorem propagateInternalQueriesOnce_leftChild_exists_of_mem {depth layer : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent : (labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    ∃ value : C,
      (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
        trace labels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value := by
  unfold propagateInternalQueriesOnce
  have hmemInternal :
      ⟨Sum.inr (left, right), answer⟩ ∈
        (partitionTrace (M := M) (S := S) (C := C) trace).internalQueries := by
    exact (mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
      trace ⟨Sum.inr (left, right), answer⟩).mpr ⟨hmem, ⟨(left, right), rfl⟩⟩
  exact propagateInternalQueriesFold_leftChild_exists_of_mem
    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
    ((partitionTrace (M := M) (S := S) (C := C) trace).internalQueries)
    labels labels hlayer parent left right answer hparent hmemInternal

private theorem propagateInternalQueriesOnce_rightChild_exists_of_mem {depth layer : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent : (labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    ∃ value : C,
      (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
        trace labels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value := by
  unfold propagateInternalQueriesOnce
  have hmemInternal :
      ⟨Sum.inr (left, right), answer⟩ ∈
        (partitionTrace (M := M) (S := S) (C := C) trace).internalQueries := by
    exact (mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
      trace ⟨Sum.inr (left, right), answer⟩).mpr ⟨hmem, ⟨(left, right), rfl⟩⟩
  exact propagateInternalQueriesFold_rightChild_exists_of_mem
    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
    ((partitionTrace (M := M) (S := S) (C := C) trace).internalQueries)
    labels labels hlayer parent left right answer hparent hmemInternal

private theorem closeInternalQueries_leftChild_origin {depth layer : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) :
    ∀ (n : ℕ) (labels : PartialLabels C depth)
      (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C),
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace n labels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value →
        (labels ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value ∨
          ∃ right answer,
            ⟨Sum.inr (value, right), answer⟩ ∈ trace ∧
              (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
                trace n labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer
  | 0, labels, hlayer, parent, value, hget => by
      exact Or.inl hget
  | Nat.succ n, labels, hlayer, parent, value, hget => by
      rw [closeInternalQueries] at hget
      have horigin :=
        closeInternalQueries_leftChild_origin trace n
          (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
            trace labels)
          hlayer parent value hget
      cases horigin with
      | inl hchildOnce =>
          have honce :=
            propagateInternalQueriesOnce_leftChild_origin (M := M) (S := S) (C := C)
              (depth := depth) (layer := layer) trace labels hlayer parent value hchildOnce
          cases honce with
          | inl hchild =>
              exact Or.inl hchild
          | inr hnew =>
              rcases hnew with ⟨right, answer, hmem, hparent⟩
              have hparentOnce :
                  (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
                    (depth := depth) trace labels
                    ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
                propagateInternalQueriesOnce_get_eq_of_some (M := M) (S := S) (C := C)
                  (depth := depth) trace labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩
                  parent answer hparent
              have hparentFinal :
                  (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
                    trace n
                    (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
                      (depth := depth) trace labels)
                    ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
                closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
                  (depth := depth) trace n
                  (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
                    (depth := depth) trace labels)
                  ⟨layer, Nat.lt_of_succ_lt hlayer⟩ parent answer hparentOnce
              exact Or.inr ⟨right, answer, hmem, by simpa [closeInternalQueries] using hparentFinal⟩
      | inr hnew =>
          rcases hnew with ⟨right, answer, hmem, hparent⟩
          exact Or.inr ⟨right, answer, hmem, by simpa [closeInternalQueries] using hparent⟩

private theorem closeInternalQueries_rightChild_origin {depth layer : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) :
    ∀ (n : ℕ) (labels : PartialLabels C depth)
      (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer)) (value : C),
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace n labels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value →
        (labels ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value ∨
          ∃ left answer,
            ⟨Sum.inr (left, value), answer⟩ ∈ trace ∧
              (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
                trace n labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer
  | 0, labels, hlayer, parent, value, hget => by
      exact Or.inl hget
  | Nat.succ n, labels, hlayer, parent, value, hget => by
      rw [closeInternalQueries] at hget
      have horigin :=
        closeInternalQueries_rightChild_origin trace n
          (propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
            trace labels)
          hlayer parent value hget
      cases horigin with
      | inl hchildOnce =>
          have honce :=
            propagateInternalQueriesOnce_rightChild_origin (M := M) (S := S) (C := C)
              (depth := depth) (layer := layer) trace labels hlayer parent value hchildOnce
          cases honce with
          | inl hchild =>
              exact Or.inl hchild
          | inr hnew =>
              rcases hnew with ⟨left, answer, hmem, hparent⟩
              have hparentOnce :
                  (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
                    (depth := depth) trace labels
                    ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
                propagateInternalQueriesOnce_get_eq_of_some (M := M) (S := S) (C := C)
                  (depth := depth) trace labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩
                  parent answer hparent
              have hparentFinal :
                  (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
                    trace n
                    (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
                      (depth := depth) trace labels)
                    ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
                closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
                  (depth := depth) trace n
                  (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
                    (depth := depth) trace labels)
                  ⟨layer, Nat.lt_of_succ_lt hlayer⟩ parent answer hparentOnce
              exact Or.inr ⟨left, answer, hmem, by simpa [closeInternalQueries] using hparentFinal⟩
      | inr hnew =>
          rcases hnew with ⟨left, answer, hmem, hparent⟩
          exact Or.inr ⟨left, answer, hmem, by simpa [closeInternalQueries] using hparent⟩

private theorem closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close {depth : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C)) :
    ∀ (n : ℕ) (labels : PartialLabels C depth),
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (n + 1) labels =
        propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
          trace
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace n labels)
  | 0, labels => by
      simp [closeInternalQueries]
  | Nat.succ n, labels => by
      rw [show Nat.succ n + 1 = n + 1 + 1 by omega]
      rw [closeInternalQueries]
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        trace n
        (propagateInternalQueriesOnce (M := M) (S := S) (C := C)
          (depth := depth) trace labels)]
      rfl

private theorem closeInternalQueries_add {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) :
    ∀ (m n : ℕ) (labels : PartialLabels C depth),
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (m + n) labels =
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace n
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace m labels)
  | m, 0, labels => by
      simp [closeInternalQueries]
  | m, Nat.succ n, labels => by
      rw [Nat.add_succ]
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        trace (m + n) labels]
      rw [closeInternalQueries_add trace m n labels]
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        trace n
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace m labels)]

private theorem closeInternalQueries_leftChild_exists_of_mem_after_pass {depth layer : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C))
    (passes : ℕ) (labels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    ∃ value : C,
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace (passes + 1) labels ⟨layer + 1, hlayer⟩).get
        (leftChildPos parent) = some value := by
  rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
    (M := M) (S := S) (C := C) (depth := depth) trace passes labels]
  exact propagateInternalQueriesOnce_leftChild_exists_of_mem
    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
    trace
    (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
      trace passes labels)
    hlayer parent left right answer hparent hmem

private theorem closeInternalQueries_rightChild_exists_of_mem_after_pass {depth layer : ℕ}
    [DecidableEq C] (trace : QueryLog (Oracle M S C))
    (passes : ℕ) (labels : PartialLabels C depth)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    ∃ value : C,
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace (passes + 1) labels ⟨layer + 1, hlayer⟩).get
        (rightChildPos parent) = some value := by
  rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
    (M := M) (S := S) (C := C) (depth := depth) trace passes labels]
  exact propagateInternalQueriesOnce_rightChild_exists_of_mem
    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
    trace
    (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
      trace passes labels)
    hlayer parent left right answer hparent hmem

/-- Build the partial internal-node tree rooted at `commitment` from the
commit-phase trace. -/
def buildPartialTreeFromTrace {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    PartialLabels C depth :=
  closeInternalQueries (M := M) (S := S) (C := C) (depth := depth) trace (depth + 1)
    (seedRoot (depth := depth) commitment)

/-- Build the partial internal-node tree after an explicit number of closure
passes. This is useful for path-by-path extractor proofs that establish a parent
before using the next pass to populate its children. -/
def buildPartialTreeFromTraceAfterPasses {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ) :
    PartialLabels C depth :=
  closeInternalQueries (M := M) (S := S) (C := C) (depth := depth) trace passes
    (seedRoot (depth := depth) commitment)

/-- The closure construction never changes the seeded root label, even after an
arbitrary number of internal-query propagation passes. -/
@[simp] theorem buildPartialTreeFromTraceAfterPasses_root {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ) :
    (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
      (depth := depth) commitment trace passes ⟨0, Nat.succ_pos _⟩).head =
      some commitment := by
  suffices hroot :
      ∀ n : ℕ, ∀ labels : PartialLabels C depth,
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace n labels ⟨0, Nat.succ_pos _⟩).head =
          (labels ⟨0, Nat.succ_pos _⟩).head by
    simpa [buildPartialTreeFromTraceAfterPasses, seedRoot, Vector.head] using
      hroot passes (seedRoot (C := C) (depth := depth) commitment)
  intro n
  induction n with
  | zero =>
      intro labels
      simp [closeInternalQueries]
  | succ n ih =>
      intro labels
      rw [closeInternalQueries]
      rw [ih]
      exact propagateInternalQueriesOnce_root (M := M) (S := S) (C := C)
        (depth := depth) trace labels

/-- Labels learned after an intermediate number of closure passes remain known
in the final closed partial tree. -/
theorem buildPartialTreeFromTrace_get_eq_of_after_passes {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (layer : Fin (depth + 1)) (pos : Fin (2 ^ layer.1)) (value : C)
    (hpasses : passes ≤ depth + 1)
    (hget :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes layer).get pos = some value) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      commitment trace layer).get pos = some value := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  let remaining := depth + 1 - passes
  have hsum : passes + remaining = depth + 1 := by omega
  have hfinal :
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (depth + 1) seed =
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace remaining
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace passes seed) := by
    rw [← hsum]
    exact closeInternalQueries_add (M := M) (S := S) (C := C)
      (depth := depth) trace passes remaining seed
  have hgetClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed layer).get pos = some value := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hget
  have hpreserve :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace remaining
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace passes seed)
        layer).get pos = some value :=
    closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
      (depth := depth) trace remaining
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed)
      layer pos value hgetClose
  simpa [buildPartialTreeFromTrace, seed, hfinal] using hpreserve

/-- One closure pass after a known parent recovers the exact left child when
all internal queries with the same answer agree. -/
theorem buildPartialTreeFromTraceAfterPasses_leftChild_get_of_unique_internal
    {depth layer : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace)
    (hunique :
      ∀ left' right' : C,
        ⟨Sum.inr (left', right'), answer⟩ ∈ trace →
          left' = left ∧ right' = right) :
    (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
      (depth := depth) commitment trace (passes + 1)
      ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some left := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  have hparentClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent =
        some answer := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hparent
  rcases closeInternalQueries_leftChild_exists_of_mem_after_pass
      (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
      trace passes seed hlayer parent left right answer hparentClose hmem with
    ⟨value, hvalue⟩
  have horigin :=
    closeInternalQueries_leftChild_origin (M := M) (S := S) (C := C)
      (depth := depth) (layer := layer) trace (passes + 1) seed
      hlayer parent value hvalue
  cases horigin with
  | inl hseed =>
      simp [seed, seedRoot] at hseed
  | inr hnew =>
      rcases hnew with ⟨originRight, originAnswer, hmemOrigin, hparentOrigin⟩
      have hparentAfter' :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace 1
            (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
              trace passes seed)
            ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
        closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
          (depth := depth) trace 1
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace passes seed)
          ⟨layer, Nat.lt_of_succ_lt hlayer⟩ parent answer hparentClose
      have hparentAfter :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (passes + 1) seed
            ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
        by
          rw [closeInternalQueries_add (M := M) (S := S) (C := C)
            (depth := depth) trace passes 1 seed]
          exact hparentAfter'
      have hanswer : originAnswer = answer := by
        exact Option.some.inj (by rw [← hparentOrigin, hparentAfter])
      have huniq := hunique value originRight (by simpa [hanswer] using hmemOrigin)
      simpa [buildPartialTreeFromTraceAfterPasses, seed, huniq.1] using hvalue

/-- One closure pass after a known parent recovers the exact right child when
all internal queries with the same answer agree. -/
theorem buildPartialTreeFromTraceAfterPasses_rightChild_get_of_unique_internal
    {depth layer : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace)
    (hunique :
      ∀ left' right' : C,
        ⟨Sum.inr (left', right'), answer⟩ ∈ trace →
          left' = left ∧ right' = right) :
    (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
      (depth := depth) commitment trace (passes + 1)
      ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some right := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  have hparentClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent =
        some answer := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hparent
  rcases closeInternalQueries_rightChild_exists_of_mem_after_pass
      (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
      trace passes seed hlayer parent left right answer hparentClose hmem with
    ⟨value, hvalue⟩
  have horigin :=
    closeInternalQueries_rightChild_origin (M := M) (S := S) (C := C)
      (depth := depth) (layer := layer) trace (passes + 1) seed
      hlayer parent value hvalue
  cases horigin with
  | inl hseed =>
      simp [seed, seedRoot] at hseed
  | inr hnew =>
      rcases hnew with ⟨originLeft, originAnswer, hmemOrigin, hparentOrigin⟩
      have hparentAfter' :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace 1
            (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
              trace passes seed)
            ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
        closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
          (depth := depth) trace 1
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace passes seed)
          ⟨layer, Nat.lt_of_succ_lt hlayer⟩ parent answer hparentClose
      have hparentAfter :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (passes + 1) seed
            ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
        by
          rw [closeInternalQueries_add (M := M) (S := S) (C := C)
            (depth := depth) trace passes 1 seed]
          exact hparentAfter'
      have hanswer : originAnswer = answer := by
        exact Option.some.inj (by rw [← hparentOrigin, hparentAfter])
      have huniq := hunique originLeft value (by simpa [hanswer] using hmemOrigin)
      simpa [buildPartialTreeFromTraceAfterPasses, seed, huniq.2] using hvalue

/-- The final closed partial tree is always rooted at the claimed commitment. -/
@[simp] theorem buildPartialTreeFromTrace_root {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth) commitment trace
      ⟨0, Nat.succ_pos _⟩).head = some commitment := by
  suffices hroot :
      ∀ n : ℕ, ∀ labels : PartialLabels C depth,
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace n labels ⟨0, Nat.succ_pos _⟩).head =
          (labels ⟨0, Nat.succ_pos _⟩).head by
    simpa [buildPartialTreeFromTrace, seedRoot, Vector.head] using
      hroot (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
  intro n
  induction n with
  | zero =>
      intro labels
      simp [closeInternalQueries]
  | succ n ih =>
      intro labels
      rw [closeInternalQueries]
      rw [ih]
      exact propagateInternalQueriesOnce_root (M := M) (S := S) (C := C)
        (depth := depth) trace labels

/-- A known parent after `passes` closure passes plus a matching internal trace
entry ensures that the final closed partial tree contains some left-child
label. -/
theorem buildPartialTreeFromTrace_leftChild_exists_of_internal_after_passes
    {depth layer : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hpasses : passes + 1 ≤ depth + 1)
    (hparent :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    ∃ value : C,
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitment trace ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  have hparentClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent =
        some answer := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hparent
  rcases closeInternalQueries_leftChild_exists_of_mem_after_pass
      (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
      trace passes seed hlayer parent left right answer hparentClose hmem with
    ⟨value, hvalue⟩
  refine ⟨value, ?_⟩
  let remaining := depth + 1 - (passes + 1)
  have hsum : passes + 1 + remaining = depth + 1 := by
    omega
  have hfinal :
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (depth + 1) seed =
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace remaining
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (passes + 1) seed) := by
    rw [← hsum]
    exact closeInternalQueries_add (M := M) (S := S) (C := C)
      (depth := depth) trace (passes + 1) remaining seed
  have hpreserve :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace remaining
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (passes + 1) seed)
        ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value :=
    closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
      (depth := depth) trace remaining
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace (passes + 1) seed)
      ⟨layer + 1, hlayer⟩ (leftChildPos parent) value hvalue
  simpa [buildPartialTreeFromTrace, seed, hfinal] using hpreserve

/-- A known parent after `passes` closure passes plus a matching internal trace
entry ensures that the final closed partial tree contains some right-child
label. -/
theorem buildPartialTreeFromTrace_rightChild_exists_of_internal_after_passes
    {depth layer : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hpasses : passes + 1 ≤ depth + 1)
    (hparent :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    ∃ value : C,
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitment trace ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  have hparentClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent =
        some answer := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hparent
  rcases closeInternalQueries_rightChild_exists_of_mem_after_pass
      (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
      trace passes seed hlayer parent left right answer hparentClose hmem with
    ⟨value, hvalue⟩
  refine ⟨value, ?_⟩
  let remaining := depth + 1 - (passes + 1)
  have hsum : passes + 1 + remaining = depth + 1 := by
    omega
  have hfinal :
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (depth + 1) seed =
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace remaining
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (passes + 1) seed) := by
    rw [← hsum]
    exact closeInternalQueries_add (M := M) (S := S) (C := C)
      (depth := depth) trace (passes + 1) remaining seed
  have hpreserve :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace remaining
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (passes + 1) seed)
        ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value :=
    closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
      (depth := depth) trace remaining
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace (passes + 1) seed)
      ⟨layer + 1, hlayer⟩ (rightChildPos parent) value hvalue
  simpa [buildPartialTreeFromTrace, seed, hfinal] using hpreserve

/-- Recover a populated left child in the closure-built partial tree from the
unique internal query that opens its known parent label. -/
theorem buildPartialTreeFromTrace_leftChild_get_of_unique_internal {depth layer : ℕ}
    [DecidableEq C] (commitment : C) (trace : QueryLog (Oracle M S C))
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent :
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitment trace ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hchild :
      ∃ value : C,
        (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
          commitment trace ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace)
    (hunique :
      ∀ left' right' : C,
        ⟨Sum.inr (left', right'), answer⟩ ∈ trace →
          left' = left ∧ right' = right) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      commitment trace ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some left := by
  have htarget := hunique left right hmem
  rcases hchild with ⟨value, hvalue⟩
  have hvalueClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
        ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value := by
    simpa [buildPartialTreeFromTrace] using hvalue
  have horigin :=
    closeInternalQueries_leftChild_origin (M := M) (S := S) (C := C)
      (depth := depth) (layer := layer) trace (depth + 1)
      (seedRoot (C := C) (depth := depth) commitment) hlayer parent value hvalueClose
  cases horigin with
  | inl hseed =>
      simp [seedRoot] at hseed
  | inr hnew =>
      rcases hnew with ⟨originRight, originAnswer, hmemOrigin, hparentOrigin⟩
      have hparentClose :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
            ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
        simpa [buildPartialTreeFromTrace] using hparent
      have hanswer : originAnswer = answer := by
        exact Option.some.inj (by rw [← hparentOrigin, hparentClose])
      have huniq := hunique value originRight (by simpa [hanswer] using hmemOrigin)
      simpa [huniq.1, htarget.1] using hvalue

/-- Recover a populated right child in the closure-built partial tree from the
unique internal query that opens its known parent label. -/
theorem buildPartialTreeFromTrace_rightChild_get_of_unique_internal {depth layer : ℕ}
    [DecidableEq C] (commitment : C) (trace : QueryLog (Oracle M S C))
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hparent :
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitment trace ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hchild :
      ∃ value : C,
        (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
          commitment trace ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace)
    (hunique :
      ∀ left' right' : C,
        ⟨Sum.inr (left', right'), answer⟩ ∈ trace →
          left' = left ∧ right' = right) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      commitment trace ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some right := by
  have htarget := hunique left right hmem
  rcases hchild with ⟨value, hvalue⟩
  have hvalueClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
        ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value := by
    simpa [buildPartialTreeFromTrace] using hvalue
  have horigin :=
    closeInternalQueries_rightChild_origin (M := M) (S := S) (C := C)
      (depth := depth) (layer := layer) trace (depth + 1)
      (seedRoot (C := C) (depth := depth) commitment) hlayer parent value hvalueClose
  cases horigin with
  | inl hseed =>
      simp [seedRoot] at hseed
  | inr hnew =>
      rcases hnew with ⟨originLeft, originAnswer, hmemOrigin, hparentOrigin⟩
      have hparentClose :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
            ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
        simpa [buildPartialTreeFromTrace] using hparent
      have hanswer : originAnswer = answer := by
        exact Option.some.inj (by rw [← hparentOrigin, hparentClose])
      have huniq := hunique originLeft value (by simpa [hanswer] using hmemOrigin)
      simpa [huniq.2, htarget.2] using hvalue

/-- Exact left-child recovery from a parent known after a specified closure
pass, a matching internal trace entry, and an explicit uniqueness hypothesis for
that parent label. -/
theorem buildPartialTreeFromTrace_leftChild_get_of_unique_internal_after_passes
    {depth layer : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hpasses : passes + 1 ≤ depth + 1)
    (hparent :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace)
    (hunique :
      ∀ left' right' : C,
        ⟨Sum.inr (left', right'), answer⟩ ∈ trace →
          left' = left ∧ right' = right) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      commitment trace ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some left := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  have hparentClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent =
        some answer := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hparent
  let remainingParent := depth + 1 - passes
  have hsumParent : passes + remainingParent = depth + 1 := by
    omega
  have hparentFinal :
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitment trace ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
    have hfinal :
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (depth + 1) seed =
          closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace remainingParent
            (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
              trace passes seed) := by
      rw [← hsumParent]
      exact closeInternalQueries_add (M := M) (S := S) (C := C)
        (depth := depth) trace passes remainingParent seed
    have hpreserve :
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace remainingParent
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace passes seed)
          ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
      closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
        (depth := depth) trace remainingParent
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace passes seed)
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩ parent answer hparentClose
    simpa [buildPartialTreeFromTrace, seed, hfinal] using hpreserve
  have hchild :=
    buildPartialTreeFromTrace_leftChild_exists_of_internal_after_passes
      (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
      commitment trace passes hlayer parent left right answer hpasses hparent hmem
  exact buildPartialTreeFromTrace_leftChild_get_of_unique_internal
    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
    commitment trace hlayer parent left right answer hparentFinal hchild hmem hunique

/-- Exact right-child recovery from a parent known after a specified closure
pass, a matching internal trace entry, and an explicit uniqueness hypothesis for
that parent label. -/
theorem buildPartialTreeFromTrace_rightChild_get_of_unique_internal_after_passes
    {depth layer : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hlayer : layer + 1 < depth + 1) (parent : Fin (2 ^ layer))
    (left right answer : C)
    (hpasses : passes + 1 ≤ depth + 1)
    (hparent :
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace)
    (hunique :
      ∀ left' right' : C,
        ⟨Sum.inr (left', right'), answer⟩ ∈ trace →
          left' = left ∧ right' = right) :
    (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
      commitment trace ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some right := by
  let seed := seedRoot (C := C) (depth := depth) commitment
  have hparentClose :
      (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
        trace passes seed ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent =
        some answer := by
    simpa [buildPartialTreeFromTraceAfterPasses, seed] using hparent
  let remainingParent := depth + 1 - passes
  have hsumParent : passes + remainingParent = depth + 1 := by
    omega
  have hparentFinal :
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitment trace ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer := by
    have hfinal :
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (depth + 1) seed =
          closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace remainingParent
            (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
              trace passes seed) := by
      rw [← hsumParent]
      exact closeInternalQueries_add (M := M) (S := S) (C := C)
        (depth := depth) trace passes remainingParent seed
    have hpreserve :
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace remainingParent
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace passes seed)
          ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get parent = some answer :=
      closeInternalQueries_get_eq_of_some (M := M) (S := S) (C := C)
        (depth := depth) trace remainingParent
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace passes seed)
        ⟨layer, Nat.lt_of_succ_lt hlayer⟩ parent answer hparentClose
    simpa [buildPartialTreeFromTrace, seed, hfinal] using hpreserve
  have hchild :=
    buildPartialTreeFromTrace_rightChild_exists_of_internal_after_passes
      (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
      commitment trace passes hlayer parent left right answer hpasses hparent hmem
  exact buildPartialTreeFromTrace_rightChild_get_of_unique_internal
    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
    commitment trace hlayer parent left right answer hparentFinal hchild hmem hunique

/-- Non-dummy label values at one layer of a partial tree. -/
def knownLabelsAtLayer {depth : ℕ} (labels : PartialLabels C depth)
    (layer : Fin (depth + 1)) : List C :=
  (labels layer).toList.filterMap id

/-- Non-dummy label values in a partial tree, listed layer-by-layer. -/
def knownLabelsList {depth : ℕ} (labels : PartialLabels C depth) : List C :=
  (List.finRange (depth + 1)).flatMap fun layer => knownLabelsAtLayer labels layer

/-- The finite set of non-dummy label values in a partial tree. -/
def knownLabels {depth : ℕ} [DecidableEq C] (labels : PartialLabels C depth) : Finset C :=
  (knownLabelsList labels).toFinset

/-- The finite set of non-dummy label values extracted from a trace. -/
def traceKnownLabels {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) : Finset C :=
  knownLabels (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
    (depth := depth) commitment trace)

/-- Internal-query input labels in a trace. These form a compact superset of
all non-root labels that can become known from the trace. -/
def internalInputLabels (trace : QueryLog (Oracle M S C)) : List C :=
  match trace with
  | [] => []
  | ⟨Sum.inr (left, right), _⟩ :: rest =>
      left :: right :: internalInputLabels rest
  | ⟨Sum.inl _, _⟩ :: rest =>
      internalInputLabels rest

/-- Root plus all internal-query input labels in a trace. -/
def traceLabelCandidates (commitment : C) (trace : QueryLog (Oracle M S C)) : List C :=
  commitment :: internalInputLabels (M := M) (S := S) (C := C) trace

/-- The answer component of a typed Merkle-oracle trace entry, viewed as a
label value. -/
def traceEntryAnswer (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) : C :=
  match entry with
  | ⟨Sum.inl _, answer⟩ => answer
  | ⟨Sum.inr _, answer⟩ => answer

/-
Known-label accounting.

These lemmas expose the finite target set used by extractability probability
bounds. A commit trace of length `q` can justify at most `2q + 1` labels
(`left` and `right` inputs per internal query plus the root), and never more
than the full perfect-tree size `2^(depth + 1)`.
-/

/-- Membership in the known-label list at one layer is equivalent to some
partial-tree slot at that layer containing the value. -/
theorem mem_knownLabelsAtLayer_iff {depth : ℕ} (labels : PartialLabels C depth)
    (layer : Fin (depth + 1)) (value : C) :
    value ∈ knownLabelsAtLayer labels layer ↔
      ∃ pos : Fin (2 ^ layer.1), (labels layer).get pos = some value := by
  constructor
  · intro hmem
    rcases List.mem_filterMap.mp hmem with ⟨value?, hvalueMem, hvalue⟩
    cases value? with
    | none =>
        simp at hvalue
    | some value' =>
        simp at hvalue
        subst value'
        have hvec : some value ∈ labels layer := Vector.mem_toList_iff.mp hvalueMem
        rcases (Vector.mem_iff_getElem.mp hvec) with ⟨i, hi, hget⟩
        exact ⟨⟨i, hi⟩, by simpa using hget⟩
  · rintro ⟨pos, hget⟩
    have hvec : some value ∈ labels layer :=
      Vector.mem_iff_getElem.mpr ⟨pos.1, pos.2, by simpa using hget⟩
    exact List.mem_filterMap.mpr
      ⟨some value, Vector.mem_toList_iff.mpr hvec, rfl⟩

/-- Membership in the full known-label list is equivalent to some slot in some
layer containing the value. -/
theorem mem_knownLabelsList_iff {depth : ℕ} (labels : PartialLabels C depth)
    (value : C) :
    value ∈ knownLabelsList labels ↔
      ∃ layer : Fin (depth + 1), ∃ pos : Fin (2 ^ layer.1),
        (labels layer).get pos = some value := by
  simp [knownLabelsList, mem_knownLabelsAtLayer_iff]

/-- Finset version of `mem_knownLabelsList_iff`. -/
theorem mem_knownLabels_iff {depth : ℕ} [DecidableEq C]
    (labels : PartialLabels C depth) (value : C) :
    value ∈ knownLabels labels ↔
      ∃ layer : Fin (depth + 1), ∃ pos : Fin (2 ^ layer.1),
        (labels layer).get pos = some value := by
  simp [knownLabels, mem_knownLabelsList_iff]

/-- Membership in `traceKnownLabels` means the closed partial tree built from
that trace contains the value at some layer and position. -/
theorem mem_traceKnownLabels_iff {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (value : C) :
    value ∈ traceKnownLabels (M := M) (S := S) (C := C)
        (depth := depth) commitment trace ↔
      ∃ layer : Fin (depth + 1), ∃ pos : Fin (2 ^ layer.1),
        (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment trace layer).get pos = some value := by
  simp [traceKnownLabels, mem_knownLabels_iff]

/-- Convenience introduction rule for `traceKnownLabels`. -/
theorem mem_traceKnownLabels_of_get_eq_some {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C))
    (layer : Fin (depth + 1)) (pos : Fin (2 ^ layer.1)) (value : C)
    (hget :
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment trace layer).get pos = some value) :
    value ∈ traceKnownLabels (M := M) (S := S) (C := C)
      (depth := depth) commitment trace := by
  exact (mem_traceKnownLabels_iff (M := M) (S := S) (C := C)
    (depth := depth) commitment trace value).mpr ⟨layer, pos, hget⟩

/-- The left input of an internal trace query appears in
`internalInputLabels`. -/
theorem mem_internalInputLabels_left_of_mem {trace : QueryLog (Oracle M S C)}
    {left right answer : C}
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    left ∈ internalInputLabels (M := M) (S := S) (C := C) trace := by
  induction trace with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        simp [internalInputLabels]
      · cases entry with
        | mk domain queryAnswer =>
            cases domain with
            | inl ms =>
                simpa [internalInputLabels] using ih htail
            | inr pair =>
                rcases pair with ⟨queryLeft, queryRight⟩
                simpa [internalInputLabels] using (Or.inr (Or.inr (ih htail)))

/-- The right input of an internal trace query appears in
`internalInputLabels`. -/
theorem mem_internalInputLabels_right_of_mem {trace : QueryLog (Oracle M S C)}
    {left right answer : C}
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ trace) :
    right ∈ internalInputLabels (M := M) (S := S) (C := C) trace := by
  induction trace with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        simp [internalInputLabels]
      · cases entry with
        | mk domain queryAnswer =>
            cases domain with
            | inl ms =>
                simpa [internalInputLabels] using ih htail
            | inr pair =>
                rcases pair with ⟨queryLeft, queryRight⟩
                simpa [internalInputLabels] using (Or.inr (Or.inr (ih htail)))

private theorem leftChildPos_parentPos_self_of_even {layer : ℕ}
    (pos : Fin (2 ^ (layer + 1))) (hpos : pos.1 % 2 = 0) :
    leftChildPos (parentPos pos) = pos := by
  apply Fin.ext
  simp [leftChildPos, parentPos]
  omega

private theorem rightChildPos_parentPos_self_of_odd {layer : ℕ}
    (pos : Fin (2 ^ (layer + 1))) (hpos : pos.1 % 2 = 1) :
    rightChildPos (parentPos pos) = pos := by
  apply Fin.ext
  simp [rightChildPos, parentPos]
  omega

/-- Every known label in the closed partial tree is in the compact candidate
list consisting of the commitment and internal-query input labels from the
trace. -/
theorem mem_traceLabelCandidates_of_get_eq_some {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C))
    (layer : Fin (depth + 1)) (pos : Fin (2 ^ layer.1)) (value : C)
    (hget :
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment trace layer).get pos = some value) :
    value ∈ traceLabelCandidates (M := M) (S := S) (C := C) commitment trace := by
  rcases layer with ⟨(_ | layer), hlayer⟩
  · have hroot :
        (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment trace ⟨0, hlayer⟩).get pos =
        some commitment := by
        have hpos : pos = 0 := by
          apply Fin.ext
          have hpow : 2 ^ (⟨0, hlayer⟩ : Fin (depth + 1)).1 = 1 := by
            simp
          have hlt : pos.1 < 1 := by
            simpa [hpow] using pos.2
          omega
        subst hpos
        simpa [Vector.head] using
          buildPartialTreeFromTrace_root (M := M) (S := S) (C := C)
            (depth := depth) commitment trace
    have hvalue : value = commitment := Option.some.inj (by rw [← hget, hroot])
    simp [traceLabelCandidates, hvalue]
  · have hclose :
        (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
          ⟨layer + 1, hlayer⟩).get pos = some value := by
        simpa [buildPartialTreeFromTrace] using hget
    by_cases hparity : pos.1 % 2 = 0
    · let parent : Fin (2 ^ layer) := parentPos pos
      have hpos : leftChildPos parent = pos :=
        leftChildPos_parentPos_self_of_even (layer := layer) pos hparity
      have hleft :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
            ⟨layer + 1, hlayer⟩).get (leftChildPos parent) = some value := by
        simpa [hpos] using hclose
      have horigin :=
        closeInternalQueries_leftChild_origin (M := M) (S := S) (C := C)
          (depth := depth) (layer := layer) trace (depth + 1)
          (seedRoot (C := C) (depth := depth) commitment) hlayer parent value hleft
      cases horigin with
      | inl hseed =>
          simp [seedRoot] at hseed
      | inr hnew =>
          rcases hnew with ⟨right, answer, hmem, _⟩
          exact List.mem_cons_of_mem _
            (mem_internalInputLabels_left_of_mem (M := M) (S := S) (C := C) hmem)
    · have hodd : pos.1 % 2 = 1 := by
        have hlt := Nat.mod_lt pos.1 (by decide : 0 < 2)
        omega
      let parent : Fin (2 ^ layer) := parentPos pos
      have hpos : rightChildPos parent = pos :=
        rightChildPos_parentPos_self_of_odd (layer := layer) pos hodd
      have hright :
          (closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
            trace (depth + 1) (seedRoot (C := C) (depth := depth) commitment)
            ⟨layer + 1, hlayer⟩).get (rightChildPos parent) = some value := by
        simpa [hpos] using hclose
      have horigin :=
        closeInternalQueries_rightChild_origin (M := M) (S := S) (C := C)
          (depth := depth) (layer := layer) trace (depth + 1)
          (seedRoot (C := C) (depth := depth) commitment) hlayer parent value hright
      cases horigin with
      | inl hseed =>
          simp [seedRoot] at hseed
      | inr hnew =>
          rcases hnew with ⟨left, answer, hmem, _⟩
          exact List.mem_cons_of_mem _
            (mem_internalInputLabels_right_of_mem (M := M) (S := S) (C := C) hmem)

/-- Every label reconstructed from a trace is either the root commitment or an
input to an internal query in the trace. -/
theorem traceKnownLabels_subset_candidates {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    traceKnownLabels (M := M) (S := S) (C := C) (depth := depth) commitment trace ⊆
      (traceLabelCandidates (M := M) (S := S) (C := C) commitment trace).toFinset := by
  intro value hvalue
  rcases (mem_traceKnownLabels_iff (M := M) (S := S) (C := C)
      (depth := depth) commitment trace value).mp hvalue with
    ⟨layer, pos, hget⟩
  exact (List.mem_toFinset).mpr
    (mem_traceLabelCandidates_of_get_eq_some (M := M) (S := S) (C := C)
      (depth := depth) commitment trace layer pos value hget)

/-- Internal-query input labels contribute at most two candidates per trace
entry. -/
private theorem internalInputLabels_length_le (trace : QueryLog (Oracle M S C)) :
    (internalInputLabels (M := M) (S := S) (C := C) trace).length ≤ 2 * trace.length := by
  induction trace with
  | nil =>
      simp [internalInputLabels]
  | cons entry rest ih =>
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              simp [internalInputLabels]
              omega
          | inr pair =>
              rcases pair with ⟨left, right⟩
              simp [internalInputLabels]
              omega

/-- Candidate-list length bound: root plus at most two inputs per trace entry. -/
theorem traceLabelCandidates_length_le (commitment : C)
    (trace : QueryLog (Oracle M S C)) :
    (traceLabelCandidates (M := M) (S := S) (C := C) commitment trace).length ≤
      2 * trace.length + 1 := by
  simp [traceLabelCandidates]
  exact internalInputLabels_length_le (M := M) (S := S) (C := C) trace

/-- Query-count target bound for extractability:
`|traceKnownLabels| <= 2 * trace.length + 1`. -/
theorem traceKnownLabels_card_le_trace_length {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    (traceKnownLabels (M := M) (S := S) (C := C) (depth := depth) commitment trace).card ≤
      2 * trace.length + 1 := by
  calc
    (traceKnownLabels (M := M) (S := S) (C := C)
        (depth := depth) commitment trace).card
        ≤ ((traceLabelCandidates (M := M) (S := S) (C := C)
          commitment trace).toFinset).card :=
          Finset.card_le_card
            (traceKnownLabels_subset_candidates (M := M) (S := S) (C := C)
              (depth := depth) commitment trace)
    _ ≤ (traceLabelCandidates (M := M) (S := S) (C := C)
          commitment trace).length :=
          List.toFinset_card_le _
    _ ≤ 2 * trace.length + 1 :=
          traceLabelCandidates_length_le (M := M) (S := S) (C := C) commitment trace

/-- At one layer, the number of known labels is bounded by the layer width. -/
private theorem knownLabelsAtLayer_length_le {depth : ℕ} (labels : PartialLabels C depth)
    (layer : Fin (depth + 1)) :
    (knownLabelsAtLayer labels layer).length ≤ 2 ^ layer.1 := by
  rw [knownLabelsAtLayer, List.filterMap_eq_flatMap_toList]
  rw [List.length_flatMap]
  calc
    ((labels layer).toList.map fun value => (id value).toList.length).sum
        ≤ ((labels layer).toList.map fun _ => 1).sum := by
          apply List.sum_le_sum
          intro value _
          cases value <;> simp
    _ = (labels layer).toList.length := by
          simp
    _ = 2 ^ layer.1 := by
          simp

/-- Pull a factor of two out of a finite list sum. -/
private theorem list_sum_map_two_mul (xs : List ℕ) :
    (xs.map fun x => 2 * x).sum = 2 * xs.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.mul_add]

/-- Perfect-binary-tree arithmetic:
`1 + sum_{i < n} 2^i <= 2^n`. -/
private theorem finRange_pow_two_sum_add_one_le : ∀ n : ℕ,
    ((List.finRange n).map fun i => 2 ^ i.1).sum + 1 ≤ 2 ^ n
  | 0 => by
      simp
  | n + 1 => by
      have ih := finRange_pow_two_sum_add_one_le n
      rw [List.finRange_succ]
      simp only [List.map_cons, List.sum_cons, Fin.val_zero, pow_zero, List.map_map]
      change 1 + (List.map (fun x : Fin n => 2 ^ (x.1 + 1)) (List.finRange n)).sum + 1 ≤
        2 ^ (n + 1)
      rw [show (List.map (fun x : Fin n => 2 ^ (x.1 + 1)) (List.finRange n)) =
          (List.map (fun x : Fin n => 2 * 2 ^ x.1) (List.finRange n)) by
        apply List.map_congr_left
        intro x _
        rw [pow_succ]
        omega]
      rw [show (List.map (fun x : Fin n => 2 * 2 ^ x.1) (List.finRange n)) =
          (List.map (fun y : ℕ => 2 * y) ((List.finRange n).map fun x => 2 ^ x.1)) by
        rw [List.map_map]
        rfl]
      rw [list_sum_map_two_mul]
      rw [pow_succ]
      omega

/-- Tree-size target bound: a depth-`d` partial tree has at most
`2^(d + 1)` known labels. -/
private theorem knownLabelsList_length_le {depth : ℕ} (labels : PartialLabels C depth) :
    (knownLabelsList labels).length ≤ 2 ^ (depth + 1) := by
  rw [knownLabelsList, List.length_flatMap]
  calc
    ((List.finRange (depth + 1)).map fun layer =>
        (knownLabelsAtLayer labels layer).length).sum
        ≤ ((List.finRange (depth + 1)).map fun layer => 2 ^ layer.1).sum := by
          apply List.sum_le_sum
          intro layer _
          exact knownLabelsAtLayer_length_le labels layer
    _ ≤ 2 ^ (depth + 1) := by
          have h := finRange_pow_two_sum_add_one_le (depth + 1)
          omega

/-- Tree-size cardinality bound for `traceKnownLabels`. -/
theorem traceKnownLabels_card_le_tree_size {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    (traceKnownLabels (M := M) (S := S) (C := C) (depth := depth) commitment trace).card ≤
      2 ^ (depth + 1) := by
  calc
    (traceKnownLabels (M := M) (S := S) (C := C)
        (depth := depth) commitment trace).card
        ≤ (knownLabelsList (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment trace)).length :=
          List.toFinset_card_le _
    _ ≤ 2 ^ (depth + 1) :=
          knownLabelsList_length_le
            (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
              (depth := depth) commitment trace)

/-- Final target-count bound used in extractability:

`|traceKnownLabels| <= min (2 * trace.length + 1) (2^(depth + 1))`. -/
theorem traceKnownLabels_card_le_min {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    (traceKnownLabels (M := M) (S := S) (C := C) (depth := depth) commitment trace).card ≤
      min (2 * trace.length + 1) (2 ^ (depth + 1)) := by
  exact le_min
    (traceKnownLabels_card_le_trace_length (M := M) (S := S) (C := C)
      (depth := depth) commitment trace)
    (traceKnownLabels_card_le_tree_size (M := M) (S := S) (C := C)
      (depth := depth) commitment trace)

/-- Labels known after an intermediate closure pass are included in the final
`traceKnownLabels` target set. -/
theorem knownLabels_after_passes_subset_traceKnownLabels {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (passes : ℕ)
    (hpasses : passes ≤ depth + 1) :
    knownLabels (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
      (depth := depth) commitment trace passes) ⊆
      traceKnownLabels (M := M) (S := S) (C := C) (depth := depth) commitment trace := by
  intro value hvalue
  rcases (mem_knownLabels_iff (C := C)
      (buildPartialTreeFromTraceAfterPasses (M := M) (S := S) (C := C)
        (depth := depth) commitment trace passes) value).mp hvalue with
    ⟨layer, pos, hget⟩
  exact mem_traceKnownLabels_of_get_eq_some (M := M) (S := S) (C := C)
    (depth := depth) commitment trace layer pos value
    (buildPartialTreeFromTrace_get_eq_of_after_passes
      (M := M) (S := S) (C := C) (depth := depth)
      commitment trace passes layer pos value hpasses hget)

private theorem partitionTrace_foldr_internalQueries
    (trace : QueryLog (Oracle M S C)) (acc : TracePartition M S C) :
    (trace.foldr
      (fun entry acc =>
        match entry.1 with
        | Sum.inl _ => { acc with leafQueries := entry :: acc.leafQueries }
        | Sum.inr _ => { acc with internalQueries := entry :: acc.internalQueries })
      acc).internalQueries =
      (partitionTrace (M := M) (S := S) (C := C) trace).internalQueries ++
        acc.internalQueries := by
  induction trace with
  | nil =>
      simp [partitionTrace]
  | cons entry rest ih =>
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              simpa [partitionTrace, ih]
          | inr pair =>
              simpa [partitionTrace, ih]

theorem partitionTrace_internalQueries_append
    (left right : QueryLog (Oracle M S C)) :
    (partitionTrace (M := M) (S := S) (C := C) (left ++ right)).internalQueries =
      (partitionTrace (M := M) (S := S) (C := C) left).internalQueries ++
        (partitionTrace (M := M) (S := S) (C := C) right).internalQueries := by
  unfold partitionTrace
  rw [List.foldr_append]
  exact partitionTrace_foldr_internalQueries (M := M) (S := S) (C := C) left
    (partitionTrace (M := M) (S := S) (C := C) right)

private theorem propagateInternalQueryAtLayer_eq_self_of_answer_not_parent
    {layer : ℕ} [DecidableEq C] (left right answer : C)
    (oldChildren : Vector (Option C) (2 ^ (layer + 1)))
    (parents : Vector (Option C) (2 ^ layer))
    (hanswer : ∀ parent : Fin (2 ^ layer), parents.get parent ≠ some answer) :
    propagateInternalQueryAtLayer left right answer oldChildren parents = oldChildren := by
  apply Vector.ext
  intro i hi
  let pos : Fin (2 ^ (layer + 1)) := ⟨i, hi⟩
  change (propagateInternalQueryAtLayer left right answer oldChildren parents).get pos =
    oldChildren.get pos
  simp [propagateInternalQueryAtLayer]
  cases hchild : oldChildren.get pos with
  | some value =>
      simp [hchild]
  | none =>
      cases hparent : parents.get (parentPos pos) with
      | none =>
          simp [hchild, hparent]
      | some parentValue =>
          have hne : parentValue ≠ answer := by
            intro heq
            exact hanswer (parentPos pos) (by simp [hparent, heq])
          simp [hchild, hparent, hne]

private theorem propagateInternalQueryUsingBase_eq_self_of_answer_not_known
    {depth : ℕ} [DecidableEq C] (left right answer : C)
    (baseLabels currentLabels : PartialLabels C depth)
    (hanswer : answer ∉ knownLabels baseLabels) :
    propagateInternalQueryUsingBase (depth := depth) left right answer
      baseLabels currentLabels = currentLabels := by
  funext layer
  rcases layer with ⟨(_ | layer), hlayer⟩
  · simp [propagateInternalQueryUsingBase]
  · apply propagateInternalQueryAtLayer_eq_self_of_answer_not_parent
    intro parent hparent
    exact hanswer ((mem_knownLabels_iff (C := C) baseLabels answer).mpr
      ⟨⟨layer, Nat.lt_of_succ_lt hlayer⟩, parent, hparent⟩)

private theorem propagateInternalQueriesFold_eq_self_of_answers_not_known
    {depth : ℕ} [DecidableEq C] :
    ∀ (entries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth),
      (∀ left right answer,
        ⟨Sum.inr (left, right), answer⟩ ∈ entries →
          answer ∉ knownLabels baseLabels) →
        entries.foldl
          (fun current entry =>
            match entry with
            | ⟨Sum.inr (left, right), answer⟩ =>
                propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels current
            | ⟨Sum.inl _, _⟩ => current)
          currentLabels = currentLabels
  | [], _, currentLabels, _ => by
      rfl
  | entry :: entries, baseLabels, currentLabels, hanswers => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              exact propagateInternalQueriesFold_eq_self_of_answers_not_known
                (depth := depth)
                entries baseLabels currentLabels
                (fun left right queryAnswer hmem =>
                  hanswers left right queryAnswer (List.mem_cons_of_mem _ hmem))
          | inr pair =>
              rcases pair with ⟨left, right⟩
              rw [List.foldl_cons]
              simp only
              rw [propagateInternalQueryUsingBase_eq_self_of_answer_not_known
                (depth := depth) left right answer baseLabels currentLabels
                (hanswers left right answer (by simp))]
              exact propagateInternalQueriesFold_eq_self_of_answers_not_known
                (depth := depth)
                entries baseLabels currentLabels
                (fun left' right' queryAnswer hmem =>
                  hanswers left' right' queryAnswer (List.mem_cons_of_mem _ hmem))

private theorem propagateInternalQueryUsingBase_eq_self_of_mem_fold
    {depth : ℕ} [DecidableEq C]
    (entries : QueryLog (Oracle M S C)) (left right answer : C)
    (baseLabels currentLabels : PartialLabels C depth)
    (hmem : ⟨Sum.inr (left, right), answer⟩ ∈ entries) :
    propagateInternalQueryUsingBase (depth := depth) left right answer baseLabels
        (entries.foldl
          (fun current entry =>
            match entry with
            | ⟨Sum.inr (left, right), answer⟩ =>
                propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels current
            | ⟨Sum.inl _, _⟩ => current)
          currentLabels) =
      entries.foldl
        (fun current entry =>
          match entry with
          | ⟨Sum.inr (left, right), answer⟩ =>
              propagateInternalQueryUsingBase (depth := depth)
                left right answer baseLabels current
          | ⟨Sum.inl _, _⟩ => current)
        currentLabels := by
  funext layer
  rcases layer with ⟨(_ | layer), hlayer⟩
  · simp [propagateInternalQueryUsingBase]
  · apply Vector.ext
    intro i hi
    let pos : Fin (2 ^ (layer + 1)) := ⟨i, hi⟩
    let folded : PartialLabels C depth :=
      entries.foldl
        (fun current entry =>
          match entry with
          | ⟨Sum.inr (left, right), answer⟩ =>
              propagateInternalQueryUsingBase (depth := depth)
                left right answer baseLabels current
          | ⟨Sum.inl _, _⟩ => current)
        currentLabels
    change
      (propagateInternalQueryAtLayer left right answer
          (folded ⟨layer + 1, hlayer⟩)
          (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩)).get pos =
        (folded ⟨layer + 1, hlayer⟩).get pos
    cases hchild : (folded ⟨layer + 1, hlayer⟩).get pos with
    | some value =>
        simp [propagateInternalQueryAtLayer, hchild]
    | none =>
        cases hparent :
            (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get (parentPos pos) with
        | none =>
            simp [propagateInternalQueryAtLayer, hchild, hparent]
        | some parentValue =>
            by_cases hanswer : parentValue = answer
            · have hparentAnswer :
                  (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩).get
                    (parentPos pos) = some answer := by
                simpa [hanswer] using hparent
              by_cases hparity : pos.1 % 2 = 0
              · have hpos : leftChildPos (parentPos pos) = pos :=
                  leftChildPos_parentPos_self_of_even (layer := layer) pos hparity
                rcases propagateInternalQueriesFold_leftChild_exists_of_mem
                    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
                    entries baseLabels currentLabels hlayer (parentPos pos)
                    left right answer hparentAnswer hmem with
                  ⟨value, hvalue⟩
                have hvaluePos :
                    (folded ⟨layer + 1, hlayer⟩).get pos = some value := by
                  simpa [folded, hpos] using hvalue
                rw [hchild] at hvaluePos
                cases hvaluePos
              · have hodd : pos.1 % 2 = 1 := by
                  have hlt := Nat.mod_lt pos.1 (by decide : 0 < 2)
                  omega
                have hpos : rightChildPos (parentPos pos) = pos :=
                  rightChildPos_parentPos_self_of_odd (layer := layer) pos hodd
                rcases propagateInternalQueriesFold_rightChild_exists_of_mem
                    (M := M) (S := S) (C := C) (depth := depth) (layer := layer)
                    entries baseLabels currentLabels hlayer (parentPos pos)
                    left right answer hparentAnswer hmem with
                  ⟨value, hvalue⟩
                have hvaluePos :
                    (folded ⟨layer + 1, hlayer⟩).get pos = some value := by
                  simpa [folded, hpos] using hvalue
                rw [hchild] at hvaluePos
                cases hvaluePos
            · simp [propagateInternalQueryAtLayer, hchild, hparent, hanswer]

private theorem propagateInternalQueriesFold_eq_self_of_mem_or_answers_not_known
    {depth : ℕ} [DecidableEq C] :
    ∀ (leftEntries rightEntries : QueryLog (Oracle M S C))
      (baseLabels currentLabels : PartialLabels C depth),
      (∀ queryLeft queryRight answer,
        ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ rightEntries →
          ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ leftEntries ∨
            answer ∉ knownLabels baseLabels) →
        rightEntries.foldl
          (fun current entry =>
            match entry with
            | ⟨Sum.inr (left, right), answer⟩ =>
                propagateInternalQueryUsingBase (depth := depth)
                  left right answer baseLabels current
            | ⟨Sum.inl _, _⟩ => current)
          (leftEntries.foldl
            (fun current entry =>
              match entry with
              | ⟨Sum.inr (left, right), answer⟩ =>
                  propagateInternalQueryUsingBase (depth := depth)
                    left right answer baseLabels current
              | ⟨Sum.inl _, _⟩ => current)
            currentLabels) =
          leftEntries.foldl
            (fun current entry =>
              match entry with
              | ⟨Sum.inr (left, right), answer⟩ =>
                  propagateInternalQueryUsingBase (depth := depth)
                    left right answer baseLabels current
              | ⟨Sum.inl _, _⟩ => current)
            currentLabels
  | _, [], _, _, _ => by
      rfl
  | leftEntries, entry :: entries, baseLabels, currentLabels, hanswers => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              exact propagateInternalQueriesFold_eq_self_of_mem_or_answers_not_known
                (depth := depth)
                leftEntries entries baseLabels currentLabels
                (fun queryLeft queryRight queryAnswer hmem =>
                  hanswers queryLeft queryRight queryAnswer (List.mem_cons_of_mem _ hmem))
          | inr pair =>
              rcases pair with ⟨queryLeft, queryRight⟩
              rw [List.foldl_cons]
              simp only
              cases hanswers queryLeft queryRight answer (by simp) with
              | inl hmemLeft =>
                  rw [propagateInternalQueryUsingBase_eq_self_of_mem_fold
                    (M := M) (S := S) (C := C) (depth := depth)
                    leftEntries queryLeft queryRight answer baseLabels currentLabels hmemLeft]
                  exact propagateInternalQueriesFold_eq_self_of_mem_or_answers_not_known
                    (depth := depth)
                    leftEntries entries baseLabels currentLabels
                    (fun queryLeft' queryRight' queryAnswer hmem =>
                      hanswers queryLeft' queryRight' queryAnswer
                        (List.mem_cons_of_mem _ hmem))
              | inr hnotKnown =>
                  rw [propagateInternalQueryUsingBase_eq_self_of_answer_not_known
                    (depth := depth)
                    queryLeft queryRight answer baseLabels
                    (leftEntries.foldl
                      (fun current entry =>
                        match entry with
                        | ⟨Sum.inr (left, right), answer⟩ =>
                            propagateInternalQueryUsingBase (depth := depth)
                              left right answer baseLabels current
                        | ⟨Sum.inl _, _⟩ => current)
                      currentLabels)
                    hnotKnown]
                  exact propagateInternalQueriesFold_eq_self_of_mem_or_answers_not_known
                    (depth := depth)
                    leftEntries entries baseLabels currentLabels
                    (fun queryLeft' queryRight' queryAnswer hmem =>
                      hanswers queryLeft' queryRight' queryAnswer
                        (List.mem_cons_of_mem _ hmem))

private theorem propagateInternalQueriesOnce_append_eq_left_of_answers_not_known
    {depth : ℕ} [DecidableEq C]
    (left right : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (hanswers : ∀ queryLeft queryRight answer,
      ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ right →
        answer ∉ knownLabels labels) :
    propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
      (left ++ right) labels =
      propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
        left labels := by
  unfold propagateInternalQueriesOnce
  rw [partitionTrace_internalQueries_append (M := M) (S := S) (C := C) left right]
  rw [List.foldl_append]
  exact propagateInternalQueriesFold_eq_self_of_answers_not_known
    (depth := depth)
    (partitionTrace (M := M) (S := S) (C := C) right).internalQueries labels
    (((partitionTrace (M := M) (S := S) (C := C) left).internalQueries).foldl
      (fun current entry =>
        match entry with
        | ⟨Sum.inr (left, right), answer⟩ =>
            propagateInternalQueryUsingBase (depth := depth)
              left right answer labels current
        | ⟨Sum.inl _, _⟩ => current)
      labels)
    (fun queryLeft queryRight answer hmem =>
      hanswers queryLeft queryRight answer
        ((mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
          right ⟨Sum.inr (queryLeft, queryRight), answer⟩).mp hmem).1)

private theorem propagateInternalQueriesOnce_append_eq_left_of_mem_or_answers_not_known
    {depth : ℕ} [DecidableEq C]
    (left right : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (hanswers : ∀ queryLeft queryRight answer,
      ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ right →
        ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ left ∨
          answer ∉ knownLabels labels) :
    propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
      (left ++ right) labels =
      propagateInternalQueriesOnce (M := M) (S := S) (C := C) (depth := depth)
        left labels := by
  unfold propagateInternalQueriesOnce
  rw [partitionTrace_internalQueries_append (M := M) (S := S) (C := C) left right]
  rw [List.foldl_append]
  exact propagateInternalQueriesFold_eq_self_of_mem_or_answers_not_known
    (M := M) (S := S) (C := C) (depth := depth)
    (partitionTrace (M := M) (S := S) (C := C) left).internalQueries
    (partitionTrace (M := M) (S := S) (C := C) right).internalQueries labels labels
    (fun queryLeft queryRight answer hmem =>
      Or.imp
        (fun hmemLeft =>
          (mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
            left ⟨Sum.inr (queryLeft, queryRight), answer⟩).mpr
            ⟨hmemLeft, ⟨(queryLeft, queryRight), rfl⟩⟩)
        id
        (hanswers queryLeft queryRight answer
          ((mem_partitionTrace_internalQueries_iff (M := M) (S := S) (C := C)
            right ⟨Sum.inr (queryLeft, queryRight), answer⟩).mp hmem).1))

private theorem closeInternalQueries_append_eq_left_of_answers_not_final
    {depth : ℕ} [DecidableEq C]
    (commitment : C) (commitTrace openTrace : QueryLog (Oracle M S C))
    (hanswers : ∀ queryLeft queryRight answer,
      ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ openTrace →
        answer ∉ traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace) :
    ∀ n : ℕ, n ≤ depth + 1 →
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          (commitTrace ++ openTrace) n (seedRoot (C := C) (depth := depth) commitment) =
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          commitTrace n (seedRoot (C := C) (depth := depth) commitment)
  | 0, _ => by
      rfl
  | n + 1, hn => by
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        (M := M) (S := S) (C := C) (depth := depth)
        (commitTrace ++ openTrace) n]
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        (M := M) (S := S) (C := C) (depth := depth) commitTrace n]
      rw [closeInternalQueries_append_eq_left_of_answers_not_final
        (depth := depth)
        commitment commitTrace openTrace hanswers n (by omega)]
      apply propagateInternalQueriesOnce_append_eq_left_of_answers_not_known
      intro queryLeft queryRight answer hmem hknown
      have hsubset :=
        knownLabels_after_passes_subset_traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace n (by omega)
      exact hanswers queryLeft queryRight answer hmem (hsubset (by
        simpa [buildPartialTreeFromTraceAfterPasses] using hknown))

/-- Appending internal queries whose answers are not already known cannot
change the closed partial label tree. -/
theorem buildPartialTreeFromTrace_append_eq_left_of_answers_not_mem
    {depth : ℕ} [DecidableEq C]
    (commitment : C) (commitTrace openTrace : QueryLog (Oracle M S C))
    (hanswers : ∀ queryLeft queryRight answer,
      ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ openTrace →
        answer ∉ traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace) :
    buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment (commitTrace ++ openTrace) =
      buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment commitTrace := by
  simpa [buildPartialTreeFromTrace] using
    closeInternalQueries_append_eq_left_of_answers_not_final
      (M := M) (S := S) (C := C) (depth := depth)
      commitment commitTrace openTrace hanswers (depth + 1) (by rfl)

private theorem closeInternalQueries_append_eq_left_of_mem_or_answers_not_final
    {depth : ℕ} [DecidableEq C]
    (commitment : C) (commitTrace openTrace : QueryLog (Oracle M S C))
    (hanswers : ∀ queryLeft queryRight answer,
      ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ openTrace →
        ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ commitTrace ∨
          answer ∉ traceKnownLabels (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) :
    ∀ n : ℕ, n ≤ depth + 1 →
      closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          (commitTrace ++ openTrace) n (seedRoot (C := C) (depth := depth) commitment) =
        closeInternalQueries (M := M) (S := S) (C := C) (depth := depth)
          commitTrace n (seedRoot (C := C) (depth := depth) commitment)
  | 0, _ => by
      rfl
  | n + 1, hn => by
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        (M := M) (S := S) (C := C) (depth := depth)
        (commitTrace ++ openTrace) n]
      rw [closeInternalQueries_succ_eq_propagateInternalQueriesOnce_close
        (M := M) (S := S) (C := C) (depth := depth) commitTrace n]
      rw [closeInternalQueries_append_eq_left_of_mem_or_answers_not_final
        (depth := depth)
        commitment commitTrace openTrace hanswers n (by omega)]
      apply propagateInternalQueriesOnce_append_eq_left_of_mem_or_answers_not_known
      intro queryLeft queryRight answer hmem
      cases hanswers queryLeft queryRight answer hmem with
      | inl hmemCommit =>
          exact Or.inl hmemCommit
      | inr hnotKnown =>
          right
          intro hknown
          have hsubset :=
            knownLabels_after_passes_subset_traceKnownLabels (M := M) (S := S) (C := C)
              (depth := depth) commitment commitTrace n (by omega)
          exact hnotKnown (hsubset (by
            simpa [buildPartialTreeFromTraceAfterPasses] using hknown))

private theorem buildPartialTreeFromTrace_append_eq_left_of_mem_or_answers_not_mem
    {depth : ℕ} [DecidableEq C]
    (commitment : C) (commitTrace openTrace : QueryLog (Oracle M S C))
    (hanswers : ∀ queryLeft queryRight answer,
      ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ openTrace →
        ⟨Sum.inr (queryLeft, queryRight), answer⟩ ∈ commitTrace ∨
          answer ∉ traceKnownLabels (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) :
    buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment (commitTrace ++ openTrace) =
      buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment commitTrace := by
  simpa [buildPartialTreeFromTrace] using
    closeInternalQueries_append_eq_left_of_mem_or_answers_not_final
      (M := M) (S := S) (C := C) (depth := depth)
      commitment commitTrace openTrace hanswers (depth + 1) (by rfl)

/-
Leaf-population closure.

After internal labels are reconstructed, a leaf query
`H(message, salt) = answer` can recover a leaf opening only when the leaf label
slot is already known to be `answer`. These lemmas mirror the internal closure
lemmas above and are used by the same-tree extractability proof.
-/

/-- Apply one leaf query to the partial leaf table. -/
private def populateLeafQuery {depth : ℕ} [DecidableEq C] (message : M) (salt : S) (answer : C)
    (labels : PartialLabels C depth) (leaves : PartialLeaves M S depth) :
    PartialLeaves M S depth :=
  Vector.ofFn fun idx =>
    match leaves.get idx with
    | some value => some value
    | none =>
        match (labels ⟨depth, Nat.lt_succ_self _⟩).get idx with
        | some label => if label = answer then some (message, salt) else none
        | none => none

private theorem populateLeafQuery_get_eq_of_some {depth : ℕ} [DecidableEq C]
    (queryMessage : M) (querySalt : S) (queryAnswer : C)
    (labels : PartialLabels C depth) (leaves : PartialLeaves M S depth) (idx : Index depth)
    (value : M × S) (hvalue : leaves.get idx = some value) :
    (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
      queryMessage querySalt queryAnswer labels leaves).get idx = some value := by
  simp [populateLeafQuery, hvalue]

private theorem populateLeafQuery_get_eq_some_of_none {depth : ℕ} [DecidableEq C]
    (message : M) (salt : S) (answer : C)
    (labels : PartialLabels C depth) (leaves : PartialLeaves M S depth) (idx : Index depth)
    (hleaves : leaves.get idx = none)
    (hlabel : (labels ⟨depth, Nat.lt_succ_self _⟩).get idx = some answer) :
    (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
      message salt answer labels leaves).get idx = some (message, salt) := by
  simp [populateLeafQuery, hleaves, hlabel]

private theorem populateLeavesFold_get_eq_of_some {depth : ℕ} [DecidableEq C]
    (labels : PartialLabels C depth) :
    ∀ (entries : QueryLog (Oracle M S C)) (leaves : PartialLeaves M S depth)
      (idx : Index depth) (value : M × S),
      leaves.get idx = some value →
        (entries.foldl
            (fun leaves entry =>
              match entry with
              | ⟨Sum.inl (message, salt), answer⟩ =>
                  populateLeafQuery (depth := depth) message salt answer labels leaves
              | ⟨Sum.inr _, _⟩ => leaves)
            leaves).get idx = some value
  | [], _, _, _, hvalue => by
      simpa using hvalue
  | entry :: entries, leaves, idx, value, hvalue => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              rcases ms with ⟨message, salt⟩
              exact populateLeavesFold_get_eq_of_some labels entries
                (populateLeafQuery (depth := depth) message salt answer labels leaves)
                idx value
                (populateLeafQuery_get_eq_of_some (M := M) (S := S) (C := C)
                  (depth := depth) message salt answer labels leaves idx value hvalue)
          | inr cs =>
              exact populateLeavesFold_get_eq_of_some labels entries leaves idx value hvalue

private theorem populateLeafQuery_get_eq_none_or_target_of_unique {depth : ℕ}
    [DecidableEq C] (targetMessage : M) (targetSalt : S) (targetAnswer : C)
    (queryMessage : M) (querySalt : S) (queryAnswer : C)
    (labels : PartialLabels C depth) (leaves : PartialLeaves M S depth) (idx : Index depth)
    (hlabel : (labels ⟨depth, Nat.lt_succ_self _⟩).get idx = some targetAnswer)
    (hstate : leaves.get idx = none ∨ leaves.get idx = some (targetMessage, targetSalt))
    (hunique :
      queryAnswer = targetAnswer → queryMessage = targetMessage ∧ querySalt = targetSalt) :
    (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
      queryMessage querySalt queryAnswer labels leaves).get idx = none ∨
      (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
        queryMessage querySalt queryAnswer labels leaves).get idx =
        some (targetMessage, targetSalt) := by
  cases hstate with
  | inl hnone =>
      by_cases hanswer : queryAnswer = targetAnswer
      · rcases hunique hanswer with ⟨hmessage, hsalt⟩
        subst queryAnswer
        subst queryMessage
        subst querySalt
        exact Or.inr (populateLeafQuery_get_eq_some_of_none
          (M := M) (S := S) (C := C) (depth := depth)
          targetMessage targetSalt targetAnswer labels leaves idx hnone hlabel)
      · have hlabelNe :
            (labels ⟨depth, Nat.lt_succ_self _⟩).get idx ≠ some queryAnswer := by
          intro hquery
          have hsome : some targetAnswer = some queryAnswer := by
            rw [← hlabel, hquery]
          exact hanswer (Option.some.inj hsome).symm
        have hanswerSymm : ¬ targetAnswer = queryAnswer := fun h => hanswer h.symm
        left
        simp [populateLeafQuery, hnone, hlabel, hanswerSymm]
  | inr hsome =>
      exact Or.inr (populateLeafQuery_get_eq_of_some
        (M := M) (S := S) (C := C) (depth := depth)
        queryMessage querySalt queryAnswer labels leaves idx (targetMessage, targetSalt) hsome)

private theorem populateLeavesFold_get_eq_some_of_unique_leaf {depth : ℕ} [DecidableEq C]
    (labels : PartialLabels C depth) :
    ∀ (entries : QueryLog (Oracle M S C)) (leaves : PartialLeaves M S depth)
      (idx : Index depth) (message : M) (salt : S) (answer : C),
      (leaves.get idx = none ∨ leaves.get idx = some (message, salt)) →
        (labels ⟨depth, Nat.lt_succ_self _⟩).get idx = some answer →
          ⟨Sum.inl (message, salt), answer⟩ ∈ entries →
            (∀ (message' : M) (salt' : S),
              ⟨Sum.inl (message', salt'), answer⟩ ∈ entries →
                message' = message ∧ salt' = salt) →
              (entries.foldl
                  (fun leaves entry =>
                    match entry with
                    | ⟨Sum.inl (queryMessage, querySalt), queryAnswer⟩ =>
                        populateLeafQuery (depth := depth)
                          queryMessage querySalt queryAnswer labels leaves
                    | ⟨Sum.inr _, _⟩ => leaves)
                  leaves).get idx = some (message, salt)
  | [], _, _, _, _, _, _, _, hmem, _ => by
      cases hmem
  | entry :: entries, leaves, idx, message, salt, answer, hstate, hlabel, hmem, hunique => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        have hafter :
            (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
              message salt answer labels leaves).get idx = some (message, salt) := by
          cases hstate with
          | inl hnone =>
              exact populateLeafQuery_get_eq_some_of_none
                (M := M) (S := S) (C := C) (depth := depth)
                message salt answer labels leaves idx hnone hlabel
          | inr hsome =>
              exact populateLeafQuery_get_eq_of_some
                (M := M) (S := S) (C := C) (depth := depth)
                message salt answer labels leaves idx (message, salt) hsome
        exact populateLeavesFold_get_eq_of_some (M := M) (S := S) (C := C)
          (depth := depth) labels entries
          (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
            message salt answer labels leaves)
          idx (message, salt) hafter
      · cases entry with
        | mk domain queryAnswer =>
            cases domain with
            | inl ms =>
                rcases ms with ⟨queryMessage, querySalt⟩
                have hnextState :
                    (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
                      queryMessage querySalt queryAnswer labels leaves).get idx = none ∨
                      (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
                        queryMessage querySalt queryAnswer labels leaves).get idx =
                        some (message, salt) :=
                  populateLeafQuery_get_eq_none_or_target_of_unique
                    (M := M) (S := S) (C := C) (depth := depth)
                    message salt answer queryMessage querySalt queryAnswer labels leaves idx
                    hlabel hstate (by
                      intro hanswer
                      subst hanswer
                      exact hunique queryMessage querySalt (by simp))
                exact populateLeavesFold_get_eq_some_of_unique_leaf labels entries
                  (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
                    queryMessage querySalt queryAnswer labels leaves)
                  idx message salt answer hnextState hlabel htail
                  (fun message' salt' hmemTail =>
                    hunique message' salt' (List.mem_cons_of_mem _ hmemTail))
            | inr cs =>
                exact populateLeavesFold_get_eq_some_of_unique_leaf labels entries leaves
                  idx message salt answer hstate hlabel htail
                  (fun message' salt' hmemTail =>
                    hunique message' salt' (List.mem_cons_of_mem _ hmemTail))

/-- Populate the known leaves of a partial tree from commit-phase leaf queries. -/
def populateLeavesFromTrace {depth : ℕ} [DecidableEq C] (trace : QueryLog (Oracle M S C))
    (labels : PartialLabels C depth) : PartialLeaves M S depth :=
  let leafs := (partitionTrace (M := M) (S := S) (C := C) trace).leafQueries
  leafs.foldl
    (fun leaves entry =>
      match entry with
      | ⟨Sum.inl (message, salt), answer⟩ =>
          populateLeafQuery (depth := depth) message salt answer labels leaves
      | ⟨Sum.inr _, _⟩ => leaves)
    (emptyPartialLeaves (M := M) (S := S) (depth := depth))

/-- If a known leaf label has a unique matching leaf query in the trace, leaf
population recovers that message/salt pair. -/
theorem populateLeavesFromTrace_get_eq_some_of_unique_leaf {depth : ℕ} [DecidableEq C]
    (trace : QueryLog (Oracle M S C)) (labels : PartialLabels C depth)
    (idx : Index depth) (message : M) (salt : S) (answer : C)
    (hlabel : (labels ⟨depth, Nat.lt_succ_self _⟩).get idx = some answer)
    (hmem : ⟨Sum.inl (message, salt), answer⟩ ∈ trace)
    (hunique :
      ∀ (message' : M) (salt' : S),
        ⟨Sum.inl (message', salt'), answer⟩ ∈ trace →
          message' = message ∧ salt' = salt) :
    (populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
      trace labels).get idx = some (message, salt) := by
  let target : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t :=
    ⟨Sum.inl (message, salt), answer⟩
  have hmemLeaf :
      target ∈ (partitionTrace (M := M) (S := S) (C := C) trace).leafQueries := by
    exact (mem_partitionTrace_leafQueries_iff (M := M) (S := S) (C := C)
      trace target).mpr ⟨hmem, ⟨(message, salt), rfl⟩⟩
  have huniqueLeaf :
      ∀ (message' : M) (salt' : S),
        ⟨Sum.inl (message', salt'), answer⟩ ∈
          (partitionTrace (M := M) (S := S) (C := C) trace).leafQueries →
          message' = message ∧ salt' = salt := by
    intro message' salt' hmem'
    exact hunique message' salt'
      ((mem_partitionTrace_leafQueries_iff (M := M) (S := S) (C := C)
        trace ⟨Sum.inl (message', salt'), answer⟩).mp hmem').1
  have hempty :
      (emptyPartialLeaves (M := M) (S := S) (depth := depth)).get idx = none := by
    simp [emptyPartialLeaves]
  simpa [populateLeavesFromTrace, target] using
    populateLeavesFold_get_eq_some_of_unique_leaf (M := M) (S := S) (C := C)
      (depth := depth) labels
      ((partitionTrace (M := M) (S := S) (C := C) trace).leafQueries)
      (emptyPartialLeaves (M := M) (S := S) (depth := depth))
      idx message salt answer (Or.inl hempty) hlabel hmemLeaf huniqueLeaf

private theorem partitionTrace_foldr_leafQueries
    (trace : QueryLog (Oracle M S C)) (acc : TracePartition M S C) :
    (trace.foldr
      (fun entry acc =>
        match entry.1 with
        | Sum.inl _ => { acc with leafQueries := entry :: acc.leafQueries }
        | Sum.inr _ => { acc with internalQueries := entry :: acc.internalQueries })
      acc).leafQueries =
      (partitionTrace (M := M) (S := S) (C := C) trace).leafQueries ++
        acc.leafQueries := by
  induction trace with
  | nil =>
      simp [partitionTrace]
  | cons entry rest ih =>
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              simpa [partitionTrace, ih]
          | inr pair =>
              simpa [partitionTrace, ih]

theorem partitionTrace_leafQueries_append
    (left right : QueryLog (Oracle M S C)) :
    (partitionTrace (M := M) (S := S) (C := C) (left ++ right)).leafQueries =
      (partitionTrace (M := M) (S := S) (C := C) left).leafQueries ++
        (partitionTrace (M := M) (S := S) (C := C) right).leafQueries := by
  unfold partitionTrace
  rw [List.foldr_append]
  exact partitionTrace_foldr_leafQueries (M := M) (S := S) (C := C) left
    (partitionTrace (M := M) (S := S) (C := C) right)

private theorem populateLeafQuery_eq_self_of_answer_not_known {depth : ℕ}
    [DecidableEq C] (message : M) (salt : S) (answer : C)
    (labels : PartialLabels C depth) (leaves : PartialLeaves M S depth)
    (hanswer : answer ∉ knownLabels labels) :
    populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
      message salt answer labels leaves = leaves := by
  apply Vector.ext
  intro i hi
  let idx : Index depth := ⟨i, hi⟩
  change (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
      message salt answer labels leaves).get idx = leaves.get idx
  simp [populateLeafQuery]
  cases hleaf : leaves.get idx with
  | some value =>
      simp [hleaf]
  | none =>
      cases hlabel : (labels ⟨depth, Nat.lt_succ_self _⟩).get idx with
      | none =>
          simp [hleaf, hlabel]
      | some label =>
          have hne : label ≠ answer := by
            intro heq
            exact hanswer ((mem_knownLabels_iff (C := C) labels answer).mpr
              ⟨⟨depth, Nat.lt_succ_self _⟩, idx, by simpa [heq] using hlabel⟩)
          simp [hleaf, hlabel, hne]

private theorem populateLeavesFold_eq_self_of_answers_not_known {depth : ℕ}
    [DecidableEq C] (labels : PartialLabels C depth) :
    ∀ (entries : QueryLog (Oracle M S C)) (leaves : PartialLeaves M S depth),
      (∀ message salt answer,
        ⟨Sum.inl (message, salt), answer⟩ ∈ entries →
          answer ∉ knownLabels labels) →
        entries.foldl
          (fun leaves entry =>
            match entry with
            | ⟨Sum.inl (message, salt), answer⟩ =>
                populateLeafQuery (depth := depth) message salt answer labels leaves
            | ⟨Sum.inr _, _⟩ => leaves)
          leaves = leaves
  | [], leaves, _ => by
      rfl
  | entry :: entries, leaves, hanswers => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              rcases ms with ⟨message, salt⟩
              rw [List.foldl_cons]
              simp only
              rw [populateLeafQuery_eq_self_of_answer_not_known
                (M := M) (S := S) (C := C) (depth := depth)
                message salt answer labels leaves
                (hanswers message salt answer (by simp))]
              exact populateLeavesFold_eq_self_of_answers_not_known labels entries leaves
                (fun message' salt' answer' hmem =>
                  hanswers message' salt' answer' (List.mem_cons_of_mem _ hmem))
          | inr cs =>
              exact populateLeavesFold_eq_self_of_answers_not_known labels entries leaves
                (fun message salt answer hmem =>
                  hanswers message salt answer (List.mem_cons_of_mem _ hmem))

private theorem populateLeavesFold_get_eq_some_of_mem {depth : ℕ} [DecidableEq C]
    (labels : PartialLabels C depth) :
    ∀ (entries : QueryLog (Oracle M S C)) (leaves : PartialLeaves M S depth)
      (idx : Index depth) (message : M) (salt : S) (answer : C),
      (labels ⟨depth, Nat.lt_succ_self _⟩).get idx = some answer →
        ⟨Sum.inl (message, salt), answer⟩ ∈ entries →
          ∃ value : M × S,
            (entries.foldl
                (fun leaves entry =>
                  match entry with
                  | ⟨Sum.inl (message, salt), answer⟩ =>
                      populateLeafQuery (depth := depth)
                        message salt answer labels leaves
                  | ⟨Sum.inr _, _⟩ => leaves)
                leaves).get idx = some value
  | [], _, _, _, _, _, _, hmem => by
      cases hmem
  | entry :: entries, leaves, idx, message, salt, answer, hlabel, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        cases hleaf : leaves.get idx with
        | some value =>
            refine ⟨value, ?_⟩
            exact populateLeavesFold_get_eq_of_some (M := M) (S := S) (C := C)
              (depth := depth) labels entries
              (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
                message salt answer labels leaves)
              idx value
              (populateLeafQuery_get_eq_of_some (M := M) (S := S) (C := C)
                (depth := depth) message salt answer labels leaves idx value hleaf)
        | none =>
            refine ⟨(message, salt), ?_⟩
            exact populateLeavesFold_get_eq_of_some (M := M) (S := S) (C := C)
              (depth := depth) labels entries
              (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
                message salt answer labels leaves)
              idx (message, salt)
              (populateLeafQuery_get_eq_some_of_none (M := M) (S := S) (C := C)
                (depth := depth) message salt answer labels leaves idx hleaf hlabel)
      · cases entry with
        | mk domain queryAnswer =>
            cases domain with
            | inl ms =>
                rcases ms with ⟨queryMessage, querySalt⟩
                exact populateLeavesFold_get_eq_some_of_mem labels entries
                  (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
                    queryMessage querySalt queryAnswer labels leaves)
                  idx message salt answer hlabel htail
            | inr cs =>
                exact populateLeavesFold_get_eq_some_of_mem labels entries leaves
                  idx message salt answer hlabel htail

private theorem populateLeafQuery_eq_self_of_mem_fold {depth : ℕ} [DecidableEq C]
    (entries : QueryLog (Oracle M S C)) (message : M) (salt : S) (answer : C)
    (labels : PartialLabels C depth) (leaves : PartialLeaves M S depth)
    (hmem : ⟨Sum.inl (message, salt), answer⟩ ∈ entries) :
    populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
        message salt answer labels
        (entries.foldl
          (fun leaves entry =>
            match entry with
            | ⟨Sum.inl (message, salt), answer⟩ =>
                populateLeafQuery (depth := depth)
                  message salt answer labels leaves
            | ⟨Sum.inr _, _⟩ => leaves)
          leaves) =
      entries.foldl
        (fun leaves entry =>
          match entry with
          | ⟨Sum.inl (message, salt), answer⟩ =>
              populateLeafQuery (depth := depth)
                message salt answer labels leaves
          | ⟨Sum.inr _, _⟩ => leaves)
        leaves := by
  apply Vector.ext
  intro i hi
  let idx : Index depth := ⟨i, hi⟩
  let folded : PartialLeaves M S depth :=
    entries.foldl
      (fun leaves entry =>
        match entry with
        | ⟨Sum.inl (message, salt), answer⟩ =>
            populateLeafQuery (depth := depth)
              message salt answer labels leaves
        | ⟨Sum.inr _, _⟩ => leaves)
      leaves
  change
    (populateLeafQuery (M := M) (S := S) (C := C) (depth := depth)
      message salt answer labels folded).get idx = folded.get idx
  cases hleaf : folded.get idx with
  | some value =>
      simp [populateLeafQuery, hleaf]
  | none =>
      cases hlabel : (labels ⟨depth, Nat.lt_succ_self _⟩).get idx with
      | none =>
          simp [populateLeafQuery, hleaf, hlabel]
      | some label =>
          by_cases hanswer : label = answer
          · have hlabelAnswer :
                (labels ⟨depth, Nat.lt_succ_self _⟩).get idx = some answer := by
              simpa [hanswer] using hlabel
            rcases populateLeavesFold_get_eq_some_of_mem
                (M := M) (S := S) (C := C) (depth := depth)
                labels entries leaves idx message salt answer hlabelAnswer hmem with
              ⟨value, hvalue⟩
            have hvalueFolded : folded.get idx = some value := by
              simpa [folded] using hvalue
            rw [hleaf] at hvalueFolded
            cases hvalueFolded
          · simp [populateLeafQuery, hleaf, hlabel, hanswer]

private theorem populateLeavesFold_eq_self_of_mem_or_answers_not_known {depth : ℕ}
    [DecidableEq C] (labels : PartialLabels C depth) :
    ∀ (leftEntries rightEntries : QueryLog (Oracle M S C))
      (leaves : PartialLeaves M S depth),
      (∀ message salt answer,
        ⟨Sum.inl (message, salt), answer⟩ ∈ rightEntries →
          ⟨Sum.inl (message, salt), answer⟩ ∈ leftEntries ∨
            answer ∉ knownLabels labels) →
        rightEntries.foldl
          (fun leaves entry =>
            match entry with
            | ⟨Sum.inl (message, salt), answer⟩ =>
                populateLeafQuery (depth := depth)
                  message salt answer labels leaves
            | ⟨Sum.inr _, _⟩ => leaves)
          (leftEntries.foldl
            (fun leaves entry =>
              match entry with
              | ⟨Sum.inl (message, salt), answer⟩ =>
                  populateLeafQuery (depth := depth)
                    message salt answer labels leaves
              | ⟨Sum.inr _, _⟩ => leaves)
            leaves) =
          leftEntries.foldl
            (fun leaves entry =>
              match entry with
              | ⟨Sum.inl (message, salt), answer⟩ =>
                  populateLeafQuery (depth := depth)
                    message salt answer labels leaves
              | ⟨Sum.inr _, _⟩ => leaves)
            leaves
  | _, [], _, _ => by
      rfl
  | leftEntries, entry :: entries, leaves, hanswers => by
      cases entry with
      | mk domain answer =>
          cases domain with
          | inl ms =>
              rcases ms with ⟨message, salt⟩
              rw [List.foldl_cons]
              simp only
              cases hanswers message salt answer (by simp) with
              | inl hmemLeft =>
                  rw [populateLeafQuery_eq_self_of_mem_fold
                    (M := M) (S := S) (C := C) (depth := depth)
                    leftEntries message salt answer labels leaves hmemLeft]
                  exact populateLeavesFold_eq_self_of_mem_or_answers_not_known labels
                    leftEntries entries leaves
                    (fun message' salt' answer' hmem =>
                      hanswers message' salt' answer'
                        (List.mem_cons_of_mem _ hmem))
              | inr hnotKnown =>
                  rw [populateLeafQuery_eq_self_of_answer_not_known
                    (M := M) (S := S) (C := C) (depth := depth)
                    message salt answer labels
                    (leftEntries.foldl
                      (fun leaves entry =>
                        match entry with
                        | ⟨Sum.inl (message, salt), answer⟩ =>
                            populateLeafQuery (depth := depth)
                              message salt answer labels leaves
                        | ⟨Sum.inr _, _⟩ => leaves)
                      leaves)
                    hnotKnown]
                  exact populateLeavesFold_eq_self_of_mem_or_answers_not_known labels
                    leftEntries entries leaves
                    (fun message' salt' answer' hmem =>
                      hanswers message' salt' answer'
                        (List.mem_cons_of_mem _ hmem))
          | inr cs =>
              exact populateLeavesFold_eq_self_of_mem_or_answers_not_known labels
                leftEntries entries leaves
                (fun message salt answer hmem =>
                  hanswers message salt answer (List.mem_cons_of_mem _ hmem))

/-- Appending leaf queries whose answers are not known labels cannot change the
populated leaf table. -/
theorem populateLeavesFromTrace_append_eq_left_of_answers_not_known {depth : ℕ}
    [DecidableEq C] (commitTrace openTrace : QueryLog (Oracle M S C))
    (labels : PartialLabels C depth)
    (hanswers : ∀ message salt answer,
      ⟨Sum.inl (message, salt), answer⟩ ∈ openTrace →
        answer ∉ knownLabels labels) :
    populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
        (commitTrace ++ openTrace) labels =
      populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitTrace labels := by
  unfold populateLeavesFromTrace
  rw [partitionTrace_leafQueries_append (M := M) (S := S) (C := C)
    commitTrace openTrace]
  rw [List.foldl_append]
  exact populateLeavesFold_eq_self_of_answers_not_known
    (M := M) (S := S) (C := C) (depth := depth) labels
    (partitionTrace (M := M) (S := S) (C := C) openTrace).leafQueries
    (((partitionTrace (M := M) (S := S) (C := C) commitTrace).leafQueries).foldl
      (fun leaves entry =>
        match entry with
        | ⟨Sum.inl (message, salt), answer⟩ =>
            populateLeafQuery (depth := depth) message salt answer labels leaves
        | ⟨Sum.inr _, _⟩ => leaves)
      (emptyPartialLeaves (M := M) (S := S) (depth := depth)))
    (fun message salt answer hmem =>
      hanswers message salt answer
        ((mem_partitionTrace_leafQueries_iff (M := M) (S := S) (C := C)
          openTrace ⟨Sum.inl (message, salt), answer⟩).mp hmem).1)

private theorem populateLeavesFromTrace_append_eq_left_of_mem_or_answers_not_known
    {depth : ℕ} [DecidableEq C] (commitTrace openTrace : QueryLog (Oracle M S C))
    (labels : PartialLabels C depth)
    (hanswers : ∀ message salt answer,
      ⟨Sum.inl (message, salt), answer⟩ ∈ openTrace →
        ⟨Sum.inl (message, salt), answer⟩ ∈ commitTrace ∨
          answer ∉ knownLabels labels) :
    populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
        (commitTrace ++ openTrace) labels =
      populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
        commitTrace labels := by
  unfold populateLeavesFromTrace
  rw [partitionTrace_leafQueries_append (M := M) (S := S) (C := C)
    commitTrace openTrace]
  rw [List.foldl_append]
  exact populateLeavesFold_eq_self_of_mem_or_answers_not_known
    (M := M) (S := S) (C := C) (depth := depth) labels
    (partitionTrace (M := M) (S := S) (C := C) commitTrace).leafQueries
    (partitionTrace (M := M) (S := S) (C := C) openTrace).leafQueries
    (emptyPartialLeaves (M := M) (S := S) (depth := depth))
    (fun message salt answer hmem =>
      Or.imp
        (fun hmemCommit =>
          (mem_partitionTrace_leafQueries_iff (M := M) (S := S) (C := C)
            commitTrace ⟨Sum.inl (message, salt), answer⟩).mpr
            ⟨hmemCommit, ⟨(message, salt), rfl⟩⟩)
        id
        (hanswers message salt answer
          ((mem_partitionTrace_leafQueries_iff (M := M) (S := S) (C := C)
            openTrace ⟨Sum.inl (message, salt), answer⟩).mp hmem).1))

/-- The partial extractor state reconstructed from a trace. -/
def extractedStateFromTrace {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    ExtractedState M S C depth :=
  let labels := buildPartialTreeFromTrace (M := M) (S := S) (C := C)
    (depth := depth) commitment trace
  let leaves := populateLeavesFromTrace (M := M) (S := S) (C := C)
    (depth := depth) trace labels
  ⟨labels, leaves⟩

/-- Appending trace entries whose answers avoid the known-label target set does
not change the extractor state. -/
theorem extractedStateFromTrace_append_eq_left_of_answers_not_mem {depth : ℕ}
    [DecidableEq C] (commitment : C)
    (commitTrace openTrace : QueryLog (Oracle M S C))
    (hanswers : ∀ entry, entry ∈ openTrace →
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∉
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace) :
    extractedStateFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment (commitTrace ++ openTrace) =
      extractedStateFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment commitTrace := by
  have hlabels :
      buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment (commitTrace ++ openTrace) =
        buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace :=
    buildPartialTreeFromTrace_append_eq_left_of_answers_not_mem
      (M := M) (S := S) (C := C) (depth := depth)
      commitment commitTrace openTrace
      (fun left right answer hmem => by
        simpa [traceEntryAnswer] using
          hanswers ⟨Sum.inr (left, right), answer⟩ hmem)
  have hleaves :
      populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
          (commitTrace ++ openTrace)
          (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) =
        populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
          commitTrace
          (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) :=
    populateLeavesFromTrace_append_eq_left_of_answers_not_known
      (M := M) (S := S) (C := C) (depth := depth)
      commitTrace openTrace
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment commitTrace)
      (fun message salt answer hmem => by
        simpa [traceEntryAnswer, traceKnownLabels] using
          hanswers ⟨Sum.inl (message, salt), answer⟩ hmem)
  simp [extractedStateFromTrace, hlabels, hleaves]

/-- If appending an open trace changes the extractor state, then some appended
query answer hit a label already known from the commit trace.

This is the deterministic implication behind the extractability fresh-hit bad
event. The probability layer bounds exactly this kind of hit by
`query_count * |traceKnownLabels| / |C|`. -/
theorem exists_open_answer_mem_traceKnownLabels_of_extractedStateFromTrace_append_ne
    {depth : ℕ} [DecidableEq C] (commitment : C)
    (commitTrace openTrace : QueryLog (Oracle M S C))
    (hchange :
      extractedStateFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment (commitTrace ++ openTrace) ≠
        extractedStateFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace) :
    ∃ entry, entry ∈ openTrace ∧
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace := by
  classical
  by_contra hnone
  apply hchange
  exact extractedStateFromTrace_append_eq_left_of_answers_not_mem
    (M := M) (S := S) (C := C) (depth := depth)
    commitment commitTrace openTrace
    (fun entry hmem htarget =>
      hnone ⟨entry, hmem, htarget⟩)

private theorem extractedStateFromTrace_append_eq_left_of_mem_or_answers_not_mem
    {depth : ℕ} [DecidableEq C] (commitment : C)
    (commitTrace openTrace : QueryLog (Oracle M S C))
    (hanswers : ∀ entry, entry ∈ openTrace →
      entry ∈ commitTrace ∨
        traceEntryAnswer (M := M) (S := S) (C := C) entry ∉
          traceKnownLabels (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) :
    extractedStateFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment (commitTrace ++ openTrace) =
      extractedStateFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment commitTrace := by
  have hlabels :
      buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment (commitTrace ++ openTrace) =
        buildPartialTreeFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace :=
    buildPartialTreeFromTrace_append_eq_left_of_mem_or_answers_not_mem
      (M := M) (S := S) (C := C) (depth := depth)
      commitment commitTrace openTrace
      (fun left right answer hmem => by
        exact Or.imp id
          (by simp [traceEntryAnswer])
          (hanswers ⟨Sum.inr (left, right), answer⟩ hmem))
  have hleaves :
      populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
          (commitTrace ++ openTrace)
          (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) =
        populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
          commitTrace
          (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
            (depth := depth) commitment commitTrace) :=
    populateLeavesFromTrace_append_eq_left_of_mem_or_answers_not_known
      (M := M) (S := S) (C := C) (depth := depth)
      commitTrace openTrace
      (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
        (depth := depth) commitment commitTrace)
      (fun message salt answer hmem => by
        exact Or.imp id
          (by simp [traceEntryAnswer, traceKnownLabels])
          (hanswers ⟨Sum.inl (message, salt), answer⟩ hmem))
  simp [extractedStateFromTrace, hlabels, hleaves]

/-- If an open-phase extension changes the extractor state, then some new
open-phase query answer hit a label already known from the commit trace.

This stronger form additionally rules out entries already present in the
commit trace. It is the deterministic origin statement used before the ROM
fresh-hit probability bound. -/
theorem
exists_open_answer_mem_traceKnownLabels_and_not_mem_commitTrace_of_extractedStateFromTrace_append_ne
    {depth : ℕ} [DecidableEq C] (commitment : C)
    (commitTrace openTrace : QueryLog (Oracle M S C))
    (hchange :
      extractedStateFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment (commitTrace ++ openTrace) ≠
        extractedStateFromTrace (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace) :
    ∃ entry, entry ∈ openTrace ∧ entry ∉ commitTrace ∧
      traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
        traceKnownLabels (M := M) (S := S) (C := C)
          (depth := depth) commitment commitTrace := by
  classical
  by_contra hnone
  apply hchange
  exact extractedStateFromTrace_append_eq_left_of_mem_or_answers_not_mem
    (M := M) (S := S) (C := C) (depth := depth)
    commitment commitTrace openTrace
    (fun entry hmem => by
      by_cases hcommit : entry ∈ commitTrace
      · exact Or.inl hcommit
      · exact Or.inr (fun hknown =>
          hnone ⟨entry, hmem, hcommit, hknown⟩))

/-- Deterministically totalize an extracted partial state into a full message
and trapdoor. -/
def fillMissing {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) :
    Leaves M depth × Trapdoor S C depth :=
  let defaultLeaf : M × S := (default, default)
  let fullLeafData := Vector.ofFn fun idx => (state.leaves.get idx).getD defaultLeaf
  let messages := Vector.ofFn fun idx => (fullLeafData.get idx).1
  let salts := Vector.ofFn fun idx => (fullLeafData.get idx).2
  let labels : Labels C depth := fun layer =>
    Vector.ofFn fun idx => (state.labels layer).get idx |>.getD default
  (messages, ⟨salts, labels⟩)

/-- `fillMissing` preserves any known extracted message/salt pair at the
message projection. -/
@[simp] theorem fillMissing_message_get_eq_of_some_leaf {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) (idx : Index depth) (message : M) (salt : S)
    (hleaf : state.leaves.get idx = some (message, salt)) :
    (fillMissing (M := M) (S := S) (C := C) state).1.get idx = message := by
  simp [fillMissing, hleaf]

/-- `fillMissing` preserves any known extracted message/salt pair at the salt
projection of the trapdoor. -/
@[simp] theorem fillMissing_salt_get_eq_of_some_leaf {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) (idx : Index depth) (message : M) (salt : S)
    (hleaf : state.leaves.get idx = some (message, salt)) :
    (fillMissing (M := M) (S := S) (C := C) state).2.salts.get idx = salt := by
  simp [fillMissing, hleaf]

/-- `fillMissing` preserves every known internal or leaf label in the trapdoor
label table. -/
@[simp] theorem fillMissing_label_get_eq_of_some_label {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) (layer : Fin (depth + 1))
    (idx : Fin (2 ^ layer.1)) (label : C)
    (hlabel : (state.labels layer).get idx = some label) :
    ((fillMissing (M := M) (S := S) (C := C) state).2.labels layer).get idx = label := by
  simp [fillMissing, hlabel]

/-!
The public extractor returns a default-filled tree only when the commitment
never appears as an oracle answer in the commit trace. These private helpers
connect leaf/internal trace membership to the branch condition.
-/

private def commitmentAppears [DecidableEq C] (commitment : C)
    (trace : QueryLog (Oracle M S C)) : Bool :=
  trace.any fun
    | ⟨Sum.inl _, answer⟩ => decide (answer = commitment)
    | ⟨Sum.inr _, answer⟩ => decide (answer = commitment)

private theorem commitmentAppears_eq_true_of_leaf_mem [DecidableEq C]
    (commitment : C) :
    ∀ (trace : QueryLog (Oracle M S C)) (message : M) (salt : S),
      ⟨Sum.inl (message, salt), commitment⟩ ∈ trace →
        commitmentAppears (M := M) (S := S) (C := C) commitment trace = true
  | [], _, _, hmem => by
      cases hmem
  | entry :: trace, message, salt, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        simp [commitmentAppears]
      · cases entry with
        | mk domain answer =>
            cases domain with
            | inl _ =>
                by_cases hanswer : answer = commitment
                · simp [commitmentAppears, hanswer]
                · simp [commitmentAppears, hanswer]
                  exact Or.inl ⟨message, salt, htail⟩
            | inr _ =>
                by_cases hanswer : answer = commitment
                · simp [commitmentAppears, hanswer]
                · simp [commitmentAppears, hanswer]
                  exact Or.inl ⟨message, salt, htail⟩

private theorem commitmentAppears_eq_true_of_internal_mem [DecidableEq C]
    (commitment : C) :
    ∀ (trace : QueryLog (Oracle M S C)) (left right : C),
      ⟨Sum.inr (left, right), commitment⟩ ∈ trace →
        commitmentAppears (M := M) (S := S) (C := C) commitment trace = true
  | [], _, _, hmem => by
      cases hmem
  | entry :: trace, left, right, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst entry
        simp [commitmentAppears]
      · cases entry with
        | mk domain answer =>
            cases domain with
            | inl _ =>
                by_cases hanswer : answer = commitment
                · simp [commitmentAppears, hanswer]
                · simp [commitmentAppears, hanswer]
                  exact Or.inr ⟨left, right, htail⟩
            | inr _ =>
                by_cases hanswer : answer = commitment
                · simp [commitmentAppears, hanswer]
                · simp [commitmentAppears, hanswer]
                  exact Or.inr ⟨left, right, htail⟩

/-- Deterministic extractor helper that fails only when `commitment` does not
appear as a commit-phase query answer. -/
def extract? {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    Option (Leaves M depth × Trapdoor S C depth) :=
  if commitmentAppears (C := C) commitment trace then
    let labels := buildPartialTreeFromTrace (M := M) (S := S) (C := C)
      (depth := depth) commitment trace
    let leaves := populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth) trace labels
    some <| fillMissing (depth := depth) ⟨labels, leaves⟩
  else
    none

/-- Public deterministic extractor, matching the 18.5 interface. -/
def extract {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    Leaves M depth × Trapdoor S C depth :=
  (extract? (M := M) (S := S) (C := C) (depth := depth) commitment trace).getD
    (fillMissing (M := M) (S := S) (C := C) (depth := depth)
      ⟨seedRoot (depth := depth) commitment, emptyPartialLeaves (M := M) (S := S) (depth := depth)⟩)

/-- If the commitment appears as a leaf-query answer in the trace, `extract`
takes its reconstructed-state branch rather than the fallback branch. -/
theorem extract_eq_fillMissing_of_leaf_answer_mem {depth : ℕ}
    [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (message : M) (salt : S)
    (hmem : ⟨Sum.inl (message, salt), commitment⟩ ∈ trace) :
    extract (M := M) (S := S) (C := C) (depth := depth) commitment trace =
      fillMissing (M := M) (S := S) (C := C) (depth := depth)
        ⟨buildPartialTreeFromTrace (M := M) (S := S) (C := C)
            (depth := depth) commitment trace,
          populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
            trace
            (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
              (depth := depth) commitment trace)⟩ := by
  unfold extract extract?
  rw [commitmentAppears_eq_true_of_leaf_mem (M := M) (S := S) (C := C)
    commitment trace message salt hmem]
  rfl

/-- If the commitment appears as an internal-query answer in the trace,
`extract` takes its reconstructed-state branch rather than the fallback branch. -/
theorem extract_eq_fillMissing_of_internal_answer_mem {depth : ℕ}
    [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) (left right : C)
    (hmem : ⟨Sum.inr (left, right), commitment⟩ ∈ trace) :
    extract (M := M) (S := S) (C := C) (depth := depth) commitment trace =
      fillMissing (M := M) (S := S) (C := C) (depth := depth)
        ⟨buildPartialTreeFromTrace (M := M) (S := S) (C := C)
            (depth := depth) commitment trace,
          populateLeavesFromTrace (M := M) (S := S) (C := C) (depth := depth)
            trace
            (buildPartialTreeFromTrace (M := M) (S := S) (C := C)
              (depth := depth) commitment trace)⟩ := by
  unfold extract extract?
  rw [commitmentAppears_eq_true_of_internal_mem (M := M) (S := S) (C := C)
    commitment trace left right hmem]
  rfl

section Bundled

variable [DecidableEq C] [SampleableType S]

/-- The Merkle commitment tuple at a fixed depth. -/
structure Scheme (M S C : Type) (depth : ℕ) where
  commitWithSalts :
    Leaves M depth → Leaves S depth →
      OracleComp (Oracle M S C) (C × Trapdoor S C depth)
  commit :
    Leaves M depth → OracleComp (unifSpec + Oracle M S C) (C × Trapdoor S C depth)
  openSingle : Trapdoor S C depth → Index depth → AuthPath S C depth
  openBatch : (trapdoor : Trapdoor S C depth) → (I : IndexSet depth) → Proof S C I
  checkSingle :
    C → Index depth → M → AuthPath S C depth → OracleComp (Oracle M S C) Bool
  checkBatch :
    C → (I : IndexSet depth) → Subvector M I → Proof S C I →
      OracleComp (Oracle M S C) Bool

/-- The textbook Merkle commitment construction packaged as a `Scheme`. -/
noncomputable def scheme {depth : ℕ} : Scheme M S C depth where
  commitWithSalts := commitWithSalts (M := M) (S := S) (C := C)
  commit := commit (M := M) (S := S) (C := C)
  openSingle := openSingle (S := S) (C := C)
  openBatch := «open» (S := S) (C := C)
  checkSingle := checkSingle (M := M) (S := S) (C := C)
  checkBatch := check (M := M) (S := S) (C := C)

end Bundled

end MerkleTree
