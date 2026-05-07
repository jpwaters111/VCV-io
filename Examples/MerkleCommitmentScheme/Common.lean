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
# Merkle Commitment Scheme — Shared Definitions

This file models the textbook Merkle commitment scheme from
`docs/merklecommitment.tex` in a proof-oriented way.

The honest Merkle data is flattened into `Vector`s indexed by tree layer. A
message of length `2^depth` is represented as a `Vector` of that length, and
the trapdoor stores the full table of labels together with the sampled leaf
salts. Single-leaf opening and checking are the primitive algorithms; the
textbook batch-opening interface is then indexed by a fixed finite set of leaf
positions. The same layer/index view is also used by the partial-tree extractor
state built from query traces.
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

private def emptyPartialLabels {depth : ℕ} : PartialLabels C depth :=
  fun layer => Vector.ofFn fun _ => none

private def emptyPartialLeaves {depth : ℕ} : PartialLeaves M S depth :=
  Vector.ofFn fun _ => none

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

private def propagateInternalQueryUsingBase {depth : ℕ} [DecidableEq C]
    (left right answer : C) (baseLabels currentLabels : PartialLabels C depth) :
    PartialLabels C depth :=
  fun
    | ⟨0, _⟩ => currentLabels ⟨0, Nat.succ_pos _⟩
    | ⟨Nat.succ layer, hlayer⟩ =>
        propagateInternalQueryAtLayer left right answer
          (currentLabels ⟨Nat.succ layer, hlayer⟩)
          (baseLabels ⟨layer, Nat.lt_of_succ_lt hlayer⟩)

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

@[simp] theorem fillMissing_message_get_eq_of_some_leaf {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) (idx : Index depth) (message : M) (salt : S)
    (hleaf : state.leaves.get idx = some (message, salt)) :
    (fillMissing (M := M) (S := S) (C := C) state).1.get idx = message := by
  simp [fillMissing, hleaf]

@[simp] theorem fillMissing_salt_get_eq_of_some_leaf {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) (idx : Index depth) (message : M) (salt : S)
    (hleaf : state.leaves.get idx = some (message, salt)) :
    (fillMissing (M := M) (S := S) (C := C) state).2.salts.get idx = salt := by
  simp [fillMissing, hleaf]

@[simp] theorem fillMissing_label_get_eq_of_some_label {depth : ℕ}
    [Inhabited M] [Inhabited S] [Inhabited C]
    (state : ExtractedState M S C depth) (layer : Fin (depth + 1))
    (idx : Fin (2 ^ layer.1)) (label : C)
    (hlabel : (state.labels layer).get idx = some label) :
    ((fillMissing (M := M) (S := S) (C := C) state).2.labels layer).get idx = label := by
  simp [fillMissing, hlabel]

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
