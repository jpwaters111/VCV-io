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

private def propagateInternalQuery {depth : ℕ} [DecidableEq C] (left right answer : C)
    (labels : PartialLabels C depth) : PartialLabels C depth :=
  fun
    | ⟨0, _⟩ => labels ⟨0, Nat.succ_pos _⟩
    | ⟨Nat.succ layer, hlayer⟩ =>
        propagateInternalQueryAtLayer left right answer
          (labels ⟨Nat.succ layer, hlayer⟩)
          (labels ⟨layer, Nat.lt_of_succ_lt hlayer⟩)

/-- Build the partial internal-node tree rooted at `commitment` from the
commit-phase trace. -/
def buildPartialTreeFromTrace {depth : ℕ} [DecidableEq C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    PartialLabels C depth :=
  let internal := (partitionTrace (M := M) (S := S) (C := C) trace).internalQueries
  internal.foldl
    (fun labels entry =>
      match entry with
      | ⟨Sum.inr (left, right), answer⟩ =>
          propagateInternalQuery (depth := depth) left right answer labels
      | ⟨Sum.inl _, _⟩ => labels)
    (seedRoot (depth := depth) commitment)

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

private def commitmentAppears [DecidableEq C] (commitment : C) (trace : QueryLog (Oracle M S C)) : Bool :=
  trace.any fun
    | ⟨Sum.inl _, answer⟩ => decide (answer = commitment)
    | ⟨Sum.inr _, answer⟩ => decide (answer = commitment)

/-- Deterministic extractor helper that fails only when `commitment` does not
appear as a commit-phase query answer. -/
def extract? {depth : ℕ} [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (commitment : C) (trace : QueryLog (Oracle M S C)) :
    Option (Leaves M depth × Trapdoor S C depth) :=
  if commitmentAppears (C := C) commitment trace then
    let labels := buildPartialTreeFromTrace (M := M) (S := S) (C := C) (depth := depth) commitment trace
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
