/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Data.Vector.Basic
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.ProbComp

/-!
# Merkle Commitment Scheme — Shared Definitions

This file models the textbook Merkle commitment scheme from
`docs/merklecommitment.tex` in a proof-oriented way.

The Merkle data itself is flattened into vectors indexed by tree layer. A
message of length `2^depth` is represented as a `List.Vector` of that length,
and the trapdoor stores the full table of labels together with the sampled leaf
salts. Single-leaf opening and checking are the primitive algorithms; the
textbook batch-opening interface is then indexed by a fixed finite set of leaf
positions.
-/

open OracleComp OracleSpec

/-! ## Vector Model -/

/-- A Merkle message or salt vector of length `2^depth`. -/
abbrev MTVector (α : Type) (depth : ℕ) := List.Vector α (2 ^ depth)

/-- Leaf positions in a Merkle tree of depth `depth`. -/
abbrev MTIndex (depth : ℕ) := Fin (2 ^ depth)

/-- A finite set of leaf positions. -/
abbrev MTIndexSet (depth : ℕ) := Finset (MTIndex depth)

/-- The commitment labels stored at a fixed tree layer. Layer `0` is the root,
and layer `depth` contains the leaf labels. -/
abbrev MTLayerVector (C : Type) (layer : ℕ) := List.Vector C (2 ^ layer)

/-- All commitment labels of a Merkle tree, flattened by layer. -/
abbrev MTVertexLabels (C : Type) (depth : ℕ) :=
  (layer : Fin (depth + 1)) → MTLayerVector C layer.1

namespace MTVertexLabels

variable {C : Type} {depth : ℕ}

/-- The root commitment stored in a flattened label table. -/
def root (labels : MTVertexLabels C depth) : C :=
  (labels ⟨0, Nat.succ_pos _⟩).head

end MTVertexLabels

/-! ## Trapdoors And Openings -/

/-- The Merkle trapdoor stores the leaf salts and the full table of commitment
labels. -/
structure MTTrapdoor (S C : Type) (depth : ℕ) where
  salts : MTVector S depth
  labels : MTVertexLabels C depth

/-- A single-leaf authentication path: the leaf salt and one sibling label per
layer, ordered by tree layer from the root's children down to the leaf layer. -/
structure MTAuthPath (S C : Type) (depth : ℕ) where
  salt : S
  siblings : List.Vector C depth

/-- The opened message values at a fixed index set. -/
abbrev MTSubVector (M : Type) {depth : ℕ} (I : MTIndexSet depth) :=
  {i // i ∈ I} → M

/-- The authentication paths for a fixed index set. -/
abbrev MTProof (S C : Type) {depth : ℕ} (I : MTIndexSet depth) :=
  {i // i ∈ I} → MTAuthPath S C depth

namespace MTSubVector

variable {M : Type} {depth : ℕ}

/-- Restrict a full message vector to a fixed index set. -/
def ofVector (messages : MTVector M depth) (I : MTIndexSet depth) : MTSubVector M I :=
  fun i => messages.get i.1

/-- Transport an opened subvector across an equality of index sets. -/
def cast {I J : MTIndexSet depth} (h : I = J) (values : MTSubVector M I) :
    MTSubVector M J :=
  fun j => values ⟨j.1, by subst h; exact j.2⟩

@[simp] theorem cast_rfl {I : MTIndexSet depth} (values : MTSubVector M I) :
    cast rfl values = values := by
  funext i
  rfl

end MTSubVector

namespace MTProof

variable {S C : Type} {depth : ℕ}

/-- Transport a proof family across an equality of index sets. -/
def cast {I J : MTIndexSet depth} (h : I = J) (proof : MTProof S C I) :
    MTProof S C J :=
  fun j => proof ⟨j.1, by subst h; exact j.2⟩

@[simp] theorem cast_rfl {I : MTIndexSet depth} (proof : MTProof S C I) :
    cast rfl proof = proof := by
  funext i
  rfl

end MTProof

/-! ## Oracle Specification -/

/-- Leaf-query oracle for the basic commitment step `(m, s) ↦ c`. -/
abbrev MTLeafOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

/-- Internal-node oracle for hashing a pair of child commitments. -/
abbrev MTNodeOracle (C : Type) : OracleSpec (C × C) := fun _ => C

/-- The typed random-oracle interface used by the Merkle scheme. The left
summand handles leaf commitments and the right summand handles internal-node
hashes. -/
abbrev MTOracle (M : Type) (S : Type) (C : Type) :
    OracleSpec ((M × S) ⊕ (C × C)) :=
  MTLeafOracle M S C + MTNodeOracle C

variable {M S C : Type}

/-- Uniform sampling on `List.Vector` via its equivalence with functions on `Fin`. -/
instance instSampleableTypeListVector (α : Type) [SampleableType α] (n : ℕ) :
    SampleableType (List.Vector α n) :=
  SampleableType.ofEquiv
    { toFun := List.Vector.ofFn
      invFun := fun xs i => xs.get i
      left_inv := fun f => funext fun i => by simp
      right_inv := fun xs => List.Vector.ext fun i => by simp }

/-- Commit to a single leaf value using the leaf-query oracle. -/
def MTLeafCommit (m : M) (s : S) : OracleComp (MTLeafOracle M S C) C :=
  query (spec := MTLeafOracle M S C) (m, s)

/-- Hash a pair of child commitments into their parent commitment. -/
def MTNodeCommit (cLeft cRight : C) : OracleComp (MTNodeOracle C) C :=
  query (spec := MTNodeOracle C) (cLeft, cRight)

/-! ## Vector Helpers -/

private lemma pow_two_le_succ (depth : ℕ) : 2 ^ depth ≤ 2 ^ Nat.succ depth := by
  rw [pow_succ, Nat.mul_comm, two_mul]
  exact Nat.le_add_left (2 ^ depth) (2 ^ depth)

/-- The length-1 vector containing only `x`. -/
def MTSingleton {α : Type} (x : α) : List.Vector α 1 :=
  List.Vector.ofFn fun _ => x

/-- The left half of a vector of length `2^(depth+1)`. -/
def MTLeftHalf {α : Type} {depth : ℕ} (xs : MTVector α (Nat.succ depth)) :
    MTVector α depth :=
  List.Vector.ofFn fun i => xs.get ⟨i.1, lt_of_lt_of_le i.2 (pow_two_le_succ depth)⟩

/-- The right half of a vector of length `2^(depth+1)`. -/
def MTRightHalf {α : Type} {depth : ℕ} (xs : MTVector α (Nat.succ depth)) :
    MTVector α depth :=
  List.Vector.ofFn fun i => xs.get ⟨2 ^ depth + i.1, by
    have hi : 2 ^ depth + i.1 < 2 ^ depth + 2 ^ depth := Nat.add_lt_add_left i.2 (2 ^ depth)
    rw [pow_succ, Nat.mul_comm, two_mul]
    exact hi⟩

/-- Concatenate the labels from two sibling subtrees into a single layer vector. -/
def MTCombineLayer {α : Type} {depth : ℕ} (left right : MTLayerVector α depth) :
    MTLayerVector α (Nat.succ depth) :=
  List.Vector.congr (by simp [pow_succ, two_mul, Nat.mul_comm]) (left ++ right)

/-- Split a leaf index into a left-half or right-half index. -/
def MTSplitIndex {depth : ℕ} (idx : MTIndex (Nat.succ depth)) :
    MTIndex depth ⊕ MTIndex depth :=
  if h : idx.1 < 2 ^ depth then
    Sum.inl ⟨idx.1, h⟩
  else
    Sum.inr ⟨idx.1 - 2 ^ depth, by
      have hidx : idx.1 < 2 ^ depth + 2 ^ depth := by
        simpa [pow_succ, two_mul, Nat.mul_comm] using idx.2
      omega⟩

/-- Restrict a flattened label table to the left subtree. -/
def MTLeftLabels {C : Type} {depth : ℕ} (labels : MTVertexLabels C (Nat.succ depth)) :
    MTVertexLabels C depth :=
  fun layer => MTLeftHalf (labels ⟨Nat.succ layer.1, Nat.succ_lt_succ layer.2⟩)

/-- Restrict a flattened label table to the right subtree. -/
def MTRightLabels {C : Type} {depth : ℕ} (labels : MTVertexLabels C (Nat.succ depth)) :
    MTVertexLabels C depth :=
  fun layer => MTRightHalf (labels ⟨Nat.succ layer.1, Nat.succ_lt_succ layer.2⟩)

/-! ## Commit, Open, And Check -/

/-- Build the full table of Merkle labels from a message vector and matching
salt vector. -/
def MTBuildTree : {depth : ℕ} → MTVector M depth → MTVector S depth →
    OracleComp (MTOracle M S C) (MTVertexLabels C depth)
  | 0, messages, salts => do
      let c ← (MTLeafCommit (M := M) (S := S) (C := C) messages.head salts.head :
        OracleComp (MTOracle M S C) C)
      pure (fun | ⟨0, _⟩ => MTSingleton c)
  | Nat.succ _, messages, salts => do
      let leftMessages := MTLeftHalf messages
      let rightMessages := MTRightHalf messages
      let leftSalts := MTLeftHalf salts
      let rightSalts := MTRightHalf salts
      let leftLabels ← MTBuildTree leftMessages leftSalts
      let rightLabels ← MTBuildTree rightMessages rightSalts
      let root ←
        (MTNodeCommit (C := C) leftLabels.root rightLabels.root :
          OracleComp (MTOracle M S C) C)
      pure fun
        | ⟨0, _⟩ => MTSingleton root
        | ⟨Nat.succ layer, hlayer⟩ =>
            MTCombineLayer
              (leftLabels ⟨layer, Nat.lt_of_succ_lt_succ hlayer⟩)
              (rightLabels ⟨layer, Nat.lt_of_succ_lt_succ hlayer⟩)

/-- Deterministic Merkle commit once the leaf salts are fixed. -/
def MTCommitWithSalts {depth : ℕ} (message : MTVector M depth) (salts : MTVector S depth) :
    OracleComp (MTOracle M S C) (C × MTTrapdoor S C depth) := do
  let labels ← MTBuildTree (M := M) (S := S) (C := C) message salts
  pure (labels.root, ⟨salts, labels⟩)

/-- Textbook probabilistic Merkle commit: sample leaf salts uniformly and then
call `MTCommitWithSalts`. -/
def MTCommit {depth : ℕ} [SampleableType S] (message : MTVector M depth) :
    OracleComp (unifSpec + MTOracle M S C) (C × MTTrapdoor S C depth) := do
  let salts ← OracleComp.liftComp (spec := unifSpec)
    (superSpec := unifSpec + MTOracle M S C) ($ᵗ MTVector S depth)
  MTCommitWithSalts (M := M) (S := S) (C := C) message salts

/-- Extract the authentication path for a single leaf position. -/
def MTOpenSingle : {depth : ℕ} → MTTrapdoor S C depth → MTIndex depth → MTAuthPath S C depth
  | 0, trapdoor, _ => ⟨trapdoor.salts.head, List.Vector.nil⟩
  | Nat.succ _, trapdoor, idx =>
      let leftLabels := MTLeftLabels trapdoor.labels
      let rightLabels := MTRightLabels trapdoor.labels
      match MTSplitIndex idx with
      | .inl childIdx =>
          let childPath :=
            MTOpenSingle
              ⟨MTLeftHalf trapdoor.salts, leftLabels⟩
              childIdx
          ⟨childPath.salt, List.Vector.cons rightLabels.root childPath.siblings⟩
      | .inr childIdx =>
          let childPath :=
            MTOpenSingle
              ⟨MTRightHalf trapdoor.salts, rightLabels⟩
              childIdx
          ⟨childPath.salt, List.Vector.cons leftLabels.root childPath.siblings⟩

/-- Extract the authentication paths for a fixed index set. -/
def MTOpen {depth : ℕ} (trapdoor : MTTrapdoor S C depth) (I : MTIndexSet depth) :
    MTProof S C I :=
  fun i => MTOpenSingle trapdoor i.1

/-- Recompute the claimed Merkle root for a single opened leaf. -/
def MTRecomputeRootSingle : {depth : ℕ} → MTIndex depth → M → MTAuthPath S C depth →
    OracleComp (MTOracle M S C) C
  | 0, _, message, authPath =>
      (MTLeafCommit (M := M) (S := S) (C := C) message authPath.salt :
        OracleComp (MTOracle M S C) C)
  | Nat.succ _, idx, message, authPath =>
      match MTSplitIndex idx with
      | .inl childIdx => do
          let child ←
            MTRecomputeRootSingle childIdx message
              ⟨authPath.salt, authPath.siblings.tail⟩
          (MTNodeCommit (C := C) child authPath.siblings.head :
            OracleComp (MTOracle M S C) C)
      | .inr childIdx => do
          let child ←
            MTRecomputeRootSingle childIdx message
              ⟨authPath.salt, authPath.siblings.tail⟩
          (MTNodeCommit (C := C) authPath.siblings.head child :
            OracleComp (MTOracle M S C) C)

/-- Check a single Merkle opening by recomputing the root and comparing it to
the claimed commitment. -/
def MTCheckSingle [DecidableEq C] {depth : ℕ} (commitment : C) (index : MTIndex depth)
    (message : M) (authPath : MTAuthPath S C depth) :
    OracleComp (MTOracle M S C) Bool := do
  let root ← MTRecomputeRootSingle (M := M) (S := S) (C := C) index message authPath
  pure (commitment == root)

/-- Internal list-based evaluator for batch checking over a fixed index set. -/
def MTCheckEntriesAux [DecidableEq C] {depth : ℕ} {I : MTIndexSet depth} (commitment : C)
    (message : MTSubVector M I) (proof : MTProof S C I) :
    List {i // i ∈ I} → OracleComp (MTOracle M S C) (List Bool)
  | [] => pure []
  | i :: rest => do
      let ok ← MTCheckSingle (M := M) (S := S) (C := C)
        commitment i.1 (message i) (proof i)
      let restChecks ← MTCheckEntriesAux commitment message proof rest
      pure (ok :: restChecks)

/-- Evaluate all single-leaf checks for a fixed index set. -/
noncomputable def MTCheckEntries [DecidableEq C] {depth : ℕ} (commitment : C) (I : MTIndexSet depth)
    (message : MTSubVector M I) (proof : MTProof S C I) :
    OracleComp (MTOracle M S C) (List Bool) :=
  MTCheckEntriesAux (M := M) (S := S) (C := C) commitment message proof I.attach.toList

/-- Batch verification checks each requested authentication path against the
same root commitment. -/
noncomputable def MTCheck [DecidableEq C] {depth : ℕ} (commitment : C) (I : MTIndexSet depth)
    (message : MTSubVector M I) (proof : MTProof S C I) :
    OracleComp (MTOracle M S C) Bool := do
  let oks ← MTCheckEntries (M := M) (S := S) (C := C) commitment I message proof
  pure (oks.all fun b => b)

section Bundled

variable [DecidableEq C] [SampleableType S]

/-- The Merkle commitment tuple at a fixed depth. -/
structure MTScheme (M S C : Type) (depth : ℕ) where
  commitWithSalts :
    MTVector M depth → MTVector S depth →
      OracleComp (MTOracle M S C) (C × MTTrapdoor S C depth)
  commit :
    MTVector M depth → OracleComp (unifSpec + MTOracle M S C) (C × MTTrapdoor S C depth)
  openSingle : MTTrapdoor S C depth → MTIndex depth → MTAuthPath S C depth
  openBatch : (trapdoor : MTTrapdoor S C depth) → (I : MTIndexSet depth) → MTProof S C I
  checkSingle :
    C → MTIndex depth → M → MTAuthPath S C depth → OracleComp (MTOracle M S C) Bool
  checkBatch :
    C → (I : MTIndexSet depth) → MTSubVector M I → MTProof S C I →
      OracleComp (MTOracle M S C) Bool

/-- The textbook Merkle commitment construction packaged as an `MTScheme`. -/
noncomputable def merkleScheme {depth : ℕ} : MTScheme M S C depth where
  commitWithSalts := MTCommitWithSalts (M := M) (S := S) (C := C)
  commit := MTCommit (M := M) (S := S) (C := C)
  openSingle := MTOpenSingle (S := S) (C := C)
  openBatch := MTOpen (S := S) (C := C)
  checkSingle := MTCheckSingle (M := M) (S := S) (C := C)
  checkBatch := MTCheck (M := M) (S := S) (C := C)

end Bundled
