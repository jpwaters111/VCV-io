/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Scheme

/-!
# Merkle Commitment Scheme — Indexing Support

Arithmetic and pointwise indexing lemmas for the `MerkleTree` representation.
-/

namespace MerkleTree

variable {M S C α : Type}

/-- The root layer contains one vertex, so every leaf path reaches position `0`
at layer `0`. -/
@[simp] theorem pathPos_root {depth : ℕ} (idx : Index depth) :
    pathPos idx ⟨0, Nat.succ_pos _⟩ = 0 := by
  cases depth with
  | zero =>
      rfl
  | succ depth =>
      simpa [pathPos] using pathPos_root (depth := depth) (idx := parentPos idx)

/-- At the leaf layer, the path position is the leaf index itself. -/
@[simp] theorem pathPos_last {depth : ℕ} (idx : Index depth) :
    pathPos idx (Fin.last depth) = idx := by
  cases depth with
  | zero =>
      cases idx with
      | mk val isLt =>
          have hval : val = 0 := by omega
          subst hval
          rfl
  | succ depth =>
      simp [pathPos]

/-- Closed form for top-down path positions.

If the leaf index is `idx`, then its position at layer `layer` is
`idx / 2^(depth - layer)`. This is the arithmetic bridge between the recursive
Merkle path definition and the parity tests used by verifier traces. -/
theorem pathPos_val_eq_div_pow {depth : ℕ} (idx : Index depth) (layer : Fin (depth + 1)) :
    (pathPos idx layer).1 = idx.1 / 2 ^ (depth - layer.1) := by
  cases depth with
  | zero =>
      have hlayer : layer = 0 := by
        apply Fin.ext
        omega
      subst hlayer
      have hidx : idx = 0 := by
        apply Fin.ext
        omega
      subst hidx
      simp [pathPos]
  | succ depth =>
      by_cases hlast : layer.1 = depth + 1
      · have hlayer : layer = Fin.last (depth + 1) := by
          apply Fin.ext
          simpa using hlast
        subst hlayer
        simp [pathPos]
      · have hrec :=
          pathPos_val_eq_div_pow (depth := depth) (idx := parentPos idx)
            (layer := ⟨layer.1, lt_of_le_of_ne (Nat.le_of_lt_succ layer.2) hlast⟩)
        rw [show pathPos idx layer =
            pathPos (depth := depth) (parentPos idx)
              ⟨layer.1, lt_of_le_of_ne (Nat.le_of_lt_succ layer.2) hlast⟩ by
              simp [pathPos, hlast]]
        rw [hrec, parentPos]
        have hdiv :
            idx.1 / 2 / 2 ^ (depth - layer.1) =
              idx.1 / 2 ^ (depth + 1 - layer.1) := by
          rw [Nat.div_div_eq_div_mul]
          have hden :
              2 * 2 ^ (depth - layer.1) = 2 ^ (depth + 1 - layer.1) := by
            rw [show depth + 1 - layer.1 = depth - layer.1 + 1 by omega, pow_succ]
            ring
          simpa [hden]
        simpa using hdiv

/-- Moving from a parent to its left child and back returns the parent. -/
@[simp] theorem parentPos_leftChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    parentPos (leftChildPos i) = i := by
  apply Fin.ext
  simp [parentPos, leftChildPos]

/-- Moving from a parent to its right child and back returns the parent. -/
@[simp] theorem parentPos_rightChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    parentPos (rightChildPos i) = i := by
  apply Fin.ext
  rw [parentPos, rightChildPos]
  simp
  omega

/-- The sibling of a left child is the corresponding right child. -/
@[simp] theorem siblingIndex_leftChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    siblingIndex (leftChildPos i) = rightChildPos i := by
  apply Fin.ext
  simp [siblingIndex, leftChildPos, rightChildPos]

/-- The sibling of a right child is the corresponding left child. -/
@[simp] theorem siblingIndex_rightChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    siblingIndex (rightChildPos i) = leftChildPos i := by
  apply Fin.ext
  simp [siblingIndex, leftChildPos, rightChildPos]

/-- Even-positioned children are left children of their parents. -/
theorem leftChildPos_parentPos_of_even {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 0) :
    leftChildPos (parentPos i) = i := by
  apply Fin.ext
  simp [leftChildPos, parentPos]
  omega

/-- If `i` is an even-positioned child, the right child of its parent is its
sibling. -/
theorem rightChildPos_parentPos_of_even {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 0) :
    rightChildPos (parentPos i) = siblingIndex i := by
  apply Fin.ext
  simp [rightChildPos, parentPos, siblingIndex, h]
  omega

/-- If `i` is an odd-positioned child, the left child of its parent is its
sibling. -/
theorem leftChildPos_parentPos_of_odd {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 1) :
    leftChildPos (parentPos i) = siblingIndex i := by
  apply Fin.ext
  simp [leftChildPos, parentPos, siblingIndex, h]
  omega

/-- Odd-positioned children are right children of their parents. -/
theorem rightChildPos_parentPos_of_odd {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 1) :
    rightChildPos (parentPos i) = i := by
  apply Fin.ext
  simp [rightChildPos, parentPos]
  omega

/-- Opening a leaf reads exactly the salt stored at that leaf in the trapdoor. -/
@[simp] theorem openSingle_salt_eq {depth : ℕ} (trapdoor : Trapdoor S C depth)
    (idx : Index depth) :
    (openSingle trapdoor idx).salt = trapdoor.salts.get idx := by
  simp [openSingle]

end MerkleTree
