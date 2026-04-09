/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Common

/-!
# Merkle Commitment Scheme — Indexing Support

Arithmetic and pointwise indexing lemmas for the `MerkleTree` representation.
-/

namespace MerkleTree

variable {M S C α : Type}

@[simp] theorem pathPos_root {depth : ℕ} (idx : Index depth) :
    pathPos idx ⟨0, Nat.succ_pos _⟩ = 0 := by
  cases depth with
  | zero =>
      rfl
  | succ depth =>
      simpa [pathPos] using pathPos_root (depth := depth) (idx := parentPos idx)

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

@[simp] theorem parentPos_leftChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    parentPos (leftChildPos i) = i := by
  apply Fin.ext
  simp [parentPos, leftChildPos]

@[simp] theorem parentPos_rightChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    parentPos (rightChildPos i) = i := by
  apply Fin.ext
  rw [parentPos, rightChildPos]
  simp
  omega

@[simp] theorem siblingIndex_leftChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    siblingIndex (leftChildPos i) = rightChildPos i := by
  apply Fin.ext
  simp [siblingIndex, leftChildPos, rightChildPos]

@[simp] theorem siblingIndex_rightChildPos {layer : ℕ} (i : Fin (2 ^ layer)) :
    siblingIndex (rightChildPos i) = leftChildPos i := by
  apply Fin.ext
  simp [siblingIndex, leftChildPos, rightChildPos]

theorem leftChildPos_parentPos_of_even {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 0) :
    leftChildPos (parentPos i) = i := by
  apply Fin.ext
  simp [leftChildPos, parentPos]
  omega

theorem rightChildPos_parentPos_of_even {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 0) :
    rightChildPos (parentPos i) = siblingIndex i := by
  apply Fin.ext
  simp [rightChildPos, parentPos, siblingIndex, h]
  omega

theorem leftChildPos_parentPos_of_odd {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 1) :
    leftChildPos (parentPos i) = siblingIndex i := by
  apply Fin.ext
  simp [leftChildPos, parentPos, siblingIndex, h]
  omega

theorem rightChildPos_parentPos_of_odd {layer : ℕ} (i : Fin (2 ^ (layer + 1)))
    (h : i.1 % 2 = 1) :
    rightChildPos (parentPos i) = i := by
  apply Fin.ext
  simp [rightChildPos, parentPos]
  omega

@[simp] theorem openSingle_salt_eq {depth : ℕ} (trapdoor : Trapdoor S C depth)
    (idx : Index depth) :
    (openSingle trapdoor idx).salt = trapdoor.salts.get idx := by
  simp [openSingle]

end MerkleTree
