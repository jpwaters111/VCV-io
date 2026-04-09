/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Common

/-!
# Merkle Commitment Scheme — Indexing Support

Pointwise indexing helpers for flattened Merkle trees. These definitions let
later proofs reason about path and copath labels directly by leaf position and
tree layer, instead of unfolding the recursive opening/checking code.
-/

open OracleComp OracleSpec

variable {M S C α : Type}

/-- Embed a position from a layer of size `2^layer` into the left half of the
next layer. -/
def MTLeftPos {layer : ℕ} (i : Fin (2 ^ layer)) : Fin (2 ^ (layer + 1)) :=
  ⟨i.1, by
    have hi : i.1 < 2 ^ layer := i.2
    have h' : i.1 < 2 ^ layer + 2 ^ layer :=
      lt_of_lt_of_le hi (Nat.le_add_left (2 ^ layer) (2 ^ layer))
    simpa [pow_succ, two_mul, Nat.mul_comm] using h'⟩

/-- Embed a position from a layer of size `2^layer` into the right half of the
next layer. -/
def MTRightPos {layer : ℕ} (i : Fin (2 ^ layer)) : Fin (2 ^ (layer + 1)) :=
  ⟨2 ^ layer + i.1, by
    have hi : 2 ^ layer + i.1 < 2 ^ layer + 2 ^ layer := Nat.add_lt_add_left i.2 (2 ^ layer)
    simpa [pow_succ, two_mul, Nat.mul_comm] using hi⟩

/-- The position of a leaf's path vertex at a given tree layer. -/
def MTPathPos : {depth : ℕ} → MTIndex depth → (layer : Fin (depth + 1)) → Fin (2 ^ layer.1)
  | 0, _, _ => 0
  | Nat.succ _, _, ⟨0, _⟩ => 0
  | Nat.succ depth, idx, ⟨Nat.succ layer, hlayer⟩ =>
      match MTSplitIndex idx with
      | .inl childIdx =>
          MTLeftPos (MTPathPos childIdx ⟨layer, Nat.lt_of_succ_lt_succ hlayer⟩)
      | .inr childIdx =>
          MTRightPos (MTPathPos childIdx ⟨layer, Nat.lt_of_succ_lt_succ hlayer⟩)

/-- The position of the sibling vertex to a leaf's path vertex at a given
non-root layer. The parameter `layer` corresponds to the textbook layers
`1, ..., depth`. -/
def MTSiblingPos : {depth : ℕ} → MTIndex depth → (layer : Fin depth) → Fin (2 ^ (layer.1 + 1))
  | 0, _, layer => nomatch layer
  | Nat.succ _, idx, ⟨0, _⟩ =>
      match MTSplitIndex idx with
      | .inl _ => 1
      | .inr _ => 0
  | Nat.succ depth, idx, ⟨Nat.succ layer, hlayer⟩ =>
      match MTSplitIndex idx with
      | .inl childIdx =>
          MTLeftPos (MTSiblingPos childIdx ⟨layer, Nat.lt_of_succ_lt_succ hlayer⟩)
      | .inr childIdx =>
          MTRightPos (MTSiblingPos childIdx ⟨layer, Nat.lt_of_succ_lt_succ hlayer⟩)

/-- The label on the path from `idx` at tree layer `layer`. -/
def MTPathLabel {depth : ℕ} (labels : MTVertexLabels C depth) (idx : MTIndex depth)
    (layer : Fin (depth + 1)) : C :=
  (labels layer).get (MTPathPos idx layer)

/-- The sibling label stored in an authentication path at the given tree layer.
The parameter `layer` corresponds to textbook layers `1, ..., depth`. -/
def MTCopathLabel {depth : ℕ} (authPath : MTAuthPath S C depth) (layer : Fin depth) : C :=
  authPath.siblings.get layer

@[simp] theorem MTPathPos_root {depth : ℕ} (idx : MTIndex depth) :
    MTPathPos idx ⟨0, Nat.succ_pos _⟩ = 0 := by
  cases depth <;> rfl

lemma MTLeftHalf_get_of_split_left {depth : ℕ} {xs : MTVector α (Nat.succ depth)}
    {idx : MTIndex (Nat.succ depth)} {childIdx : MTIndex depth}
    (h : MTSplitIndex idx = Sum.inl childIdx) :
    (MTLeftHalf xs).get childIdx = xs.get idx := by
  by_cases hlt : idx.1 < 2 ^ depth
  · simp [MTSplitIndex, hlt, MTLeftHalf] at h ⊢
    subst childIdx
    have hidx : (⟨idx.1, by
        have hi : idx.1 < 2 ^ depth + 2 ^ depth :=
          lt_of_lt_of_le hlt (Nat.le_add_left (2 ^ depth) (2 ^ depth))
        simpa [pow_succ, two_mul, Nat.mul_comm] using hi⟩ :
          Fin (2 ^ (depth + 1))) = idx := by
      apply Fin.ext
      rfl
    simpa using congrArg (fun j => xs.get j) hidx
  · simpa [MTSplitIndex, hlt] using h

lemma MTRightHalf_get_of_split_right {depth : ℕ} {xs : MTVector α (Nat.succ depth)}
    {idx : MTIndex (Nat.succ depth)} {childIdx : MTIndex depth}
    (h : MTSplitIndex idx = Sum.inr childIdx) :
    (MTRightHalf xs).get childIdx = xs.get idx := by
  by_cases hlt : idx.1 < 2 ^ depth
  · simpa [MTSplitIndex, hlt] using h
  · simp [MTSplitIndex, hlt, MTRightHalf] at h ⊢
    subst childIdx
    have hval : 2 ^ depth + (idx.1 - 2 ^ depth) = idx.1 := by
      omega
    have hidx :
        (⟨2 ^ depth + (idx.1 - 2 ^ depth), by
          simpa [hval] using idx.2⟩ : Fin (2 ^ (depth + 1))) = idx := by
      apply Fin.ext
      exact hval
    simpa using congrArg (fun j => xs.get j) hidx

@[simp] theorem MTOpenSingle_salt_eq {depth : ℕ} (trapdoor : MTTrapdoor S C depth)
    (idx : MTIndex depth) :
    (MTOpenSingle trapdoor idx).salt = trapdoor.salts.get idx := by
  induction depth with
  | zero =>
      cases trapdoor
      cases idx with
      | mk val isLt =>
          have hval : val = 0 := by omega
          subst hval
          simp [MTOpenSingle]
  | succ depth ih =>
      cases hsplit : MTSplitIndex idx with
      | inl childIdx =>
          simp [MTOpenSingle, hsplit, ih, MTLeftHalf_get_of_split_left hsplit]
      | inr childIdx =>
          simp [MTOpenSingle, hsplit, ih, MTRightHalf_get_of_split_right hsplit]
