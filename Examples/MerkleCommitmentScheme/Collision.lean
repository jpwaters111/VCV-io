/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support
import Examples.MerkleCommitmentScheme.Completeness

/-!
# Merkle Commitment Scheme — Collision Workspace

This module collects the support needed for the textbook collision lemmas.
-/

open OracleComp OracleSpec

namespace MerkleTree

variable {M S C : Type}

/-- Two opened subvectors disagree on at least one shared index. -/
def SharedValueMismatch {depth : ℕ} {I₀ I₁ : IndexSet depth}
    (message₀ : Subvector M I₀) (message₁ : Subvector M I₁) : Prop :=
  ∃ i, ∃ hi₀ : i ∈ I₀, ∃ hi₁ : i ∈ I₁,
    message₀ ⟨i, hi₀⟩ ≠ message₁ ⟨i, hi₁⟩

/-- Two proof families over the same index set differ after transporting one of
them across the index-set equality. -/
def SameIndexSetDifferentProof {depth : ℕ} {I₀ I₁ : IndexSet depth}
    (proof₀ : Proof S C I₀) (proof₁ : Proof S C I₁) : Prop :=
  ∃ h : I₀ = I₁, Proof.cast (S := S) (C := C) h proof₀ ≠ proof₁

theorem proof_ne_iff_exists_point {depth : ℕ} {I : IndexSet depth}
    (proof₀ proof₁ : Proof S C I) :
    proof₀ ≠ proof₁ ↔ ∃ i, proof₀ i ≠ proof₁ i := by
  constructor
  · intro hne
    by_contra hforall
    apply hne
    funext i
    by_contra hi
    exact hforall ⟨i, hi⟩
  · rintro ⟨i, hi⟩ hEq
    exact hi (congrArg (fun p => p i) hEq)

theorem sameIndexSetDifferentProof_witness {depth : ℕ} {I₀ I₁ : IndexSet depth}
    {proof₀ : Proof S C I₀} {proof₁ : Proof S C I₁}
    (h : SameIndexSetDifferentProof (S := S) (C := C) proof₀ proof₁) :
    ∃ hEq : I₀ = I₁, ∃ i, (Proof.cast (S := S) (C := C) hEq proof₀) i ≠ proof₁ i := by
  rcases h with ⟨hEq, hne⟩
  refine ⟨hEq, ?_⟩
  exact (proof_ne_iff_exists_point (S := S) (C := C)
    (Proof.cast (S := S) (C := C) hEq proof₀) proof₁).mp hne

private theorem list_all_true_of_mem {xs : List Bool} {b : Bool}
    (h : xs.all (fun x => x) = true) (hb : b ∈ xs) : b = true := by
  have hfalse : false ∉ xs := by
    simpa using h
  cases b <;> simp [hfalse] at hb ⊢

private theorem checkEntriesAux_eval_eq_map [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) {I : IndexSet depth} (commitment : C)
    (message : Subvector M I) (proof : Proof S C I) :
    ∀ xs : List {i // i ∈ I},
      eval f (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs) =
        xs.map (fun i =>
          eval f (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (message i) (proof i)))
  | [] => by
      simp [checkEntriesAux]
  | i :: xs => by
      rw [checkEntriesAux, eval_bind, eval_bind,
        checkEntriesAux_eval_eq_map f commitment message proof xs]
      simp

theorem check_eval_eq_true_implies_single [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I) (i : {j // j ∈ I})
    (hcheck : eval f
      (check (M := M) (S := S) (C := C) commitment I message proof) = true) :
    eval f
      (checkSingle (M := M) (S := S) (C := C) commitment i.1 (message i) (proof i)) = true := by
  classical
  let g : {j // j ∈ I} → Bool := fun j =>
    eval f
      (checkSingle (M := M) (S := S) (C := C) commitment j.1 (message j) (proof j))
  have hentries :
      eval f
          (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof I.attach.toList) =
        I.attach.toList.map g := by
    simpa [g] using checkEntriesAux_eval_eq_map (M := M) (S := S) (C := C)
      f commitment message proof I.attach.toList
  rw [check, eval_bind, eval_pure, checkEntries] at hcheck
  rw [hentries] at hcheck
  have hmem : g i ∈ I.attach.toList.map g := by
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    exact Finset.mem_toList.mpr (Finset.mem_attach I i)
  exact list_all_true_of_mem hcheck hmem

end MerkleTree
