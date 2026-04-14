/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support
import Examples.MerkleCommitmentScheme.Completeness

/-!
# Merkle Commitment Scheme — Collision Lemmas

This module collects the deterministic collision lemmas used by the textbook
binding and extractability arguments.
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

private theorem vector_tail_get {α : Type} {n : ℕ} (v : Vector α (n + 1)) (i : Fin n) :
    v.tail.get i = v.get i.succ := by
  have hsize : (v.toArray.extract 1 (n + 1)).size = n := by
    simp [Array.size_extract]
  change (Vector.mk (v.toArray.extract 1 (n + 1)) hsize).get i = v.get i.succ
  change (v.toArray.extract 1 (n + 1))[i.1] = v.toArray[i.1 + 1]
  rw [Array.getElem_extract]
  · rw [Vector.getElem_toArray, Vector.getElem_toArray]
    simp [Nat.add_comm]

private theorem vector_eq_of_head_tail_eq {n : ℕ} {v₀ v₁ : Vector C (n + 1)}
    (hhead : v₀.head = v₁.head) (htail : v₀.tail = v₁.tail) :
    v₀ = v₁ := by
  apply Vector.ext
  intro i hi
  cases i with
  | zero =>
      simpa using hhead
  | succ j =>
      have hj : j < n := Nat.lt_of_succ_lt_succ hi
      have htailGet : v₀.tail[j] = v₁.tail[j] := by
        exact congrArg (fun t => t[j]) htail
      simpa [Nat.add_comm] using htailGet

private theorem vector_zero_eq (v₀ v₁ : Vector C 0) : v₀ = v₁ := by
  apply Vector.ext
  intro i hi
  omega

private theorem authPath_eq_of_salt_siblings_eq {depth : ℕ}
    {authPath₀ authPath₁ : AuthPath S C depth}
    (hsalt : authPath₀.salt = authPath₁.salt)
    (hsiblings : authPath₀.siblings = authPath₁.siblings) :
    authPath₀ = authPath₁ := by
  cases authPath₀
  cases authPath₁
  cases hsalt
  cases hsiblings
  rfl

private theorem leafQuery_eq_implies_message_salt_eq {depth : ℕ}
    {message₀ message₁ : M} {authPath₀ authPath₁ : AuthPath S C depth}
    (h :
      checkLeafQuery (M := M) (S := S) (C := C) message₀ authPath₀ =
      checkLeafQuery (M := M) (S := S) (C := C) message₁ authPath₁) :
    message₀ = message₁ ∧ authPath₀.salt = authPath₁.salt := by
  cases authPath₀
  cases authPath₁
  simp [checkLeafQuery] at h
  simpa using h

private def recomputeRootAuxFirstQuery {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1)) :
    (Oracle M S C).Domain :=
  if idx.1 % 2 = 0 then
    Sum.inr (current, siblings.head)
  else
    Sum.inr (siblings.head, current)

private theorem logEval_nodeCommit (f : OracleFn M S C) (left right : C) :
    logEval f (nodeCommit (C := C) left right : OracleComp (Oracle M S C) C) =
      (f (Sum.inr (left, right)), [⟨Sum.inr (left, right), f (Sum.inr (left, right))⟩]) := by
  change logEval f (liftM (query (spec := Oracle M S C) (Sum.inr (left, right)))) = _
  rw [logEval_query]

private theorem logEval_recomputeRootAux_step_even (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 0) :
    logEval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
      let parent : C := f (Sum.inr (current, siblings.head))
      let rest := logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) (parentPos idx) parent siblings.tail)
      (rest.1, [⟨Sum.inr (current, siblings.head), parent⟩] ++ rest.2) := by
  rw [recomputeRootAux, if_pos hparity, logEval_bind, logEval_nodeCommit]

private theorem logEval_recomputeRootAux_step_odd (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 1) :
    logEval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
      let parent : C := f (Sum.inr (siblings.head, current))
      let rest := logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) (parentPos idx) parent siblings.tail)
      (rest.1, [⟨Sum.inr (siblings.head, current), parent⟩] ++ rest.2) := by
  have hne : ¬ idx.1 % 2 = 0 := by omega
  rw [recomputeRootAux, if_neg hne, logEval_bind, logEval_nodeCommit]

private theorem eval_recomputeRootAux_step_even (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 0) :
    eval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
      eval f
        (recomputeRootAux (M := M) (S := S) (C := C)
          (parentPos idx) (f (Sum.inr (current, siblings.head))) siblings.tail) := by
  rw [recomputeRootAux, if_pos hparity, eval_bind, eval_nodeCommit]

private theorem eval_recomputeRootAux_step_odd (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 1) :
    eval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
      eval f
        (recomputeRootAux (M := M) (S := S) (C := C)
          (parentPos idx) (f (Sum.inr (siblings.head, current))) siblings.tail) := by
  have hne : ¬ idx.1 % 2 = 0 := by omega
  rw [recomputeRootAux, if_neg hne, eval_bind, eval_nodeCommit]

private theorem recomputeRootAuxFirstEntry_mem_logEval_even (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 0) :
    ⟨Sum.inr (current, siblings.head), f (Sum.inr (current, siblings.head))⟩ ∈
      (logEval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)).2 := by
  rw [logEval_recomputeRootAux_step_even (M := M) (S := S) (C := C) f idx current siblings hparity]
  simp

private theorem recomputeRootAuxFirstEntry_mem_logEval_odd (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 1) :
    ⟨Sum.inr (siblings.head, current), f (Sum.inr (siblings.head, current))⟩ ∈
      (logEval f (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)).2 := by
  rw [logEval_recomputeRootAux_step_odd (M := M) (S := S) (C := C) f idx current siblings hparity]
  simp

private theorem logContains_recomputeRootAux_tail_even (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 0) :
    LogContains
      (logEval f
        (recomputeRootAux (M := M) (S := S) (C := C)
          (parentPos idx) (f (Sum.inr (current, siblings.head))) siblings.tail)).2
      (logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)).2 := by
  rw [logEval_recomputeRootAux_step_even (M := M) (S := S) (C := C) f idx current siblings hparity]
  exact LogContains.append_right _ _

private theorem logContains_recomputeRootAux_tail_odd (f : OracleFn M S C) {depth : ℕ}
    (idx : Index (depth + 1)) (current : C) (siblings : Vector C (depth + 1))
    (hparity : idx.1 % 2 = 1) :
    LogContains
      (logEval f
        (recomputeRootAux (M := M) (S := S) (C := C)
          (parentPos idx) (f (Sum.inr (siblings.head, current))) siblings.tail)).2
      (logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)).2 := by
  rw [logEval_recomputeRootAux_step_odd (M := M) (S := S) (C := C) f idx current siblings hparity]
  exact LogContains.append_right _ _

private theorem checkLeafQuery_mem_logEval_recomputeRootSingle (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    ⟨checkLeafQuery (M := M) (S := S) (C := C) message authPath,
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩ ∈
      (logEval f
        (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath)).2 := by
  rw [logEval_recomputeRootSingle]
  simp

private theorem logContains_recomputeRootAux_recomputeRootSingle (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    LogContains
      (logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) idx
          (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
          authPath.siblings)).2
      (logEval f
        (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath)).2 := by
  rw [logEval_recomputeRootSingle]
  exact LogContains.append_right _ _

private theorem recomputeRootAux_crossLogCollision :
    {depth : ℕ} →
    (f : OracleFn M S C) →
    (idx : Index depth) →
    ∀ current₀ current₁ : C, ∀ siblings₀ siblings₁ : Vector C depth,
      eval f (recomputeRootAux (M := M) (S := S) (C := C) idx current₀ siblings₀) =
        eval f (recomputeRootAux (M := M) (S := S) (C := C) idx current₁ siblings₁) →
      (current₀ ≠ current₁ ∨ siblings₀ ≠ siblings₁) →
      CrossLogCollision
        (logEval f (recomputeRootAux (M := M) (S := S) (C := C) idx current₀ siblings₀)).2
        (logEval f (recomputeRootAux (M := M) (S := S) (C := C) idx current₁ siblings₁)).2
  | 0, f, idx, current₀, current₁, siblings₀, siblings₁, hroot, hdiff => by
      simp [recomputeRootAux, eval_pure] at hroot
      cases hdiff with
      | inl hcurr =>
          exact False.elim (hcurr hroot)
      | inr hsiblings =>
          exact False.elim (hsiblings (vector_zero_eq _ _))
  | depth + 1, f, idx, current₀, current₁, siblings₀, siblings₁, hroot, hdiff => by
      rcases Nat.mod_two_eq_zero_or_one idx.1 with hparity | hparity
      · let parent₀ : C := f (Sum.inr (current₀, siblings₀.head))
        let parent₁ : C := f (Sum.inr (current₁, siblings₁.head))
        have hroot' := hroot
        rw [eval_recomputeRootAux_step_even (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity] at hroot'
        rw [eval_recomputeRootAux_step_even (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity] at hroot'
        by_cases hq :
            ((Sum.inr (current₀, siblings₀.head) : (Oracle M S C).Domain) =
              Sum.inr (current₁, siblings₁.head))
        · have hcurrHead : current₀ = current₁ ∧ siblings₀.head = siblings₁.head := by
            simpa using hq
          have htail : siblings₀.tail ≠ siblings₁.tail := by
            intro htailEq
            apply hdiff.elim
            · intro hcurrNe
              exact hcurrNe hcurrHead.1
            · intro hsiblingsNe
              exact hsiblingsNe (vector_eq_of_head_tail_eq hcurrHead.2 htailEq)
          have hrec :=
            recomputeRootAux_crossLogCollision
              f (parentPos idx) parent₀ parent₁ siblings₀.tail siblings₁.tail hroot'
              (Or.inr htail)
          exact CrossLogCollision.mono
            (logContains_recomputeRootAux_tail_even (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity)
            (logContains_recomputeRootAux_tail_even (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity)
            hrec
        · by_cases hp : parent₀ = parent₁
          · exact ⟨⟨Sum.inr (current₀, siblings₀.head), f (Sum.inr (current₀, siblings₀.head))⟩,
              recomputeRootAuxFirstEntry_mem_logEval_even (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity,
              ⟨Sum.inr (current₁, siblings₁.head), f (Sum.inr (current₁, siblings₁.head))⟩,
              recomputeRootAuxFirstEntry_mem_logEval_even (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity,
              hq, heq_of_eq hp⟩
          · have hrec :=
              recomputeRootAux_crossLogCollision
                f (parentPos idx) parent₀ parent₁ siblings₀.tail siblings₁.tail hroot'
                (Or.inl hp)
            exact CrossLogCollision.mono
              (logContains_recomputeRootAux_tail_even (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity)
              (logContains_recomputeRootAux_tail_even (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity)
              hrec
      · let parent₀ : C := f (Sum.inr (siblings₀.head, current₀))
        let parent₁ : C := f (Sum.inr (siblings₁.head, current₁))
        have hroot' := hroot
        rw [eval_recomputeRootAux_step_odd (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity] at hroot'
        rw [eval_recomputeRootAux_step_odd (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity] at hroot'
        by_cases hq :
            ((Sum.inr (siblings₀.head, current₀) : (Oracle M S C).Domain) =
              Sum.inr (siblings₁.head, current₁))
        · have hcurrHead : siblings₀.head = siblings₁.head ∧ current₀ = current₁ := by
            simpa using hq
          have htail : siblings₀.tail ≠ siblings₁.tail := by
            intro htailEq
            apply hdiff.elim
            · intro hcurrNe
              exact hcurrNe hcurrHead.2
            · intro hsiblingsNe
              exact hsiblingsNe (vector_eq_of_head_tail_eq hcurrHead.1 htailEq)
          have hrec :=
            recomputeRootAux_crossLogCollision
              f (parentPos idx) parent₀ parent₁ siblings₀.tail siblings₁.tail hroot'
              (Or.inr htail)
          exact CrossLogCollision.mono
            (logContains_recomputeRootAux_tail_odd (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity)
            (logContains_recomputeRootAux_tail_odd (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity)
            hrec
        · by_cases hp : parent₀ = parent₁
          · exact ⟨⟨Sum.inr (siblings₀.head, current₀), f (Sum.inr (siblings₀.head, current₀))⟩,
              recomputeRootAuxFirstEntry_mem_logEval_odd (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity,
              ⟨Sum.inr (siblings₁.head, current₁), f (Sum.inr (siblings₁.head, current₁))⟩,
              recomputeRootAuxFirstEntry_mem_logEval_odd (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity,
              hq, heq_of_eq hp⟩
          · have hrec :=
              recomputeRootAux_crossLogCollision
                f (parentPos idx) parent₀ parent₁ siblings₀.tail siblings₁.tail hroot'
                (Or.inl hp)
            exact CrossLogCollision.mono
              (logContains_recomputeRootAux_tail_odd (M := M) (S := S) (C := C) f idx current₀ siblings₀ hparity)
              (logContains_recomputeRootAux_tail_odd (M := M) (S := S) (C := C) f idx current₁ siblings₁ hparity)
              hrec

/-- Textbook single-index collision lemma. -/
theorem checkSingle_crossLogCollision [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (idx : Index depth)
    (message₀ message₁ : M) (authPath₀ authPath₁ : AuthPath S C depth)
    (hcheck₀ : eval f
      (checkSingle (M := M) (S := S) (C := C) commitment idx message₀ authPath₀) = true)
    (hcheck₁ : eval f
      (checkSingle (M := M) (S := S) (C := C) commitment idx message₁ authPath₁) = true)
    (hdiff : message₀ ≠ message₁ ∨ authPath₀ ≠ authPath₁) :
    CrossLogCollision
      (logEval f
        (checkSingle (M := M) (S := S) (C := C) commitment idx message₀ authPath₀)).2
      (logEval f
        (checkSingle (M := M) (S := S) (C := C) commitment idx message₁ authPath₁)).2 := by
  let leafQuery₀ := checkLeafQuery (M := M) (S := S) (C := C) message₀ authPath₀
  let leafQuery₁ := checkLeafQuery (M := M) (S := S) (C := C) message₁ authPath₁
  let leafLabel₀ := f leafQuery₀
  let leafLabel₁ := f leafQuery₁
  have hroot₀ :
      eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message₀ authPath₀) =
        commitment :=
    (eval_checkSingle_eq_true_iff (M := M) (S := S) (C := C)
      f commitment idx message₀ authPath₀).mp hcheck₀
  have hroot₁ :
      eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message₁ authPath₁) =
        commitment :=
    (eval_checkSingle_eq_true_iff (M := M) (S := S) (C := C)
      f commitment idx message₁ authPath₁).mp hcheck₁
  have hrootAux₀ :
      eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message₀ authPath₀) =
        eval f
          (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel₀ authPath₀.siblings) := by
    simp [recomputeRootSingle, checkLeafQuery, leafLabel₀, leafQuery₀, eval_bind]
  have hrootAux₁ :
      eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message₁ authPath₁) =
        eval f
          (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel₁ authPath₁.siblings) := by
    simp [recomputeRootSingle, checkLeafQuery, leafLabel₁, leafQuery₁, eval_bind]
  have hauxEq :
      eval f (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel₀ authPath₀.siblings) =
        eval f (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel₁ authPath₁.siblings) := by
    calc
      eval f (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel₀ authPath₀.siblings)
          = eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message₀ authPath₀) :=
        hrootAux₀.symm
      _ = commitment := hroot₀
      _ = eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message₁ authPath₁) := hroot₁.symm
      _ = eval f (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel₁ authPath₁.siblings) :=
        hrootAux₁
  by_cases hleafQuery : leafQuery₀ = leafQuery₁
  · have hmsgSalt :=
      leafQuery_eq_implies_message_salt_eq (M := M) (S := S) (C := C) hleafQuery
    have hsiblings :
        authPath₀.siblings ≠ authPath₁.siblings := by
      intro hsiblingsEq
      apply hdiff.elim
      · intro hmsgNe
        exact hmsgNe hmsgSalt.1
      · intro hpathNe
        exact hpathNe (authPath_eq_of_salt_siblings_eq hmsgSalt.2 hsiblingsEq)
    have hcolAux :=
      recomputeRootAux_crossLogCollision
        f idx leafLabel₀ leafLabel₁ authPath₀.siblings authPath₁.siblings hauxEq (Or.inr hsiblings)
    have hcolRoot :
        CrossLogCollision
          (logEval f
            (recomputeRootSingle (M := M) (S := S) (C := C) idx message₀ authPath₀)).2
          (logEval f
            (recomputeRootSingle (M := M) (S := S) (C := C) idx message₁ authPath₁)).2 :=
      CrossLogCollision.mono
        (logContains_recomputeRootAux_recomputeRootSingle (M := M) (S := S) (C := C)
          f idx message₀ authPath₀)
        (logContains_recomputeRootAux_recomputeRootSingle (M := M) (S := S) (C := C)
          f idx message₁ authPath₁)
        hcolAux
    simpa [logEval_checkSingle] using hcolRoot
  · by_cases hleafLabel : leafLabel₀ = leafLabel₁
    · exact
        ⟨⟨leafQuery₀, leafLabel₀⟩,
          checkLeafQuery_mem_logEval_checkSingle (M := M) (S := S) (C := C)
            f commitment idx message₀ authPath₀,
          ⟨leafQuery₁, leafLabel₁⟩,
          checkLeafQuery_mem_logEval_checkSingle (M := M) (S := S) (C := C)
            f commitment idx message₁ authPath₁,
          hleafQuery, heq_of_eq hleafLabel⟩
    · have hcolAux :=
        recomputeRootAux_crossLogCollision
          f idx leafLabel₀ leafLabel₁ authPath₀.siblings authPath₁.siblings hauxEq (Or.inl hleafLabel)
      have hcolRoot :
          CrossLogCollision
            (logEval f
              (recomputeRootSingle (M := M) (S := S) (C := C) idx message₀ authPath₀)).2
            (logEval f
              (recomputeRootSingle (M := M) (S := S) (C := C) idx message₁ authPath₁)).2 :=
        CrossLogCollision.mono
          (logContains_recomputeRootAux_recomputeRootSingle (M := M) (S := S) (C := C)
            f idx message₀ authPath₀)
          (logContains_recomputeRootAux_recomputeRootSingle (M := M) (S := S) (C := C)
            f idx message₁ authPath₁)
          hcolAux
      simpa [logEval_checkSingle] using hcolRoot

/-- Textbook batch collision lemma. -/
theorem check_crossLogCollision [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C)
    (I₀ I₁ : IndexSet depth) (message₀ : Subvector M I₀) (message₁ : Subvector M I₁)
    (proof₀ : Proof S C I₀) (proof₁ : Proof S C I₁)
    (hcheck₀ : eval f
      (check (M := M) (S := S) (C := C) commitment I₀ message₀ proof₀) = true)
    (hcheck₁ : eval f
      (check (M := M) (S := S) (C := C) commitment I₁ message₁ proof₁) = true)
    (hdiff :
      SharedValueMismatch (M := M) message₀ message₁ ∨
      SameIndexSetDifferentProof (S := S) (C := C) proof₀ proof₁) :
    CrossLogCollision
      (logEval f (check (M := M) (S := S) (C := C) commitment I₀ message₀ proof₀)).2
      (logEval f (check (M := M) (S := S) (C := C) commitment I₁ message₁ proof₁)).2 := by
  cases hdiff with
  | inl hmsg =>
      rcases hmsg with ⟨idx, hi₀, hi₁, hneq⟩
      let i₀ : {j // j ∈ I₀} := ⟨idx, hi₀⟩
      let i₁ : {j // j ∈ I₁} := ⟨idx, hi₁⟩
      have hsingle₀ := check_eval_eq_true_implies_single
        (M := M) (S := S) (C := C) f commitment I₀ message₀ proof₀ i₀ hcheck₀
      have hsingle₁ := check_eval_eq_true_implies_single
        (M := M) (S := S) (C := C) f commitment I₁ message₁ proof₁ i₁ hcheck₁
      have hcol :=
        checkSingle_crossLogCollision (M := M) (S := S) (C := C)
          f commitment idx (message₀ i₀) (message₁ i₁) (proof₀ i₀) (proof₁ i₁)
          hsingle₀ hsingle₁ (.inl hneq)
      exact CrossLogCollision.mono
        (logContains_checkSingle_check (M := M) (S := S) (C := C)
          f commitment I₀ message₀ proof₀ i₀)
        (logContains_checkSingle_check (M := M) (S := S) (C := C)
          f commitment I₁ message₁ proof₁ i₁)
        hcol
  | inr hproof =>
      rcases sameIndexSetDifferentProof_witness (S := S) (C := C) hproof with ⟨hEq, i, hne⟩
      subst hEq
      have hsingle₀ := check_eval_eq_true_implies_single
        (M := M) (S := S) (C := C) f commitment I₀ message₀ proof₀ i hcheck₀
      have hsingle₁ := check_eval_eq_true_implies_single
        (M := M) (S := S) (C := C) f commitment I₀ message₁ proof₁ i hcheck₁
      have hcol :=
        checkSingle_crossLogCollision (M := M) (S := S) (C := C)
          f commitment i.1 (message₀ i) (message₁ i) (proof₀ i) (proof₁ i)
          hsingle₀ hsingle₁ (.inr hne)
      exact CrossLogCollision.mono
        (logContains_checkSingle_check (M := M) (S := S) (C := C)
          f commitment I₀ message₀ proof₀ i)
        (logContains_checkSingle_check (M := M) (S := S) (C := C)
          f commitment I₀ message₁ proof₁ i)
        hcol

end MerkleTree
