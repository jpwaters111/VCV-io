/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support.Trace
import Examples.CommitmentScheme.Support.QueryBound

/-!
# Merkle Commitment Scheme — Query-Bound Support

Total-query-bound lemmas for Merkle opening verification.
-/

open OracleSpec OracleComp

namespace MerkleTree

variable {M S C : Type}

private theorem isTotalQueryBound_liftQuery_one {ι : Type} {spec : OracleSpec ι}
    {t : spec.Domain} :
    IsTotalQueryBound (liftM (query (spec := spec) t) : OracleComp spec (spec.Range t)) 1 := by
  change IsTotalQueryBound
    ((liftM (query (spec := spec) t) : OracleComp spec (spec.Range t)) >>= fun u => pure u) 1
  rw [OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.succ_pos _, fun _ => trivial⟩

private theorem mapFinM_totalQueryBound {ι : Type} {spec : OracleSpec ι} {α : Type}
    {n k : ℕ} (f : Fin n → OracleComp spec α)
    (hf : ∀ i, IsTotalQueryBound (f i) k) :
    IsTotalQueryBound (mapFinM (spec := spec) f) (n * k) := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      simp [mapFinM]
      have hhead : IsTotalQueryBound (f 0) k := hf 0
      have htail :
          IsTotalQueryBound
            (mapFinM (spec := spec) fun i : Fin n => f i.succ)
            (n * k) := by
        exact ih (fun i => f i.succ) fun i => hf i.succ
      have hraw :
          IsTotalQueryBound
            (f 0 >>= fun head =>
              mapFinM (spec := spec) (fun i : Fin n => f i.succ) >>= fun tail =>
                pure
                  (Vector.ofFn fun
                    | ⟨0, _⟩ => head
                    | ⟨Nat.succ i, hi⟩ =>
                        tail.get ⟨i, Nat.lt_of_succ_lt_succ hi⟩))
            (k + (n * k + 0)) := by
        exact isTotalQueryBound_bind (n₁ := k) (n₂ := n * k + 0)
          hhead fun _ =>
            isTotalQueryBound_bind (n₁ := n * k) (n₂ := 0) htail
              fun _ => trivial
      exact hraw.mono (by
        rw [Nat.succ_mul]
        omega)

/-- Hashing all leaves costs one oracle query per leaf. -/
theorem buildLeafLayer_totalQueryBound {depth : ℕ}
    (messages : Leaves M depth) (salts : Leaves S depth) :
    IsTotalQueryBound
      (buildLeafLayer (M := M) (S := S) (C := C) messages salts)
      (2 ^ depth) := by
  unfold buildLeafLayer
  simpa using
    (mapFinM_totalQueryBound
      (spec := Oracle M S C)
      (k := 1)
      (fun i =>
        leafCommit (M := M) (S := S) (C := C)
          (messages.get i) (salts.get i))
      (fun i => by
        simpa [leafCommit] using
          (isTotalQueryBound_liftQuery_one
            (spec := Oracle M S C)
            (t := Sum.inl (messages.get i, salts.get i)))))

/-- Hashing one internal layer costs one oracle query per parent. -/
theorem buildLayer_totalQueryBound {depth : ℕ}
    (children : LayerVector C (depth + 1)) :
    IsTotalQueryBound
      (buildLayer (M := M) (S := S) (C := C) children)
      (2 ^ depth) := by
  unfold buildLayer
  simpa using
    (mapFinM_totalQueryBound
      (spec := Oracle M S C)
      (k := 1)
      (fun i =>
        nodeCommit (C := C)
          (children.get (leftChildPos i))
          (children.get (rightChildPos i)))
      (fun i => by
        simpa [nodeCommit] using
          (isTotalQueryBound_liftQuery_one
            (spec := Oracle M S C)
            (t := Sum.inr
              (children.get (leftChildPos i), children.get (rightChildPos i))))))

/-- Building all internal labels above a leaf layer costs one query per internal
tree node. -/
theorem buildLabels_totalQueryBound {depth : ℕ}
    (leaves : LayerVector C depth) :
    IsTotalQueryBound
      (buildLabels (M := M) (S := S) (C := C) leaves)
      (2 ^ depth - 1) := by
  induction depth with
  | zero =>
      change IsTotalQueryBound
        (pure (fun layer => by
          have hlayer : layer = 0 := by
            apply Fin.ext
            omega
          subst hlayer
          exact leaves) : OracleComp (Oracle M S C) (Labels C 0))
        0
      trivial
  | succ depth ih =>
      have hlayer :
          IsTotalQueryBound
            (buildLayer (M := M) (S := S) (C := C) leaves)
            (2 ^ depth) :=
        buildLayer_totalQueryBound (M := M) (S := S) (C := C) leaves
      have hcont : ∀ upperLayer : LayerVector C depth,
          IsTotalQueryBound
            (do
              let upper ← buildLabels (M := M) (S := S) (C := C) upperLayer
              pure
                (Fin.snoc
                  (α := fun layer : Fin (depth + 2) => LayerVector C layer.1)
                  upper leaves))
            (2 ^ depth - 1) := by
        intro upperLayer
        exact isTotalQueryBound_bind (n₁ := 2 ^ depth - 1) (n₂ := 0)
          (ih upperLayer) fun _ => trivial
      have hraw :=
        isTotalQueryBound_bind (n₁ := 2 ^ depth) (n₂ := 2 ^ depth - 1)
          hlayer hcont
      change IsTotalQueryBound
        (buildLayer (M := M) (S := S) (C := C) leaves >>= fun upperLayer =>
          buildLabels (M := M) (S := S) (C := C) upperLayer >>= fun upper =>
            pure
              (Fin.snoc
                (α := fun layer : Fin (depth + 2) => LayerVector C layer.1)
                upper leaves))
        (2 ^ (depth + 1) - 1)
      exact hraw.mono (by
        have hpow : 2 ^ (depth + 1) = 2 * 2 ^ depth := by
          rw [pow_succ]
          ring
        omega)

/-- Building the full Merkle tree costs one query per tree node. -/
theorem buildTree_totalQueryBound {depth : ℕ}
    (messages : Leaves M depth) (salts : Leaves S depth) :
    IsTotalQueryBound
      (buildTree (M := M) (S := S) (C := C) messages salts)
      (2 ^ (depth + 1) - 1) := by
  change IsTotalQueryBound
    (buildLeafLayer (M := M) (S := S) (C := C) messages salts >>= fun leafLayer =>
      buildLabels (M := M) (S := S) (C := C) leafLayer)
    (2 ^ (depth + 1) - 1)
  have hleaf :=
    buildLeafLayer_totalQueryBound (M := M) (S := S) (C := C) messages salts
  have hcont : ∀ leafLayer : LayerVector C depth,
      IsTotalQueryBound
        (buildLabels (M := M) (S := S) (C := C) leafLayer)
        (2 ^ depth - 1) := by
    intro leafLayer
    exact buildLabels_totalQueryBound (M := M) (S := S) (C := C) leafLayer
  have hraw :=
    isTotalQueryBound_bind (n₁ := 2 ^ depth) (n₂ := 2 ^ depth - 1)
      hleaf hcont
  exact hraw.mono (by
    have hpow : 2 ^ (depth + 1) = 2 * 2 ^ depth := by
      rw [pow_succ]
      ring
    omega)

/-- Fixed-salt commitment costs one query per tree node. -/
theorem commitWithSalts_totalQueryBound {depth : ℕ}
    (messages : Leaves M depth) (salts : Leaves S depth) :
    IsTotalQueryBound
      (commitWithSalts (M := M) (S := S) (C := C) messages salts)
      (2 ^ (depth + 1) - 1) := by
  unfold commitWithSalts
  exact isTotalQueryBound_bind (n₁ := 2 ^ (depth + 1) - 1) (n₂ := 0)
    (buildTree_totalQueryBound (M := M) (S := S) (C := C) messages salts)
    fun _ => trivial

/-- Recomputing a single Merkle root makes exactly `depth + 1` oracle queries. -/
theorem recomputeRootAux_totalQueryBound {depth : ℕ} (idx : Index depth)
    (current : C) (siblings : Vector C depth) :
    IsTotalQueryBound
      (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)
      depth := by
  induction depth generalizing current with
  | zero =>
      trivial
  | succ depth ih =>
      by_cases hparity : idx.1 % 2 = 0
      · simp [recomputeRootAux, hparity]
        have hnode :
            IsTotalQueryBound
              (nodeCommit (C := C) current siblings.head : OracleComp (Oracle M S C) C)
              1 := by
          simpa [nodeCommit] using
            (isTotalQueryBound_liftQuery_one
              (spec := Oracle M S C) (t := Sum.inr (current, siblings.head)))
        have hcont : ∀ parent,
            IsTotalQueryBound
              (recomputeRootAux (M := M) (S := S) (C := C)
                (parentPos idx) parent siblings.tail)
              depth := by
          intro parent
          simpa using ih (parentPos idx) parent siblings.tail
        simpa [Nat.add_comm] using
          (isTotalQueryBound_bind (n₁ := 1) (n₂ := depth) hnode hcont)
      · simp [recomputeRootAux, hparity]
        have hnode :
            IsTotalQueryBound
              (nodeCommit (C := C) siblings.head current : OracleComp (Oracle M S C) C)
              1 := by
          simpa [nodeCommit] using
            (isTotalQueryBound_liftQuery_one
              (spec := Oracle M S C) (t := Sum.inr (siblings.head, current)))
        have hcont : ∀ parent,
            IsTotalQueryBound
              (recomputeRootAux (M := M) (S := S) (C := C)
                (parentPos idx) parent siblings.tail)
              depth := by
          intro parent
          simpa using ih (parentPos idx) parent siblings.tail
        simpa [Nat.add_comm] using
          (isTotalQueryBound_bind (n₁ := 1) (n₂ := depth) hnode hcont)

/-- Recomputing a single Merkle root makes exactly `depth + 1` oracle queries. -/
theorem recomputeRootSingle_totalQueryBound {depth : ℕ} (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) :
    IsTotalQueryBound
      (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath)
      (depth + 1) := by
  change IsTotalQueryBound
    ((leafCommit (M := M) (S := S) (C := C) message authPath.salt :
        OracleComp (Oracle M S C) C) >>= fun leaf =>
      recomputeRootAux (M := M) (S := S) (C := C) idx leaf authPath.siblings)
    (depth + 1)
  have hleaf :
      IsTotalQueryBound
        (leafCommit (M := M) (S := S) (C := C) message authPath.salt :
          OracleComp (Oracle M S C) C)
        1 := by
    simpa [leafCommit] using
      (isTotalQueryBound_liftQuery_one
        (spec := Oracle M S C) (t := Sum.inl (message, authPath.salt)))
  have hcont : ∀ leaf,
      IsTotalQueryBound
        (recomputeRootAux (M := M) (S := S) (C := C) idx leaf authPath.siblings)
        depth := by
    intro leaf
    exact recomputeRootAux_totalQueryBound (M := M) (S := S) (C := C) idx leaf authPath.siblings
  simpa [Nat.add_comm] using
    (isTotalQueryBound_bind (n₁ := 1) (n₂ := depth) hleaf hcont)

/-- Checking a single Merkle opening makes exactly `depth + 1` oracle queries. -/
theorem checkSingle_totalQueryBound [DecidableEq C] {depth : ℕ} (commitment : C)
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    IsTotalQueryBound
      (checkSingle (M := M) (S := S) (C := C) commitment idx message authPath)
      (depth + 1) := by
  change IsTotalQueryBound
    (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath >>= fun root =>
      pure (commitment == root))
    (depth + 1)
  exact isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 0)
    (recomputeRootSingle_totalQueryBound (M := M) (S := S) (C := C) idx message authPath)
    (fun _ => trivial)

/-- Internal list-based batch checking uses at most one single-check budget per
list entry. -/
theorem checkEntriesAux_totalQueryBound [DecidableEq C] {depth : ℕ} {I : IndexSet depth}
    (commitment : C) (message : Subvector M I) (proof : Proof S C I)
    (xs : List {i // i ∈ I}) :
    IsTotalQueryBound
      (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs)
      (xs.length * (depth + 1)) := by
  induction xs with
  | nil =>
      trivial
  | cons i xs ih =>
      simp [checkEntriesAux]
      have hsingle :
          IsTotalQueryBound
            (checkSingle (M := M) (S := S) (C := C)
              commitment i.1 (message i) (proof i))
            (depth + 1) :=
        checkSingle_totalQueryBound (M := M) (S := S) (C := C)
          commitment i.1 (message i) (proof i)
      have hcont : ∀ ok,
          IsTotalQueryBound
            (do
              let restChecks ← checkEntriesAux (M := M) (S := S) (C := C)
                commitment message proof xs
              pure (ok :: restChecks))
            (xs.length * (depth + 1)) := by
        intro ok
        simpa using
          (isTotalQueryBound_bind (n₁ := xs.length * (depth + 1)) (n₂ := 0) ih
            (fun restChecks => by
              show IsTotalQueryBound
                (pure (ok :: restChecks) : OracleComp (Oracle M S C) (List Bool))
                0
              trivial))
      have hbound :
          depth + 1 + xs.length * (depth + 1) = (xs.length + 1) * (depth + 1) := by
        rw [Nat.succ_mul, Nat.add_comm]
      exact (isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := xs.length * (depth + 1))
        hsingle hcont).mono (le_of_eq hbound)

/-- Evaluating all batch-check components costs `I.card * (depth + 1)` oracle
queries. -/
theorem checkEntries_totalQueryBound [DecidableEq C] {depth : ℕ}
    (commitment : C) (I : IndexSet depth) (message : Subvector M I) (proof : Proof S C I) :
    IsTotalQueryBound
      (checkEntries (M := M) (S := S) (C := C) commitment I message proof)
      (I.card * (depth + 1)) := by
  classical
  simpa [checkEntries] using
    checkEntriesAux_totalQueryBound (M := M) (S := S) (C := C)
      commitment message proof I.attach.toList

/-- Batch checking a fixed index set costs `I.card * (depth + 1)` oracle
queries. -/
theorem check_totalQueryBound [DecidableEq C] {depth : ℕ} (commitment : C)
    (I : IndexSet depth) (message : Subvector M I) (proof : Proof S C I) :
    IsTotalQueryBound
      (check (M := M) (S := S) (C := C) commitment I message proof)
      (I.card * (depth + 1)) := by
  change IsTotalQueryBound
    (checkEntries (M := M) (S := S) (C := C) commitment I message proof >>= fun oks =>
      pure (oks.all fun b => b))
    (I.card * (depth + 1))
  simpa using
    (isTotalQueryBound_bind (n₁ := I.card * (depth + 1)) (n₂ := 0)
      (checkEntries_totalQueryBound (M := M) (S := S) (C := C) commitment I message proof)
      (fun oks => by
        show IsTotalQueryBound
          (pure (oks.all fun b => b) : OracleComp (Oracle M S C) Bool)
          0
        trivial))

end MerkleTree
