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
