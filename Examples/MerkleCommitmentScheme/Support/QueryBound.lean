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

variable {M S C : Type}

private theorem isTotalQueryBound_liftQuery_one {ι : Type} {spec : OracleSpec ι}
    {t : spec.Domain} :
    IsTotalQueryBound (liftM (query (spec := spec) t) : OracleComp spec (spec.Range t)) 1 := by
  change IsTotalQueryBound
    ((liftM (query (spec := spec) t) : OracleComp spec (spec.Range t)) >>= fun u => pure u) 1
  rw [OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.succ_pos _, fun _ => trivial⟩

/-- Recomputing a single Merkle root makes exactly `depth + 1` oracle queries. -/
theorem mtRecomputeRootSingle_totalQueryBound {depth : ℕ} (idx : MTIndex depth)
    (message : M) (authPath : MTAuthPath S C depth) :
    IsTotalQueryBound
      (MTRecomputeRootSingle (M := M) (S := S) (C := C) idx message authPath)
      (depth + 1) := by
  induction depth generalizing message with
  | zero =>
      simpa [MTRecomputeRootSingle, MTLeafCommit] using
        (isTotalQueryBound_liftQuery_one
          (spec := MTOracle M S C) (t := Sum.inl (message, authPath.salt)))
  | succ depth ih =>
      cases hsplit : MTSplitIndex idx with
      | inl childIdx =>
          simp [MTRecomputeRootSingle, hsplit]
          have hchild :
              IsTotalQueryBound
                (MTRecomputeRootSingle (M := M) (S := S) (C := C)
                  childIdx message ⟨authPath.salt, authPath.siblings.tail⟩)
                (depth + 1) :=
            ih childIdx message ⟨authPath.salt, authPath.siblings.tail⟩
          have hnext : ∀ child,
              IsTotalQueryBound
                (MTNodeCommit (C := C) child authPath.siblings.head :
                  OracleComp (MTOracle M S C) C)
                1 := by
            intro child
            simpa [MTNodeCommit] using
              (isTotalQueryBound_liftQuery_one
                (spec := MTOracle M S C) (t := Sum.inr (child, authPath.siblings.head)))
          exact (isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 1) hchild hnext).mono
            (by omega)
      | inr childIdx =>
          simp [MTRecomputeRootSingle, hsplit]
          have hchild :
              IsTotalQueryBound
                (MTRecomputeRootSingle (M := M) (S := S) (C := C)
                  childIdx message ⟨authPath.salt, authPath.siblings.tail⟩)
                (depth + 1) :=
            ih childIdx message ⟨authPath.salt, authPath.siblings.tail⟩
          have hnext : ∀ child,
              IsTotalQueryBound
                (MTNodeCommit (C := C) authPath.siblings.head child :
                  OracleComp (MTOracle M S C) C)
                1 := by
            intro child
            simpa [MTNodeCommit] using
              (isTotalQueryBound_liftQuery_one
                (spec := MTOracle M S C) (t := Sum.inr (authPath.siblings.head, child)))
          exact (isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 1) hchild hnext).mono
            (by omega)

/-- Checking a single Merkle opening makes exactly `depth + 1` oracle queries. -/
theorem mtCheckSingle_totalQueryBound [DecidableEq C] {depth : ℕ} (commitment : C)
    (idx : MTIndex depth) (message : M) (authPath : MTAuthPath S C depth) :
    IsTotalQueryBound
      (MTCheckSingle (M := M) (S := S) (C := C) commitment idx message authPath)
      (depth + 1) := by
  change IsTotalQueryBound
    (MTRecomputeRootSingle (M := M) (S := S) (C := C) idx message authPath >>= fun root =>
      pure (commitment == root))
    (depth + 1)
  exact isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 0)
    (mtRecomputeRootSingle_totalQueryBound (M := M) (S := S) (C := C) idx message authPath)
    (fun _ => trivial)

/-- Internal list-based batch checking uses at most one single-check budget per
list entry. -/
theorem mtCheckEntriesAux_totalQueryBound [DecidableEq C] {depth : ℕ} {I : MTIndexSet depth}
    (commitment : C) (message : MTSubVector M I) (proof : MTProof S C I)
    (xs : List {i // i ∈ I}) :
    IsTotalQueryBound
      (MTCheckEntriesAux (M := M) (S := S) (C := C) commitment message proof xs)
      (xs.length * (depth + 1)) := by
  induction xs with
  | nil =>
      trivial
  | cons i xs ih =>
      simp [MTCheckEntriesAux]
      have hsingle :
          IsTotalQueryBound
            (MTCheckSingle (M := M) (S := S) (C := C)
              commitment i.1 (message i) (proof i))
            (depth + 1) :=
        mtCheckSingle_totalQueryBound (M := M) (S := S) (C := C)
          commitment i.1 (message i) (proof i)
      have hcont : ∀ ok,
          IsTotalQueryBound
            (do
              let restChecks ← MTCheckEntriesAux (M := M) (S := S) (C := C)
                commitment message proof xs
              pure (ok :: restChecks))
            (xs.length * (depth + 1)) := by
        intro ok
        simpa using
          (isTotalQueryBound_bind (n₁ := xs.length * (depth + 1)) (n₂ := 0) ih
            (fun restChecks => by
              show IsTotalQueryBound
                (pure (ok :: restChecks) : OracleComp (MTOracle M S C) (List Bool))
                0
              trivial))
      have hbound :
          depth + 1 + xs.length * (depth + 1) = (xs.length + 1) * (depth + 1) := by
        rw [Nat.succ_mul, Nat.add_comm]
      exact (isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := xs.length * (depth + 1))
        hsingle hcont).mono (le_of_eq hbound)

/-- Evaluating all batch-check components costs `I.card * (depth + 1)` oracle
queries. -/
theorem mtCheckEntries_totalQueryBound [DecidableEq C] {depth : ℕ}
    (commitment : C) (I : MTIndexSet depth) (message : MTSubVector M I) (proof : MTProof S C I) :
    IsTotalQueryBound
      (MTCheckEntries (M := M) (S := S) (C := C) commitment I message proof)
      (I.card * (depth + 1)) := by
  classical
  simpa [MTCheckEntries] using
    mtCheckEntriesAux_totalQueryBound (M := M) (S := S) (C := C)
      commitment message proof I.attach.toList

/-- Batch checking a fixed index set costs `I.card * (depth + 1)` oracle
queries. -/
theorem mtCheck_totalQueryBound [DecidableEq C] {depth : ℕ} (commitment : C)
    (I : MTIndexSet depth) (message : MTSubVector M I) (proof : MTProof S C I) :
    IsTotalQueryBound
      (MTCheck (M := M) (S := S) (C := C) commitment I message proof)
      (I.card * (depth + 1)) := by
  change IsTotalQueryBound
    (MTCheckEntries (M := M) (S := S) (C := C) commitment I message proof >>= fun oks =>
      pure (oks.all fun b => b))
    (I.card * (depth + 1))
  simpa using
    (isTotalQueryBound_bind (n₁ := I.card * (depth + 1)) (n₂ := 0)
      (mtCheckEntries_totalQueryBound (M := M) (S := S) (C := C) commitment I message proof)
      (fun oks => by
        show IsTotalQueryBound
          (pure (oks.all fun b => b) : OracleComp (MTOracle M S C) Bool)
          0
        trivial))
