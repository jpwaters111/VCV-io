/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support.Indexing
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Merkle Commitment Scheme — Trace Support

Deterministic evaluation helpers for Merkle computations against a fixed oracle
function, together with log-level collision predicates used in the textbook
collision lemmas.
-/

open OracleComp OracleSpec

/-- Every entry of `small` also occurs in `big`. -/
def LogContains {ι : Type} {spec : OracleSpec ι} (small big : QueryLog spec) : Prop :=
  ∀ entry, entry ∈ small → entry ∈ big

namespace LogContains

variable {ι : Type} {spec : OracleSpec ι}

theorem refl (log : QueryLog spec) : LogContains log log := fun _ h => h

theorem trans {l₀ l₁ l₂ : QueryLog spec}
    (h₀₁ : LogContains l₀ l₁) (h₁₂ : LogContains l₁ l₂) :
    LogContains l₀ l₂ := fun entry h => h₁₂ entry (h₀₁ entry h)

theorem append_left (left right : QueryLog spec) : LogContains left (left ++ right) :=
  fun _ h => List.mem_append.mpr (.inl h)

theorem append_right (left right : QueryLog spec) : LogContains right (left ++ right) :=
  fun _ h => List.mem_append.mpr (.inr h)

end LogContains

/-- Two traces have a cross-collision if they contain distinct queries with the
same answer. -/
def CrossLogCollision {ι : Type} {spec : OracleSpec ι} (log₀ log₁ : QueryLog spec) : Prop :=
  ∃ entry₀ ∈ log₀, ∃ entry₁ ∈ log₁, entry₀.1 ≠ entry₁.1 ∧ HEq entry₀.2 entry₁.2

namespace CrossLogCollision

variable {ι : Type} {spec : OracleSpec ι}

theorem mono {log₀ log₀' log₁ log₁' : QueryLog spec}
    (h₀ : LogContains log₀ log₀') (h₁ : LogContains log₁ log₁') :
    CrossLogCollision log₀ log₁ → CrossLogCollision log₀' log₁' := by
  rintro ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
  exact ⟨entry₀, h₀ _ hentry₀, entry₁, h₁ _ hentry₁, hne, heq⟩

end CrossLogCollision

namespace MerkleTree

variable {M S C α β : Type}

/-- A fixed oracle function for the Merkle oracle specification. -/
abbrev OracleFn (M : Type) (S : Type) (C : Type) :=
  (t : (Oracle M S C).Domain) → (Oracle M S C).Range t

/-- Evaluate a Merkle oracle computation against a fixed oracle function. -/
def eval (f : OracleFn M S C) (oa : OracleComp (Oracle M S C) α) : α :=
  simulateQ (QueryImpl.ofFn f) oa

/-- Evaluate a Merkle oracle computation against a fixed oracle function while
recording its query-answer trace. -/
def logEval (f : OracleFn M S C) (oa : OracleComp (Oracle M S C) α) :
    α × QueryLog (Oracle M S C) :=
  (simulateQ ((QueryImpl.ofFn f).withLogging) oa).run

@[simp] theorem eval_query (f : OracleFn M S C) (t : (Oracle M S C).Domain) :
    eval f (liftM (query (spec := Oracle M S C) t)) = f t := rfl

@[simp] theorem eval_pure (f : OracleFn M S C) (x : α) :
    eval f (pure x : OracleComp (Oracle M S C) α) = x := rfl

@[simp] theorem eval_bind (f : OracleFn M S C) (oa : OracleComp (Oracle M S C) α)
    (ob : α → OracleComp (Oracle M S C) β) :
    eval f (oa >>= ob) = eval f (ob (eval f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rfl
  | query_bind t oa ih =>
      simpa [eval, simulateQ_bind] using ih (f t)

@[simp] theorem eval_map (f : OracleFn M S C) (g : α → β)
    (oa : OracleComp (Oracle M S C) α) :
    eval f (g <$> oa) = g (eval f oa) := by
  change simulateQ (QueryImpl.ofFn f) (g <$> oa) = g (simulateQ (QueryImpl.ofFn f) oa)
  rw [simulateQ_map]
  rfl

@[simp] theorem eval_leafCommit (f : OracleFn M S C) (message : M) (salt : S) :
    eval f (leafCommit (M := M) (S := S) (C := C) message salt :
      OracleComp (Oracle M S C) C) = f (Sum.inl (message, salt)) := rfl

@[simp] theorem eval_nodeCommit (f : OracleFn M S C) (left right : C) :
    eval f (nodeCommit (C := C) left right : OracleComp (Oracle M S C) C) =
      f (Sum.inr (left, right)) := rfl

@[simp] theorem logEval_query (f : OracleFn M S C) (t : (Oracle M S C).Domain) :
    logEval f (liftM (query (spec := Oracle M S C) t)) = (f t, [⟨t, f t⟩]) := rfl

@[simp] theorem logEval_pure (f : OracleFn M S C) (x : α) :
    logEval f (pure x : OracleComp (Oracle M S C) α) = (x, []) := rfl

theorem logEval_bind (f : OracleFn M S C) (oa : OracleComp (Oracle M S C) α)
    (ob : α → OracleComp (Oracle M S C) β) :
    logEval f (oa >>= ob) =
      let p := logEval f oa
      let q := logEval f (ob p.1)
      (q.1, p.2 ++ q.2) := by
  unfold logEval
  rw [simulateQ_bind, WriterT.run_bind']
  cases h : (simulateQ ((QueryImpl.ofFn f).withLogging) oa).run with
  | mk a log =>
      rfl

theorem eval_checkSingle_eq_true_iff [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) :
    eval f (checkSingle (M := M) (S := S) (C := C) commitment idx message authPath) = true ↔
      eval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath) = commitment := by
  rw [checkSingle, eval_bind, eval_pure]
  constructor
  · intro h
    exact (beq_iff_eq.mp h).symm
  · intro h
    exact beq_iff_eq.mpr h.symm

/-- The leaf query checked by `checkSingle`. -/
def checkLeafQuery {depth : ℕ} (message : M) (authPath : AuthPath S C depth) :
    (Oracle M S C).Domain :=
  Sum.inl (message, authPath.salt)

/-- The leaf index of `idx` inside the subtree rooted at layer `layer`. -/
def localIndex {depth : ℕ} (idx : Index depth) (layer : Fin (depth + 1)) :
    Fin (2 ^ (depth - layer.1)) :=
  ⟨idx.1 % 2 ^ (depth - layer.1), Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩

/-- The path label recomputed by `checkSingle` at a given tree layer. -/
def checkPathLabel (f : OracleFn M S C) {depth : ℕ} (idx : Index depth) (message : M)
    (authPath : AuthPath S C depth) (layer : Fin (depth + 1)) : C :=
  let truncSiblings : Vector C (depth - layer.1) := by
    simpa [Nat.min_eq_left (Nat.sub_le _ _)] using authPath.siblings.take (depth - layer.1)
  recomputeRootSingleWithHash
    (M := M) (S := S) (C := C)
    (fun x => f (Sum.inl x))
    (fun x => f (Sum.inr x))
    (localIndex idx layer)
    message
    ⟨authPath.salt, truncSiblings⟩

/-- The internal-node query used by `checkSingle` at the given non-root tree
layer, indexed from the root downward. -/
def checkInternalQuery (f : OracleFn M S C) {depth : ℕ} (idx : Index depth) (message : M)
    (authPath : AuthPath S C depth) (layer : Fin depth) : (Oracle M S C).Domain :=
  let childLayer : Fin (depth + 1) := ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩
  let childLabel := checkPathLabel f idx message authPath childLayer
  let siblingLabel := copathLabel authPath layer
  if (pathPos idx childLayer).1 % 2 = 0 then
    Sum.inr (childLabel, siblingLabel)
  else
    Sum.inr (siblingLabel, childLabel)

@[simp] theorem checkPathLabel_root (f : OracleFn M S C) {depth : ℕ} (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) :
    checkPathLabel f idx message authPath ⟨0, Nat.succ_pos _⟩ =
      let truncSiblings : Vector C depth := by
        simpa [Nat.min_eq_left (Nat.sub_le _ _)] using authPath.siblings.take depth
      recomputeRootSingleWithHash
        (M := M) (S := S) (C := C)
        (fun x => f (Sum.inl x))
        (fun x => f (Sum.inr x))
        (localIndex idx ⟨0, Nat.succ_pos _⟩)
        message
        ⟨authPath.salt, truncSiblings⟩ := by
  rfl

@[simp] theorem checkPathLabel_leaf (f : OracleFn M S C) {depth : ℕ} (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) :
    checkPathLabel f idx message authPath (Fin.last depth) =
      let truncSiblings : Vector C (depth - (Fin.last depth).1) := by
        simpa [Nat.min_eq_left (Nat.sub_le _ _)] using
          authPath.siblings.take (depth - (Fin.last depth).1)
      recomputeRootSingleWithHash
        (M := M) (S := S) (C := C)
        (fun x => f (Sum.inl x))
        (fun x => f (Sum.inr x))
        (localIndex idx (Fin.last depth))
        message
        ⟨authPath.salt, truncSiblings⟩ := by
  simp [checkPathLabel]

theorem checkPathLabel_parent (f : OracleFn M S C) {depth : ℕ} (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) (layer : Fin depth) :
    checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer =
      let childLayer : Fin (depth + 1) := ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩
      let childLabel := checkPathLabel f idx message authPath childLayer
      let siblingLabel := copathLabel authPath layer
      if (pathPos idx childLayer).1 % 2 = 0 then
        Sum.inr (childLabel, siblingLabel)
      else
        Sum.inr (siblingLabel, childLabel) := by
  rfl

theorem logEval_map (f : OracleFn M S C) (g : α → β)
    (oa : OracleComp (Oracle M S C) α) :
    logEval f (g <$> oa) = let p := logEval f oa; (g p.1, p.2) := by
  cases h : logEval f oa with
  | mk a log =>
      simp [map_eq_bind_pure_comp, logEval_bind, logEval_pure, h]

theorem logEval_recomputeRootSingle (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    logEval f (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath) =
      let leafQuery := checkLeafQuery (M := M) (S := S) (C := C) message authPath
      let leafLabel := f leafQuery
      let rest := logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) idx leafLabel authPath.siblings)
      (rest.1, [⟨leafQuery, leafLabel⟩] ++ rest.2) := by
  change logEval f
      ((liftM (query (spec := Oracle M S C) (Sum.inl (message, authPath.salt)))) >>= fun leaf =>
        recomputeRootAux (M := M) (S := S) (C := C) idx leaf authPath.siblings) = _
  rw [logEval_bind, logEval_query]
  rfl

theorem logEval_checkSingle [DecidableEq C] (f : OracleFn M S C) {depth : ℕ}
    (commitment : C) (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    logEval f (checkSingle (M := M) (S := S) (C := C) commitment idx message authPath) =
      let rootEval := logEval f
        (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath)
      (commitment == rootEval.1, rootEval.2) := by
  simpa [checkSingle] using
    logEval_map (M := M) (S := S) (C := C) f (BEq.beq commitment)
      (recomputeRootSingle (M := M) (S := S) (C := C) idx message authPath)

theorem checkLeafQuery_mem_logEval_checkSingle [DecidableEq C] (f : OracleFn M S C) {depth : ℕ}
    (commitment : C) (idx : Index depth) (message : M) (authPath : AuthPath S C depth) :
    ⟨checkLeafQuery (M := M) (S := S) (C := C) message authPath,
      f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩ ∈
        (logEval f
          (checkSingle (M := M) (S := S) (C := C) commitment idx message authPath)).2 := by
  rw [logEval_checkSingle]
  simp [logEval_recomputeRootSingle]

theorem logContains_checkSingle_checkEntriesAux [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) {I : IndexSet depth} (commitment : C)
    (message : Subvector M I) (proof : Proof S C I) :
    ∀ xs : List {i // i ∈ I}, ∀ i, i ∈ xs →
      LogContains
        (logEval f
          (checkSingle (M := M) (S := S) (C := C) commitment i.1 (message i) (proof i))).2
        (logEval f
          (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs)).2
  | [], _, hi => by
      cases hi
  | j :: xs, i, hi => by
      simp [checkEntriesAux, logEval_bind]
      by_cases hij : i = j
      · subst hij
        exact LogContains.append_left _ _
      · have hmap :
            (logEval f
              (List.cons
                (logEval f
                  (checkSingle (M := M) (S := S) (C := C)
                    commitment j.1 (message j) (proof j))).1 <$>
                checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs)).2 =
              (logEval f
                (checkEntriesAux (M := M) (S := S) (C := C) commitment message proof xs)).2 := by
            rw [logEval_map]
        simpa [hmap] using
          LogContains.trans
            (logContains_checkSingle_checkEntriesAux f commitment message proof xs i
              ((List.mem_cons.1 hi).resolve_left hij))
            (LogContains.append_right _ _)

theorem logContains_checkSingle_check [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (commitment : C) (I : IndexSet depth)
    (message : Subvector M I) (proof : Proof S C I) (i : {j // j ∈ I}) :
    LogContains
      (logEval f
        (checkSingle (M := M) (S := S) (C := C) commitment i.1 (message i) (proof i))).2
      (logEval f
        (check (M := M) (S := S) (C := C) commitment I message proof)).2 := by
  rw [show check (M := M) (S := S) (C := C) commitment I message proof =
      (fun bs => bs.all fun b => b) <$>
        checkEntriesAux (M := M) (S := S) (C := C) commitment message proof I.attach.toList by
      simp [check, checkEntries]]
  rw [logEval_map]
  simpa [checkEntries] using
    logContains_checkSingle_checkEntriesAux (M := M) (S := S) (C := C)
      f commitment message proof I.attach.toList i
      (by exact Finset.mem_toList.mpr (Finset.mem_attach I i))

end MerkleTree
