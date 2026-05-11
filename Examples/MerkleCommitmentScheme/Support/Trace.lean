/- 
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support.Indexing
import Mathlib.Data.Array.Extract
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

/-- Interpret a lazy random-oracle cache as a total fixed oracle, using `default`
for points that have not been sampled. -/
noncomputable def oracleFnOfCache [Inhabited C]
    (cache : QueryCache (Oracle M S C)) : OracleFn M S C :=
  fun t =>
    match cache t with
    | some v => v
    | none => default

@[simp] theorem oracleFnOfCache_apply_of_some [Inhabited C]
    {cache : QueryCache (Oracle M S C)} {t : (Oracle M S C).Domain}
    {v : (Oracle M S C).Range t} (h : cache t = some v) :
    oracleFnOfCache (M := M) (S := S) (C := C) cache t = v := by
  simp [oracleFnOfCache, h]

/-- Evaluate a Merkle oracle computation against a fixed oracle function. -/
def eval (f : OracleFn M S C) (oa : OracleComp (Oracle M S C) α) : α :=
  simulateQ (QueryImpl.ofFn f) oa

/-- Evaluate a Merkle oracle computation against a fixed oracle function while
recording its query-answer trace. -/
def logEval (f : OracleFn M S C) (oa : OracleComp (Oracle M S C) α) :
    α × QueryLog (Oracle M S C) :=
  (simulateQ ((QueryImpl.ofFn f).withLogging) oa).run

/-- The value component of fixed-oracle logging is fixed-oracle evaluation. -/
theorem logEval_fst_eq_eval (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) α) :
    (logEval f oa).1 = eval f oa := by
  unfold logEval eval
  have h :=
    QueryImpl.fst_map_run_withLogging (QueryImpl.ofFn f) oa
  simpa using h

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
  let truncSiblings : Vector C (depth - layer.1) :=
    Vector.cast (by simp)
      (authPath.siblings.take (depth - layer.1))
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
      let truncSiblings : Vector C depth :=
        Vector.cast (by simp)
          (authPath.siblings.take depth)
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
      let truncSiblings : Vector C (depth - (Fin.last depth).1) :=
        Vector.cast (by simp)
          (authPath.siblings.take (depth - (Fin.last depth).1))
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

private def vectorTakeLE {α : Type} {n : ℕ} (v : Vector α n) (k : ℕ) (hk : k ≤ n) :
    Vector α k :=
  Vector.cast (by simp [Nat.min_eq_left hk]) (v.take k)

private theorem vector_tail_getElem {α : Type} {n : ℕ} (v : Vector α (n + 1))
    {i : ℕ} (hi : i < n) :
    v.tail[i] = v[i + 1] := by
  have hsize : (v.toArray.extract 1 (n + 1)).size = n := by
    simp [Array.size_extract]
  change (Vector.mk (v.toArray.extract 1 (n + 1)) hsize)[i] = v[i + 1]
  rw [Vector.getElem_mk]
  change (v.toArray.extract 1 (n + 1))[i] = v[i + 1]
  rw [Array.getElem_extract]
  rw [Vector.getElem_toArray]
  simp [Nat.add_comm]

private theorem vectorTakeLE_succ_head {α : Type} {n k : ℕ} (v : Vector α (n + 1))
    (hk : k ≤ n) :
    (vectorTakeLE v (k + 1) (Nat.succ_le_succ hk)).head = v.head := by
  unfold vectorTakeLE
  change (Vector.cast _ (v.take (k + 1)))[0] = v[0]
  rw [Vector.getElem_cast]
  unfold Vector.take Array.take
  rw [Vector.getElem_mk]
  rw [Array.getElem_extract]
  rw [Vector.getElem_toArray]

private theorem vectorTakeLE_succ_tail {α : Type} {n k : ℕ} (v : Vector α (n + 1))
    (hk : k ≤ n) :
    (vectorTakeLE v (k + 1) (Nat.succ_le_succ hk)).tail =
      vectorTakeLE v.tail k (by simpa using hk) := by
  apply Vector.ext
  intro i hi
  rw [vector_tail_getElem]
  unfold vectorTakeLE
  change (Vector.cast _ (v.take (k + 1)))[i + 1] =
    (Vector.cast _ (v.tail.take k))[i]
  rw [Vector.getElem_cast]
  rw [Vector.getElem_cast]
  unfold Vector.take Array.take
  rw [Vector.getElem_mk]
  rw [Vector.getElem_mk]
  rw [Array.getElem_extract]
  rw [Array.getElem_extract]
  rw [Vector.getElem_toArray]
  rw [Vector.getElem_toArray]
  rw [vector_tail_getElem]
  simp

private theorem vector_reverse_get_last {α : Type} {n : ℕ} (v : Vector α (n + 1)) :
    v.reverse.get ⟨n, by omega⟩ = v.head := by
  change v.reverse[n] = v[0]
  rw [Vector.getElem_reverse]
  congr
  omega

private theorem vector_reverse_get_cast_succ {α : Type} {n : ℕ} (v : Vector α (n + 1))
    (i : Fin n) :
    v.reverse.get ⟨i.1, by omega⟩ = v.tail.reverse.get i := by
  change v.reverse[i.1] = v.tail.reverse[i.1]
  rw [Vector.getElem_reverse]
  rw [Vector.getElem_reverse]
  rw [vector_tail_getElem]
  congr
  omega

private def pathLabelPrefix (f : OracleFn M S C) (idxVal : ℕ) (current : C)
    {height : ℕ} (siblings : Vector C height) : C :=
  recomputeRootAuxWithHash (fun x => f (Sum.inr x))
    ⟨idxVal % 2 ^ height, Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩
    current siblings

@[simp] private theorem pathLabelPrefix_zero (f : OracleFn M S C) (idxVal : ℕ)
    (current : C) (siblings : Vector C 0) :
    pathLabelPrefix f idxVal current siblings = current := by
  simp [pathLabelPrefix, recomputeRootAuxWithHash]

private theorem pathLabelPrefix_vectorTakeLE_congr (f : OracleFn M S C)
    {n k l : ℕ} (idxVal : ℕ) (current : C) (siblings : Vector C n)
    (hk : k ≤ n) (hl : l ≤ n) (h : k = l) :
    pathLabelPrefix f idxVal current (vectorTakeLE siblings k hk) =
      pathLabelPrefix f idxVal current (vectorTakeLE siblings l hl) := by
  subst h
  rfl

private theorem pathLabelPrefix_succ (f : OracleFn M S C) {n k : ℕ}
    (idxVal : ℕ) (current : C) (siblings : Vector C (n + 1)) (hk : k ≤ n) :
    pathLabelPrefix f idxVal current (vectorTakeLE siblings (k + 1) (Nat.succ_le_succ hk)) =
      let parent :=
        if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
        else f (Sum.inr (siblings.head, current))
      pathLabelPrefix f (idxVal / 2) parent (vectorTakeLE siblings.tail k (by simpa using hk)) := by
  unfold pathLabelPrefix
  rw [recomputeRootAuxWithHash]
  rw [vectorTakeLE_succ_head (v := siblings) (hk := hk)]
  rw [vectorTakeLE_succ_tail (v := siblings) (hk := hk)]
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]
    ring
  have hparity : idxVal % 2 ^ (k + 1) % 2 = idxVal % 2 := by
    rw [hpow]
    rw [Nat.mod_mul_right_mod]
  have hparentIdx :
      parentPos
          ⟨idxVal % 2 ^ (k + 1),
            Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩ =
        (⟨idxVal / 2 % 2 ^ k,
          Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩ :
          Fin (2 ^ k)) := by
    apply Fin.ext
    simp [parentPos]
    rw [hpow]
    rw [Nat.mod_mul_right_div_self]
  by_cases h : idxVal % 2 = 0
  · simp [hparity, h, hparentIdx]
  · simp [hparity, h, hparentIdx]

private def internalQueryPrefix (f : OracleFn M S C) (idxVal : ℕ) (current : C)
    {height : ℕ} (siblings : Vector C height) (layer : Fin height) :
    (Oracle M S C).Domain :=
  let childHeight := height - (layer.1 + 1)
  let childLabel := pathLabelPrefix f idxVal current
    (vectorTakeLE siblings childHeight (by omega))
  let siblingLabel := siblings.reverse.get layer
  if (idxVal / 2 ^ childHeight) % 2 = 0 then
    Sum.inr (childLabel, siblingLabel)
  else
    Sum.inr (siblingLabel, childLabel)

private def queryAnswer (f : OracleFn M S C) (t : (Oracle M S C).Domain) : C :=
  match t with
  | Sum.inl q => f (Sum.inl q)
  | Sum.inr q => f (Sum.inr q)

private theorem internalQueryPrefix_answer (f : OracleFn M S C) :
    {height : ℕ} → (idxVal : ℕ) → (current : C) → (siblings : Vector C height) →
      (layer : Fin height) →
      queryAnswer f (internalQueryPrefix f idxVal current siblings layer) =
        pathLabelPrefix f idxVal current
          (vectorTakeLE siblings (height - layer.1) (Nat.sub_le _ _))
  | 0, _, _, _, layer => by
      exact Fin.elim0 layer
  | n + 1, idxVal, current, siblings, ⟨layer, hlayer⟩ => by
      by_cases hlast : layer = n
      · subst layer
        have hparent :
            pathLabelPrefix f idxVal current
                (vectorTakeLE siblings (n + 1 - n) (Nat.sub_le _ _)) =
              if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
              else f (Sum.inr (siblings.head, current)) := by
          have h := pathLabelPrefix_succ (f := f) (n := n) (k := 0)
            (idxVal := idxVal) (current := current) (siblings := siblings)
            (hk := Nat.zero_le n)
          have hlen :
              pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings (n + 1 - n) (Nat.sub_le _ _)) =
                pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings 1 (by omega)) :=
            pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
              (Nat.sub_le _ _) (by omega) (by omega)
          have hbase :
              pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings 1 (by omega)) =
                if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
                else f (Sum.inr (siblings.head, current)) := by
            simpa [pathLabelPrefix] using h
          exact hlen.trans hbase
        have hchild0 :
            pathLabelPrefix f idxVal current
                (vectorTakeLE siblings (n + 1 - (n + 1)) (by omega)) = current := by
          have hlen :
              pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings (n + 1 - (n + 1)) (by omega)) =
                pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings 0 (by omega)) :=
            pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
              (by omega) (by omega) (by omega)
          simpa using hlen
        unfold internalQueryPrefix queryAnswer
        by_cases h : idxVal % 2 = 0
        · simpa [h, hchild0, vector_reverse_get_last] using hparent.symm
        · simpa [h, hchild0, vector_reverse_get_last] using hparent.symm
      · let parent :=
          if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
          else f (Sum.inr (siblings.head, current))
        let layer' : Fin n := ⟨layer, by omega⟩
        have hquery :
            internalQueryPrefix f idxVal current siblings ⟨layer, hlayer⟩ =
              internalQueryPrefix f (idxVal / 2) parent siblings.tail layer' := by
          unfold internalQueryPrefix
          have hchild : n + 1 - (layer + 1) = (n - (layer + 1)) + 1 := by
            omega
          have hpow : 2 ^ ((n - (layer + 1)) + 1) = 2 * 2 ^ (n - (layer + 1)) := by
            rw [pow_succ]
            ring
          have hdiv' :
              idxVal / 2 ^ ((n - (layer + 1)) + 1) =
                idxVal / 2 / 2 ^ (n - (layer + 1)) := by
            rw [Nat.div_div_eq_div_mul]
            rw [hpow]
          have hchildLabel :
              pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings (n + 1 - (layer + 1)) (by omega)) =
                pathLabelPrefix f (idxVal / 2) parent
                  (vectorTakeLE siblings.tail (n + 1 - 1 - (layer'.1 + 1)) (by omega)) := by
            have h := pathLabelPrefix_succ (f := f) (k := n - (layer + 1))
              (idxVal := idxVal) (current := current)
              (siblings := siblings) (hk := by omega)
            have hleft :
                pathLabelPrefix f idxVal current
                    (vectorTakeLE siblings (n + 1 - (layer + 1)) (by omega)) =
                  pathLabelPrefix f idxVal current
                    (vectorTakeLE siblings ((n - (layer + 1)) + 1) (by omega)) :=
              pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
                (by omega) (by omega) hchild
            have hright :
                pathLabelPrefix f (idxVal / 2) parent
                    (vectorTakeLE siblings.tail (n - (layer + 1)) (by omega)) =
                  pathLabelPrefix f (idxVal / 2) parent
                    (vectorTakeLE siblings.tail (n + 1 - 1 - (layer'.1 + 1)) (by omega)) :=
              pathLabelPrefix_vectorTakeLE_congr (f := f) (idxVal / 2) parent siblings.tail
                (by omega) (by omega) (by simp [layer'])
            have hstep :
                pathLabelPrefix f idxVal current
                    (vectorTakeLE siblings ((n - (layer + 1)) + 1) (by omega)) =
                  pathLabelPrefix f (idxVal / 2) parent
                    (vectorTakeLE siblings.tail (n - (layer + 1)) (by omega)) := by
              simpa [parent] using h
            exact hleft.trans (hstep.trans hright)
          simp [hchild, hchildLabel, hdiv',
            vector_reverse_get_cast_succ (v := siblings) (i := layer'), layer']
        rw [hquery]
        rw [internalQueryPrefix_answer (height := n) f (idxVal / 2) parent siblings.tail layer']
        have hparentLabel :
            pathLabelPrefix f (idxVal / 2) parent
                (vectorTakeLE siblings.tail (n - layer) (by omega)) =
              pathLabelPrefix f idxVal current
                (vectorTakeLE siblings (n + 1 - layer) (by omega)) := by
          have h := pathLabelPrefix_succ (f := f) (k := n - layer)
            (idxVal := idxVal) (current := current)
            (siblings := siblings) (hk := by omega)
          have hright :
              pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings ((n - layer) + 1) (by omega)) =
                pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings (n + 1 - layer) (by omega)) :=
            pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
              (by omega) (by omega) (by omega)
          have hstep :
              pathLabelPrefix f (idxVal / 2) parent
                  (vectorTakeLE siblings.tail (n - layer) (by omega)) =
                pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings ((n - layer) + 1) (by omega)) := by
            simpa [parent] using h.symm
          exact hstep.trans hright
        simpa [layer'] using hparentLabel

private theorem checkPathLabel_eq_pathLabelPrefix (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (layer : Fin (depth + 1)) :
    checkPathLabel f idx message authPath layer =
      pathLabelPrefix f idx.1
        (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
        (vectorTakeLE authPath.siblings (depth - layer.1) (Nat.sub_le _ _)) := by
  simp [checkPathLabel, pathLabelPrefix, checkLeafQuery, vectorTakeLE,
    recomputeRootSingleWithHash, localIndex]

private theorem checkInternalQuery_eq_internalQueryPrefix (f : OracleFn M S C) {depth : ℕ}
    (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (layer : Fin depth) :
    checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer =
      internalQueryPrefix f idx.1
        (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
        authPath.siblings layer := by
  unfold checkInternalQuery internalQueryPrefix
  have hpath :
      (pathPos idx ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩).1 =
        idx.1 / 2 ^ (depth - (layer.1 + 1)) := by
    simpa using
      pathPos_val_eq_div_pow (depth := depth) (idx := idx)
        (layer := ⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩)
  simp [checkPathLabel_eq_pathLabelPrefix, checkLeafQuery, copathLabel, hpath]

/-- The nondependent `C`-valued answer to the internal query used by
`checkSingle` at a non-root layer. -/
def checkInternalQueryAnswer (f : OracleFn M S C) {depth : ℕ} (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth) (layer : Fin depth) : C :=
  queryAnswer f (checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer)

theorem checkInternalQueryAnswer_eq_checkPathLabel_parent (f : OracleFn M S C)
    {depth : ℕ} (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (layer : Fin depth) :
    checkInternalQueryAnswer (M := M) (S := S) (C := C) f idx message authPath layer =
      checkPathLabel f idx message authPath ⟨layer.1, Nat.lt_succ_of_lt layer.2⟩ := by
  rw [checkInternalQueryAnswer, checkInternalQuery_eq_internalQueryPrefix,
    checkPathLabel_eq_pathLabelPrefix]
  simpa using
    internalQueryPrefix_answer (M := M) (S := S) (C := C) f idx.1
      (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
      authPath.siblings layer

theorem traceEntryAnswer_checkInternalQuery (f : OracleFn M S C)
    {depth : ℕ} (idx : Index depth) (message : M) (authPath : AuthPath S C depth)
    (layer : Fin depth) :
    traceEntryAnswer (M := M) (S := S) (C := C)
        ⟨checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer,
          f (checkInternalQuery (M := M) (S := S) (C := C)
            f idx message authPath layer)⟩ =
      checkInternalQueryAnswer (M := M) (S := S) (C := C)
        f idx message authPath layer := by
  unfold checkInternalQueryAnswer checkInternalQuery
  by_cases hparity :
      (pathPos idx
        (⟨layer.1 + 1, Nat.succ_lt_succ layer.2⟩ : Fin (depth + 1))).1 % 2 = 0
  · rw [if_pos hparity]
    simp [queryAnswer, traceEntryAnswer]
  · rw [if_neg hparity]
    simp [queryAnswer, traceEntryAnswer]

private theorem logEval_nodeCommit (f : OracleFn M S C) (left right : C) :
    logEval f (nodeCommit (C := C) left right : OracleComp (Oracle M S C) C) =
      (f (Sum.inr (left, right)), [⟨Sum.inr (left, right), f (Sum.inr (left, right))⟩]) := by
  simpa [nodeCommit] using
    (logEval_query (M := M) (S := S) (C := C) f (Sum.inr (left, right)))

private def recomputeRootAuxLogPrefix (f : OracleFn M S C) (idxVal : ℕ) (current : C) :
    {height : ℕ} → Vector C height → QueryLog (Oracle M S C)
  | 0, _ => []
  | _ + 1, siblings =>
      if idxVal % 2 = 0 then
        let parent := f (Sum.inr (current, siblings.head))
        ⟨Sum.inr (current, siblings.head), parent⟩ ::
          recomputeRootAuxLogPrefix f (idxVal / 2) parent siblings.tail
      else
        let parent := f (Sum.inr (siblings.head, current))
        ⟨Sum.inr (siblings.head, current), parent⟩ ::
          recomputeRootAuxLogPrefix f (idxVal / 2) parent siblings.tail

private theorem logEval_recomputeRootAux_prefix (f : OracleFn M S C) :
    {height : ℕ} → (idxVal : ℕ) → (current : C) → (siblings : Vector C height) →
      logEval f
          (recomputeRootAux (M := M) (S := S) (C := C)
            ⟨idxVal % 2 ^ height, Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩
            current siblings) =
        (pathLabelPrefix f idxVal current siblings,
          recomputeRootAuxLogPrefix f idxVal current siblings)
  | 0, idxVal, current, siblings => by
      simp [recomputeRootAux, recomputeRootAuxLogPrefix]
  | n + 1, idxVal, current, siblings => by
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [pow_succ]
        ring
      have hparity : idxVal % 2 ^ (n + 1) % 2 = idxVal % 2 := by
        rw [hpow]
        rw [Nat.mod_mul_right_mod]
      have hparentIdx :
          parentPos
              ⟨idxVal % 2 ^ (n + 1),
                Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩ =
            (⟨idxVal / 2 % 2 ^ n,
              Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩ :
              Fin (2 ^ n)) := by
        apply Fin.ext
        simp [parentPos]
        rw [hpow]
        rw [Nat.mod_mul_right_div_self]
      by_cases h : idxVal % 2 = 0
      · rw [recomputeRootAux, pathLabelPrefix, recomputeRootAuxWithHash]
        simp [hparity, h, hparentIdx, recomputeRootAuxLogPrefix, logEval_bind,
          logEval_nodeCommit, logEval_recomputeRootAux_prefix, pathLabelPrefix]
      · rw [recomputeRootAux, pathLabelPrefix, recomputeRootAuxWithHash]
        simp [hparity, h, hparentIdx, recomputeRootAuxLogPrefix, logEval_bind,
          logEval_nodeCommit, logEval_recomputeRootAux_prefix, pathLabelPrefix]

private theorem internalQueryPrefix_succ_of_lt (f : OracleFn M S C) {n : ℕ}
    (idxVal : ℕ) (current : C) (siblings : Vector C (n + 1))
    (layer : Fin (n + 1)) (hlast : layer.1 ≠ n) :
    let parent :=
      if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
      else f (Sum.inr (siblings.head, current))
    internalQueryPrefix f idxVal current siblings layer =
      internalQueryPrefix f (idxVal / 2) parent siblings.tail ⟨layer.1, by omega⟩ := by
  rcases layer with ⟨layer, hlayer⟩
  have hne : layer ≠ n := by
    simpa using hlast
  have hlt : layer < n := by
    omega
  let parent :=
    if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
    else f (Sum.inr (siblings.head, current))
  let layer' : Fin n := ⟨layer, hlt⟩
  unfold internalQueryPrefix
  have hchild : n + 1 - (layer + 1) = (n - (layer + 1)) + 1 := by
    omega
  have hpow : 2 ^ ((n - (layer + 1)) + 1) = 2 * 2 ^ (n - (layer + 1)) := by
    rw [pow_succ]
    ring
  have hdiv' :
      idxVal / 2 ^ ((n - (layer + 1)) + 1) =
        idxVal / 2 / 2 ^ (n - (layer + 1)) := by
    rw [Nat.div_div_eq_div_mul]
    rw [hpow]
  have hchildLabel :
      pathLabelPrefix f idxVal current
          (vectorTakeLE siblings (n + 1 - (layer + 1)) (by omega)) =
        pathLabelPrefix f (idxVal / 2) parent
          (vectorTakeLE siblings.tail (n + 1 - 1 - (layer'.1 + 1)) (by omega)) := by
    have h := pathLabelPrefix_succ (f := f) (k := n - (layer + 1))
      (idxVal := idxVal) (current := current) (siblings := siblings) (hk := by omega)
    have hleft :
        pathLabelPrefix f idxVal current
            (vectorTakeLE siblings (n + 1 - (layer + 1)) (by omega)) =
          pathLabelPrefix f idxVal current
            (vectorTakeLE siblings ((n - (layer + 1)) + 1) (by omega)) :=
      pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
        (by omega) (by omega) hchild
    have hright :
        pathLabelPrefix f (idxVal / 2) parent
            (vectorTakeLE siblings.tail (n - (layer + 1)) (by omega)) =
          pathLabelPrefix f (idxVal / 2) parent
            (vectorTakeLE siblings.tail (n + 1 - 1 - (layer'.1 + 1)) (by omega)) :=
      pathLabelPrefix_vectorTakeLE_congr (f := f) (idxVal / 2) parent siblings.tail
        (by omega) (by omega) (by simp [layer'])
    have hstep :
        pathLabelPrefix f idxVal current
            (vectorTakeLE siblings ((n - (layer + 1)) + 1) (by omega)) =
          pathLabelPrefix f (idxVal / 2) parent
            (vectorTakeLE siblings.tail (n - (layer + 1)) (by omega)) := by
      simpa [parent] using h
    exact hleft.trans (hstep.trans hright)
  simp [hchild, hchildLabel, hdiv',
    vector_reverse_get_cast_succ (v := siblings) (i := layer'), layer', parent]

private theorem internalQueryPrefix_mem_recomputeRootAuxLogPrefix (f : OracleFn M S C) :
    {height : ℕ} → (idxVal : ℕ) → (current : C) → (siblings : Vector C height) →
      (layer : Fin height) →
      ⟨internalQueryPrefix f idxVal current siblings layer,
        f (internalQueryPrefix f idxVal current siblings layer)⟩ ∈
        recomputeRootAuxLogPrefix f idxVal current siblings
  | 0, _, _, _, layer => by
      exact Fin.elim0 layer
  | n + 1, idxVal, current, siblings, layer => by
      by_cases hlast : layer.1 = n
      · rcases layer with ⟨layer, hlayer⟩
        have heq : layer = n := by
          simpa using hlast
        subst layer
        have hchild0 :
            pathLabelPrefix f idxVal current
                (vectorTakeLE siblings (n + 1 - (n + 1)) (by omega)) = current := by
          have hlen :
              pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings (n + 1 - (n + 1)) (by omega)) =
                pathLabelPrefix f idxVal current
                  (vectorTakeLE siblings 0 (by omega)) :=
            pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
              (by omega) (by omega) (by omega)
          simpa using hlen
        by_cases h : idxVal % 2 = 0
        · have hcond : idxVal / 2 ^ (n + 1 - (n + 1)) % 2 = 0 := by
            simpa using h
          unfold recomputeRootAuxLogPrefix
          rw [if_pos h]
          simp only [List.mem_cons]
          left
          unfold internalQueryPrefix
          dsimp
          rw [if_pos hcond]
          rw [hchild0, vector_reverse_get_last]
        · have hcond : ¬ idxVal / 2 ^ (n + 1 - (n + 1)) % 2 = 0 := by
            simpa using h
          unfold recomputeRootAuxLogPrefix
          rw [if_neg h]
          simp only [List.mem_cons]
          left
          unfold internalQueryPrefix
          dsimp
          rw [if_neg hcond]
          rw [hchild0, vector_reverse_get_last]
      · let parent :=
          if idxVal % 2 = 0 then f (Sum.inr (current, siblings.head))
          else f (Sum.inr (siblings.head, current))
        let layer' : Fin n := ⟨layer.1, by omega⟩
        have hquery :
            internalQueryPrefix f idxVal current siblings layer =
              internalQueryPrefix f (idxVal / 2) parent siblings.tail layer' := by
          simpa [parent, layer'] using
            internalQueryPrefix_succ_of_lt f idxVal current siblings layer hlast
        have ih :=
          internalQueryPrefix_mem_recomputeRootAuxLogPrefix f (idxVal / 2) parent
            siblings.tail layer'
        unfold recomputeRootAuxLogPrefix
        by_cases h : idxVal % 2 = 0
        · simp [h]
          right
          rw [hquery]
          simpa [h, parent] using ih
        · simp [h]
          right
          rw [hquery]
          simpa [h, parent] using ih

private theorem internalQueryPrefix_last_eq_first (f : OracleFn M S C) {n : ℕ}
    (idxVal : ℕ) (current : C) (siblings : Vector C (n + 1)) :
    internalQueryPrefix f idxVal current siblings (Fin.last n) =
      if idxVal % 2 = 0 then
        Sum.inr (current, siblings.head)
      else
        Sum.inr (siblings.head, current) := by
  unfold internalQueryPrefix
  have hchild0 :
      pathLabelPrefix f idxVal current
          (vectorTakeLE siblings (n + 1 - (n + 1)) (by omega)) =
        current := by
    have hlen :
        pathLabelPrefix f idxVal current
            (vectorTakeLE siblings (n + 1 - (n + 1)) (by omega)) =
          pathLabelPrefix f idxVal current (vectorTakeLE siblings 0 (by omega)) :=
      pathLabelPrefix_vectorTakeLE_congr (f := f) idxVal current siblings
        (by omega) (by omega) (by omega)
    rw [hlen]
    exact
      pathLabelPrefix_zero (M := M) (S := S) (C := C)
        f idxVal current (vectorTakeLE siblings 0 (by omega))
  by_cases h : idxVal % 2 = 0
  · dsimp
    have hcond : idxVal / 2 ^ (n + 1 - (n + 1)) % 2 = 0 := by
      simpa using h
    rw [if_pos hcond, if_pos h]
    rw [hchild0]
    exact congrArg (fun x => Sum.inr (current, x))
      (by simpa using vector_reverse_get_last siblings)
  · dsimp
    have hcond : ¬ idxVal / 2 ^ (n + 1 - (n + 1)) % 2 = 0 := by
      simpa using h
    rw [if_neg hcond, if_neg h]
    rw [hchild0]
    exact congrArg (fun x => Sum.inr (x, current))
      (by simpa using vector_reverse_get_last siblings)

private theorem mem_recomputeRootAuxLogPrefix_iff_internalQueryPrefix
    (f : OracleFn M S C) :
    {height : ℕ} → (idxVal : ℕ) → (current : C) → (siblings : Vector C height) →
      (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) →
      entry ∈ recomputeRootAuxLogPrefix f idxVal current siblings ↔
        ∃ layer : Fin height,
          entry =
            ⟨internalQueryPrefix f idxVal current siblings layer,
              f (internalQueryPrefix f idxVal current siblings layer)⟩
  | 0, _, _, _, entry => by
      constructor
      · intro h
        cases h
      · rintro ⟨layer, _⟩
        exact Fin.elim0 layer
  | n + 1, idxVal, current, siblings, entry => by
      constructor
      · intro hmem
        unfold recomputeRootAuxLogPrefix at hmem
        by_cases h : idxVal % 2 = 0
        · simp [h] at hmem
          rcases hmem with hhead | htail
          · refine ⟨Fin.last n, ?_⟩
            rw [hhead, internalQueryPrefix_last_eq_first, if_pos h]
          · let parent := f (Sum.inr (current, siblings.head))
            rcases
              (mem_recomputeRootAuxLogPrefix_iff_internalQueryPrefix f
                (idxVal / 2) parent siblings.tail entry).mp
                (by simpa [parent] using htail) with
              ⟨layer, hlayer⟩
            let layer' : Fin (n + 1) := ⟨layer.1, Nat.lt_trans layer.2 (Nat.lt_succ_self n)⟩
            have hlast : layer'.1 ≠ n := by
              simp [layer']
              omega
            have hquery :
                internalQueryPrefix f idxVal current siblings layer' =
                  internalQueryPrefix f (idxVal / 2) parent siblings.tail layer := by
              simpa [parent, layer', h] using
                internalQueryPrefix_succ_of_lt f idxVal current siblings layer' hlast
            refine ⟨layer', ?_⟩
            rw [← hquery] at hlayer
            exact hlayer
        · simp [h] at hmem
          rcases hmem with hhead | htail
          · refine ⟨Fin.last n, ?_⟩
            rw [hhead, internalQueryPrefix_last_eq_first, if_neg h]
          · let parent := f (Sum.inr (siblings.head, current))
            rcases
              (mem_recomputeRootAuxLogPrefix_iff_internalQueryPrefix f
                (idxVal / 2) parent siblings.tail entry).mp
                (by simpa [parent] using htail) with
              ⟨layer, hlayer⟩
            let layer' : Fin (n + 1) := ⟨layer.1, Nat.lt_trans layer.2 (Nat.lt_succ_self n)⟩
            have hlast : layer'.1 ≠ n := by
              simp [layer']
              omega
            have hquery :
                internalQueryPrefix f idxVal current siblings layer' =
                  internalQueryPrefix f (idxVal / 2) parent siblings.tail layer := by
              simpa [parent, layer', h] using
                internalQueryPrefix_succ_of_lt f idxVal current siblings layer' hlast
            refine ⟨layer', ?_⟩
            rw [← hquery] at hlayer
            exact hlayer
      · rintro ⟨layer, rfl⟩
        exact internalQueryPrefix_mem_recomputeRootAuxLogPrefix
          (M := M) (S := S) (C := C) f idxVal current siblings layer

private theorem mem_logEval_recomputeRootAux_iff_internalQueryPrefix
    (f : OracleFn M S C) {height : ℕ} (idx : Index height)
    (current : C) (siblings : Vector C height)
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    entry ∈
        (logEval f
          (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)).2 ↔
      ∃ layer : Fin height,
        entry =
          ⟨internalQueryPrefix f idx.1 current siblings layer,
            f (internalQueryPrefix f idx.1 current siblings layer)⟩ := by
  have hidx :
      (⟨idx.1 % 2 ^ height,
        Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩ : Index height) = idx := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt idx.2
  have hlog := logEval_recomputeRootAux_prefix (M := M) (S := S) (C := C)
    f idx.1 current siblings
  have hlogIdx :
      logEval f
          (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
        (pathLabelPrefix f idx.1 current siblings,
          recomputeRootAuxLogPrefix f idx.1 current siblings) := by
    conv_lhs =>
      rw [← hidx]
    exact hlog
  rw [hlogIdx]
  exact mem_recomputeRootAuxLogPrefix_iff_internalQueryPrefix
    f idx.1 current siblings entry

private theorem internalQueryPrefix_mem_logEval_recomputeRootAux (f : OracleFn M S C)
    {height : ℕ} (idx : Index height) (current : C) (siblings : Vector C height)
    (layer : Fin height) :
    ⟨internalQueryPrefix f idx.1 current siblings layer,
      f (internalQueryPrefix f idx.1 current siblings layer)⟩ ∈
      (logEval f
        (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings)).2 := by
  have hidx :
      (⟨idx.1 % 2 ^ height,
        Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) _)⟩ : Index height) = idx := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt idx.2
  have hlog := logEval_recomputeRootAux_prefix (M := M) (S := S) (C := C)
    f idx.1 current siblings
  have hmem := internalQueryPrefix_mem_recomputeRootAuxLogPrefix
    (M := M) (S := S) (C := C) f idx.1 current siblings layer
  have hlogIdx :
      logEval f
          (recomputeRootAux (M := M) (S := S) (C := C) idx current siblings) =
        (pathLabelPrefix f idx.1 current siblings,
          recomputeRootAuxLogPrefix f idx.1 current siblings) := by
    conv_lhs =>
      rw [← hidx]
    exact hlog
  rw [hlogIdx]
  exact hmem

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

theorem checkInternalQuery_mem_logEval_checkSingle [DecidableEq C] (f : OracleFn M S C)
    {depth : ℕ} (commitment : C) (idx : Index depth) (message : M)
    (authPath : AuthPath S C depth) (layer : Fin depth) :
    ⟨checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer,
      f (checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer)⟩ ∈
        (logEval f
          (checkSingle (M := M) (S := S) (C := C) commitment idx message authPath)).2 := by
  have hmem :=
    internalQueryPrefix_mem_logEval_recomputeRootAux (M := M) (S := S) (C := C)
      f idx
      (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
      authPath.siblings layer
  have hmem' :
      ⟨checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer,
        f (checkInternalQuery (M := M) (S := S) (C := C) f idx message authPath layer)⟩ ∈
        (logEval f
          (recomputeRootAux (M := M) (S := S) (C := C) idx
            (f (checkLeafQuery (M := M) (S := S) (C := C) message authPath))
            authPath.siblings)).2 := by
    rw [checkInternalQuery_eq_internalQueryPrefix]
    exact hmem
  simp [logEval_checkSingle, logEval_recomputeRootSingle, hmem']

theorem mem_logEval_checkSingle_iff_leaf_or_internal [DecidableEq C]
    (f : OracleFn M S C) {depth : ℕ} (commitment : C) (idx : Index depth)
    (message : M) (authPath : AuthPath S C depth)
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    entry ∈
        (logEval f
          (checkSingle (M := M) (S := S) (C := C)
            commitment idx message authPath)).2 ↔
      entry =
          ⟨checkLeafQuery (M := M) (S := S) (C := C) message authPath,
            f (checkLeafQuery (M := M) (S := S) (C := C) message authPath)⟩ ∨
        ∃ layer : Fin depth,
          entry =
            ⟨checkInternalQuery (M := M) (S := S) (C := C)
                f idx message authPath layer,
              f (checkInternalQuery (M := M) (S := S) (C := C)
                f idx message authPath layer)⟩ := by
  let leafQuery := checkLeafQuery (M := M) (S := S) (C := C) message authPath
  let leafEntry :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t :=
    ⟨leafQuery, f leafQuery⟩
  have hlog :
      (logEval f
        (checkSingle (M := M) (S := S) (C := C)
          commitment idx message authPath)).2 =
        leafEntry ::
          (logEval f
            (recomputeRootAux (M := M) (S := S) (C := C)
              idx (f leafQuery) authPath.siblings)).2 := by
    rw [logEval_checkSingle, logEval_recomputeRootSingle]
    rfl
  rw [hlog]
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with hleaf | htail
    · exact .inl hleaf
    · right
      rcases
        (mem_logEval_recomputeRootAux_iff_internalQueryPrefix
          (M := M) (S := S) (C := C) f idx (f leafQuery) authPath.siblings entry).mp
          htail with
        ⟨layer, hlayer⟩
      refine ⟨layer, ?_⟩
      have hquery :
          checkInternalQuery (M := M) (S := S) (C := C)
              f idx message authPath layer =
            internalQueryPrefix f idx.1 (f leafQuery) authPath.siblings layer := by
        simpa [leafQuery] using
          checkInternalQuery_eq_internalQueryPrefix
            (M := M) (S := S) (C := C) f idx message authPath layer
      rw [hquery]
      exact hlayer
  · rintro (hleaf | hinternal)
    · exact List.mem_cons.mpr (.inl (by simpa [leafEntry] using hleaf))
    · rcases hinternal with ⟨layer, hlayer⟩
      apply List.mem_cons.mpr
      right
      have htail :
          entry ∈
            (logEval f
              (recomputeRootAux (M := M) (S := S) (C := C)
                idx (f leafQuery) authPath.siblings)).2 := by
        apply
          (mem_logEval_recomputeRootAux_iff_internalQueryPrefix
            (M := M) (S := S) (C := C) f idx (f leafQuery)
              authPath.siblings entry).mpr
        refine ⟨layer, ?_⟩
        have hquery :
            checkInternalQuery (M := M) (S := S) (C := C)
                f idx message authPath layer =
              internalQueryPrefix f idx.1 (f leafQuery) authPath.siblings layer := by
          simpa [leafQuery] using
            checkInternalQuery_eq_internalQueryPrefix
              (M := M) (S := S) (C := C) f idx message authPath layer
        rw [hquery] at hlayer
        exact hlayer
      exact htail

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
