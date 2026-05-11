/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support.QueryBound
import Examples.CommitmentScheme.Support.Collision
import Examples.CommitmentScheme.Support.Probability

/-!
# Merkle Commitment Scheme — ROM Support

Random-oracle helper lemmas specialized to the Merkle oracle shape.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C : Type}

/-- All Merkle oracle queries return values in `C`.

Lean event/game: this turns generic ROM bounds over `spec.Range default` into
Merkle bounds over `|C|`. -/
theorem merkleOracleRange_card_eq [Fintype C]
    (q : (Oracle M S C).Domain) :
    Fintype.card ((Oracle M S C).Range q) = Fintype.card C := by
  cases q <;> rfl

theorem merkleOracleRange_card_le [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (q : (Oracle M S C).Domain) :
    Fintype.card ((Oracle M S C).Range default) ≤
      Fintype.card ((Oracle M S C).Range q) := by
  rw [merkleOracleRange_card_eq (M := M) (S := S) (C := C) default,
    merkleOracleRange_card_eq (M := M) (S := S) (C := C) q]

theorem traceEntryAnswer_heq_of_entry
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    HEq entry.2 (traceEntryAnswer (M := M) (S := S) (C := C) entry) := by
  cases entry with
  | mk domain answer =>
      cases domain <;> rfl

/-- Finite set of Merkle oracle answers appearing in a query log.

Lean event/game: extractability fresh-hit bounds use this as the target set of
known labels that a later fresh query must hit. -/
noncomputable def merkleLogAnswerTargets [DecidableEq C] [Inhabited M] [Inhabited S]
    [Inhabited C]
    (log : QueryLog (Oracle M S C)) : Finset C :=
  (log.map (traceEntryAnswer (M := M) (S := S) (C := C))).toFinset

theorem merkleLogAnswerTargets_card_le [DecidableEq C] [Inhabited M] [Inhabited S]
    [Inhabited C]
    (log : QueryLog (Oracle M S C)) :
    (merkleLogAnswerTargets (M := M) (S := S) (C := C) log).card ≤ log.length := by
  classical
  unfold merkleLogAnswerTargets
  calc
    (List.map (traceEntryAnswer (M := M) (S := S) (C := C)) log).toFinset.card
        ≤ (List.map (traceEntryAnswer (M := M) (S := S) (C := C)) log).length :=
          List.toFinset_card_le _
    _ = log.length := by simp

theorem traceEntryAnswer_mem_merkleLogAnswerTargets [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {log : QueryLog (Oracle M S C)}
    {entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t}
    (hentry : entry ∈ log) :
    traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
      merkleLogAnswerTargets (M := M) (S := S) (C := C) log := by
  classical
  unfold merkleLogAnswerTargets
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨entry, hentry, rfl⟩)

/-- Merkle-specialized fresh-hit bound for a finite target set.

Textbook statement: a post-commit computation with at most `n` queries hits one
of `targets` with probability at most `n * targets.card / |C|`.

Lean event/game: used by Merkle extractability after the commit phase, where
`targets` is the set of known labels in the extracted partial tree. -/
theorem probEvent_merkle_cache_has_value_mem_finset_le {α : Type}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (oa : OracleComp (Oracle M S C) α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (targets : Finset C) (cache₀ : QueryCache (Oracle M S C))
    (hno : ¬ CacheHasCollision cache₀) :
    Pr[fun z =>
      ∃ target ∈ targets, ∃ t₀ : (Oracle M S C).Domain,
        ∃ v : (Oracle M S C).Range t₀,
          z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target |
      (simulateQ cachingOracle oa).run cache₀] ≤
      (((n * targets.card : ℕ) : ℝ≥0∞) *
        (Fintype.card C : ℝ≥0∞)⁻¹) := by
  classical
  calc
    Pr[fun z =>
      ∃ target ∈ targets, ∃ t₀ : (Oracle M S C).Domain,
        ∃ v : (Oracle M S C).Range t₀,
          z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target |
      (simulateQ cachingOracle oa).run cache₀]
        ≤ (targets.card : ℝ≥0∞) *
            ((n : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) := by
          simpa [merkleOracleRange_card_eq (M := M) (S := S) (C := C) default] using
            (OracleComp.probEvent_cache_has_value_mem_finset_le_of_noCollision
              (spec := Oracle M S C) (oa := oa) (n := n) hbound
              (merkleOracleRange_card_le (M := M) (S := S) (C := C))
              targets cache₀ hno)
    _ = (((n * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
          simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

end MerkleTree
