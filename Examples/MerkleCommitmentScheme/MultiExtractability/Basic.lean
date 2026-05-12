/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Extractability.Basic

/-!
# Merkle Commitment Scheme — Multi-Extractability Basic Definitions
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- Local normalization helper for projected witness transcripts.

Projected single-commitment games sometimes append an empty open trace to match
the stateful transcript shape; this keeps those projections definitionally easy
to simplify. -/
private theorem queryLog_append_nil (log : QueryLog (Oracle M S C)) :
    log ++ ([] : QueryLog (Oracle M S C)) = log := by
  exact List.append_nil log

/-- Multi-extractability fails when at least one selected transcript is a
single-commitment extractability failure. -/
def MultiExtractabilityWin [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n : ℕ} (f : OracleFn M S C)
    (xs : Fin n → ExtractTranscript M S C AUX depth) : Prop :=
  ∃ k : Fin n, ExtractabilityWin (M := M) (S := S) (C := C) f (xs k)

/-- The family-level bad event is the union of the single-transcript bad events. -/
def MultiExtractabilityBadEvent [DecidableEq C]
    {depth n : ℕ} (f : OracleFn M S C)
    (xs : Fin n → ExtractTranscript M S C AUX depth) : Prop :=
  ∃ k : Fin n, BadEvent (M := M) (S := S) (C := C) f (xs k)

/-- Simple stateful multi-extractability union-bound error term.

This is `n` times the selected-witness single-commitment error. It is the public
stateful theorem proved in this module family, not the tighter textbook
multi-extractability expression with the equal-commitment/different-tree branch.

Bound expression: `n * extractabilityErrorTerm C depth t₁ t₂`.
Textbook notation instead gives the tighter macro
`MTMultiExtractabilityExpression(λ, q, L, d, n) =
  3/2 * (q - 1) * q / 2^λ
  + (d + 1) * 2L / 2^λ
  + (n - 1) * q / 2^λ`, where `L = 2^depth`.
-/
noncomputable def multiExtractabilityErrorTerm (C : Type) [Fintype C]
    (depth t₁ t₂ n : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * extractabilityErrorTerm C depth t₁ t₂

/-- Stateful multi-extractability adversary with one shared commit phase and one
selected opening phase. -/
structure MultiExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth n t : ℕ) where
  /-- Shared commit phase: outputs all `n` commitments and auxiliary state. -/
  commit : OracleComp (Oracle M S C) ((Fin n → C) × AUX)
  /-- Open phase: selects one commitment coordinate and an opening for it. -/
  open_ : AUX → OracleComp (Oracle M S C) (Σ _ : Fin n, OpeningData M S C depth)
  /-- Commit-phase query budget. -/
  t₁ : ℕ
  /-- Open-phase query budget. The selected verifier path is charged
  separately through the single-commitment extractability theorem. -/
  t₂ : ℕ
  /-- Total adversarial budget, excluding the selected verifier path. -/
  totalBound : t₁ + t₂ ≤ t
  /-- Query-bound certificate for `commit`. -/
  commitBound : IsTotalQueryBound commit t₁
  /-- Query-bound certificate for each `open_ aux`. -/
  openBound : ∀ aux, IsTotalQueryBound (open_ aux) t₂

/-- Transcript for the stateful multi-commitment witness game. It stores the
shared commit trace, the selected commitment/opening, and the selected
single-check verifier trace. -/
structure MultiExtractabilityStatefulWitnessTranscript
    (M : Type) (S : Type) (C : Type) (AUX : Type) (depth n : ℕ) where
  commitments : Fin n → C
  aux : AUX
  commitTrace : QueryLog (Oracle M S C)
  opening : Σ _ : Fin n, OpeningData M S C depth
  openTrace : QueryLog (Oracle M S C)
  witness? : Option {i // i ∈ opening.2.I}
  singleCheck? : Option (Bool × QueryLog (Oracle M S C))

/-- View a stateful selected multi transcript as the corresponding
single-commitment witness transcript for its selected coordinate. -/
def MultiExtractabilityStatefulWitnessTranscript.toWitnessTranscript
    {depth n : ℕ}
    (x : MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n) :
    WitnessExtractTranscript M S C AUX depth where
  base :=
    { commitment := x.commitments x.opening.1
      aux := x.aux
      commitTrace := x.commitTrace
      opening := x.opening.2
      openTrace := x.openTrace }
  witness? := x.witness?
  singleCheck? := x.singleCheck?

/-- ROM win event for the stateful multi witness game.

Lean event/game: delegate the selected coordinate to the single-commitment
witness predicate `WitnessExtractabilityWinROM`.

Scope note: this event tracks one selected commitment coordinate, not every
coordinate simultaneously. -/
noncomputable def MultiExtractabilityStatefulWitnessWinROM
    [DecidableEq S] [DecidableEq C]
    {depth n : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (z :
      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) : Prop :=
  WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
    (z.1.toWitnessTranscript, z.2)

/-- Inner stateful multi-extractability witness experiment before running under
the shared cached ROM. It logs one shared commit phase, one selected open phase,
and only the selected single-check verifier path. -/
noncomputable def multiExtractabilityStatefulWitnessInner
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t) :
    OracleComp (Oracle M S C)
      (MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n) := do
  let ((commitments, aux), commitTrace) ← (simulateQ loggingOracle A.commit).run
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitments opening.1
      aux := aux
      commitTrace := commitTrace
      opening := opening.2
      openTrace := openTrace }
  match selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      pure
        { commitments := commitments
          aux := aux
          commitTrace := commitTrace
          opening := opening
          openTrace := openTrace
          witness? := none
          singleCheck? := none }
  | some i =>
      let single ←
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            (commitments opening.1) i.1 (opening.2.message i) (opening.2.proof i))).run
      pure
        { commitments := commitments
          aux := aux
          commitTrace := commitTrace
          opening := opening
          openTrace := openTrace
          witness? := some i
          singleCheck? := some single }

/-- Stateful multi-extractability witness game with a shared commit trace and a
single selected verifier path.

Lean event/game: the commit phase outputs all commitments and one shared trace;
the open phase selects one coordinate; the verifier logs only the selected
mismatching `checkSingle` path. -/
noncomputable def multiExtractabilityStatefulWitnessGame
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t) :
    OracleComp (Oracle M S C)
      (MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle
    (multiExtractabilityStatefulWitnessInner (M := M) (S := S) (C := C) A)).run ∅

/-- Textbook-facing name for the stateful selected-witness ROM win event.

The longer `MultiExtractabilityStatefulWitnessWinROM` name remains available
for proofs that need to emphasize the exact experiment shape.

Scope note: despite the textbook-facing name, this is the simple selected
coordinate event and does not include the equal-commitment/different-tree
branch. -/
noncomputable def MultiExtractabilityWinROM
    [DecidableEq S] [DecidableEq C]
    {depth n : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (z :
      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) : Prop :=
  MultiExtractabilityStatefulWitnessWinROM (M := M) (S := S) (C := C) z

/-- Textbook-facing name for the stateful selected-witness multi-extractability
game.

Lean event/game: `multiExtractabilityStatefulWitnessGame` with a shorter public
name used by the final union-bound theorem. -/
noncomputable def multiExtractabilityGame
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t) :
    OracleComp (Oracle M S C)
      (MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) :=
  multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A

/-- Empty opening data used by projected single-commitment adversaries when the
shared multi opening selected a different coordinate. -/
def emptyOpeningData {depth : ℕ} : OpeningData M S C depth where
  I := ∅
  message := fun i => False.elim (Finset.notMem_empty i.1 i.2)
  proof := fun i => False.elim (Finset.notMem_empty i.1 i.2)

/-- The selected-coordinate branch of the stateful game. -/
def StatefulSelectedWin
    [DecidableEq S] [DecidableEq C]
    {depth n : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (k : Fin n)
    (z :
      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) : Prop :=
  z.1.opening.1 = k ∧
    MultiExtractabilityStatefulWitnessWinROM (M := M) (S := S) (C := C) z

/-- Textbook-facing selected-coordinate event for the stateful witness game.

Lean event/game: branch `k` of `multiExtractabilityGame`; summing these events
over `Fin n` gives the public multi-extractability union bound. -/
noncomputable def MultiExtractabilitySelectedWinROM
    [DecidableEq S] [DecidableEq C]
    {depth n : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    (k : Fin n)
    (z :
      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) : Prop :=
  StatefulSelectedWin (M := M) (S := S) (C := C) (AUX := AUX) k z

end MerkleTree
