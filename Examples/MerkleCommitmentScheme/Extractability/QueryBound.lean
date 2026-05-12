/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Extractability.Basic

/-!
# Merkle Commitment Scheme — Extractability Query Bounds

This file isolates the selected-witness experiment budget used by
`extractability_bound`.

Quantitative map:
* the commit phase is logged and costs `A.t₁`;
* the rest phase logs the adversary open phase and, if a mismatch witness is
  selected, one `checkSingle` verifier path;
* one selected verifier path costs `depth + 1`, so the rest budget is
  `A.t₂ + (depth + 1)`.

The probability file uses these budgets to derive
`A.t₁^2 / (2 * |C|) + (A.t₂ + depth + 1) * targets / |C|`.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-! ## Witness-game ROM decomposition -/

/-- Commit part of the selected-witness extractability game.

It runs the adversary commit phase under `loggingOracle`, returning the
commitment/auxiliary output together with the commit trace that the extractor
will later inspect. -/
noncomputable def extractabilityWitnessCommitPart
    {depth t : ℕ} (A : ExtractAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) ((C × AUX) × QueryLog (Oracle M S C)) :=
  (simulateQ loggingOracle A.commit).run

/-- Rest part of the selected-witness extractability game.

It logs the adversary open phase, computes the deterministic mismatch witness
from the extracted output, and logs exactly one `checkSingle` verifier path if
such a witness exists. -/
noncomputable def extractabilityWitnessRest {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (commitment : C) (aux : AUX) (commitTrace : QueryLog (Oracle M S C)) :
    OracleComp (Oracle M S C) (WitnessExtractTranscript M S C AUX depth) := do
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ aux)).run
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  match selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      pure { base := base, witness? := none, singleCheck? := none }
  | some i =>
      let single ←
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))).run
      pure { base := base, witness? := some i, singleCheck? := some single }

/-- Operational normal form separating commit and rest phases. -/
theorem extractabilityWitnessInner_eq_bind {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    extractabilityWitnessInner (M := M) (S := S) (C := C) A =
      extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun x =>
        extractabilityWitnessRest (M := M) (S := S) (C := C) A x.1.1 x.1.2 x.2 := by
  rfl

/-- The logged commit part uses exactly the adversary commit budget `A.t₁`. -/
theorem extractabilityWitnessCommitPart_totalBound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t) :
    IsTotalQueryBound
      (extractabilityWitnessCommitPart (M := M) (S := S) (C := C) A) A.t₁ := by
  simpa [extractabilityWitnessCommitPart] using
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff A.commit A.t₁).mpr A.commitBound

/-- The selected-witness rest phase uses at most
`extractabilityPostCommitQueryCount depth A.t₂` queries.

The `A.t₂` part is the adversary open phase. The `depth + 1` part is present
only if a mismatch witness is selected and corresponds to one leaf query plus
`depth` internal-node queries in `checkSingle`. -/
theorem extractabilityWitnessRest_totalBound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (A : ExtractAdversary M S C AUX depth t)
    (commitment : C) (aux : AUX) (commitTrace : QueryLog (Oracle M S C)) :
    IsTotalQueryBound
      (extractabilityWitnessRest (M := M) (S := S) (C := C)
        A commitment aux commitTrace)
      (extractabilityPostCommitQueryCount depth A.t₂) := by
  unfold extractabilityWitnessRest
  have hopen :
      IsTotalQueryBound ((simulateQ loggingOracle (A.open_ aux)).run) A.t₂ :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff (A.open_ aux) A.t₂).mpr
      (A.openBound aux)
  refine isTotalQueryBound_bind (n₁ := A.t₂)
    (n₂ := extractabilityVerifierPathQueryCount depth) hopen ?_
  intro ⟨opening, openTrace⟩
  let base : ExtractTranscript M S C AUX depth :=
    { commitment := commitment
      aux := aux
      commitTrace := commitTrace
      opening := opening
      openTrace := openTrace }
  dsimp only
  cases hw : selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      trivial
  | some i =>
      have hsingle :
          IsTotalQueryBound
            ((simulateQ loggingOracle
              (checkSingle (M := M) (S := S) (C := C)
                commitment i.1 (opening.message i) (opening.proof i))).run)
            (depth + 1) :=
        (isTotalQueryBound_run_simulateQ_loggingOracle_iff
          (checkSingle (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))
          (depth + 1)).mpr
          (checkSingle_totalQueryBound (M := M) (S := S) (C := C)
            commitment i.1 (opening.message i) (opening.proof i))
      have hpure :
          ∀ single : Bool × QueryLog (Oracle M S C),
            IsTotalQueryBound
              ((pure
                ({ base := base
                   witness? := some i
                   singleCheck? := some single } :
                  WitnessExtractTranscript M S C AUX depth)) :
                OracleComp (Oracle M S C)
                  (WitnessExtractTranscript M S C AUX depth))
              0 := by
        intro single
        trivial
      exact
        (isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 0)
          hsingle hpure).mono (by
            simp [extractabilityVerifierPathQueryCount])

end MerkleTree
