/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Extractability

/-!
# Merkle Commitment Scheme — Multi-Extractability

This module packages the family-level extractability event for Merkle
commitments. The deterministic reduction is pointwise: a successful
multi-transcript extraction failure gives one single-transcript bad event.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

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

/-- The textbook multi-extractability counting term obtained by summing the
single-transcript bound over `n` selected commitments. -/
noncomputable def multiExtractabilityErrorTerm (C : Type) [Fintype C]
    (depth t₁ t₂ n : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * extractabilityErrorTerm C depth t₁ t₂

/-- Stateful multi-extractability adversary with one shared commit phase and one
selected opening phase. -/
structure MultiExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth n t : ℕ) where
  commit : OracleComp (Oracle M S C) ((Fin n → C) × AUX)
  open_ : AUX → OracleComp (Oracle M S C) (Σ _ : Fin n, OpeningData M S C depth)
  t₁ : ℕ
  t₂ : ℕ
  totalBound : t₁ + t₂ ≤ t
  commitBound : IsTotalQueryBound commit t₁
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

/-- ROM win event for the stateful multi witness game, delegated to the
single-commitment witness predicate on the selected coordinate. -/
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
single selected verifier path. -/
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

/-- A family-level extractability win implies a family-level bad event. -/
theorem multi_extractabilityWin_implies_badEvent {depth n : ℕ}
    [DecidableEq C] [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C)
    (xs : Fin n → ExtractTranscript M S C AUX depth) :
    MultiExtractabilityWin (M := M) (S := S) (C := C) f xs →
      MultiExtractabilityBadEvent (M := M) (S := S) (C := C) f xs := by
  rintro ⟨k, hwin⟩
  exact ⟨k, extractabilityWin_implies_badEvent (M := M) (S := S) (C := C) f (xs k) hwin⟩

/-- Any probability bound for the family bad event immediately bounds the
multi-extractability failure event. -/
theorem multi_extractability_bound_of_badEvent_bound {depth n : ℕ}
    [DecidableEq C] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C)
      (Fin n → ExtractTranscript M S C AUX depth))
    (ε : ℝ≥0∞)
    (hbad :
      Pr[ fun xs =>
        MultiExtractabilityBadEvent (M := M) (S := S) (C := C) f xs | oa] ≤ ε) :
    Pr[ fun xs =>
      MultiExtractabilityWin (M := M) (S := S) (C := C) f xs | oa] ≤ ε :=
  le_trans
    (probEvent_mono fun xs _ hx =>
      multi_extractabilityWin_implies_badEvent (M := M) (S := S) (C := C) f xs hx)
    hbad

/-- Multi-extractability bound obtained from a family-level bad-event estimate.

This is a conditional helper; the final ROM theorem should prove the
family-level bad-event estimate for the stateful multi-commitment game. -/
theorem multi_extractability_bound_of_family_badEvent_bound {depth n : ℕ}
    [DecidableEq C] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C)
      (Fin n → ExtractTranscript M S C AUX depth))
    (t₁ t₂ : ℕ)
    (hbad :
      Pr[ fun xs =>
        MultiExtractabilityBadEvent (M := M) (S := S) (C := C) f xs | oa] ≤
        multiExtractabilityErrorTerm C depth t₁ t₂ n) :
    Pr[ fun xs =>
      MultiExtractabilityWin (M := M) (S := S) (C := C) f xs | oa] ≤
      multiExtractabilityErrorTerm C depth t₁ t₂ n :=
  multi_extractability_bound_of_badEvent_bound
    (M := M) (S := S) (C := C) f oa
    (multiExtractabilityErrorTerm C depth t₁ t₂ n) hbad

/-- Pointwise witness multi-extractability game for a selected commitment in a
family. This is the first final ROM surface: the stateful tighter game can be
introduced later without changing the single-commitment extractor. -/
noncomputable def multiExtractabilityWitnessGame
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth t n : ℕ}
    (A : Fin n → ExtractAdversary M S C AUX depth t) (k : Fin n) :
    OracleComp (Oracle M S C)
      (WitnessExtractTranscript M S C AUX depth × QueryCache (Oracle M S C)) :=
  extractabilityWitnessGame (M := M) (S := S) (C := C) (A k)

/-- Pointwise simple union-bound style multi-extractability estimate for a selected
witness coordinate. Since `k : Fin n`, the family has at least one coordinate,
so the single-commitment error is bounded by `n` times that error. -/
theorem multi_extractability_bound_pointwise {depth t n : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : Fin n → ExtractAdversary M S C AUX depth t)
    (k : Fin n)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z |
      multiExtractabilityWitnessGame (M := M) (S := S) (C := C) A k] ≤
      multiExtractabilityErrorTerm C depth (A k).t₁ (A k).t₂ n := by
  have hsingle :=
    extractability_bound (M := M) (S := S) (C := C) (A := A k) hC
  have hscale :
      extractabilityErrorTerm C depth (A k).t₁ (A k).t₂ ≤
        multiExtractabilityErrorTerm C depth (A k).t₁ (A k).t₂ n := by
    unfold multiExtractabilityErrorTerm
    calc
      extractabilityErrorTerm C depth (A k).t₁ (A k).t₂
          = (1 : ℝ≥0∞) *
              extractabilityErrorTerm C depth (A k).t₁ (A k).t₂ := by
            simp
      _ ≤ (n : ℝ≥0∞) *
              extractabilityErrorTerm C depth (A k).t₁ (A k).t₂ := by
            gcongr
            have hnpos : 1 ≤ n := by
              exact Nat.succ_le_of_lt
                (Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2)
            exact_mod_cast hnpos
  exact le_trans (by
    simpa [multiExtractabilityWitnessGame] using hsingle) hscale

/-- Final simple multi-extractability estimate for the selected-coordinate
witness game. This public theorem intentionally uses the pointwise witness game;
the tighter shared-trace stateful game can be added as a refinement. -/
theorem multi_extractability_bound {depth t n : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : Fin n → ExtractAdversary M S C AUX depth t)
    (k : Fin n)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z |
      multiExtractabilityWitnessGame (M := M) (S := S) (C := C) A k] ≤
      multiExtractabilityErrorTerm C depth (A k).t₁ (A k).t₂ n :=
  multi_extractability_bound_pointwise (M := M) (S := S) (C := C) A k hC

end MerkleTree
