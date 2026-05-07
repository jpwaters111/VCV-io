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

/-- Named multi-extractability bound once the union-bound estimate for the
family-level bad event has been established. -/
theorem multi_extractability_bound {depth n : ℕ}
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

end MerkleTree
