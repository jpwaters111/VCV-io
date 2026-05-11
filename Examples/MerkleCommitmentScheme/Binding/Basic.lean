/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Collision
import Examples.MerkleCommitmentScheme.Extractability.Basic
import Examples.CommitmentScheme.Support.Collision
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Merkle Commitment Scheme — Binding Basic Definitions
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

structure BindingOutput (M : Type) (S : Type) (C : Type) (depth : ℕ) where
  commitment : C
  I₀ : IndexSet depth
  I₁ : IndexSet depth
  message₀ : Subvector M I₀
  message₁ : Subvector M I₁
  proof₀ : Proof S C I₀
  proof₁ : Proof S C I₁

/-- A Merkle binding adversary with a total query bound. -/
structure BindingAdversary (M : Type) (S : Type) (C : Type) (depth t : ℕ) where
  /-- The adversary outputs one commitment and two claimed batch openings. -/
  run : OracleComp (Oracle M S C) (BindingOutput M S C depth)
  /-- Total random-oracle query budget for `run`. -/
  queryBound : IsTotalQueryBound run t

/-- Fixed-oracle binding success for a binding output. -/
def BindingWin [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (out : BindingOutput M S C depth) : Prop :=
  SharedValueMismatch (M := M) out.message₀ out.message₁ ∧
    eval f
      (check (M := M) (S := S) (C := C)
        out.commitment out.I₀ out.message₀ out.proof₀) = true ∧
    eval f
      (check (M := M) (S := S) (C := C)
        out.commitment out.I₁ out.message₁ out.proof₁) = true

/-- The fixed-oracle cross-log collision event induced by the two verifier runs. -/
def BindingCollisionEvent [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (out : BindingOutput M S C depth) : Prop :=
  CrossLogCollision
    (logEval f
      (check (M := M) (S := S) (C := C)
        out.commitment out.I₀ out.message₀ out.proof₀)).2
    (logEval f
      (check (M := M) (S := S) (C := C)
        out.commitment out.I₁ out.message₁ out.proof₁)).2

theorem crossLogCollision_iff_oracleComp_logCrossCollision
    {log₀ log₁ : QueryLog (Oracle M S C)} :
    CrossLogCollision log₀ log₁ ↔ OracleComp.LogCrossCollision log₀ log₁ := by
  rfl

/-- The Boolean binding experiment run against a shared lazy random oracle. -/
noncomputable def bindingInner [DecidableEq M] [DecidableEq C] {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C) Bool := by
  classical
  exact do
    let out ← A.run
    let ok₀ ←
      check (M := M) (S := S) (C := C)
        out.commitment out.I₀ out.message₀ out.proof₀
    let ok₁ ←
      check (M := M) (S := S) (C := C)
        out.commitment out.I₁ out.message₁ out.proof₁
    pure (ok₀ && ok₁ && decide (SharedValueMismatch (M := M) out.message₀ out.message₁))

/-- The Merkle binding game in the random-oracle model. -/
noncomputable def bindingGame [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ} (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C) (Bool × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle (bindingInner (M := M) (S := S) (C := C) A)).run ∅

/-- A concrete shared-index mismatch selected from a binding adversary output. -/
structure BindingMismatchWitness {depth : ℕ}
    (out : BindingOutput M S C depth) where
  idx : Index depth
  leftMem : idx ∈ out.I₀
  rightMem : idx ∈ out.I₁
  mismatch :
    out.message₀ ⟨idx, leftMem⟩ ≠ out.message₁ ⟨idx, rightMem⟩

/-- Noncomputably select a mismatch witness when one exists. The witness game
checks only this selected index, which is the tight `depth + 1` verifier view. -/
noncomputable def selectBindingMismatchWitness? {depth : ℕ}
    (out : BindingOutput M S C depth) :
    Option (BindingMismatchWitness (M := M) (S := S) (C := C) out) := by
  classical
  by_cases h : SharedValueMismatch (M := M) out.message₀ out.message₁
  · let idx := Classical.choose h
    let hidx := Classical.choose_spec h
    let hleft := Classical.choose hidx
    let hleftSpec := Classical.choose_spec hidx
    let hright := Classical.choose hleftSpec
    let hmismatch := Classical.choose_spec hleftSpec
    exact some
      { idx := idx
        leftMem := hleft
        rightMem := hright
        mismatch := hmismatch }
  · exact none

/-- Witness-index binding transcript. The two optional single-check logs are
present exactly when the selector found a shared-value mismatch. -/
structure BindingWitnessTranscript (M : Type) (S : Type) (C : Type) (depth : ℕ) where
  out : BindingOutput M S C depth
  witness? : Option (BindingMismatchWitness (M := M) (S := S) (C := C) out)
  single₀? : Option (Bool × QueryLog (Oracle M S C))
  single₁? : Option (Bool × QueryLog (Oracle M S C))

/-- Binding witness success, stated over the concrete logged checks produced by
the ROM game.

Lean event/game: the mismatch selector found one shared index and both
selected `checkSingle` verifier runs accepted. -/
def BindingWitnessWinROM {depth : ℕ}
    (z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)) : Prop :=
  ∃ (w : BindingMismatchWitness (M := M) (S := S) (C := C) z.1.out)
    (single₀ single₁ : Bool × QueryLog (Oracle M S C)),
      z.1.witness? = some w ∧
      z.1.single₀? = some single₀ ∧
      z.1.single₁? = some single₁ ∧
      single₀.1 = true ∧ single₁.1 = true

/-- The ROM bad event used by the final witness binding theorem. -/
def BindingWitnessBadEventROM {depth : ℕ}
    (z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)) : Prop :=
  CacheHasCollision z.2

def BindingWitnessRestLogCrossEvent {depth : ℕ}
    (z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)) : Prop :=
  ∃ (single₀ single₁ : Bool × QueryLog (Oracle M S C)),
    z.1.single₀? = some single₀ ∧
    z.1.single₁? = some single₁ ∧
    OracleComp.LogCrossCollision single₀.2 single₁.2

/-- Witness-index binding experiment: run the adversary, select one conflicting
shared index, and log only the two single-check verifier runs for that index. -/
noncomputable def bindingWitnessInner [DecidableEq C] {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C) (BindingWitnessTranscript M S C depth) := by
  classical
  exact do
    let out ← A.run
    match selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
    | none =>
        pure
          { out := out
            witness? := none
            single₀? := none
            single₁? := none }
    | some w =>
        let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
        let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
        let single₀ ←
          (simulateQ loggingOracle
            (checkSingle (M := M) (S := S) (C := C)
              out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀))).run
        let single₁ ←
          (simulateQ loggingOracle
            (checkSingle (M := M) (S := S) (C := C)
              out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁))).run
        pure
          { out := out
            witness? := some w
            single₀? := some single₀
            single₁? := some single₁ }

/-- The witness-index Merkle binding game in the random-oracle model. -/
noncomputable def bindingWitnessGame [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C)
      (BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle (bindingWitnessInner (M := M) (S := S) (C := C) A)).run ∅

/-- Origin-aware transcript for the textbook witness binding game. It records
the adversary/commit cache separately from the verifier-rest cache growth. -/
structure BindingTextbookWitnessTranscript
    (M : Type) (S : Type) (C : Type) (depth : ℕ) where
  out : BindingOutput M S C depth
  commitCache : QueryCache (Oracle M S C)
  witness? : Option (BindingMismatchWitness (M := M) (S := S) (C := C) out)
  single₀? : Option (Bool × QueryLog (Oracle M S C))
  single₁? : Option (Bool × QueryLog (Oracle M S C))

/-- Forget the recorded origin cache and recover the ordinary witness
transcript. -/
def BindingTextbookWitnessTranscript.toWitnessTranscript {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth) :
    BindingWitnessTranscript M S C depth where
  out := z.out
  witness? := z.witness?
  single₀? := z.single₀?
  single₁? := z.single₁?

private def BindingTextbookNoFirstLogCollision {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :
    Prop :=
  ∀ single₀ : Bool × QueryLog (Oracle M S C),
    z.1.single₀? = some single₀ →
      ¬ OracleComp.LogHasCollision single₀.2

/-- Textbook witness success for the origin-aware binding game.

Textbook statement: the selected verifier paths are analyzed separately from
the adversary cache.

Lean event/game: `BindingWitnessWinROM`, plus the side conditions that no
verifier-rest query freshly hits an initial-cache value and that the first
selected verifier log has no internal collision.

Scope note: these side conditions are what make the split
`t * (t - 1) / (2 * |C|) + (depth + 1)^2 / |C|` sound for this game. -/
def BindingTextbookWinROM {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :
    Prop :=
  BindingWitnessWinROM (M := M) (S := S) (C := C)
    (z.1.toWitnessTranscript, z.2) ∧
    ¬ OracleComp.FreshHitInitialCache z.1.commitCache z.2 ∧
    BindingTextbookNoFirstLogCollision (M := M) (S := S) (C := C) z

/-- Rest-created cross-collision event for the origin-aware binding proof.

Lean event/game: the two selected verifier logs contain a cross-collision where
both colliding entries are fresh relative to the adversary/commit cache.

Scope note: this is the event charged to the `(depth + 1)^2 / |C|` verifier
term in `bindingErrorTerm`. -/
def BindingTextbookRestCreatedEvent {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :
    Prop :=
  ∃ (single₀ single₁ : Bool × QueryLog (Oracle M S C)),
    z.1.single₀? = some single₀ ∧
    z.1.single₁? = some single₁ ∧
    OracleComp.RestCreatedLogCrossCollision z.1.commitCache single₀.2 single₁.2 ∧
    ¬ OracleComp.LogHasCollision single₀.2 ∧
    ¬ OracleComp.FreshHitInitialCache z.1.commitCache z.2

noncomputable def bindingWitnessCommitPart {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C) (BindingOutput M S C depth) :=
  A.run

noncomputable def bindingWitnessRest [DecidableEq C] {depth : ℕ}
    (out : BindingOutput M S C depth) :
    OracleComp (Oracle M S C) (BindingWitnessTranscript M S C depth) := by
  classical
  exact
    match selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
    | none =>
        pure
          { out := out
            witness? := none
            single₀? := none
            single₁? := none }
    | some w =>
        let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
        let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀))).run >>= fun single₀ =>
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁))).run >>= fun single₁ =>
        pure
          { out := out
            witness? := some w
            single₀? := some single₀
            single₁? := some single₁ }

/-- Textbook rest phase: run the selected two single-check traces from the
stored commit cache and keep that commit cache in the transcript. -/
noncomputable def bindingTextbookWitnessRest [DecidableEq C] {depth : ℕ}
    (commitCache : QueryCache (Oracle M S C))
    (out : BindingOutput M S C depth) :
    OracleComp (Oracle M S C)
      (BindingTextbookWitnessTranscript M S C depth) := do
  let base ← bindingWitnessRest (M := M) (S := S) (C := C) out
  pure
    { out := base.out
      commitCache := commitCache
      witness? := base.witness?
      single₀? := base.single₀?
      single₁? := base.single₁? }

/-- Origin-aware textbook witness binding game: run the adversary under the
cached ROM, store the resulting cache, then run only the selected verifier
single checks from that cache. -/
noncomputable def bindingTextbookWitnessGame
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C)
      (BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :=
  (simulateQ cachingOracle
    (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅ >>= fun p =>
    (simulateQ cachingOracle
      (bindingTextbookWitnessRest (M := M) (S := S) (C := C) p.2 p.1)).run p.2

/-- Conservative whole-cache binding error term for the ordinary witness game.

This is the bound used by the unconditional `binding_bound`: all adversary and
selected-verifier queries are charged to one birthday term. It is easier to use
than the textbook split, but looser:

`(t + 2 * (depth + 1))^2 / (2 * |C|)`.

Lean event/game: `BindingWitnessWinROM` in `bindingWitnessGame`.

Scope note: this is not the compact textbook split; use `bindingErrorTerm` for
the origin-aware theorem.
-/
noncomputable def bindingWitnessErrorTerm (C : Type) [Fintype C]
    (depth t : ℕ) : ℝ≥0∞ :=
  ((t + 2 * (depth + 1)) ^ 2 : ℕ) / (2 * Fintype.card C)

/-- Textbook split binding error term for the origin-aware witness game.

This is the formula used in the proof of `lemma:mt-binding`: birthday collision
in the adversary cache plus a cross-collision between the two selected
authentication paths:

`t * (t - 1) / (2 * |C|) + (depth + 1)^2 / |C|`.

Lean event/game: `BindingTextbookWinROM` in `bindingTextbookWitnessGame`.

Scope note: the theorem with this term is `binding_bound_conditioned`; the
ordinary witness game uses `bindingWitnessErrorTerm`.
-/
noncomputable def bindingErrorTerm (C : Type) [Fintype C]
    (depth t : ℕ) : ℝ≥0∞ :=
  ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
    (((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C

/-- The exact witness-game binding error term implies the compact textbook
expression once the adversary query budget dominates the selected verifier
cross term. This is the arithmetic side of `lemma:mt-binding`; the ROM side is
the still-separate proof that the witness game is bounded by
`bindingErrorTerm`. -/
theorem bindingErrorTerm_le_textbook {depth t : ℕ} [Fintype C]
    (hlarge : 2 * (depth + 1) ^ 2 ≤ t) :
    bindingErrorTerm C depth t ≤
      (((t ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)) := by
  unfold bindingErrorTerm
  let d := depth + 1
  let N := Fintype.card C
  change (((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * (N : ℝ≥0∞))) +
      (((d ^ 2 : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) ≤
      (((t ^ 2 : ℕ) : ℝ≥0∞) / (2 * (N : ℝ≥0∞)))
  have hnum : t * (t - 1) + 2 * d ^ 2 ≤ t ^ 2 := by
    have hd2 : 2 * d ^ 2 ≤ t := hlarge
    have hsub : t * (t - 1) + t ≤ t ^ 2 := by
      by_cases ht0 : t = 0
      · simp [ht0]
      · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
        have htminus : t - 1 + 1 = t :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt htpos)
        calc
          t * (t - 1) + t = t * (t - 1) + t * 1 := by simp
          _ = t * ((t - 1) + 1) := by rw [Nat.mul_add]
          _ = t * t := by rw [htminus]
          _ = t ^ 2 := by ring
          _ ≤ t ^ 2 := le_rfl
    exact le_trans (Nat.add_le_add_left hd2 _) hsub
  have hhalf : (((d ^ 2 : ℕ) : ℝ≥0∞) / N) =
      (((2 * d ^ 2 : ℕ) : ℝ≥0∞) / (2 * N)) := by
    have hmul :=
      ENNReal.mul_div_mul_left (((d ^ 2 : ℕ) : ℝ≥0∞)) ((N : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    rw [← hmul]
    congr 2 <;> norm_num [Nat.cast_mul]
  rw [hhalf]
  rw [ENNReal.div_add_div_same]
  apply ENNReal.div_le_div_right
  norm_num [Nat.cast_add, Nat.cast_mul]
  exact_mod_cast hnum

end MerkleTree
