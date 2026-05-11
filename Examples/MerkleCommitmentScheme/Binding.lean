/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Collision
import Examples.MerkleCommitmentScheme.Extractability
import Examples.CommitmentScheme.Support.Collision
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Merkle Commitment Scheme — Binding

This module packages the Merkle binding experiment surface and the deterministic
reduction from a fixed-oracle binding win to the cross-log collision theorem.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- A binding adversary output: one commitment and two claimed batch openings. -/
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
  run : OracleComp (Oracle M S C) (BindingOutput M S C depth)
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

private theorem crossLogCollision_iff_oracleComp_logCrossCollision
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
private noncomputable def selectBindingMismatchWitness? {depth : ℕ}
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
the ROM game. -/
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

private def BindingWitnessRestLogCrossEvent {depth : ℕ}
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

/-- Textbook witness success: the selected checks accept, and the verifier-rest
phase did not create a fresh query whose answer hits a value already present in
the adversary/commit cache. -/
def BindingTextbookWinROM {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :
    Prop :=
  BindingWitnessWinROM (M := M) (S := S) (C := C)
    (z.1.toWitnessTranscript, z.2) ∧
    ¬ OracleComp.FreshHitInitialCache z.1.commitCache z.2 ∧
    BindingTextbookNoFirstLogCollision (M := M) (S := S) (C := C) z

private def BindingTextbookRestCreatedEvent {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :
    Prop :=
  ∃ (single₀ single₁ : Bool × QueryLog (Oracle M S C)),
    z.1.single₀? = some single₀ ∧
    z.1.single₁? = some single₁ ∧
    OracleComp.RestCreatedLogCrossCollision z.1.commitCache single₀.2 single₁.2 ∧
    ¬ OracleComp.LogHasCollision single₀.2 ∧
    ¬ OracleComp.FreshHitInitialCache z.1.commitCache z.2

private noncomputable def bindingWitnessCommitPart {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    OracleComp (Oracle M S C) (BindingOutput M S C depth) :=
  A.run

private noncomputable def bindingWitnessRest [DecidableEq C] {depth : ℕ}
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
private noncomputable def bindingTextbookWitnessRest [DecidableEq C] {depth : ℕ}
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

private theorem bindingWitnessInner_eq_bind [DecidableEq C] {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    bindingWitnessInner (M := M) (S := S) (C := C) A =
      bindingWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun out =>
        bindingWitnessRest (M := M) (S := S) (C := C) out := by
  rfl

private theorem bindingWitnessRest_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth) :
    IsTotalQueryBound
      (bindingWitnessRest (M := M) (S := S) (C := C) out)
      (2 * (depth + 1)) := by
  classical
  unfold bindingWitnessRest
  split
  · trivial
  · rename_i w heq
    let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
    let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
    let check₀ :=
      checkSingle (M := M) (S := S) (C := C)
        out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
    let check₁ :=
      checkSingle (M := M) (S := S) (C := C)
        out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
    have hcheck₀ :
        IsTotalQueryBound ((simulateQ loggingOracle check₀).run) (depth + 1) := by
      exact
        (isTotalQueryBound_run_simulateQ_loggingOracle_iff check₀ (depth + 1)).mpr
          (by
            dsimp [check₀]
            exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
              out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀))
    have hcheck₁ :
        IsTotalQueryBound ((simulateQ loggingOracle check₁).run) (depth + 1) := by
      exact
        (isTotalQueryBound_run_simulateQ_loggingOracle_iff check₁ (depth + 1)).mpr
          (by
            dsimp [check₁]
            exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
              out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁))
    have htwoRaw :
        IsTotalQueryBound
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))
          ((depth + 1) + ((depth + 1) + 0)) := by
      exact
        isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := (depth + 1) + 0)
          hcheck₀ fun _ =>
            isTotalQueryBound_bind (n₁ := depth + 1) (n₂ := 0) hcheck₁
              fun _ => trivial
    exact htwoRaw.mono (by omega)

private theorem bindingTextbookWitnessRest_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (commitCache : QueryCache (Oracle M S C))
    (out : BindingOutput M S C depth) :
    IsTotalQueryBound
      (bindingTextbookWitnessRest (M := M) (S := S) (C := C) commitCache out)
      (2 * (depth + 1)) := by
  unfold bindingTextbookWitnessRest
  have hraw :
      IsTotalQueryBound
        (bindingWitnessRest (M := M) (S := S) (C := C) out >>= fun base =>
          pure
            ({ out := base.out
               commitCache := commitCache
               witness? := base.witness?
               single₀? := base.single₀?
               single₁? := base.single₁? } :
              BindingTextbookWitnessTranscript M S C depth))
        ((2 * (depth + 1)) + 0) := by
    exact isTotalQueryBound_bind (n₁ := 2 * (depth + 1)) (n₂ := 0)
      (bindingWitnessRest_totalQueryBound (M := M) (S := S) (C := C) out)
      fun _ => trivial
  exact hraw.mono (by omega)

private theorem bindingWitnessInner_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t) :
    IsTotalQueryBound
      (bindingWitnessInner (M := M) (S := S) (C := C) A)
      (t + 2 * (depth + 1)) := by
  rw [bindingWitnessInner_eq_bind (M := M) (S := S) (C := C) A]
  refine isTotalQueryBound_bind (n₁ := t) (n₂ := 2 * (depth + 1))
    A.queryBound ?_
  intro out
  exact bindingWitnessRest_totalQueryBound (M := M) (S := S) (C := C) out

/-- A loose final ROM binding error term for the witness-index game. -/
noncomputable def bindingWitnessErrorTerm (C : Type) [Fintype C]
    (depth t : ℕ) : ℝ≥0∞ :=
  ((t + 2 * (depth + 1)) ^ 2 : ℕ) / (2 * Fintype.card C)

/-- Textbook binding error term for the witness-index Merkle binding game:
adversary-trace birthday collision plus one selected pair of authentication
paths. -/
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

private theorem oracleRange_card_eq [Fintype C]
    (q : (Oracle M S C).Domain) :
    Fintype.card ((Oracle M S C).Range q) = Fintype.card C := by
  cases q with
  | inl _ => rfl
  | inr _ => rfl

private theorem oracleRange_card_le [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C]
    (q : (Oracle M S C).Domain) :
    Fintype.card ((Oracle M S C).Range default) ≤
      Fintype.card ((Oracle M S C).Range q) := by
  rw [oracleRange_card_eq (M := M) (S := S) (C := C) default,
    oracleRange_card_eq (M := M) (S := S) (C := C) q]

private theorem probEvent_bind_le_of_forall_support
    {m : Type → Type} [Monad m] [HasEvalSPMF m]
    {α β : Type} {mx : m α} {my : α → m β}
    {E : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[E | my x] ≤ ε) :
    Pr[ E | mx >>= my] ≤ ε := by
  rw [probEvent_bind_eq_tsum]
  calc
    ∑' x, Pr[= x | mx] * Pr[ E | my x]
        ≤ ∑' x, Pr[= x | mx] * ε := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : x ∈ support mx
          · exact mul_le_mul' le_rfl (h x hx)
          · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx]) * ε := by
          rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ε := by
          exact mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = ε := by simp

private noncomputable def logAnswerTargets [DecidableEq C] [Inhabited M] [Inhabited S]
    [Inhabited C]
    (log : QueryLog (Oracle M S C)) : Finset C :=
  (log.map (traceEntryAnswer (M := M) (S := S) (C := C))).toFinset

private theorem logAnswerTargets_card_le [DecidableEq C] [Inhabited M] [Inhabited S]
    [Inhabited C]
    (log : QueryLog (Oracle M S C)) :
    (logAnswerTargets (M := M) (S := S) (C := C) log).card ≤ log.length := by
  classical
  unfold logAnswerTargets
  calc
    (List.map (traceEntryAnswer (M := M) (S := S) (C := C)) log).toFinset.card
        ≤ (List.map (traceEntryAnswer (M := M) (S := S) (C := C)) log).length :=
          List.toFinset_card_le _
    _ = log.length := by simp

private theorem probEvent_cache_has_value_mem_finset_le {α : Type}
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
        ≤ ∑ target ∈ targets,
            Pr[fun z => ∃ t₀ : (Oracle M S C).Domain,
              ∃ v : (Oracle M S C).Range t₀,
                z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target |
              (simulateQ cachingOracle oa).run cache₀] :=
          probEvent_exists_finset_le_sum targets
            ((simulateQ cachingOracle oa).run cache₀)
            (fun target z => ∃ t₀ : (Oracle M S C).Domain,
              ∃ v : (Oracle M S C).Range t₀,
                z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v target)
    _ ≤ ∑ target ∈ targets,
            ((n : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹) := by
          apply Finset.sum_le_sum
          intro target _htarget
          simpa [oracleRange_card_eq (M := M) (S := S) (C := C) default] using
            (OracleComp.probEvent_cache_has_value_le_of_noCollision
              (spec := Oracle M S C) (oa := oa) (n := n) hbound
              (oracleRange_card_le (M := M) (S := S) (C := C))
              target cache₀ hno)
    _ = (((n * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [Nat.cast_mul, mul_assoc, mul_left_comm]

private theorem traceEntryAnswer_heq
    (entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t) :
    HEq entry.2 (traceEntryAnswer (M := M) (S := S) (C := C) entry) := by
  cases entry with
  | mk domain answer =>
      cases domain <;> rfl

private theorem traceEntryAnswer_mem_logAnswerTargets [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {log : QueryLog (Oracle M S C)}
    {entry : (t : (Oracle M S C).Domain) × (Oracle M S C).Range t}
    (hentry : entry ∈ log) :
    traceEntryAnswer (M := M) (S := S) (C := C) entry ∈
      logAnswerTargets (M := M) (S := S) (C := C) log := by
  classical
  unfold logAnswerTargets
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨entry, hentry, rfl⟩)

private def SecondVerifierFreshHit [DecidableEq C]
    (targets : Finset C)
    (cache₁ : QueryCache (Oracle M S C))
    (z : (Bool × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)) :
    Prop :=
  ∃ target ∈ targets, ∃ t₀ : (Oracle M S C).Domain,
    ∃ v : (Oracle M S C).Range t₀,
      z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v target

private theorem freshHitInitialCache_mono_final
    {cache₀ cache₁ cache₂ : QueryCache (Oracle M S C)}
    (hle : cache₁ ≤ cache₂) :
    OracleComp.FreshHitInitialCache cache₀ cache₁ →
      OracleComp.FreshHitInitialCache cache₀ cache₂ := by
  rintro ⟨tNew, tOld, uNew, uOld, hnone, hnew, hold, hne, heq⟩
  exact ⟨tNew, tOld, uNew, uOld, hnone, hle hnew, hold, hne, heq⟩

private theorem logHasCollision_of_mem
    {log : QueryLog (Oracle M S C)}
    {entry₀ entry₁ :
      (t : (Oracle M S C).Domain) × (Oracle M S C).Range t}
    (hentry₀ : entry₀ ∈ log) (hentry₁ : entry₁ ∈ log)
    (hne : entry₀.1 ≠ entry₁.1) (heq : HEq entry₀.2 entry₁.2) :
    OracleComp.LogHasCollision log := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hentry₀
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hentry₁
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_, heq⟩
  · intro hij
    have hval : i = j := congrArg Fin.val hij
    subst j
    exact hne rfl
  · exact hne

private theorem cacheNoCollision_after_cached_logging_of_no_initial_collision
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {α : Type}
    (oa : OracleComp (Oracle M S C) α)
    {cache₀ cache₁ cacheFinal : QueryCache (Oracle M S C)}
    {z : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀))
    (hcache₁ : z.2 = cache₁)
    (hcache₁Final : cache₁ ≤ cacheFinal)
    (hnoInitial : ¬ CacheHasCollision cache₀)
    (hnoFreshInitial : ¬ OracleComp.FreshHitInitialCache cache₀ cacheFinal)
    (hnoLog : ¬ OracleComp.LogHasCollision z.1.2) :
    ¬ CacheHasCollision cache₁ := by
  classical
  subst cache₁
  intro hcollision
  rcases hcollision with ⟨t₀, t₁, u₀, u₁, hne, hcache₀', hcache₁', heq⟩
  have hentries :=
    OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) oa cache₀ z hz
  have horigin₀ :=
    OracleComp.cache_entry_in_log_or_initial
      (spec := Oracle M S C) oa cache₀ z hz t₀ u₀ hcache₀'
  have horigin₁ :=
    OracleComp.cache_entry_in_log_or_initial
      (spec := Oracle M S C) oa cache₀ z hz t₁ u₁ hcache₁'
  rcases horigin₀ with hinit₀ | hlog₀
  · rcases horigin₁ with hinit₁ | hlog₁
    · exact hnoInitial ⟨t₀, t₁, u₀, u₁, hne, hinit₀, hinit₁, heq⟩
    · rcases hlog₁ with ⟨entry₁, hentry₁, hentry₁_input, hentry₁_answer⟩
      by_cases hcached₁ : ∃ old₁ : (Oracle M S C).Range entry₁.1,
          cache₀ entry₁.1 = some old₁
      · rcases hcached₁ with ⟨old₁, hold₁⟩
        have hentry_cache : z.2 entry₁.1 = some entry₁.2 :=
          hentries.1 entry₁ hentry₁
        have hold₁_z : z.2 entry₁.1 = some old₁ := hentries.2 hold₁
        have hold₁_eq : HEq old₁ entry₁.2 := by
          have hsome : (some old₁ : Option ((Oracle M S C).Range entry₁.1)) =
              some entry₁.2 := by
            rw [← hold₁_z, hentry_cache]
          exact heq_of_eq (Option.some.inj hsome)
        have hentry_ne : t₀ ≠ entry₁.1 := by
          intro hsame
          exact hne (by rw [← hentry₁_input, ← hsame])
        exact hnoInitial
          ⟨t₀, entry₁.1, u₀, old₁, hentry_ne, hinit₀, hold₁,
            heq.trans (hentry₁_answer.symm.trans hold₁_eq.symm)⟩
      · push_neg at hcached₁
        have hentry_none : cache₀ entry₁.1 = none := by
          cases h : cache₀ entry₁.1 with
          | none => rfl
          | some old => exact False.elim (hcached₁ old h)
        have hentry_cache_final : cacheFinal entry₁.1 = some entry₁.2 :=
          hcache₁Final (hentries.1 entry₁ hentry₁)
        have hentry_ne : entry₁.1 ≠ t₀ := by
          intro hsame
          exact hne (by rw [← hentry₁_input, hsame])
        exact hnoFreshInitial
          ⟨entry₁.1, t₀, entry₁.2, u₀, hentry_none, hentry_cache_final,
            hinit₀, hentry_ne, hentry₁_answer.trans heq.symm⟩
  · rcases hlog₀ with ⟨entry₀, hentry₀, hentry₀_input, hentry₀_answer⟩
    rcases horigin₁ with hinit₁ | hlog₁
    · by_cases hcached₀ : ∃ old₀ : (Oracle M S C).Range entry₀.1,
          cache₀ entry₀.1 = some old₀
      · rcases hcached₀ with ⟨old₀, hold₀⟩
        have hentry_cache : z.2 entry₀.1 = some entry₀.2 :=
          hentries.1 entry₀ hentry₀
        have hold₀_z : z.2 entry₀.1 = some old₀ := hentries.2 hold₀
        have hold₀_eq : HEq old₀ entry₀.2 := by
          have hsome : (some old₀ : Option ((Oracle M S C).Range entry₀.1)) =
              some entry₀.2 := by
            rw [← hold₀_z, hentry_cache]
          exact heq_of_eq (Option.some.inj hsome)
        have hentry_ne : entry₀.1 ≠ t₁ := by
          intro hsame
          exact hne (by rw [← hentry₀_input, hsame])
        exact hnoInitial
          ⟨entry₀.1, t₁, old₀, u₁, hentry_ne, hold₀, hinit₁,
            hold₀_eq.trans (hentry₀_answer.trans heq)⟩
      · push_neg at hcached₀
        have hentry_none : cache₀ entry₀.1 = none := by
          cases h : cache₀ entry₀.1 with
          | none => rfl
          | some old => exact False.elim (hcached₀ old h)
        have hentry_cache_final : cacheFinal entry₀.1 = some entry₀.2 :=
          hcache₁Final (hentries.1 entry₀ hentry₀)
        have hentry_ne : entry₀.1 ≠ t₁ := by
          intro hsame
          exact hne (by rw [← hentry₀_input, hsame])
        exact hnoFreshInitial
          ⟨entry₀.1, t₁, entry₀.2, u₁, hentry_none, hentry_cache_final,
            hinit₁, hentry_ne, hentry₀_answer.trans heq⟩
    · rcases hlog₁ with ⟨entry₁, hentry₁, hentry₁_input, hentry₁_answer⟩
      have hentry_ne : entry₀.1 ≠ entry₁.1 := by
        intro hsame
        exact hne (by rw [← hentry₀_input, ← hentry₁_input, hsame])
      exact hnoLog
        (logHasCollision_of_mem
          (M := M) (S := S) (C := C)
          hentry₀ hentry₁ hentry_ne
          (hentry₀_answer.trans (heq.trans hentry₁_answer.symm)))

private theorem restCreatedLogCrossCollision_implies_secondVerifierFreshHit
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (check₀ check₁ : OracleComp (Oracle M S C) Bool)
    {commitCache cache₁ cache₂ : QueryCache (Oracle M S C)}
    {single₀ single₁ : Bool × QueryLog (Oracle M S C)}
    (hsupport₀ : (single₀, cache₁) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₀).run)).run commitCache))
    (hsupport₁ : (single₁, cache₂) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁))
    (hrest :
      OracleComp.RestCreatedLogCrossCollision commitCache single₀.2 single₁.2)
    (hnoFirst : ¬ OracleComp.LogHasCollision single₀.2) :
    SecondVerifierFreshHit (M := M) (S := S) (C := C)
      (logAnswerTargets (M := M) (S := S) (C := C) single₀.2)
      cache₁ (single₁, cache₂) := by
  classical
  rcases hrest with
    ⟨entry₀, hentry₀, entry₁, hentry₁, _hfresh₀, hfresh₁, hne, heq⟩
  have hentries₀ :=
    OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) check₀ commitCache (single₀, cache₁) hsupport₀
  have hentries₁ :=
    OracleComp.log_entry_in_cache_and_mono
      (spec := Oracle M S C) check₁ cache₁ (single₁, cache₂) hsupport₁
  have hentry₁_cache₂ : cache₂ entry₁.1 = some entry₁.2 :=
    hentries₁.1 entry₁ hentry₁
  have hentry₁_cache₁_none : cache₁ entry₁.1 = none := by
    unfold OracleComp.LogEntryFresh at hfresh₁
    cases hcache₁ : cache₁ entry₁.1 with
    | none => rfl
    | some old =>
        have horigin :=
          OracleComp.cache_entry_in_log_or_initial
            (spec := Oracle M S C) check₀ commitCache (single₀, cache₁)
            hsupport₀ entry₁.1 old hcache₁
        rcases horigin with hinit | hlog
        · rw [hfresh₁] at hinit
          contradiction
        · rcases hlog with ⟨entry₀', hentry₀', hentry₀'_input, hentry₀'_answer⟩
          have hold_cache₂ : cache₂ entry₁.1 = some old := hentries₁.2 hcache₁
          have hold_eq : HEq old entry₁.2 := by
            have hsome : (some old : Option ((Oracle M S C).Range entry₁.1)) =
                some entry₁.2 := by
              rw [← hold_cache₂, hentry₁_cache₂]
            exact heq_of_eq (Option.some.inj hsome)
          have hentry_ne : entry₀.1 ≠ entry₀'.1 := by
            intro hsame
            exact hne (hsame.trans hentry₀'_input)
          have heq_first : HEq entry₀.2 entry₀'.2 :=
            heq.trans (hold_eq.symm.trans hentry₀'_answer.symm)
          exact False.elim <| hnoFirst
            (logHasCollision_of_mem
              (M := M) (S := S) (C := C)
              hentry₀ hentry₀' hentry_ne heq_first)
  refine ⟨traceEntryAnswer (M := M) (S := S) (C := C) entry₀,
    traceEntryAnswer_mem_logAnswerTargets
      (M := M) (S := S) (C := C) hentry₀,
    entry₁.1, entry₁.2, hentry₁_cache₂, hentry₁_cache₁_none, ?_⟩
  exact heq.symm.trans (traceEntryAnswer_heq (M := M) (S := S) (C := C) entry₀)

private theorem secondVerifierFreshHit_bound_of_first_log
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (check₀ check₁ : OracleComp (Oracle M S C) Bool)
    {commitCache cache₁ : QueryCache (Oracle M S C)}
    {single₀ : Bool × QueryLog (Oracle M S C)}
    (hsupport₀ : (single₀, cache₁) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₀).run)).run commitCache))
    (hbound₀ : IsTotalQueryBound check₀ (depth + 1))
    (hbound₁ : IsTotalQueryBound check₁ (depth + 1))
    (hnoCache₁ : ¬ CacheHasCollision cache₁) :
    Pr[fun z =>
      SecondVerifierFreshHit (M := M) (S := S) (C := C)
        (logAnswerTargets (M := M) (S := S) (C := C) single₀.2)
        cache₁ z |
      (simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁] ≤
      ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C) := by
  classical
  let targets := logAnswerTargets (M := M) (S := S) (C := C) single₀.2
  have hlogBound₁ :
      IsTotalQueryBound ((simulateQ loggingOracle check₁).run) (depth + 1) :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff check₁ (depth + 1)).mpr
      hbound₁
  have hfresh :
      Pr[fun z =>
        SecondVerifierFreshHit (M := M) (S := S) (C := C) targets cache₁ z |
        (simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁] ≤
        ((((depth + 1) * targets.card : ℕ) : ℝ≥0∞) *
          (Fintype.card C : ℝ≥0∞)⁻¹) := by
    simpa [SecondVerifierFreshHit, targets] using
      (probEvent_cache_has_value_mem_finset_le
        (M := M) (S := S) (C := C)
        ((simulateQ loggingOracle check₁).run) (depth + 1) hlogBound₁
        targets cache₁ hnoCache₁)
  have hlen : single₀.2.length ≤ depth + 1 :=
    OracleComp.log_length_le_of_mem_support_run_cached_logging
      (spec := Oracle M S C) (oa := check₀) hbound₀ commitCache
      (z := (single₀, cache₁)) hsupport₀
  have htargets : targets.card ≤ depth + 1 :=
    le_trans (logAnswerTargets_card_le (M := M) (S := S) (C := C) single₀.2) hlen
  calc
    Pr[fun z =>
      SecondVerifierFreshHit (M := M) (S := S) (C := C) targets cache₁ z |
      (simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁]
        ≤ ((((depth + 1) * targets.card : ℕ) : ℝ≥0∞) *
            (Fintype.card C : ℝ≥0∞)⁻¹) := hfresh
    _ ≤ ((((depth + 1) * (depth + 1) : ℕ) : ℝ≥0∞) *
            (Fintype.card C : ℝ≥0∞)⁻¹) := by
          gcongr
    _ = ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C) := by
          rw [Nat.pow_two]
          simp [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm]

private theorem bindingTextbookRestCreatedEvent_second_bound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (commitCache : QueryCache (Oracle M S C))
    (w : BindingMismatchWitness (M := M) (S := S) (C := C) out)
    (check₀ check₁ : OracleComp (Oracle M S C) Bool)
    {single₀ : Bool × QueryLog (Oracle M S C)}
    {cache₁ : QueryCache (Oracle M S C)}
    (hsupport₀ : (single₀, cache₁) ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle check₀).run)).run commitCache))
    (hbound₀ : IsTotalQueryBound check₀ (depth + 1))
    (hbound₁ : IsTotalQueryBound check₁ (depth + 1))
    (hnoCommit : ¬ CacheHasCollision commitCache) :
    Pr[fun z =>
      BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        ((simulateQ loggingOracle check₁).run >>= fun single₁ =>
          pure
            ({ out := out
               commitCache := commitCache
               witness? := some w
               single₀? := some single₀
               single₁? := some single₁ } :
              BindingTextbookWitnessTranscript M S C depth))).run cache₁] ≤
      ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C) := by
  classical
  by_cases hnoCache₁ : ¬ CacheHasCollision cache₁
  · have hrun :
        (simulateQ cachingOracle
          ((simulateQ loggingOracle check₁).run >>= fun single₁ =>
            pure
              ({ out := out
                 commitCache := commitCache
                 witness? := some w
                 single₀? := some single₀
                 single₁? := some single₁ } :
                BindingTextbookWitnessTranscript M S C depth))).run cache₁ =
          (fun z : (Bool × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C) =>
            (({ out := out
                commitCache := commitCache
                witness? := some w
                single₀? := some single₀
                single₁? := some z.1 } :
              BindingTextbookWitnessTranscript M S C depth), z.2)) <$>
            ((simulateQ cachingOracle ((simulateQ loggingOracle check₁).run)).run cache₁) := by
      rw [simulateQ_bind, StateT.run_bind]
      simp [simulateQ_pure, StateT.run, map_eq_bind_pure_comp]
      rfl
    rw [hrun, probEvent_map]
    refine le_trans
      (probEvent_mono
        (q := fun z =>
          SecondVerifierFreshHit (M := M) (S := S) (C := C)
            (logAnswerTargets (M := M) (S := S) (C := C) single₀.2)
            cache₁ z) ?_) ?_
    · intro z hz hevent
      rcases hevent with
        ⟨single₀Event, single₁Event, hsingle₀, hsingle₁, hrest, hnoFirst, _hnoFresh⟩
      have hsingle₀Eq : single₀Event = single₀ := by
        simpa using (Option.some.inj hsingle₀).symm
      subst single₀Event
      have hsingle₁Eq : single₁Event = z.1 := by
        simpa using (Option.some.inj hsingle₁).symm
      subst single₁Event
      exact
        restCreatedLogCrossCollision_implies_secondVerifierFreshHit
          (M := M) (S := S) (C := C)
          check₀ check₁ hsupport₀ hz hrest hnoFirst
    · exact
        secondVerifierFreshHit_bound_of_first_log
          (M := M) (S := S) (C := C)
          check₀ check₁ hsupport₀ hbound₀ hbound₁ hnoCache₁
  · have hzero :
        Pr[fun z =>
          BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            ((simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   commitCache := commitCache
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingTextbookWitnessTranscript M S C depth))).run cache₁] = 0 := by
      apply probEvent_eq_zero
      intro z hz hevent
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₂⟩, hsupport₁, hpure⟩
      simp [simulateQ_pure, StateT.run] at hpure
      subst z
      rcases hevent with
        ⟨single₀Event, single₁Event, hsingle₀, hsingle₁, _hrest, hnoFirst, hnoFresh⟩
      have hsingle₀Eq : single₀Event = single₀ := by
        simpa using (Option.some.inj hsingle₀).symm
      subst single₀Event
      have hsingle₁Eq : single₁Event = single₁ := by
        simpa using (Option.some.inj hsingle₁).symm
      subst single₁Event
      have hcache₁Final : cache₁ ≤ cache₂ :=
        OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C) ((simulateQ loggingOracle check₁).run)
          cache₁ (single₁, cache₂) hsupport₁
      exact hnoCache₁
        (cacheNoCollision_after_cached_logging_of_no_initial_collision
          (M := M) (S := S) (C := C)
          check₀ hsupport₀ rfl hcache₁Final hnoCommit hnoFresh hnoFirst)
    rw [hzero]
    exact zero_le _

private theorem bindingTextbookWitnessRest_restCreatedEvent_bound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (commitCache : QueryCache (Oracle M S C))
    (hnoCommit : ¬ CacheHasCollision commitCache) :
    Pr[fun z =>
      BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
          commitCache out)).run commitCache] ≤
      ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C) := by
  classical
  unfold bindingTextbookWitnessRest bindingWitnessRest
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      have hzero :
          Pr[fun z =>
            BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (pure
                ({ out := out
                   commitCache := commitCache
                   witness? := none
                   single₀? := none
                   single₁? := none } :
                  BindingTextbookWitnessTranscript M S C depth))).run commitCache] = 0 := by
        apply probEvent_eq_zero
        intro z hz hevent
        simp [simulateQ_pure, StateT.run] at hz
        subst z
        rcases hevent with ⟨single₀, _single₁, hsingle₀, _hsingle₁, _⟩
        simp at hsingle₀
      simpa [hsel] using le_of_eq_of_le hzero (zero_le _)
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      have hbound₀ : IsTotalQueryBound check₀ (depth + 1) := by
        dsimp [check₀]
        exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      have hbound₁ : IsTotalQueryBound check₁ (depth + 1) := by
        dsimp [check₁]
        exact checkSingle_totalQueryBound (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel]
      have hcomp :
          ((do
            let base ←
              ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
                (simulateQ loggingOracle check₁).run >>= fun single₁ =>
                  pure
                    ({ out := out
                       witness? := some w
                       single₀? := some single₀
                       single₁? := some single₁ } :
                      BindingWitnessTranscript M S C depth))
            pure
              ({ out := base.out
                 commitCache := commitCache
                 witness? := base.witness?
                 single₀? := base.single₀?
                 single₁? := base.single₁? } :
                BindingTextbookWitnessTranscript M S C depth)) :
            OracleComp (Oracle M S C)
              (BindingTextbookWitnessTranscript M S C depth)) =
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   commitCache := commitCache
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingTextbookWitnessTranscript M S C depth)) := by
        simp [bind_assoc]
      rw [hcomp]
      change
        Pr[fun z =>
          BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
              (simulateQ loggingOracle check₁).run >>= fun single₁ =>
                pure
                  ({ out := out
                     commitCache := commitCache
                     witness? := some w
                     single₀? := some single₀
                     single₁? := some single₁ } :
                    BindingTextbookWitnessTranscript M S C depth))).run commitCache] ≤
          ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C)
      rw [simulateQ_bind, StateT.run_bind]
      refine probEvent_bind_le_of_forall_support ?_
      intro z hz
      rcases z with ⟨single₀, cache₁⟩
      exact
        bindingTextbookRestCreatedEvent_second_bound
          (M := M) (S := S) (C := C)
          out commitCache w check₀ check₁ hz hbound₀ hbound₁ hnoCommit

private theorem logEval_fst_eq_eval {α : Type} (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) α) :
    (logEval f oa).1 = eval f oa := by
  unfold logEval eval
  have h := QueryImpl.fst_map_run_withLogging (QueryImpl.ofFn f) oa
  simpa using h

private lemma run_simulateQ_loggingOracle_query_bind_merkle {α : Type}
    (t : (Oracle M S C).Domain)
    (mx : (Oracle M S C).Range t → OracleComp (Oracle M S C) α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp (Oracle M S C) _) >>= fun u =>
        (fun p : α × QueryLog (Oracle M S C) =>
          (p.1, (⟨t, u⟩ :
            (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def, Function.comp]

private theorem logEval_oracleFnOfCache_eq_of_cached_logging {α : Type}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    (oa : OracleComp (Oracle M S C) α)
    {cache₀ cacheFinal : QueryCache (Oracle M S C)}
    {z : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀))
    (hmono : z.2 ≤ cacheFinal) :
    logEval (M := M) (S := S) (C := C)
      (oracleFnOfCache (M := M) (S := S) (C := C) cacheFinal) oa = z.1 := by
  induction oa using OracleComp.inductionOn generalizing z cache₀ cacheFinal with
  | pure x =>
      simp [logEval] at hz
      subst z
      rfl
  | query_bind t mx ih =>
      have hzWhole := hz
      rw [run_simulateQ_loggingOracle_query_bind_merkle] at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨u, cache₁⟩, hquery, hcont⟩
      rw [simulateQ_map] at hcont
      change z ∈ support
        ((fun p : (α × QueryLog (Oracle M S C)) × QueryCache (Oracle M S C) =>
            ((p.1.1,
              (⟨t, u⟩ :
                (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: p.1.2),
              p.2)) <$>
          ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache₁))
        at hcont
      rw [support_map] at hcont
      rcases hcont with ⟨w, hw, hzw⟩
      rcases w with ⟨⟨value, tailLog⟩, cache₂⟩
      have hzEq :
          z = ((value, (⟨t, u⟩ :
              (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: tailLog),
            cache₂) := by
        simpa using hzw.symm
      subst z
      have hmonoTail : cache₂ ≤ cacheFinal := by
        simpa using hmono
      have hentryInCache : cache₂ t = some u := by
        exact
          (OracleComp.log_entry_in_cache_and_mono
            (spec := Oracle M S C) (liftM (query t) >>= mx) cache₀
            ((value,
              (⟨t, u⟩ :
                (i : (Oracle M S C).Domain) × (Oracle M S C).Range i) :: tailLog),
              cache₂)
            hzWhole).1
            (⟨t, u⟩ :
              (i : (Oracle M S C).Domain) × (Oracle M S C).Range i)
            (by simp)
      have hcacheFinal : cacheFinal t = some u := hmono hentryInCache
      have htail :
          logEval (M := M) (S := S) (C := C)
            (oracleFnOfCache (M := M) (S := S) (C := C) cacheFinal) (mx u) =
            (value, tailLog) := by
        exact ih u (z := ((value, tailLog), cache₂)) (cache₀ := cache₁)
          (cacheFinal := cacheFinal) hw hmonoTail
      have hu :
          oracleFnOfCache (M := M) (S := S) (C := C) cacheFinal t = u := by
        simpa using
          oracleFnOfCache_apply_of_some (M := M) (S := S) (C := C)
            (cache := cacheFinal) (t := t) (v := u) hcacheFinal
      simp [logEval_bind, logEval_query, hu, htail]

private theorem bindingWitnessRest_win_implies_logCrossEvent_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    {cache₀ : QueryCache (Oracle M S C)}
    {z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀))
    (hwin : BindingWitnessWinROM (M := M) (S := S) (C := C) z) :
    BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z := by
  classical
  unfold bindingWitnessRest at hz
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      simp [hsel] at hz
      subst z
      rcases hwin with ⟨w, single₀, single₁, hw, hsingle₀, hsingle₁, _, _⟩
      simp at hw
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel] at hz
      change z ∈ support
        ((simulateQ cachingOracle
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))).run cache₀) at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₀, cache₁⟩, hsingle₀Support, hz⟩
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₂⟩, hsingle₁Support, hz⟩
      simp at hz
      subst z
      rcases hwin with
        ⟨wWin, single₀Win, single₁Win, hw, hsingle₀, hsingle₁, hok₀, hok₁⟩
      cases hw
      cases hsingle₀
      cases hsingle₁
      let f := oracleFnOfCache (M := M) (S := S) (C := C) cache₂
      have hmono₁₂ : cache₁ ≤ cache₂ := by
        exact OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C) ((simulateQ loggingOracle check₁).run)
          cache₁ (single₁, cache₂) hsingle₁Support
      have hlog₀ : logEval (M := M) (S := S) (C := C) f check₀ = single₀ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₀
          (cache₀ := cache₀) (cacheFinal := cache₂)
          (z := (single₀, cache₁)) hsingle₀Support hmono₁₂
      have hlog₁ : logEval (M := M) (S := S) (C := C) f check₁ = single₁ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₁
          (cache₀ := cache₁) (cacheFinal := cache₂)
          (z := (single₁, cache₂)) hsingle₁Support (le_refl cache₂)
      have hcheck₀ : eval (M := M) (S := S) (C := C) f check₀ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₀).1 = true := by
          simpa [hlog₀] using hok₀.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₀] using hfst
      have hcheck₁ : eval (M := M) (S := S) (C := C) f check₁ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₁).1 = true := by
          simpa [hlog₁] using hok₁.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₁] using hfst
      have hcollision :
          CrossLogCollision
            (logEval (M := M) (S := S) (C := C) f check₀).2
            (logEval (M := M) (S := S) (C := C) f check₁).2 := by
        dsimp [check₀, check₁] at hcheck₀ hcheck₁
        exact checkSingle_crossLogCollision (M := M) (S := S) (C := C)
          f out.commitment w.idx (out.message₀ i₀) (out.message₁ i₁)
          (out.proof₀ i₀) (out.proof₁ i₁) hcheck₀ hcheck₁
          (Or.inl w.mismatch)
      have hcollisionStored :
          OracleComp.LogCrossCollision single₀.2 single₁.2 := by
        exact
          (crossLogCollision_iff_oracleComp_logCrossCollision
            (M := M) (S := S) (C := C)).mp
            (by simpa [hlog₀, hlog₁] using hcollision)
      exact ⟨single₀, single₁, rfl, rfl, hcollisionStored⟩

private theorem bindingWitnessRest_win_bound_of_logCrossEvent_bound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (cache₀ : QueryCache (Oracle M S C))
    (ε : ℝ≥0∞)
    (hlog :
      Pr[ fun z => BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z |
        (simulateQ cachingOracle
          (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀] ≤ ε) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      (simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀] ≤ ε :=
  le_trans
    (probEvent_mono fun _ hz hwin =>
      bindingWitnessRest_win_implies_logCrossEvent_of_support
        (M := M) (S := S) (C := C) out hz hwin)
    hlog

private theorem bindingWitnessRest_logCrossEvent_implies_restCreatedEvent_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    {cache₀ : QueryCache (Oracle M S C)}
    {z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₀))
    (hlog : BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z)
    (hnoCollision : ¬ CacheHasCollision cache₀)
    (hnoFreshHit : ¬ OracleComp.FreshHitInitialCache cache₀ z.2) :
    ∃ (single₀ single₁ : Bool × QueryLog (Oracle M S C)),
      z.1.single₀? = some single₀ ∧
      z.1.single₁? = some single₁ ∧
      OracleComp.RestCreatedLogCrossCollision cache₀ single₀.2 single₁.2 := by
  classical
  unfold bindingWitnessRest at hz
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      simp [hsel] at hz
      subst z
      rcases hlog with ⟨single₀, single₁, hsingle₀, _hsingle₁, _hcross⟩
      simp at hsingle₀
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel] at hz
      change z ∈ support
        ((simulateQ cachingOracle
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))).run cache₀) at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₀, cache₁⟩, hsingle₀Support, hz⟩
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₂⟩, hsingle₁Support, hz⟩
      simp at hz
      subst z
      rcases hlog with ⟨single₀Log, single₁Log, hsingle₀, hsingle₁, hcross⟩
      have hsingle₀Eq : single₀Log = single₀ := by
        simpa using (Option.some.inj hsingle₀).symm
      have hsingle₁Eq : single₁Log = single₁ := by
        simpa using (Option.some.inj hsingle₁).symm
      subst single₀Log
      subst single₁Log
      have h₀ :=
        OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₀ cache₀ (single₀, cache₁)
          hsingle₀Support
      have h₁ :=
        OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₁ cache₁ (single₁, cache₂)
          hsingle₁Support
      have hrest :
          OracleComp.RestCreatedLogCrossCollision cache₀ single₀.2 single₁.2 :=
        OracleComp.LogCrossCollision.to_restCreated_of_no_initial_collision_no_freshHit
          (spec := Oracle M S C)
          (cache₀ := cache₀) (cache₁ := cache₂)
          (log₀ := single₀.2) (log₁ := single₁.2)
          (le_trans h₀.2 h₁.2)
          (fun entry hentry => h₁.2 (h₀.1 entry hentry))
          (fun entry hentry => h₁.1 entry hentry)
          hnoCollision hnoFreshHit hcross
      exact ⟨single₀, single₁, rfl, rfl, hrest⟩

private theorem bindingTextbookWitnessRest_win_implies_restCreatedEvent_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth : ℕ}
    (out : BindingOutput M S C depth)
    (commitCache : QueryCache (Oracle M S C))
    {z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle
        (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
          commitCache out)).run commitCache))
    (hnoCollision : ¬ CacheHasCollision commitCache)
    (hwin : BindingTextbookWinROM (M := M) (S := S) (C := C) z) :
    BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z := by
  classical
  unfold bindingTextbookWitnessRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨baseZ, hbase, hz⟩
  simp [simulateQ_pure, StateT.run] at hz
  subst z
  rcases hwin with ⟨hbaseWin, hnoFreshHit, hnoFirstCollision⟩
  have hlog :
      BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) baseZ :=
    bindingWitnessRest_win_implies_logCrossEvent_of_support
      (M := M) (S := S) (C := C) out hbase hbaseWin
  rcases
      bindingWitnessRest_logCrossEvent_implies_restCreatedEvent_of_support
        (M := M) (S := S) (C := C) out hbase hlog hnoCollision hnoFreshHit
    with ⟨single₀, single₁, hsingle₀, hsingle₁, hrest⟩
  exact ⟨single₀, single₁, by simpa using hsingle₀, by simpa using hsingle₁,
    hrest, hnoFirstCollision single₀ (by simpa using hsingle₀), hnoFreshHit⟩

private theorem bindingWitnessWinROM_implies_badEventROM_of_support
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    {depth t : ℕ}
    (A : BindingAdversary M S C depth t)
    {z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)}
    (hz : z ∈ support (bindingWitnessGame (M := M) (S := S) (C := C) A))
    (hwin : BindingWitnessWinROM (M := M) (S := S) (C := C) z) :
    BindingWitnessBadEventROM (M := M) (S := S) (C := C) z := by
  classical
  unfold bindingWitnessGame bindingWitnessInner at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  rcases hz with ⟨⟨out, cache₁⟩, hout, hz⟩
  cases hsel : selectBindingMismatchWitness? (M := M) (S := S) (C := C) out with
  | none =>
      simp [hsel] at hz
      subst z
      rcases hwin with ⟨w, single₀, single₁, hw, hsingle₀, hsingle₁, hok₀, hok₁⟩
      simp at hw
  | some w =>
      let i₀ : {i // i ∈ out.I₀} := ⟨w.idx, w.leftMem⟩
      let i₁ : {i // i ∈ out.I₁} := ⟨w.idx, w.rightMem⟩
      let check₀ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₀ i₀) (out.proof₀ i₀)
      let check₁ :=
        checkSingle (M := M) (S := S) (C := C)
          out.commitment w.idx (out.message₁ i₁) (out.proof₁ i₁)
      simp only [hsel, Prod.fst, Prod.snd] at hz
      change z ∈ support
        ((simulateQ cachingOracle
          ((simulateQ loggingOracle check₀).run >>= fun single₀ =>
            (simulateQ loggingOracle check₁).run >>= fun single₁ =>
              pure
                ({ out := out
                   witness? := some w
                   single₀? := some single₀
                   single₁? := some single₁ } :
                  BindingWitnessTranscript M S C depth))).run cache₁) at hz
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₀, cache₂⟩, hsingle₀Support, hz⟩
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨⟨single₁, cache₃⟩, hsingle₁Support, hz⟩
      simp at hz
      subst z
      rcases hwin with
        ⟨wWin, single₀Win, single₁Win, hw, hsingle₀, hsingle₁, hok₀, hok₁⟩
      cases hw
      cases hsingle₀
      cases hsingle₁
      let f := oracleFnOfCache (M := M) (S := S) (C := C) cache₃
      have hmono₂₃ : cache₂ ≤ cache₃ := by
        exact OracleComp.simulateQ_cachingOracle_cache_le
          (spec := Oracle M S C) ((simulateQ loggingOracle check₁).run)
          cache₂ (single₁, cache₃) hsingle₁Support
      have hlog₀ : logEval (M := M) (S := S) (C := C) f check₀ = single₀ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₀
          (cache₀ := cache₁) (cacheFinal := cache₃)
          (z := (single₀, cache₂)) hsingle₀Support hmono₂₃
      have hlog₁ : logEval (M := M) (S := S) (C := C) f check₁ = single₁ := by
        exact logEval_oracleFnOfCache_eq_of_cached_logging
          (M := M) (S := S) (C := C) check₁
          (cache₀ := cache₂) (cacheFinal := cache₃)
          (z := (single₁, cache₃)) hsingle₁Support (le_refl cache₃)
      have hcheck₀ : eval (M := M) (S := S) (C := C) f check₀ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₀).1 = true := by
          simpa [hlog₀] using hok₀.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₀] using hfst
      have hcheck₁ : eval (M := M) (S := S) (C := C) f check₁ = true := by
        have hfst : (logEval (M := M) (S := S) (C := C) f check₁).1 = true := by
          simpa [hlog₁] using hok₁.symm
        simpa [logEval_fst_eq_eval (M := M) (S := S) (C := C) f check₁] using hfst
      have hcollision :
          CrossLogCollision
            (logEval (M := M) (S := S) (C := C) f check₀).2
            (logEval (M := M) (S := S) (C := C) f check₁).2 := by
        dsimp [check₀, check₁] at hcheck₀ hcheck₁
        exact checkSingle_crossLogCollision (M := M) (S := S) (C := C)
          f out.commitment w.idx (out.message₀ i₀) (out.message₁ i₁)
          (out.proof₀ i₀) (out.proof₁ i₁) hcheck₀ hcheck₁
          (Or.inl w.mismatch)
      have hcollisionStored : CrossLogCollision single₀.2 single₁.2 := by
        simpa [hlog₀, hlog₁] using hcollision
      rcases hcollisionStored with ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
      have hentry₀Cache₂ : cache₂ entry₀.1 = some entry₀.2 :=
        (OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₀ cache₁ (single₀, cache₂)
          hsingle₀Support).1 entry₀ hentry₀
      have hentry₀Cache₃ : cache₃ entry₀.1 = some entry₀.2 :=
        hmono₂₃ hentry₀Cache₂
      have hentry₁Cache₃ : cache₃ entry₁.1 = some entry₁.2 :=
        (OracleComp.log_entry_in_cache_and_mono
          (spec := Oracle M S C) check₁ cache₂ (single₁, cache₃)
          hsingle₁Support).1 entry₁ hentry₁
      exact
        ⟨entry₀.1, entry₁.1, entry₀.2, entry₁.2,
          hne, hentry₀Cache₃, hentry₁Cache₃, heq⟩

/-- A fixed-oracle binding win produces the cross-log collision from
`check_crossLogCollision`. -/
theorem bindingWin_implies_crossLogCollision [DecidableEq C] {depth : ℕ}
    (f : OracleFn M S C) (out : BindingOutput M S C depth) :
    BindingWin (M := M) (S := S) (C := C) f out →
      BindingCollisionEvent (M := M) (S := S) (C := C) f out := by
  intro hwin
  exact
    check_crossLogCollision (M := M) (S := S) (C := C)
      f out.commitment out.I₀ out.I₁ out.message₀ out.message₁
      out.proof₀ out.proof₁ hwin.2.1 hwin.2.2 (.inl hwin.1)

/-- Any probability bound for the induced cross-log collision event immediately
bounds fixed-oracle Merkle binding wins. This is the conditional combiner used
before the final ROM binding theorem bounds the collision event directly. -/
theorem binding_bound_of_collision_bound [DecidableEq C]
    [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) (BindingOutput M S C depth))
    (ε : ℝ≥0∞)
    (hcollision :
      Pr[ fun out =>
        BindingCollisionEvent (M := M) (S := S) (C := C) f out | oa] ≤ ε) :
    Pr[ fun out => BindingWin (M := M) (S := S) (C := C) f out | oa] ≤ ε :=
  le_trans
    (probEvent_mono fun out _ hout =>
      bindingWin_implies_crossLogCollision (M := M) (S := S) (C := C) f out hout)
    hcollision

/-- Conservative ROM binding bound for the witness-index Merkle binding game.

This theorem uses the generic whole-cache birthday bound for the adversary plus
the two selected single-check traces. It is intentionally looser than the
textbook split bound, but it is unconditional and applies to the witness game
that checks only one mismatching shared index. -/
theorem binding_bound_wholeCache {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t := by
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [oracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hbirthday :=
    probEvent_cacheCollision_le_birthday_total
      (spec := Oracle M S C)
      (oa := bindingWitnessInner (M := M) (S := S) (C := C) A)
      (t + 2 * (depth + 1))
      (bindingWitnessInner_totalQueryBound (M := M) (S := S) (C := C) A)
      hCdefault
      (oracleRange_card_le (M := M) (S := S) (C := C))
  calc
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A]
        ≤ Pr[fun z => BindingWitnessBadEventROM (M := M) (S := S) (C := C) z |
            bindingWitnessGame (M := M) (S := S) (C := C) A] :=
          probEvent_mono fun z hz hwin =>
            bindingWitnessWinROM_implies_badEventROM_of_support
              (M := M) (S := S) (C := C) A hz hwin
    _ ≤ bindingWitnessErrorTerm C depth t := by
          simpa [bindingWitnessGame, BindingWitnessBadEventROM, bindingWitnessErrorTerm,
            oracleRange_card_eq (M := M) (S := S) (C := C) default] using hbirthday

private theorem bindingWitnessGame_bound_of_rest_logCrossEvent_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hrest :
      ∀ (out : BindingOutput M S C depth)
        (cache₁ : QueryCache (Oracle M S C)),
        (out, cache₁) ∈ support
          ((simulateQ cachingOracle
            (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅) →
        ¬ CacheHasCollision cache₁ →
          Pr[ fun z =>
            BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₁] ≤
            ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C)) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  classical
  let commitPart :=
    bindingWitnessCommitPart (M := M) (S := S) (C := C) A
  let restPart :=
    fun x : BindingOutput M S C depth × QueryCache (Oracle M S C) =>
      (simulateQ cachingOracle
        (bindingWitnessRest (M := M) (S := S) (C := C) x.1)).run x.2
  let ε₁ : ℝ≥0∞ :=
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)
  let ε₂ : ℝ≥0∞ :=
    (((depth + 1) ^ 2 : ℕ) / Fintype.card C)
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [oracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hcommit :
      Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
        (simulateQ cachingOracle commitPart).run ∅] ≤ ε₁ := by
    have hbirthday :=
      probEvent_cacheCollision_le_birthday_total_tight
        (spec := Oracle M S C)
        (oa := commitPart)
        t
        (by
          simpa [commitPart, bindingWitnessCommitPart] using A.queryBound)
        hCdefault
        (oracleRange_card_le (M := M) (S := S) (C := C))
    simpa [ε₁, oracleRange_card_eq (M := M) (S := S) (C := C) default,
      not_not] using hbirthday
  have hrestWin :
      ∀ x ∈ support ((simulateQ cachingOracle commitPart).run ∅),
        ¬ CacheHasCollision x.2 →
          Pr[fun z => ¬
              (¬ BindingWitnessWinROM (M := M) (S := S) (C := C) z) |
            restPart x] ≤ ε₂ := by
    intro x hx hno
    rcases x with ⟨out, cache₁⟩
    have hlog :
        Pr[fun z =>
          BindingWitnessRestLogCrossEvent (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            (bindingWitnessRest (M := M) (S := S) (C := C) out)).run cache₁] ≤
          ε₂ := by
      simpa [commitPart, ε₂] using hrest out cache₁ (by simpa [commitPart] using hx) hno
    have hwin :=
      bindingWitnessRest_win_bound_of_logCrossEvent_bound
        (M := M) (S := S) (C := C) out cache₁ ε₂ hlog
    simpa [restPart, ε₂, not_not] using hwin
  have hcombine :=
    probEvent_bind_le_add
      (mx := (simulateQ cachingOracle commitPart).run ∅)
      (my := restPart)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => ¬ BindingWitnessWinROM (M := M) (S := S) (C := C) z)
      (ε₁ := ε₁)
      (ε₂ := ε₂)
      hcommit hrestWin
  rw [bindingWitnessGame, bindingWitnessInner_eq_bind (M := M) (S := S) (C := C) A,
    simulateQ_bind, StateT.run_bind]
  simpa [commitPart, restPart, ε₁, ε₂, bindingWitnessCommitPart,
    bindingErrorTerm, not_not] using hcombine

/-- Conditional textbook combiner for the origin-aware witness game.

The hypothesis is the still-missing rest-phase estimate: once the adversary
cache is collision-free, the conditioned selected-check win is bounded by the
single-pair verifier term. -/
theorem bindingTextbookWitnessGame_bound_of_rest_win_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hrest :
      ∀ (out : BindingOutput M S C depth)
        (cache₁ : QueryCache (Oracle M S C)),
        (out, cache₁) ∈ support
          ((simulateQ cachingOracle
            (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅) →
        ¬ CacheHasCollision cache₁ →
          Pr[ fun z =>
            BindingTextbookWinROM (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
                cache₁ out)).run cache₁] ≤
            ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C)) :
    Pr[ fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  classical
  let commitPart :=
    bindingWitnessCommitPart (M := M) (S := S) (C := C) A
  let restPart :=
    fun x : BindingOutput M S C depth × QueryCache (Oracle M S C) =>
      (simulateQ cachingOracle
        (bindingTextbookWitnessRest (M := M) (S := S) (C := C) x.2 x.1)).run x.2
  let ε₁ : ℝ≥0∞ :=
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)
  let ε₂ : ℝ≥0∞ :=
    (((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C
  have hCdefault :
      0 < Fintype.card ((Oracle M S C).Range default) := by
    simpa [oracleRange_card_eq (M := M) (S := S) (C := C) default] using hC
  have hcommit :
      Pr[fun x => ¬ (¬ CacheHasCollision x.2) |
        (simulateQ cachingOracle commitPart).run ∅] ≤ ε₁ := by
    have hbirthday :=
      probEvent_cacheCollision_le_birthday_total_tight
        (spec := Oracle M S C)
        (oa := commitPart)
        t
        (by
          simpa [commitPart, bindingWitnessCommitPart] using A.queryBound)
        hCdefault
        (oracleRange_card_le (M := M) (S := S) (C := C))
    simpa [ε₁, oracleRange_card_eq (M := M) (S := S) (C := C) default,
      not_not] using hbirthday
  have hrestWin :
      ∀ x ∈ support ((simulateQ cachingOracle commitPart).run ∅),
        ¬ CacheHasCollision x.2 →
          Pr[fun z => ¬
              (¬ BindingTextbookWinROM (M := M) (S := S) (C := C) z) |
            restPart x] ≤ ε₂ := by
    intro x hx hno
    rcases x with ⟨out, cache₁⟩
    have hwin :
        Pr[fun z =>
          BindingTextbookWinROM (M := M) (S := S) (C := C) z |
          (simulateQ cachingOracle
            (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
              cache₁ out)).run cache₁] ≤ ε₂ := by
      simpa [commitPart, ε₂] using hrest out cache₁ (by simpa [commitPart] using hx) hno
    simpa [restPart, ε₂, not_not] using hwin
  have hcombine :=
    probEvent_bind_le_add
      (mx := (simulateQ cachingOracle commitPart).run ∅)
      (my := restPart)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => ¬ BindingTextbookWinROM (M := M) (S := S) (C := C) z)
      (ε₁ := ε₁)
      (ε₂ := ε₂)
      hcommit hrestWin
  rw [bindingTextbookWitnessGame]
  simpa [commitPart, restPart, ε₁, ε₂, bindingWitnessCommitPart,
    bindingErrorTerm, not_not] using hcombine

/-- Conditional textbook combiner using the precise rest-created cross-collision
event. This is the form consumed by the final product-bound ROM lemma. -/
theorem bindingTextbookWitnessGame_bound_of_restCreatedEvent_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hrest :
      ∀ (out : BindingOutput M S C depth)
        (cache₁ : QueryCache (Oracle M S C)),
        (out, cache₁) ∈ support
          ((simulateQ cachingOracle
            (bindingWitnessCommitPart (M := M) (S := S) (C := C) A)).run ∅) →
        ¬ CacheHasCollision cache₁ →
          Pr[ fun z =>
            BindingTextbookRestCreatedEvent (M := M) (S := S) (C := C) z |
            (simulateQ cachingOracle
              (bindingTextbookWitnessRest (M := M) (S := S) (C := C)
                cache₁ out)).run cache₁] ≤
            ((((depth + 1) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C)) :
    Pr[ fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  refine
    bindingTextbookWitnessGame_bound_of_rest_win_bound
      (M := M) (S := S) (C := C) A hC ?_
  intro out cache₁ hsupport hnoCollision
  exact le_trans
    (probEvent_mono fun z hz hwin =>
      bindingTextbookWitnessRest_win_implies_restCreatedEvent_of_support
        (M := M) (S := S) (C := C) out cache₁ hz hnoCollision hwin)
    (hrest out cache₁ hsupport hnoCollision)

/-- Conditional textbook binding combiner for the witness-index ROM game.

The remaining hypothesis is exactly the tighter pair-fresh estimate for the two
selected single-check traces under a collision-free adversary cache. -/
theorem binding_bound_of_witnessGame_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hbound :
      Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
        bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
        bindingErrorTerm C depth t) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t :=
  hbound

/-- Textbook-expression wrapper for the witness-index binding game. Once the
ROM proof supplies the exact `bindingErrorTerm` estimate, this corollary is the
formal counterpart of `lemma:mt-binding`. -/
theorem binding_bound_textbook_of_witnessGame_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hlarge : 2 * (depth + 1) ^ 2 ≤ t)
    (hbound :
      Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
        bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
        bindingErrorTerm C depth t) :
    Pr[ fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      (((t ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)) :=
  le_trans
    (binding_bound_of_witnessGame_bound (M := M) (S := S) (C := C) A hbound)
    (bindingErrorTerm_le_textbook (C := C) (depth := depth) (t := t) hlarge)

/-- Exact ROM binding bound for the conditioned witness-index game.

The event includes the textbook rest-phase side conditions recorded in
`BindingTextbookWinROM`; use `binding_bound` below for the unconditional
witness game. -/
theorem binding_bound_conditioned {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t :=
  bindingTextbookWitnessGame_bound_of_restCreatedEvent_bound
    (M := M) (S := S) (C := C) A hC
    (fun out cache₁ _hsupport hnoCollision =>
      bindingTextbookWitnessRest_restCreatedEvent_bound
        (M := M) (S := S) (C := C) out cache₁ hnoCollision)

/-- Compact arithmetic corollary for the conditioned witness-index game. -/
theorem binding_bound_textbook_conditioned {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C)
    (hlarge : 2 * (depth + 1) ^ 2 ≤ t) :
    Pr[fun z => BindingTextbookWinROM (M := M) (S := S) (C := C) z |
      bindingTextbookWitnessGame (M := M) (S := S) (C := C) A] ≤
      (((t ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)) :=
  le_trans
    (binding_bound_conditioned (M := M) (S := S) (C := C) A hC)
    (bindingErrorTerm_le_textbook (C := C) (depth := depth) (t := t) hlarge)

/-- Public unconditional ROM binding bound for the witness-index game.

This theorem covers `BindingWitnessWinROM` directly. It uses the conservative
whole-cache birthday bound, so its error term is intentionally looser than the
conditioned split bound above. -/
theorem binding_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t :=
  binding_bound_wholeCache (M := M) (S := S) (C := C) A hC

/-- Conditional honest-binding combiner once the honest game has been reduced
to a two-opening binding output distribution. -/
theorem honest_binding_bound_of_collision_bound [DecidableEq C]
    [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth : ℕ}
    (f : OracleFn M S C)
    (oa : OracleComp (Oracle M S C) (BindingOutput M S C depth))
    (ε : ℝ≥0∞)
    (hcollision :
      Pr[ fun out =>
        BindingCollisionEvent (M := M) (S := S) (C := C) f out | oa] ≤ ε) :
    Pr[ fun out => BindingWin (M := M) (S := S) (C := C) f out | oa] ≤ ε :=
  binding_bound_of_collision_bound (M := M) (S := S) (C := C) f oa ε hcollision

/-- Honest-binding adversary: first chooses the honest message/salts, then
outputs an alternate opening after seeing the honest commitment and trapdoor. -/
structure HonestBindingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth t : ℕ) where
  choose : OracleComp (Oracle M S C) (Leaves M depth × Leaves S depth × AUX)
  open_ :
    AUX → C → Trapdoor S C depth →
      OracleComp (Oracle M S C) (OpeningData M S C depth)
  tChoose : ℕ
  tOpen : ℕ
  totalBound : tChoose + (2 ^ (depth + 1) - 1) + tOpen ≤ t
  chooseBound : IsTotalQueryBound choose tChoose
  openBound :
    ∀ aux commitment trapdoor,
      IsTotalQueryBound (open_ aux commitment trapdoor) tOpen

private noncomputable def honestBindingAsBindingRun
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : HonestBindingAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C) (BindingOutput M S C depth) := do
  let (messages, salts, aux) ← A.choose
  let (commitment, trapdoor) ←
    commitWithSalts (M := M) (S := S) (C := C) messages salts
  let opening ← A.open_ aux commitment trapdoor
  pure
    { commitment := commitment
      I₀ := opening.I
      I₁ := opening.I
      message₀ := opening.message
      message₁ := Subvector.ofVector messages opening.I
      proof₀ := opening.proof
      proof₁ := «open» (S := S) (C := C) trapdoor opening.I }

private theorem honestBindingAsBindingRun_totalQueryBound
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : HonestBindingAdversary M S C AUX depth t) :
    IsTotalQueryBound
      (honestBindingAsBindingRun (M := M) (S := S) (C := C) A) t := by
  have hraw :
      IsTotalQueryBound
        (honestBindingAsBindingRun (M := M) (S := S) (C := C) A)
        (A.tChoose + ((2 ^ (depth + 1) - 1) + A.tOpen)) := by
    unfold honestBindingAsBindingRun
    refine isTotalQueryBound_bind (n₁ := A.tChoose)
      (n₂ := (2 ^ (depth + 1) - 1) + A.tOpen)
      A.chooseBound ?_
    rintro ⟨messages, salts, aux⟩
    refine isTotalQueryBound_bind (n₁ := 2 ^ (depth + 1) - 1)
      (n₂ := A.tOpen)
      (commitWithSalts_totalQueryBound
        (M := M) (S := S) (C := C) messages salts) ?_
    rintro ⟨commitment, trapdoor⟩
    exact isTotalQueryBound_bind (n₁ := A.tOpen) (n₂ := 0)
      (A.openBound aux commitment trapdoor) fun _ => trivial
  exact hraw.mono (by
    simpa [Nat.add_assoc] using A.totalBound)

private noncomputable def honestBindingAsBindingAdversary
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : HonestBindingAdversary M S C AUX depth t) :
    BindingAdversary M S C depth t where
  run := honestBindingAsBindingRun (M := M) (S := S) (C := C) A
  queryBound := honestBindingAsBindingRun_totalQueryBound
    (M := M) (S := S) (C := C) A

/-- Honest-binding witness game, implemented by packaging the honest opening as
the second branch of the witness binding game. -/
noncomputable def honestBindingGame
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : HonestBindingAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C)
      (BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :=
  bindingWitnessGame (M := M) (S := S) (C := C)
    (honestBindingAsBindingAdversary (M := M) (S := S) (C := C) A)

/-- Honest-binding success for the witness game. -/
def HonestBindingWinROM {depth : ℕ}
    (z : BindingWitnessTranscript M S C depth × QueryCache (Oracle M S C)) : Prop :=
  BindingWitnessWinROM (M := M) (S := S) (C := C) z

/-- Origin-aware honest-binding witness game, using the conditioned textbook
binding transcript surface. -/
noncomputable def honestBindingTextbookGame
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    {depth t : ℕ}
    (A : HonestBindingAdversary M S C AUX depth t) :
    OracleComp (Oracle M S C)
      (BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :=
  bindingTextbookWitnessGame (M := M) (S := S) (C := C)
    (honestBindingAsBindingAdversary (M := M) (S := S) (C := C) A)

/-- Honest-binding success for the conditioned textbook witness game. -/
def HonestBindingTextbookWinROM {depth : ℕ}
    (z : BindingTextbookWitnessTranscript M S C depth × QueryCache (Oracle M S C)) :
    Prop :=
  BindingTextbookWinROM (M := M) (S := S) (C := C) z

/-- Honest-binding fallback currently uses the same witness-index ROM bound after the
honest second opening has been packaged as a binding witness game. -/
theorem honest_binding_bound_witnessAlias {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : BindingAdversary M S C depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => BindingWitnessWinROM (M := M) (S := S) (C := C) z |
      bindingWitnessGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t :=
  binding_bound_wholeCache (M := M) (S := S) (C := C) A hC

/-- Honest-binding bound for the conditioned witness game. -/
theorem honest_binding_bound_conditioned {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : HonestBindingAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => HonestBindingTextbookWinROM (M := M) (S := S) (C := C) z |
      honestBindingTextbookGame (M := M) (S := S) (C := C) A] ≤
      bindingErrorTerm C depth t := by
  simpa [honestBindingTextbookGame, HonestBindingTextbookWinROM] using
    binding_bound_conditioned (M := M) (S := S) (C := C)
      (honestBindingAsBindingAdversary (M := M) (S := S) (C := C) A) hC

/-- Compact arithmetic corollary for the conditioned honest-binding witness
game. -/
theorem honest_binding_bound_textbook_conditioned {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : HonestBindingAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C)
    (hlarge : 2 * (depth + 1) ^ 2 ≤ t) :
    Pr[fun z => HonestBindingTextbookWinROM (M := M) (S := S) (C := C) z |
      honestBindingTextbookGame (M := M) (S := S) (C := C) A] ≤
      (((t ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C)) :=
  le_trans
    (honest_binding_bound_conditioned (M := M) (S := S) (C := C) A hC)
    (bindingErrorTerm_le_textbook (C := C) (depth := depth) (t := t) hlarge)

/-- Public unconditional honest-binding bound for the packaged witness game.

Here `t` already includes the honest `commitWithSalts` cost via
`HonestBindingAdversary.totalBound`; the result is therefore stated with the
same conservative whole-cache term as `binding_bound`. -/
theorem honest_binding_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : HonestBindingAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => HonestBindingWinROM (M := M) (S := S) (C := C) z |
      honestBindingGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t := by
  simpa [honestBindingGame, HonestBindingWinROM] using
    binding_bound (M := M) (S := S) (C := C)
      (honestBindingAsBindingAdversary (M := M) (S := S) (C := C) A) hC

end MerkleTree
