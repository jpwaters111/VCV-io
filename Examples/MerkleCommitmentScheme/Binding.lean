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

/-- Public ROM binding bound currently backed by the unconditional whole-cache
estimate. The sharper textbook term is exposed by `bindingErrorTerm` and the
conditional combiner `binding_bound_of_witnessGame_bound`. -/
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
  binding_bound (M := M) (S := S) (C := C) A hC

/-- Public honest-binding bound for the packaged honest-second-opening game. -/
theorem honest_binding_bound {depth t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : HonestBindingAdversary M S C AUX depth t)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => HonestBindingWinROM (M := M) (S := S) (C := C) z |
      honestBindingGame (M := M) (S := S) (C := C) A] ≤
      bindingWitnessErrorTerm C depth t :=
  binding_bound (M := M) (S := S) (C := C)
    (honestBindingAsBindingAdversary (M := M) (S := S) (C := C) A) hC

end MerkleTree
