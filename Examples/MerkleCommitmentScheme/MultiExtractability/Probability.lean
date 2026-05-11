/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.MultiExtractability.QueryBound
import Examples.MerkleCommitmentScheme.Extractability.Probability
import Examples.CommitmentScheme.Support.Probability

/-!
# Merkle Commitment Scheme — Multi-Extractability Probability Bounds
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

private theorem witnessExtractabilityWinROM_none_false
    [DecidableEq S] [DecidableEq C]
    {depth : ℕ} [Inhabited M] [Inhabited S] [Inhabited C]
    {base : ExtractTranscript M S C AUX depth}
    {cache : QueryCache (Oracle M S C)} :
    ¬ WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
      (({ base := base, witness? := none, singleCheck? := none } :
        WitnessExtractTranscript M S C AUX depth), cache) := by
  rintro ⟨i, hsome, _⟩
  cases hsome

private theorem selectWitness?_congr_aux_openTrace
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {AUX₁ AUX₂ : Type} {depth : ℕ}
    (commitment : C) (aux₁ : AUX₁) (aux₂ : AUX₂)
    (commitTrace openTrace₁ openTrace₂ : QueryLog (Oracle M S C))
    (opening : OpeningData M S C depth) :
    selectWitness? (M := M) (S := S) (C := C)
      ({ commitment := commitment
         aux := aux₁
         commitTrace := commitTrace
         opening := opening
         openTrace := openTrace₁ } : ExtractTranscript M S C AUX₁ depth) =
    selectWitness? (M := M) (S := S) (C := C)
      ({ commitment := commitment
         aux := aux₂
         commitTrace := commitTrace
         opening := opening
         openTrace := openTrace₂ } : ExtractTranscript M S C AUX₂ depth) := by
  simp [selectWitness?, extractedOutputOfTranscript]

private theorem witnessWinROM_congr_aux_openTrace_singleCheck
    [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {AUX₁ AUX₂ : Type} {depth : ℕ}
    (commitment : C) (aux₁ : AUX₁) (aux₂ : AUX₂)
    (commitTrace openTrace₁ openTrace₂ : QueryLog (Oracle M S C))
    (opening : OpeningData M S C depth)
    (witness? : Option {i // i ∈ opening.I})
    (single₁? single₂? : Option (Bool × QueryLog (Oracle M S C)))
    (cache : QueryCache (Oracle M S C)) :
    WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
      (({ base :=
            { commitment := commitment
              aux := aux₁
              commitTrace := commitTrace
              opening := opening
              openTrace := openTrace₁ }
          witness? := witness?
          singleCheck? := single₁? } :
        WitnessExtractTranscript M S C AUX₁ depth), cache) ↔
    WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
      (({ base :=
            { commitment := commitment
              aux := aux₂
              commitTrace := commitTrace
              opening := opening
              openTrace := openTrace₂ }
          witness? := witness?
          singleCheck? := single₂? } :
        WitnessExtractTranscript M S C AUX₂ depth), cache) := by
  simp [WitnessExtractabilityWinROM, WitnessExtractabilityWin,
    WitnessMismatch, extractedOutputOfTranscript]

private noncomputable def multiExtractabilityWitnessCommitPart {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t) :
    OracleComp (Oracle M S C) (((Fin n → C) × AUX) × QueryLog (Oracle M S C)) :=
  (simulateQ loggingOracle A.commit).run

private noncomputable def multiExtractabilityStatefulWitnessRest
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t)
    (out : (Fin n → C) × AUX) (commitTrace : QueryLog (Oracle M S C)) :
    OracleComp (Oracle M S C)
      (MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n) := do
  let commitments := out.1
  let aux := out.2
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

private noncomputable def projectedWitnessRest
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t) (k : Fin n)
    (out : (Fin n → C) × AUX) (commitTrace : QueryLog (Oracle M S C)) :
    OracleComp (Oracle M S C)
      (WitnessExtractTranscript M S C ((Fin n → C) × AUX) depth) := do
  let (opening, openTrace) ← (simulateQ loggingOracle (A.open_ out.2)).run
  let openingForK :=
    if opening.1 = k then
      opening.2
    else
      emptyOpeningData (M := M) (S := S) (C := C) (depth := depth)
  let openTrace := openTrace ++ []
  let base : ExtractTranscript M S C ((Fin n → C) × AUX) depth :=
    { commitment := out.1 k
      aux := out
      commitTrace := commitTrace
      opening := openingForK
      openTrace := openTrace }
  match selectWitness? (M := M) (S := S) (C := C) base with
  | none =>
      pure { base := base, witness? := none, singleCheck? := none }
  | some i =>
      let single ←
        (simulateQ loggingOracle
          (checkSingle (M := M) (S := S) (C := C)
            (out.1 k) i.1 (openingForK.message i) (openingForK.proof i))).run
      pure { base := base, witness? := some i, singleCheck? := some single }

private theorem multiExtractabilityStatefulWitnessInner_eq_bind {depth n t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t) :
    multiExtractabilityStatefulWitnessInner (M := M) (S := S) (C := C) A =
      multiExtractabilityWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun x =>
        multiExtractabilityStatefulWitnessRest (M := M) (S := S) (C := C)
          A x.1 x.2 := by
  rfl

private theorem projectedWitnessInner_eq_bind {depth n t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t) (k : Fin n) :
    extractabilityWitnessInner (M := M) (S := S) (C := C)
        (projectMultiExtractAdversary (M := M) (S := S) (C := C) A k) =
      multiExtractabilityWitnessCommitPart (M := M) (S := S) (C := C) A >>= fun x =>
        projectedWitnessRest (M := M) (S := S) (C := C) A k x.1 x.2 := by
  unfold extractabilityWitnessInner projectMultiExtractAdversary
    multiExtractabilityWitnessCommitPart projectedWitnessRest
  simp only [simulateQ_bind, simulateQ_pure, WriterT.run_bind',
    WriterT.run_pure', map_pure, pure_bind, bind_assoc,
    map_eq_bind_pure_comp]
  simp [Prod.map]
  apply bind_congr
  intro x
  apply bind_congr
  intro x₁
  by_cases hsel : x₁.1.1 = k
  · repeat rw [if_pos hsel]
    simp only [WriterT.run_pure', pure_bind]
    cases h :
        selectWitness? (M := M) (S := S) (C := C)
          ({ commitment := x.1.1 k
             aux := x.1
             commitTrace := x.2
             opening := x₁.1.2
             openTrace := x₁.2 ++ [] } :
            ExtractTranscript M S C ((Fin n → C) × AUX) depth) with
    | none => rfl
    | some i => simp [h, map_eq_bind_pure_comp]
  · repeat rw [if_neg hsel]
    simp only [WriterT.run_pure', pure_bind]
    cases h :
        selectWitness? (M := M) (S := S) (C := C)
          ({ commitment := x.1.1 k
             aux := x.1
             commitTrace := x.2
             opening := emptyOpeningData (M := M) (S := S) (C := C) (depth := depth)
             openTrace := x₁.2 ++ [] } :
            ExtractTranscript M S C ((Fin n → C) × AUX) depth) with
    | none => rfl
    | some i => simp [h, map_eq_bind_pure_comp]

/-- A stateful win belongs to the branch selected by its transcript. -/
private theorem stateful_win_implies_exists_selected {depth n : ℕ}
    [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (z :
      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
        QueryCache (Oracle M S C)) :
    MultiExtractabilityStatefulWitnessWinROM (M := M) (S := S) (C := C) z →
      ∃ k : Fin n, StatefulSelectedWin (M := M) (S := S) (C := C)
        (AUX := AUX) k z := by
  intro hwin
  exact ⟨z.1.opening.1, rfl, hwin⟩

/-- The selected branch for coordinate `k` is bounded by the ordinary witness
game for the projected single-commitment adversary. -/
private theorem stateful_selected_branch_le_projected_witnessGame {depth n t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t) (k : Fin n) :
    Pr[fun z => StatefulSelectedWin (M := M) (S := S) (C := C)
        (AUX := AUX) k z |
      multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A] ≤
    Pr[fun z => WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z |
      extractabilityWitnessGame (M := M) (S := S) (C := C)
        (projectMultiExtractAdversary (M := M) (S := S) (C := C) A k)] := by
  classical
  unfold multiExtractabilityStatefulWitnessGame extractabilityWitnessGame
  rw [multiExtractabilityStatefulWitnessInner_eq_bind
      (M := M) (S := S) (C := C) A,
    projectedWitnessInner_eq_bind
      (M := M) (S := S) (C := C) A k]
  simp only [simulateQ_bind, StateT.run_bind]
  apply OracleComp.probEvent_bind_mono_hetero
  intro p
  unfold multiExtractabilityStatefulWitnessRest projectedWitnessRest StatefulSelectedWin
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure]
  apply OracleComp.probEvent_bind_mono_hetero
  intro p₁
  rcases p₁ with ⟨⟨⟨k', opening⟩, openTrace⟩, cache₂⟩
  by_cases hsel : k' = k
  · subst k'
    have hkk : k = k := rfl
    let base₀ : ExtractTranscript M S C AUX depth :=
      { commitment := p.1.1.1 k
        aux := p.1.1.2
        commitTrace := p.1.2
        opening := opening
        openTrace := openTrace }
    let base₁ : ExtractTranscript M S C ((Fin n → C) × AUX) depth :=
      { commitment := p.1.1.1 k
        aux := p.1.1
        commitTrace := p.1.2
        opening := opening
        openTrace := openTrace ++ [] }
    have hselect :
        selectWitness? (M := M) (S := S) (C := C) base₁ =
          selectWitness? (M := M) (S := S) (C := C) base₀ := by
      simpa [base₀, base₁, List.append_nil] using
        (selectWitness?_congr_aux_openTrace
          (M := M) (S := S) (C := C)
          (commitment := p.1.1.1 k) (aux₁ := p.1.1)
          (aux₂ := p.1.1.2) (commitTrace := p.1.2)
          (openTrace₁ := openTrace ++ []) (openTrace₂ := openTrace)
          (opening := opening))
    repeat rw [if_pos hkk]
    cases hw : selectWitness? (M := M) (S := S) (C := C) base₀ with
    | none =>
        have hw₁ :
            selectWitness? (M := M) (S := S) (C := C) base₁ = none := by
          calc
            selectWitness? (M := M) (S := S) (C := C) base₁ =
                selectWitness? (M := M) (S := S) (C := C) base₀ := hselect
            _ = none := hw
        have hbaseIf :
            ({ commitment := p.1.1.1 k
               aux := p.1.1
               commitTrace := p.1.2
               opening := if k = k then opening else
                 emptyOpeningData (M := M) (S := S) (C := C) (depth := depth)
               openTrace := openTrace ++ [] } :
              ExtractTranscript M S C ((Fin n → C) × AUX) depth) = base₁ := by
          simp [base₁]
        have hwIf :
            selectWitness? (M := M) (S := S) (C := C)
              ({ commitment := p.1.1.1 k
                 aux := p.1.1
                 commitTrace := p.1.2
                 opening := if k = k then opening else
                   emptyOpeningData (M := M) (S := S) (C := C) (depth := depth)
                 openTrace := openTrace ++ [] } :
                ExtractTranscript M S C ((Fin n → C) × AUX) depth) = none := by
          rw [hbaseIf]
          exact hw₁
        have hleftWin :
            ¬ MultiExtractabilityStatefulWitnessWinROM (M := M) (S := S) (C := C)
              (({ commitments := p.1.1.1
                  aux := p.1.1.2
                  commitTrace := p.1.2
                  opening := ⟨k, opening⟩
                  openTrace := openTrace
                  witness? := none
                  singleCheck? := none } :
                MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n),
                cache₂) := by
          intro h
          exact witnessExtractabilityWinROM_none_false
            (M := M) (S := S) (C := C) (AUX := AUX) (cache := cache₂)
            (by
              simpa [MultiExtractabilityStatefulWitnessWinROM,
                MultiExtractabilityStatefulWitnessTranscript.toWitnessTranscript]
                using h)
        have hrightPred :
            ¬ WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
              (({ base :=
                    { commitment := p.1.1.1 k
                      aux := p.1.1
                      commitTrace := p.1.2
                      opening := if k = k then opening else
                        emptyOpeningData (M := M) (S := S) (C := C) (depth := depth)
                      openTrace := openTrace ++ [] }
                  witness? := none
                  singleCheck? := none } :
                WitnessExtractTranscript M S C ((Fin n → C) × AUX) depth),
                cache₂) :=
          witnessExtractabilityWinROM_none_false
            (M := M) (S := S) (C := C)
            (AUX := ((Fin n → C) × AUX)) (cache := cache₂)
        simp [simulateQ_pure, StateT.run_pure, hw₁, hleftWin, hrightPred]
    | some i =>
        have hw₁ :
            selectWitness? (M := M) (S := S) (C := C) base₁ = some i := by
          calc
            selectWitness? (M := M) (S := S) (C := C) base₁ =
                selectWitness? (M := M) (S := S) (C := C) base₀ := hselect
            _ = some i := hw
        have hbaseIf :
            ({ commitment := p.1.1.1 k
               aux := p.1.1
               commitTrace := p.1.2
               opening := if k = k then opening else
                 emptyOpeningData (M := M) (S := S) (C := C) (depth := depth)
               openTrace := openTrace ++ [] } :
              ExtractTranscript M S C ((Fin n → C) × AUX) depth) = base₁ := by
          simp [base₁]
        simp [hw₁, simulateQ_bind, StateT.run_bind,
          map_eq_bind_pure_comp]
        have hprob :=
          OracleComp.probEvent_bind_congr_hetero
            (mx :=
              (simulateQ cachingOracle
                (simulateQ loggingOracle
                  (checkSingle (M := M) (S := S) (C := C)
                    (p.1.1.1 k) i.1 (opening.message i) (opening.proof i))).run).run
                cache₂)
            (my := fun single => pure
              (({ commitments := p.1.1.1
                  aux := p.1.1.2
                  commitTrace := p.1.2
                  opening := ⟨k, opening⟩
                  openTrace := openTrace
                  witness? := some i
                  singleCheck? := some single.1 },
                single.2) :
                MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
                  QueryCache (Oracle M S C)))
            (mz := fun single => pure
              (({ base :=
                    { commitment := p.1.1.1 k
                      aux := p.1.1
                      commitTrace := p.1.2
                      opening := opening
                      openTrace := openTrace ++ [] }
                  witness? := some i
                  singleCheck? := some single.1 },
                single.2) :
                WitnessExtractTranscript M S C ((Fin n → C) × AUX) depth ×
                  QueryCache (Oracle M S C)))
            (p := fun z =>
              StatefulSelectedWin (M := M) (S := S) (C := C)
                (AUX := AUX) k z)
            (q := fun z =>
              WitnessExtractabilityWinROM (M := M) (S := S) (C := C) z)
            (by
              intro z
              rcases z with ⟨single, cache⟩
              rw [probEvent_pure, probEvent_pure]
              have hiff :
                  StatefulSelectedWin (M := M) (S := S) (C := C)
                    (AUX := AUX) k
                    (({ commitments := p.1.1.1
                        aux := p.1.1.2
                        commitTrace := p.1.2
                        opening := ⟨k, opening⟩
                        openTrace := openTrace
                        witness? := some i
                        singleCheck? := some single },
                      cache) :
                      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
                        QueryCache (Oracle M S C)) ↔
                  WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
                    (({ base :=
                          { commitment := p.1.1.1 k
                            aux := p.1.1
                            commitTrace := p.1.2
                            opening := opening
                            openTrace := openTrace ++ [] }
                        witness? := some i
                        singleCheck? := some single },
                      cache) :
                      WitnessExtractTranscript M S C ((Fin n → C) × AUX) depth ×
                        QueryCache (Oracle M S C)) := by
                simpa [StatefulSelectedWin,
                  MultiExtractabilityStatefulWitnessWinROM,
                  MultiExtractabilityStatefulWitnessTranscript.toWitnessTranscript] using
                  (witnessWinROM_congr_aux_openTrace_singleCheck
                    (M := M) (S := S) (C := C)
                    (commitment := p.1.1.1 k)
                    (aux₁ := p.1.1.2) (aux₂ := p.1.1)
                    (commitTrace := p.1.2)
                    (openTrace₁ := openTrace) (openTrace₂ := openTrace ++ [])
                    (opening := opening) (witness? := some i)
                    (single₁? := some single) (single₂? := some single)
                    (cache := cache))
              by_cases hleft :
                  StatefulSelectedWin (M := M) (S := S) (C := C)
                    (AUX := AUX) k
                    (({ commitments := p.1.1.1
                        aux := p.1.1.2
                        commitTrace := p.1.2
                        opening := ⟨k, opening⟩
                        openTrace := openTrace
                        witness? := some i
                        singleCheck? := some single },
                      cache) :
                      MultiExtractabilityStatefulWitnessTranscript M S C AUX depth n ×
                        QueryCache (Oracle M S C))
              · have hright := hiff.mp hleft
                simp [hleft, hright]
              · have hright : ¬ WitnessExtractabilityWinROM (M := M) (S := S) (C := C)
                    (({ base :=
                          { commitment := p.1.1.1 k
                            aux := p.1.1
                            commitTrace := p.1.2
                            opening := opening
                            openTrace := openTrace ++ [] }
                        witness? := some i
                        singleCheck? := some single },
                      cache) :
                      WitnessExtractTranscript M S C ((Fin n → C) × AUX) depth ×
                        QueryCache (Oracle M S C)) := fun h => hleft (hiff.mpr h)
                simp [hleft, hright])
        exact le_of_eq (by
          simpa [StatefulSelectedWin, base₁, hw₁, map_eq_bind_pure_comp] using hprob)
  · trans 0
    · simp [StatefulSelectedWin]
      intro a b hz hfst _
      cases hw :
          selectWitness? (M := M) (S := S) (C := C)
            ({ commitment := p.1.1.1 k'
               aux := p.1.1.2
               commitTrace := p.1.2
               opening := opening
               openTrace := openTrace } :
              ExtractTranscript M S C AUX depth) with
      | none =>
          simp [hw, simulateQ_pure, StateT.run_pure] at hz
          rcases hz with ⟨ha, _hb⟩
          rw [ha] at hfst
          exact hsel hfst
      | some i =>
          simp [hw, map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind,
            support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
          rcases hz with ⟨single, hsingle, _hpair⟩ | ⟨single, hsingle, _hpair⟩
          · rw [hsingle] at hfst
            exact hsel hfst
          · rw [hsingle] at hfst
            exact hsel hfst
    · exact zero_le _

/-- Each selected branch of the stateful game is bounded by the corresponding
single-commitment witness extractability error. -/
private theorem stateful_selected_branch_bound {depth n t : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t) (k : Fin n)
    (hC : 0 < Fintype.card C) :
    Pr[fun z => StatefulSelectedWin (M := M) (S := S) (C := C)
        (AUX := AUX) k z |
      multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A] ≤
      extractabilityErrorTerm C depth A.t₁ A.t₂ := by
  have hsingle :=
    extractability_bound (M := M) (S := S) (C := C)
      (A := projectMultiExtractAdversary (M := M) (S := S) (C := C) A k) hC
  exact le_trans
    (stateful_selected_branch_le_projected_witnessGame
      (M := M) (S := S) (C := C) (AUX := AUX) A k)
    (by simpa [projectMultiExtractAdversary] using hsingle)

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

This is a conditional helper for the simple union-bound error term. -/
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
family. This remains as a fallback helper; the public final theorem below uses
the stateful shared-commit witness game. -/
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

/-- A stateful multi win is bounded by the sum of its selected-coordinate
branches.

Textbook statement: multi failure is bounded by a union over selected
commitment coordinates.

Lean event/game: `MultiExtractabilityWinROM` in `multiExtractabilityGame` is
covered by the union of `MultiExtractabilitySelectedWinROM k` over `Fin n`.

Scope note: this is the union-bound step used by the simple public theorem. -/
theorem multi_extractability_win_le_selected_sum {depth t n : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t) :
    Pr[MultiExtractabilityWinROM (M := M) (S := S) (C := C) |
      multiExtractabilityGame (M := M) (S := S) (C := C) A] ≤
    ∑ k ∈ (Finset.univ : Finset (Fin n)),
      Pr[MultiExtractabilitySelectedWinROM (M := M) (S := S) (C := C)
        (AUX := AUX) k |
        multiExtractabilityGame (M := M) (S := S) (C := C) A] := by
  classical
  change
    Pr[fun z =>
      MultiExtractabilityStatefulWitnessWinROM (M := M) (S := S) (C := C) z |
      multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A] ≤
    ∑ k ∈ (Finset.univ : Finset (Fin n)),
      Pr[fun z =>
        StatefulSelectedWin (M := M) (S := S) (C := C) (AUX := AUX) k z |
        multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A]
  let game :=
    multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A
  calc
    Pr[fun z =>
      MultiExtractabilityStatefulWitnessWinROM (M := M) (S := S) (C := C) z |
      multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A]
        ≤ Pr[fun z => ∃ k : Fin n,
          StatefulSelectedWin (M := M) (S := S) (C := C) (AUX := AUX) k z |
          game] := by
            simpa [game] using
              (probEvent_mono fun z _ hz =>
                stateful_win_implies_exists_selected (M := M) (S := S) (C := C)
                  (AUX := AUX) z hz)
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)),
        Pr[fun z =>
          StatefulSelectedWin (M := M) (S := S) (C := C) (AUX := AUX) k z |
          game] := by
            simpa using
              (probEvent_exists_finset_le_sum (s := (Finset.univ : Finset (Fin n)))
                (mx := game)
                (E := fun k z =>
                  StatefulSelectedWin (M := M) (S := S) (C := C) (AUX := AUX) k z))
    _ = ∑ k ∈ (Finset.univ : Finset (Fin n)),
        Pr[fun z =>
          StatefulSelectedWin (M := M) (S := S) (C := C) (AUX := AUX) k z |
          multiExtractabilityStatefulWitnessGame (M := M) (S := S) (C := C) A] := by
            rfl

private theorem multi_extractability_bound_stateful {depth t n : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t)
    (hC : 0 < Fintype.card C) :
    Pr[MultiExtractabilityWinROM (M := M) (S := S) (C := C) |
      multiExtractabilityGame (M := M) (S := S) (C := C) A] ≤
      multiExtractabilityErrorTerm C depth A.t₁ A.t₂ n := by
  calc
    Pr[MultiExtractabilityWinROM (M := M) (S := S) (C := C) |
      multiExtractabilityGame (M := M) (S := S) (C := C) A]
        ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)),
            Pr[MultiExtractabilitySelectedWinROM (M := M) (S := S) (C := C)
              (AUX := AUX) k |
              multiExtractabilityGame (M := M) (S := S) (C := C) A] :=
          multi_extractability_win_le_selected_sum (M := M) (S := S) (C := C) A
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)),
        extractabilityErrorTerm C depth A.t₁ A.t₂ := by
          exact Finset.sum_le_sum fun k _hk => by
            simpa [multiExtractabilityGame, MultiExtractabilitySelectedWinROM] using
              stateful_selected_branch_bound (M := M) (S := S) (C := C)
                (AUX := AUX) A k hC
    _ = multiExtractabilityErrorTerm C depth A.t₁ A.t₂ n := by
        simp [multiExtractabilityErrorTerm]

/-- Simple multi-extractability estimate for the selected-witness ROM game.

Textbook statement: selected-coordinate multi-extractability by union bound.

Lean event/game: `MultiExtractabilityWinROM` in `multiExtractabilityGame`.

Bound expression: `multiExtractabilityErrorTerm C depth A.t₁ A.t₂ n`, namely
`n * extractabilityErrorTerm C depth A.t₁ A.t₂`.

Textbook comparison: with `d = depth`, `L = 2^d`, and `|C| = 2^λ`,
`MTMultiExtractabilityExpression(λ, q, L, d, n) =
  3/2 * (q - 1) * q / 2^λ
  + (d + 1) * 2L / 2^λ
  + (n - 1) * q / 2^λ`.

Scope note: the event is the selected opening failure for the commitment chosen
by the adversary. It explicitly does not include the tighter textbook
equal-commitment/different-extracted-tree branch. -/
theorem multi_extractability_bound {depth t n : ℕ}
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype M] [Fintype S] [Fintype C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    (A : MultiExtractAdversary M S C AUX depth n t)
    (hC : 0 < Fintype.card C) :
    Pr[MultiExtractabilityWinROM (M := M) (S := S) (C := C) |
      multiExtractabilityGame (M := M) (S := S) (C := C) A] ≤
      multiExtractabilityErrorTerm C depth A.t₁ A.t₂ n := by
  exact multi_extractability_bound_stateful (M := M) (S := S) (C := C) A hC

end MerkleTree
