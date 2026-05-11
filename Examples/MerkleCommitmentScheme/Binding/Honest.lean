/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Binding.Probability
import Examples.MerkleCommitmentScheme.Extractability.Basic

/-!
# Merkle Commitment Scheme — Honest Binding
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- Honest-binding adversary.

Textbook statement: one opening is honestly generated from
`commitWithSalts`, and the adversary tries to produce a conflicting alternate
opening.

Budget note: `t` includes the adversary's `choose` queries, the honest Merkle
commit construction cost `2^(depth + 1) - 1`, and the adversarial `open_`
queries. -/
structure HonestBindingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type)
    (depth t : ℕ) where
  /-- Honest message/salt choice phase. -/
  choose : OracleComp (Oracle M S C) (Leaves M depth × Leaves S depth × AUX)
  /-- Adversarial alternate opening after seeing the honest commitment/trapdoor. -/
  open_ :
    AUX → C → Trapdoor S C depth →
      OracleComp (Oracle M S C) (OpeningData M S C depth)
  /-- Query budget for `choose`. -/
  tChoose : ℕ
  /-- Query budget for `open_`. -/
  tOpen : ℕ
  /-- Total budget. This includes the honest `commitWithSalts` cost
  `2^(depth + 1) - 1`, so the public bounds are stated directly in terms of
  `t`. -/
  totalBound : tChoose + (2 ^ (depth + 1) - 1) + tOpen ≤ t
  /-- Query-bound certificate for `choose`. -/
  chooseBound : IsTotalQueryBound choose tChoose
  /-- Query-bound certificate for `open_`. -/
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

/-- Textbook split honest-binding bound for the origin-aware witness game.

Textbook statement: honest Merkle binding with one honest opening and one
alternate adversarial opening.

Lean event/game: `HonestBindingTextbookWinROM` in
`honestBindingTextbookGame`, after packaging the honest opening as the second
binding branch.

Bound expression: `bindingErrorTerm C depth t`.

Scope note: the budget `t` already includes the honest Merkle commit
construction. -/
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

/-- Compact textbook arithmetic corollary for the conditioned honest-binding
witness game.

Lean event/game: same conditioned event as
`honest_binding_bound_conditioned`.

Bound expression: `t^2 / (2 * |C|)` under
`2 * (depth + 1)^2 <= t`.

Scope note: the budget `t` includes the honest commit cost. -/
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

Textbook statement: honest Merkle binding in the ROM, packaged as a binding
witness game.

Lean event/game: `HonestBindingWinROM` in `honestBindingGame`.

Bound expression: `bindingWitnessErrorTerm C depth t`, the conservative
whole-cache term from `binding_bound`.

Scope note: `t` already includes the honest `commitWithSalts` cost via
`HonestBindingAdversary.totalBound`. -/
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
