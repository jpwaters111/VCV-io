/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.MultiExtractability.Basic

/-!
# Merkle Commitment Scheme — Multi-Extractability Query Bounds

Query-bound packaging for projections from the stateful multi-extractability
game to the single-commitment witness game.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace MerkleTree

variable {M S C AUX : Type}

/-- Project a stateful multi adversary onto a fixed commitment coordinate. The
projected adversary preserves the shared commit phase and returns an empty
opening unless the multi adversary selected the projected coordinate. -/
noncomputable def projectMultiExtractAdversary
    [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Inhabited M] [Inhabited S] [Inhabited C]
    {depth n t : ℕ}
    (A : MultiExtractAdversary M S C AUX depth n t) (k : Fin n) :
    ExtractAdversary M S C ((Fin n → C) × AUX) depth t where
  commit := do
    let out ← A.commit
    pure (out.1 k, out)
  open_ := fun out => do
    let opening ← A.open_ out.2
    if opening.1 = k then
      pure opening.2
    else
      pure (emptyOpeningData (M := M) (S := S) (C := C) (depth := depth))
  t₁ := A.t₁
  t₂ := A.t₂
  totalBound := A.totalBound
  commitBound := by
    exact isTotalQueryBound_bind (n₁ := A.t₁) (n₂ := 0)
      A.commitBound (fun _ => trivial)
  openBound := by
    intro out
    exact isTotalQueryBound_bind (n₁ := A.t₂) (n₂ := 0)
      (A.openBound out.2) (fun _ => by
        split <;> trivial)

end MerkleTree
