/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Collision
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
bounds fixed-oracle Merkle binding wins. -/
theorem binding_bound [DecidableEq C]
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

/-- The honest-binding corollary has the same proof shape once the honest game
has been reduced to a two-opening binding output distribution. -/
theorem honest_binding_bound [DecidableEq C]
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
  binding_bound (M := M) (S := S) (C := C) f oa ε hcollision

end MerkleTree
