/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Common
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Merkle Commitment Scheme — Trace Support

Deterministic evaluation helpers for Merkle computations against a fixed oracle
function, together with log-level collision predicates used in the textbook
collision lemmas.
-/

open OracleComp OracleSpec

variable {M S C α β : Type}

/-- A fixed oracle function for the Merkle oracle specification. -/
abbrev MTOracleFn (M : Type) (S : Type) (C : Type) :=
  (t : (MTOracle M S C).Domain) → (MTOracle M S C).Range t

/-- Evaluate a Merkle oracle computation against a fixed oracle function. -/
def MTEval (f : MTOracleFn M S C) (oa : OracleComp (MTOracle M S C) α) : α :=
  simulateQ (QueryImpl.ofFn f) oa

/-- Evaluate a Merkle oracle computation against a fixed oracle function while
recording its query-answer trace. -/
def MTLogEval (f : MTOracleFn M S C) (oa : OracleComp (MTOracle M S C) α) :
    α × QueryLog (MTOracle M S C) :=
  (simulateQ ((QueryImpl.ofFn f).withLogging) oa).run

/-- Every entry of `small` also occurs in `big`. -/
def LogContains {ι : Type} {spec : OracleSpec ι} (small big : QueryLog spec) : Prop :=
  ∀ entry, entry ∈ small → entry ∈ big

namespace LogContains

variable {ι : Type} {spec : OracleSpec ι}

theorem refl (log : QueryLog spec) : LogContains log log := fun _ h => h

theorem trans {l₀ l₁ l₂ : QueryLog spec}
    (h₀₁ : LogContains l₀ l₁) (h₁₂ : LogContains l₁ l₂) :
    LogContains l₀ l₂ := fun entry h => h₁₂ _ (h₀₁ _ h)

theorem append_left (left right : QueryLog spec) : LogContains left (left ++ right) :=
  fun entry h => List.mem_append.mpr (.inl h)

theorem append_right (left right : QueryLog spec) : LogContains right (left ++ right) :=
  fun entry h => List.mem_append.mpr (.inr h)

end LogContains

/-- Two traces have a cross-collision if they contain distinct queries with the
same answer. -/
def CrossLogCollision {ι : Type} {spec : OracleSpec ι} (log₀ log₁ : QueryLog spec) : Prop :=
  ∃ entry₀ ∈ log₀, ∃ entry₁ ∈ log₁, entry₀.1 ≠ entry₁.1 ∧ HEq entry₀.2 entry₁.2

namespace CrossLogCollision

variable {ι : Type} {spec : OracleSpec ι}

theorem mono {log₀ log₀' log₁ log₁' : QueryLog spec}
    (h₀ : LogContains log₀ log₀') (h₁ : LogContains log₁ log₁') :
    CrossLogCollision log₀ log₁ → CrossLogCollision log₀' log₁' := by
  rintro ⟨entry₀, hentry₀, entry₁, hentry₁, hne, heq⟩
  exact ⟨entry₀, h₀ _ hentry₀, entry₁, h₁ _ hentry₁, hne, heq⟩

end CrossLogCollision

@[simp] theorem MTEval_query (f : MTOracleFn M S C) (t : (MTOracle M S C).Domain) :
    MTEval f (liftM (query (spec := MTOracle M S C) t)) = f t := rfl

@[simp] theorem MTEval_pure (f : MTOracleFn M S C) (x : α) :
    MTEval f (pure x : OracleComp (MTOracle M S C) α) = x := rfl

@[simp] theorem MTEval_bind (f : MTOracleFn M S C) (oa : OracleComp (MTOracle M S C) α)
    (ob : α → OracleComp (MTOracle M S C) β) :
    MTEval f (oa >>= ob) = MTEval f (ob (MTEval f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rfl
  | query_bind t oa ih =>
      simpa [MTEval, simulateQ_bind] using ih (f t)

@[simp] theorem MTLogEval_query (f : MTOracleFn M S C) (t : (MTOracle M S C).Domain) :
    MTLogEval f (liftM (query (spec := MTOracle M S C) t)) = (f t, [⟨t, f t⟩]) := rfl

@[simp] theorem MTLogEval_pure (f : MTOracleFn M S C) (x : α) :
    MTLogEval f (pure x : OracleComp (MTOracle M S C) α) = (x, []) := rfl
