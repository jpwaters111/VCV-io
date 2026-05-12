/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Binding.Honest

/-!
# Merkle Commitment Scheme — Binding

Public aggregator for the Merkle binding definitions, query bounds, ROM
probability bounds, and honest-binding reductions.

Relation to basic commitment support: the deterministic binding theorem is
Merkle-specific, but the probability proof reuses the basic commitment support
for `CacheHasCollision`, `LogHasCollision`, birthday estimates, and fresh-hit
estimates. The Merkle layer specializes those generic lemmas to leaf queries
`Sum.inl (message, salt)`, internal queries `Sum.inr (left, right)`, and the
selected verifier path length `depth + 1`.

## Textbook Correspondence

Textbook statement: Merkle binding reduces to a collision between the two
selected authentication paths, after selecting a shared index where the opened
messages differ.

Lean event/game: `MerkleTree.binding_bound` is the unconditional witness-index
ROM theorem for `BindingWitnessWinROM`. It uses the ordinary witness game and
charges all adversary and selected-verifier queries to one cache-collision
event.

Bound expression: with `d = depth` and `|C| = 2^λ`,
`MerkleTree.bindingWitnessErrorTerm C d t` is the conservative whole-cache term
`(t + 2 * (d + 1))^2 / (2 * |C|)`.

Scope note: the textbook split is expressed separately by
`MerkleTree.binding_bound_conditioned`, which bounds the origin-aware event
`BindingTextbookWinROM` by
`t * (t - 1) / (2 * |C|) + (d + 1)^2 / |C|`. The compact textbook macro is
`MTBindingExpression(λ, q) = 1/2 * q^2 / 2^λ`, recovered by
`MerkleTree.binding_bound_textbook_conditioned` as
`MerkleTree.bindingTextbookErrorTerm C q` under the named dominance condition
`MerkleTree.bindingTextbookDominanceThreshold d ≤ q`, i.e.
`q >= 2(d + 1)^2`.
-/
