/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Extractability.Probability

/-!
# Merkle Commitment Scheme — Extractability

Public aggregator for the Merkle extractability definitions, deterministic
reconstruction lemmas, query bounds, and ROM probability theorems.

Relation to basic commitment support: the extractor and partial-tree
reconstruction are Merkle-specific, but the ROM proof uses the same generic
cache/logging machinery as the basic commitment scheme. Leaf commitments are
represented by `Sum.inl (message, salt)` oracle queries, while internal Merkle
labels use `Sum.inr (left, right)`; generic fresh-hit and birthday bounds are
then specialized to the Merkle answer space `C`.

## Textbook Correspondence

Textbook statement: single-commitment Merkle extractability in the random-oracle
model.

Lean event/game: `MerkleTree.extractability_bound` is stated for the
selected-witness game `MerkleTree.extractabilityWitnessGame`. The adversary may
open a batch, but the game selects one mismatching opened index and logs only
that `checkSingle` verifier path.

Bound expression: with `d = depth` and `|C| = 2^λ`, Lean proves the
selected-witness term
`t₁^2 / (2 * |C|) + (t₂ + d + 1) * min (2 * t₁ + 1, 2^(d + 1)) / |C|`.
The textbook full-batch macro is
`MTExtractabilityExpression(λ, q, L, d) =
  1/2 * (q - 1) * q / 2^λ + (d + 1) * 2L / 2^λ`.

Scope note: this public theorem is the selected-witness ROM theorem. The
full-batch theorem surface is the conditional combiner
`MerkleTree.extractability_bound_of_textbook_badEvent_bound`, which requires a
separate bad-event estimate for the full batch experiment.
-/
