/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.MultiExtractability.Probability

/-!
# Merkle Commitment Scheme — Multi-Extractability

Public aggregator for the Merkle multi-extractability game definitions and
probability theorems.

## Textbook Correspondence

Textbook statement: multi-extractability asks that extraction succeed for every
commitment selected by the adversary.

Lean event/game: `MerkleTree.multi_extractability_bound` is the simple
stateful selected-witness theorem for `MerkleTree.multiExtractabilityGame`. The
game has one shared commit trace, one selected commitment coordinate, and one
selected mismatching opened index.

Bound expression: the current public term is the union bound
`n * MerkleTree.extractabilityErrorTerm C depth t₁ t₂`. With `d = depth`,
`L = 2^d`, and `|C| = 2^λ`, the tighter textbook macro is
`MTMultiExtractabilityExpression(λ, q, L, d, n) =
  3/2 * (q - 1) * q / 2^λ
  + (d + 1) * 2L / 2^λ
  + (n - 1) * q / 2^λ`.

Scope note: this theorem intentionally does not include the tighter textbook
equal-commitment/different-extracted-tree branch. The pointwise selected
coordinate helper is `MerkleTree.multi_extractability_bound_pointwise`.
-/
