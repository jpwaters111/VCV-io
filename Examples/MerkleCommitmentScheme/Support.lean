/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Examples.MerkleCommitmentScheme.Support.Indexing
import Examples.MerkleCommitmentScheme.Support.Trace
import Examples.MerkleCommitmentScheme.Support.QueryBound
import Examples.MerkleCommitmentScheme.Support.ROM

/-!
# Merkle Commitment Scheme — Support

Public aggregator for Merkle-specific proof support:

* `Indexing` contains arithmetic facts about paths, parents, and siblings;
* `Trace` contains fixed-oracle log-shape facts for Merkle verification;
* `QueryBound` contains public query bounds for Merkle computations;
* `ROM` contains Merkle-specific random-oracle/cache wrappers.

The Merkle scheme does not call the basic one-leaf commitment scheme as an
implementation. It reuses the same generic ROM proof infrastructure developed
for basic commitments: query-bound combinators, cache/log collision predicates,
birthday bounds, and fresh-cache-hit bounds. The Merkle oracle specializes that
infrastructure to two query forms: `Sum.inl (message, salt)` for leaf
commitments and `Sum.inr (left, right)` for internal tree nodes. Quantitative
Merkle bounds then plug tree-specific costs such as `depth + 1` verifier
queries and `min (2 * t + 1, 2^(depth + 1))` known labels into the generic
`1 / |C|` ROM estimates.
-/
