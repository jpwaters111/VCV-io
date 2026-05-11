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
-/
