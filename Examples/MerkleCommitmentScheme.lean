/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Examples.MerkleCommitmentScheme.Common
import Examples.MerkleCommitmentScheme.Support
import Examples.MerkleCommitmentScheme.Completeness
import Examples.MerkleCommitmentScheme.Collision
import Examples.MerkleCommitmentScheme.Extractability
import Examples.MerkleCommitmentScheme.Binding
import Examples.MerkleCommitmentScheme.MultiExtractability

/-!
# Merkle Commitment Scheme

Public aggregator for the Merkle commitment construction and security proofs.

The deterministic stack is `Common`, `Completeness`, and `Collision`.
The probability-facing security surface is:

* `MerkleTree.extractability_bound`, using `MerkleTree.extractabilityErrorTerm`;
* `MerkleTree.binding_bound`, using `MerkleTree.bindingWitnessErrorTerm`;
* `MerkleTree.binding_bound_conditioned`, using `MerkleTree.bindingErrorTerm`;
* `MerkleTree.multi_extractability_bound`, using
  `MerkleTree.multiExtractabilityErrorTerm`.
-/
