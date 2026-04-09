/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support
import Examples.MerkleCommitmentScheme.Completeness

/-!
# Merkle Commitment Scheme — Collision Workspace

This module collects the support needed for the textbook collision lemmas.

The refactor in this turn lands the ingredients those proofs need:

- typed leaf/internal random-oracle queries in `MTOracle`
- fixed-index-set proof families `MTProof`
- pointwise path and sibling indexing in `Support/Indexing`
- deterministic logged evaluation and `CrossLogCollision` in `Support/Trace`
- single and batch query bounds in `Support/QueryBound`

The actual single-leaf and general collision theorems can now be stated and
proved against these interfaces without revisiting the representation choices in
`Common`.
-/
