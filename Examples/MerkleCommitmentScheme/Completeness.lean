/-
Copyright (c) 2026 OpenAI Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Examples.MerkleCommitmentScheme.Support

/-!
# Merkle Commitment Scheme — Completeness Workspace

This module hosts the completeness-facing support imported by downstream proof
files. The core proof-oriented refactor lives in `Common` and
`Support/*`; the actual completeness theorems can now be developed against:

- fixed-index-set batch openings `MTOpen`
- fixed-index-set batch verification `MTCheck`
- pointwise path/copath accessors from `Support/Indexing`
- fixed-oracle evaluation `MTEval` and trace predicates from `Support/Trace`
- total-query-bound lemmas from `Support/QueryBound`

The current turn focuses on landing that proof-oriented API and support layer in
a compile-clean state.
-/
