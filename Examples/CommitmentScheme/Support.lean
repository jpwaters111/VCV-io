/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, jpwaters
-/
import Examples.CommitmentScheme.Support.MainCompat
import Examples.CommitmentScheme.Support.QueryBound
import Examples.CommitmentScheme.Support.Probability
import Examples.CommitmentScheme.Support.Cache
import Examples.CommitmentScheme.Support.Logging
import Examples.CommitmentScheme.Support.Collision

/-!
# Basic Commitment Scheme — Support

Public aggregator for reusable ROM support used by the basic and Merkle
commitment proofs.

Layering:

* `Cache` defines cache-collision and fresh-hit predicates;
* `Logging` defines log-collision predicates and cached-log structural facts;
* `Collision` proves the birthday, cross-log, and fresh-hit probability bounds.
-/
