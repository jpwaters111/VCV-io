/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import Examples.CommitmentScheme.Common
import Examples.CommitmentScheme.Binding
import Examples.CommitmentScheme.Extractability
import Examples.CommitmentScheme.Hiding

/-!
# Basic Commitment Scheme

Public aggregator for the basic random-oracle commitment example.

The main textbook-facing bounds are:

* `binding_bound`, with bound `cmBindingErrorTerm C t`;
* `extractability_bound`, with bound `cmExtractabilityErrorTerm C t`;
* `hiding_bound_finite`, with bound `cmHidingErrorTerm S t`.
-/
