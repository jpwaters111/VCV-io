/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import Examples.CommitmentScheme.Hiding.Defs
import Examples.CommitmentScheme.Hiding.CountBounds
import Examples.CommitmentScheme.Hiding.LoggingBounds
import Examples.CommitmentScheme.Hiding.Main

/-!
# Basic Commitment Scheme — Hiding

Public aggregator for the hiding game definitions, counted/logged query bounds,
and final statistical-distance theorem.

The main bound is `hiding_bound_finite`, stated with the named expression
`cmHidingErrorTerm S t = t / |S|`.
-/
