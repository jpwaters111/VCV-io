/-
  Proof sketches for basic_commitment_scheme.lean

  This file contains work-in-progress proof sketches for the random oracle
  commitment scheme defined in `basic_commitment_scheme.lean`.

  Three properties to prove:
  1. Binding:    Pr[collision] ≤ ½ · t² / 2^n   (birthday bound)
  2. Extractability: same error bound as binding
  3. Hiding:     |Pr[real] − Pr[sim]| ≤ t / 2^s  (statistical closeness)
-/

import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.OracleQuery

-- Re-import the definitions from the main file once they compile.
-- For now we sketch proof strategies inline.

open OracleSpec OracleComp

universe u v

section BindingSketch
/-
  ## Binding proof sketch

  Goal: For any t-query adversary A against CMOracle, the probability that A
  produces (cm, m0, s0, m1, s1) such that H(m0,s0) = H(m1,s1) = cm with
  (m0,s0) ≠ (m1,s1) is at most ½ · t² / 2^n.

  Strategy:
  - Use the birthday bound for random oracles.
  - Case 1 (E does not hold): A wins without querying both (m0,s0) and (m1,s1).
    Then at least one commitment is a fresh random oracle output, so the
    collision probability with the other is ≤ 1/2^n.
  - Case 2 (E holds): Both queries appear in the trace.
    Among t queries, the probability of any collision pair is ≤ t*(t-1)/2 · 1/2^n
    ≤ ½ · t² / 2^n.
  - Combine cases.

  Key VCV-io tools needed:
  - `simulateQ cachingOracle` for lazy sampling semantics
  - `IsQueryBound` for the t-query bound
  - Birthday-bound lemma (may need to prove or import)
  - `probOutput_bind_eq_tsum` for decomposing bind probabilities
-/

-- TODO: State and prove the binding theorem formally.
-- The main challenge is connecting the caching oracle simulation
-- to a birthday-bound argument on the query trace.

stop

end BindingSketch

section ExtractabilitySketch
/-
  ## Extractability proof sketch

  Goal: For any t-query adversary A = (commit, open) against CMOracle,
  Pr[extractability_game A = True] ≤ ½ · t² / 2^n.

  Strategy:
  - Run commit with `loggingOracle` to capture the query trace.
  - The extractor `CMExtract` searches the trace for an entry whose output
    matches the claimed commitment cm.
  - If commit queried (m,τ) and got cm, extractor finds it → game event requires
    (m',τ') ≠ (m,τ), i.e., a second preimage.
  - If commit did NOT query any pair mapping to cm, then cm is independent of
    the oracle, and Pr[H(m,τ) = cm] = 1/|C| per open query.
  - Either way, the error reduces to the binding/birthday bound.

  Key VCV-io tools needed:
  - `simulateQ loggingOracle` for trace capture
  - `QueryLog.find?` for extractor definition
  - Conditioning on trace events via `probEvent`
-/

-- TODO: Formalize the extractability game and prove the bound.
-- The reduction to binding should make this straightforward once binding is done.

stop

end ExtractabilitySketch

section HidingSketch
/-
  ## Hiding proof sketch

  Goal: For any t-query distinguisher A,
  |Pr[A wins | real game] − Pr[A wins | simulated game]| ≤ t / 2^s.

  Real game:  sample s uniformly, compute cm = H(m,s), give cm to A.
  Sim game:   sample cm uniformly from C, give cm to A.

  Strategy:
  - H is a random oracle, so H(m,s) for fresh s is uniformly random over C,
    UNLESS A has already queried (m,s).
  - Since s is sampled uniformly from S after A chooses m, the probability
    that A has already queried (m,s) for the chosen s is ≤ t / |S|.
  - Conditioned on A not having queried (m,s), the real and simulated
    distributions are identical.
  - By the fundamental lemma of game-playing (identical-until-bad):
    |Pr[real] − Pr[sim]| ≤ Pr[bad] ≤ t / |S| = t / 2^s.

  Key VCV-io tools needed:
  - `by_upto` tactic for identical-until-bad argument
  - `simulateQ cachingOracle` for lazy sampling
  - Statistical distance / TV distance lemmas
  - `probEvent` for bounding Pr[bad]
-/

-- TODO: Define the hiding adversary structure properly (two-phase).
-- TODO: Define real and simulated games.
-- TODO: Prove the hiding bound via identical-until-bad.

stop

end HidingSketch
