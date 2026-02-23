import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.OracleQuery



section definitions

-- variable {commit check : Type} [DecidableEq M]
--     [AddCommGroup G] [AddTorsor G P] {n : ℕ}
--/-- An `OracleSpec ι` is specieifes a set of oracles indexed by `ι`.
-- Defined as a map from each input to the type of the oracle's output. -/
-- def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  -- ι → Type v
universe u v w z

open OracleSpec OracleComp Polynomial MvPolynomial

variable {ι ι'} {CMOracleSpec : OracleSpec ι} {spec' σ : OracleSpec ι'} {α β γ : Type w}

-- define specific oracle spec for this commitment scheme

def CMOracle (M : Type u) (S : Type v) (C : Type w): OracleSpec (M × S) :=
  fun _ => C

-- def CMCommit (ι : Type u) (l: Int) (s : Int) (m : Type α) : Type β:=
variable {M S C}
def CMCommit (m : M) (s : S) : OracleComp (CMOracle M S C) C :=
  OracleComp.query (spec := CMOracle M S C) (m, s)

-- def CMCheck(ι : Type u) (l: Int) (s : Int) (cm : Type β) : Bool :=
def CMCheck (c : C) (m : M) (s : S) : OracleComp (CMOracle M S C) Prop :=
  do let c' ← OracleComp.query (spec := CMOracle M S C) (m, s); return (c = c')

-- * `do let x ← comp₁; comp₂ x` (`comp₁ >>= comp₂`)

-- @[inline, reducible] def cachingOracle :
--     QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
--   (QueryImpl.ofLift spec (OracleComp spec)).withCaching

variable {m : M} {s : Int}
structure CommitmentScheme (σ : OracleSpec ι') (l: Int) (s : Int) where
  Commit (m : M) (s : S): OracleComp σ C
  Check (c : C) (m: M) (s : S): OracleComp σ Prop

section properties
-- define the security definitions
-- input commitment scheme, query bound, querying algo (query with caching oracle),
-- binding_check is CM.check for the binding_thm, two messages m0, m1 given salts s0, s1
-- should not return the same commitment messages
def binding_check (m0 : M) (m1 : M) (s0 : S) (s1 : S): (OracleComp (CMOracle M S C)) Prop :=
  do
    let m0R ← OracleComp.query (spec := CMOracle M S C) (m0, s0);
    let m1R ← OracleComp.query (spec := CMOracle M S C) (m1, s1);
    return ¬(m0R = m1R)

-- output proposition (Pr two diff messages open same commitment less than 1/2*t^2/2^oracle output size)
-- proof strategy Markov's, get expected value of binding_check to prove that
-- two different messages have less than 1/2*t^2/2^t chance of happening

-- the binding adversary is a t-query algorithm that returns cm, m0, s0, m1, s1

variable {σ : OracleSpec ι'} {t : QueryCount ι}
structure BindingAdversary (σ : OracleSpec ι') (t : QueryCount ι) where
  Algorithm : OracleComp σ (C × M × S × M × S)
  t_Query : IsQueryBound Algorithm t

def binding_thm (t : ℕ) (A : BindingAdversary σ t) :Prop :=
  Pr[=
    true |
      do
        let (cm,m0,s0,m1,s1) ← A.Algorithm;
        return (binding_check m0 m1 s0 s1)] ≤ (1/2 * t^2 / 2^t)




structure ExtractAdversary (σ : OracleSpec ι') (t ≥ 3 : QueryCount ι) where
  Algorithm : OracleComp σ (C × AUX × tr)
  t_Query : IsQueryBound Algorithm t

def CMextract (cm) (tr) (s) : (M × S)  :=
  -- do let m0R ← OracleComp.query (spec := CMOracle M S C) (m0, s0);
  --   m1R ← OracleComp.query (spec := CMOracle M S C) (m0, s0);
  ∃ ((m',τ'),cm) ∈ tr → (m',τ')




def extractable_thm (t : ℕ) (A : ExtractAdversary σ t) : Prop :=
  Pr[=
    true |
      do
      -- tr is trace, how to extract from oraclecomp? needed for CMextract
        let (cm,aux,tr) ← A.Algorithm;
        let (m',τ')← CMextract(cm,tr);
        let (m, τ) ← A.Algorithm(aux);
        return ((CMCheck (cm, m, τ) = 1) ∧ ((m',τ') ≠ (m,τ)))] ≤ (1/2 * t^2 / 2^t)

-- extraction for multiple components

-- def extractable_implies_binding (t : ℕ) (A : ExtractAdversary σ t) : Prop :=

structure HidingAdversary (σ : OracleSpec ι') (t : QueryCount ι) where
  Algorithm : OracleComp σ (M × AUX)
  CMSimulate: OracleComp σ (CM)
  t_Query : IsQueryBound Algorithm t

-- according to claude what it should be
-- structure HidingAdversary (σ : OracleSpec ι') (t : QueryCount ι) where
--   -- Phase 1: adversary chooses a message (and produces auxiliary state)
--   chooseMessage : OracleComp σ (M × AUX)
--   -- Phase 2: adversary tries to distinguish given aux and commitment
--   distinguish : AUX → C → OracleComp σ Bool
--   t_Query : IsQueryBound chooseMessage t  -- (may also bound phase 2)

def hiding_thm ()
  do
    let (m, aux) ← A.Algorithm;
    let (cm,τ)← CMCommit(m);
    let (cm') ← CMSimulate;
    return Pr[=
    true |do
            |A.Algorithm(aux,cm) - A.Algorithm(aux,cm')| ≤ 1]

-- according to claude

-- def CMSimulator : OracleComp σ C :=
--   -- sample a uniformly random element of C (= Bits^n)
--   OracleComp.uniformFin _   -- or however uniform sampling is expressed

-- def hiding_real (A : HidingAdversary σ t) : OracleComp σ Bool := do
--   let (m, aux) ← A.chooseMessage
--   let cm ← CMCommit m s          -- s sampled uniformly from S
--   A.distinguish aux cm

-- def hiding_simulated (A : HidingAdversary σ t) : OracleComp σ Bool := do
--   let (m, aux) ← A.chooseMessage
--   let cm ← CMSimulator
--   A.distinguish aux cm

-- def hiding_thm (t : ℕ) (s : ℕ) (A : HidingAdversary σ t) : Prop :=
--   |(Pr[= true | hiding_real A]).toReal - (Pr[= true | hiding_simulated A]).toReal|
--     ≤ (t : ℝ) / 2^s
