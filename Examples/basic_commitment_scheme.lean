import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.LoggingOracle
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

variable {ι ι'} {CMOracleSpec : OracleSpec ι} {spec' σ : OracleSpec ι'} {α β γ : Type}

-- define specific oracle spec for this commitment scheme

abbrev CMOracle (M : Type ) (S : Type ) (C : Type ): OracleSpec (M × S) :=
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

variable {σ : OracleSpec ι'} [DecidableEq ι'] {t : QueryCount ι}
structure BindingAdversary (σ : OracleSpec ι') (t : QueryCount ι') (C) (S) (M) where
  Algorithm : OracleComp σ (C × M × S × M × S)
  t_Query : IsQueryBound Algorithm t

#print HasEvalSPMF

def binding_thm [DecidableEq M] [DecidableEq S] [Fintype C] [Inhabited C]
  (t : ℕ) (A : BindingAdversary (CMOracle M S C) t C S M) :Prop :=
    Pr[=
      True |
        do
          let (cm,m0,s0,m1,s1) ← A.Algorithm;
          (binding_check m0 m1 s0 s1)] ≤ (1/2 * t^2 / 2^t)

-- prove completeness for binding
-- In particular, (m0;  0) and (m1;  1) form a collision for f.
-- Let E be the event that A makes the queries (m0;  0) and (m1;  1) to f (i.e., the query-answer
-- trace of A contains (m0;  0) and (m1;  1) as queries). We distinguish between two cases.
-- Case 1: A wins the binding game and E does not hold. meaning collision in A probability happens is 1/2^oracle size
-- Case 2: A wins the binding game and E holds. meaning collision in trace. 1/2*(t-1)*t/2^oracle size

-- Extractability (Lemma cm-extractability from textbook)
-- The adversary has two phases:
--   Phase 1 (commit): produces (cm, aux) while making oracle queries (recorded in trace)
--   Phase 2 (open):   given aux, produces an opening (m, τ)
variable {AUX : Type}
structure ExtractAdversary (σ : OracleSpec ι') (t : QueryCount ι') (C AUX M S : Type) where
  commit : OracleComp σ (C × AUX)
  open_ : AUX → OracleComp σ (M × S)
  t_Query : IsQueryBound commit t

-- The extractor searches the query trace for an entry ((m', τ'), cm).
-- It is a deterministic pure function (no oracle access).
def CMExtract [DecidableEq C] (cm : C) (tr : QueryLog (CMOracle M S C)) : Option (M × S) :=
  match tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => some entry.1
  | none => none

-- The extractability game: run commit with logging, extract from trace,
-- run open phase, check that the commitment verifies and extractor disagrees.
def extractability_game [DecidableEq C] [DecidableEq M] [DecidableEq S]
    {qb : QueryCount (M × S)}
    (A : ExtractAdversary (CMOracle M S C) qb C AUX M S) :
    OracleComp (CMOracle M S C) Prop := do
  -- Phase 1: run commit with logging oracle to capture the query trace
  let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
  -- Phase 2: adversary opens the commitment
  let (m, τ) ← A.open_ aux
  -- Check: H(m, τ) = cm (commitment verifies)
  let c ← OracleComp.query (spec := CMOracle M S C) (m, τ)
  -- Extractor output from the trace
  let extracted := CMExtract cm tr
  return match extracted with
  | some (m', τ') => (c = cm) ∧ ((m', τ') ≠ (m, τ))
  | none => (c = cm)  -- extractor failed; event still counts if check passes

-- Extractability theorem: Pr[game] ≤ 1/2 · t²/2^n
-- Error bound equals the binding error (CMExtractabilityExpression = CMBindingExpression)
def extractable_thm [DecidableEq M] [DecidableEq S] [DecidableEq C]
    [Fintype C] [Inhabited C]
    (t : ℕ) (A : ExtractAdversary (CMOracle M S C) t C AUX M S)
    (ht : t ≥ 3) : Prop :=
  Pr[= True | extractability_game A] ≤ (1/2 * t^2 / 2^t)

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


-- first define statistical difference
-- do later
def hiding_thm ()
  do
    let (m, aux) ← A.Algorithm;
    let (cm,τ)← CMCommit(m);
    let (cm') ← CMSimulate;
    return Pr[=
    true |do
            |A.Algorithm(aux,cm) - A.Algorithm(aux,cm')| ≤ 1] ≤ t/2^s
-- statistical difference less than t/2^s
-- integral over the difference times 1/2 should be less than t/2^s
-- uniformFIn in oracle comp according to claude


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
