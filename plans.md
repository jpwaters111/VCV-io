# Proof Ladders Migration And Intake Plan

## Objective

Establish `Examples/ProofLadders` as the canonical landing area for proofs imported or adapted
from the Proof Ladders ecosystem, starting with the examples that already fit VCV-io's existing
`CryptoFoundations` APIs and proof style.

This plan covers both:

1. the completed first migration of existing in-repo examples into `Examples/ProofLadders`, and
2. the next-wave intake process for deciding which additional Proof Ladders material should be
   ported into VCV-io.

## Scope

### In Scope

- Reorganizing existing example files into `Examples/ProofLadders`
- Repairing Lean module imports after the move
- Verifying that umbrella example targets still build
- Ranking follow-on Proof Ladders targets against the current codebase
- Using subagents for bounded analysis tasks with concrete outputs

### Out Of Scope

- Rewriting the content of the moved proofs
- Finishing unrelated `sorry`s elsewhere in the repo
- Large foundational changes to `VCVio/CryptoFoundations`
- Porting heavy examples that do not yet fit the repo's mature abstractions

## Success Criteria

The migration is considered successful when all of the following hold:

1. The first-tranche examples live under `Examples/ProofLadders`.
2. Repo imports point at `Examples.ProofLadders.*` module paths.
3. `lake build Examples` succeeds.
4. The moved examples still illustrate the repo's strongest proof workflows:
   direct probability arguments, relational equivalence, algebraic extraction, and game-hopping.
5. There is a documented ranked queue for the next tranche of Proof Ladders imports.

## Decision Principles

When deciding whether a Proof Ladders proof belongs in the next tranche, prefer proofs that:

- map directly onto an existing abstraction in `VCVio/CryptoFoundations`
- already have at least one nearby example in the repo
- avoid introducing new meta-theory just to state the result
- exercise mature tactics and workflows already documented in `docs/agents/`
- can build pedagogically from small proofs to reductions and then to ROM/CCA-style proofs

Deprioritize proofs that:

- depend on large unfinished foundations
- need substantial engineering or performance infrastructure
- are only weakly connected to the repo's existing teaching spine
- would land as a one-off artifact with little reuse

## Current Status

### Completed First-Tranche Move

The following existing examples have already been moved into `Examples/ProofLadders`:

- `Examples/OneTimePad.lean` -> `Examples/ProofLadders/OneTimePad.lean`
- `Examples/Pedersen.lean` -> `Examples/ProofLadders/Pedersen.lean`
- `Examples/Schnorr.lean` -> `Examples/ProofLadders/Schnorr.lean`
- `Examples/ElGamal/Common.lean` -> `Examples/ProofLadders/ElGamal/Common.lean`
- `Examples/ElGamal/Basic.lean` -> `Examples/ProofLadders/ElGamal/Basic.lean`
- `Examples/ElGamal/Hash.lean` -> `Examples/ProofLadders/ElGamal/Hash.lean`

### Completed Repair Work

The module-path repair work has already been completed:

- `Examples.lean` imports now target `Examples.ProofLadders.*`
- `Examples/Signature.lean` now imports `Examples.ProofLadders.Schnorr`
- moved ElGamal files now import `Examples.ProofLadders.ElGamal.Common`

### Build Verification

The move and repair were verified successfully with:

```bash
lake build Examples Examples.Signature \
  Examples.ProofLadders.OneTimePad \
  Examples.ProofLadders.Pedersen \
  Examples.ProofLadders.Schnorr \
  Examples.ProofLadders.ElGamal.Basic \
  Examples.ProofLadders.ElGamal.Hash
```

And with the umbrella target:

```bash
lake build Examples
```

### Completed Folder Index

A local directory index now exists at `Examples/ProofLadders/README.md` to record:

- the current ladder order
- the rationale for the first tranche
- the next intake order
- the rule for what belongs in this folder

## Why This First Tranche

These are the right canonical starting proofs for `Examples/ProofLadders` because they line up
with the repo's most mature proof interfaces.

### Tier 1: Minimal Foundational Examples

1. `OneTimePad`
   - smallest polished secrecy example
   - shows both direct probability reasoning and relational equivalence
   - good onboarding proof for `SymmEncAlg` and `ProgramLogic.Tactics`

2. `Pedersen`
   - clean commitment example
   - combines perfect hiding with algebraic binding reduction
   - strongest current template for commitment-style imports

3. `Schnorr`
   - canonical `SigmaProtocol` example
   - packages completeness, special soundness, and HVZK in a single proof spine
   - natural feeder for Fiat-Shamir and Fischlin later

### Tier 2: Reduction-Oriented Examples

4. `ElGamal/Basic`
   - direct DDH-to-IND-CPA reduction
   - clean example of one-time-to-many-query lift

5. `ElGamal/Hash`
   - natural step up from basic ElGamal
   - introduces entropy smoothing and a richer multi-game proof

## Canonical Intake Order After The First Tranche

This is the current recommended order for follow-on work.

1. `Schnorr Signature / Fiat-Shamir`
   - best immediate next step because it composes directly on moved `Schnorr`
   - main blocker is unfinished generic security proof infrastructure

2. `BR93`
   - good ROM / up-to-bad example
   - already scaffolded and localized enough to finish incrementally

3. `PRG from PRF`
   - strong medium-complexity reduction example
   - exercises mature `PRF` and `PRG` foundations

4. `Fischlin`
   - natural extension once sigma-protocol examples are established as canonical
   - depends on unfinished generic theorems

5. `Fujisaki-Okamoto`
   - strategically important, but should wait until the surrounding generic theorems are firmer

Explicitly deprioritized for near-term Proof Ladders intake:

- `Regev`
- `MLKEM`
- `SimpleTwoServerPIR`
- random-oracle commitment examples that still depend on immature query-bound infrastructure

## Follow-On Review Results

Two immediate follow-on targets have now been reviewed more concretely.

### `BR93`

Status:

- remains the best non-move completion target after the current reorg

Why:

- the game ladder, reduction, and final theorem shape are already in place
- two of the three missing lemmas appear to be directly supported by existing infrastructure
- the main bespoke remaining proof is the bad-event to trapdoor-permutation advantage bound

Practical implication:

- `BR93` should stay ahead of `PRGfromPRF`

### `PRGfromPRF`

Status:

- still worth keeping high in the queue, but not ahead of `BR93`

Why:

- the file is well scaffolded, but the central ideal-world gap still needs either:
  - an intermediate fresh-independent-oracle game and bad-state simulation, or
  - lower-level random-oracle lemmas to be finished first

Practical implication:

- `PRGfromPRF` is partly an infrastructure task, not just a local proof-completion task

## Agent Operating Model

Agents should be used for bounded analysis tasks with concrete deliverables. The main agent
remains responsible for integration, patching, and verification.

### Agent 1: Import Repair Audit

Purpose:

- Enumerate every stale import or module-path reference after a move

Inputs:

- current file tree under `Examples/` and `Examples/ProofLadders/`
- `Examples.lean`
- any files that import moved modules

Expected deliverable:

- exact file list to patch
- old module path -> new module path mapping
- confirmation that no additional stale imports remain

Definition of done:

- the output is precise enough to apply a patch without additional discovery

### Agent 2: Proof Ladders Prioritization Notes

Purpose:

- rank future Proof Ladders intake candidates against the current VCV-io codebase

Inputs:

- `Examples/`
- `VCVio/CryptoFoundations/`
- `docs/agents/`
- the already moved Proof Ladders tranche

Expected deliverable:

- ranked list of next candidate proofs
- concrete rationale tied to existing abstractions and example coverage
- explicit blockers for anything recommended later rather than sooner

Definition of done:

- the ranking is actionable and supported by specific codebase references

### Agent 3: Build-Risk Check

Purpose:

- identify the real failure modes caused by module moves

Inputs:

- moved file list
- umbrella imports
- Lean build targets

Expected deliverable:

- likely failing imports
- minimal repair sequence
- correct verification command to use as the canary

Definition of done:

- the risk report points directly to the fewest necessary repairs and the right build target

## Main-Agent Execution Sequence

When performing a new Proof Ladders migration, the main agent should follow this sequence:

1. Identify candidate files to move.
2. Confirm they match mature repo abstractions.
3. Write or update `plans.md` before parallelizing work.
4. Spawn bounded analysis agents.
5. Move files.
6. Repair module imports.
7. Run the smallest targeted builds first.
8. Run `lake build Examples` as the real umbrella canary.
9. Record next-wave priorities and blockers.

## Build And Verification Guidance

### Preferred Verification Order

1. Build moved modules directly.
2. Build immediately dependent examples such as `Examples.Signature`.
3. Build `Examples`.

### Important Nuance

Bare `lake build` is not the best canary for this migration, because only `VCVio` is the
default target in `lakefile.lean`. For example-module moves, `lake build Examples` is the
correct umbrella verification target.

## Risks And Mitigations

### Risk 1: Stale Module Paths

Symptom:

- Lean cannot find old `Examples.*` paths after files are moved.

Mitigation:

- always run an import audit before and after patching

### Risk 2: Hidden Downstream Imports

Symptom:

- the moved files build in isolation, but a dependent example still imports an old path

Mitigation:

- build at least one downstream dependent module and then the `Examples` umbrella target

### Risk 3: Overreaching Into Immature Areas

Symptom:

- a new Proof Ladders intake requires finishing foundational theorems before the example can land

Mitigation:

- rank by codebase maturity, not by external appeal

### Risk 4: Example Folder Becoming A Dumping Ground

Symptom:

- unrelated examples get grouped under `ProofLadders` without a clear intake policy

Mitigation:

- only place proofs there if they are imported from, adapted from, or explicitly aligned with
  the Proof Ladders progression

## Open Follow-Ups

- decide whether to add a dedicated `Examples/ProofLadders` umbrella module
- decide whether to normalize naming between external Proof Ladders labels and local Lean module names

## Recommended Next Actions

1. Promote `Examples/Signature.lean` as the next candidate to move or expand as a Proof Ladders follow-on.
2. Treat `BR93` as the first non-move completion target after the current reorg.
3. Keep `PRGfromPRF` behind `BR93` until the random-oracle-side blockers are reduced or isolated.
4. Decide whether `Examples/ProofLadders` should gain its own Lean umbrella module.
