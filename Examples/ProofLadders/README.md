# Proof Ladders Examples

This directory is the canonical landing area for examples that are imported from,
adapted from, or intentionally aligned with the Proof Ladders progression.

## Current Ladder

The current first tranche is ordered from smallest foundational proof to richer
reduction-style examples:

1. `OneTimePad`
   - minimal secrecy example
   - direct probability reasoning plus relational equivalence
2. `Pedersen`
   - commitment hiding and algebraic binding
3. `Schnorr`
   - canonical sigma-protocol example
4. `ElGamal/Basic`
   - DDH-to-IND-CPA reduction
5. `ElGamal/Hash`
   - entropy smoothing and multi-game proof

## Why These Are Here First

These examples match the strongest currently finished abstractions in
`VCVio/CryptoFoundations`:

- `SymmEncAlg`
- `CommitmentScheme`
- `SigmaProtocol`
- `AsymmEncAlg`
- `DiffieHellman`
- `EntropySmoothing`

They are also good onboarding examples because they escalate cleanly from:

1. simple distribution arguments
2. relational proof mode
3. algebraic extraction
4. game-hopping reductions

## Next Intake Order

The current recommended order for follow-on Proof Ladders work is:

1. `Signature` / Fiat-Shamir on top of `Schnorr`
2. `BR93`
3. `PRGfromPRF`
4. `Fischlin`
5. `Fujisaki-Okamoto`

## Intake Rule

Add a proof here only if at least one of the following is true:

- it is directly ported from external Proof Ladders material
- it is a close local adaptation of a Proof Ladders proof
- it is intentionally placed here as the next rung in the same pedagogical sequence

Do not use this folder as a generic bucket for unrelated examples.
