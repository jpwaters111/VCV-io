# Hiding Proof Final Handoff

This handoff is for finishing the last remaining proof hole in
`Examples/CommitmentSchemeRO.lean`.

## Current state

- `lake env lean Examples/CommitmentSchemeRO.lean` is clean except for one final `sorry`.
- `rg -n "sorry" Examples/CommitmentSchemeRO.lean` shows:
  - the status/doc note near line 641
  - the real proof hole at `sum_probEvent_hidingBad_le`
- The remaining theorem is:
  - `sum_probEvent_hidingBad_le` at roughly line 4354

## What already compiles

These are the key local lemmas now in place:

- `exists_new_salt_cacheEntry_of_count_gt_one` at roughly line 2020
- `sum_wp_freshDistinguishIncrement_eq_query` at roughly line 3847
- `sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging` at roughly line 4065
- `run_cached_logging_proj_eq_cachingOracle` at roughly line 4212
- `fresh_incrementIndicator_le_querySaltIndicator_cached_logging` at roughly line 4255

The new bridge `fresh_incrementIndicator_le_querySaltIndicator_cached_logging` is important:

- input state is the fresh post-challenge counted state
- lhs is counted `wp ... (propInd (1 < z.2.2 s))`
- rhs is cached-over-logging `wp ... (propInd (0 < QueryLog.countQ ... salt=s))`

It compiles and uses:

- `exists_new_salt_cacheEntry_of_count_gt_one`
- `run_hidingImplCountAll_proj_eq_cachingOracle`
- `run_cached_logging_proj_eq_cachingOracle`
- `cache_entry_in_log_or_initial`

## What does not work

Do not revive the earlier projection idea

```lean
Prod.fst <$> (simulateQ cachingOracle oa).run cache₀ = oa
```

It is false for nonempty caches.

Do not pivot back to the older `countPred` route either. The file is already aligned
to the fresh-salt / cached-over-logging route.

## The remaining gap

The final theorem still needs the fresh diagonal residual bound.

The intended missing lemma is essentially:

```lean
private lemma sum_wp_fresh_query_then_distinguish_increment_le_queryResidual
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose :
      qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
        OracleComp.ProgramLogic.wp
          (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
            OracleComp (CMOracle M S C) C)
          (fun cm =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
                (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                  Function.update qchoose.2.2 s 1))
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (1 < z.2.2 s)))) ≤
      (t - ∑ s : S, qchoose.2.2 s)
```

## Recommended proof route

1. Start from `sum_wp_freshDistinguishIncrement_eq_query`.
2. Push the outer finite sum through the challenge query with `wp_finset_sum`.
3. For each `s`, apply `wp_mono` pointwise using
   `fresh_incrementIndicator_le_querySaltIndicator_cached_logging`.
4. For each sampled `cm`, apply
   `sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging`
   to `A.distinguish qchoose.1.2 cm`.
5. Use
   `hiding_distinguish_totalBound_of_choose_count_support`
   to supply the residual query bound
   `t - ∑ s, qchoose.2.2 s`.
6. Keep the factor `propInd (qchoose.2.2 s = 0)` outside until after the `wp_query`
   rewrite. At that point it only deletes branches, so `Finset.sum_le_sum` should be enough.

## How to close the final theorem

The last branch of `sum_probEvent_hidingBad_le` should then be:

1. split on `qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))`
2. in the supported branch:
   - bound choose-hit mass by `sum_chooseHitIndicators_le_sumCounts`
   - rewrite the fresh term via `sum_wp_freshDistinguishIncrement_eq_query`
   - bound it by the new residual lemma above
   - combine with `sum_counts_le_queryBound_of_mem_support_run_hidingChoose`
   - finish with `tsub_add_cancel_of_le`
3. in the unsupported branch:
   - use `probOutput_eq_zero_of_not_mem_support`

## Useful commands

```bash
lake env lean Examples/CommitmentSchemeRO.lean
rg -n "sorry" Examples/CommitmentSchemeRO.lean
rg -n "sum_probEvent_hidingBad_le|fresh_incrementIndicator_le_querySaltIndicator_cached_logging|sum_wp_freshDistinguishIncrement_eq_query|sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging" Examples/CommitmentSchemeRO.lean
```

## Practical notes

- The file is sensitive to proof-shape drift. Prefer adding one lemma, compiling, then
  wiring it into the theorem.
- The fresh bridge already compiles, so the next task is aggregation, not semantics of
  cache/log support.
- If the direct residual lemma gets awkward, prove an equivalent branchwise lemma after
  `wp_query`, then wrap it with `wp_finset_sum`.
