# Next Session: Launch These Two Agents

Read `project_session_handoff.md` in memory first, then launch these agents.

## Agent 1: Finset Bookkeeping + Total Query Bound (Textbook)

Focus: Sorrys 1, 3, 4 in CollisionResistance.lean — the mechanical parts.

```
Task: Prove three sorrys in CollisionResistance.lean:

1. `IsTotalQueryBound.of_perIndex` (line ~105): Induction on OracleComp.
   Key: at query step, ∑ (Function.update qb t (qb t - 1)) = (∑ qb) - 1.
   Read QueryBound.lean for IsQueryBound/IsPerIndexQueryBound definitions.

2. Two finset membership sorrys inside `probEvent_logCollision_le_birthday_total`:
   (a) Reverse membership: if (i,j) ∈ emb(old pairs) ∪ newEmb(new pairs) then i < j
   (b) Disjointness: emb(old) ∩ newEmb(new) = ∅

   These are about Fin castSucc/castPred embeddings. Use:
   - Fin.castSucc_lt_castSucc_iff
   - Fin.castSucc_lt_last
   - Fin.castSucc_ne_last
   - Prod.mk.inj for destructuring pair equalities

Full codebase access. Test: lake env lean VCVio/OracleComp/QueryTracking/CollisionResistance.lean
```

## Agent 2: ROM Independence (Research)

Focus: Sorry 2 — `probEvent_pair_collision_le` — the core research problem.

```
Task: Prove that for positions i,j in a loggingOracle trace with distinct inputs,
Pr[same output] ≤ 1/|C|.

This is the formal independence property of the random oracle.

Key insight: In evalDist, each query returns independent uniform. loggingOracle
just records queries without changing the distribution. So log outputs at any
two positions are independent uniform draws from C.

For two independent uniform draws from C, Pr[equal] = 1/|C|.

Approaches to try:
A. Show loggingOracle.probEvent_fst_run_simulateQ preserves probability structure
B. Decompose via probEvent_bind_eq_tsum through the query chain
C. Use evalDist_simulateQ_run'_eq_evalDist to show loggingOracle preserves evalDist
D. Adapt Fork.lean's collision reasoning (probOutput_collision_given_seed_le)

Read: CollisionResistance.lean, LoggingOracle.lean, OracleComp/EvalDist.lean,
Fork.lean (lines 100-250), novel_strategies/union_bound_birthday.md

Full codebase access including modifying library files.
```
