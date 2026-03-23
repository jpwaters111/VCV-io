/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jpwaters
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.EvalDist

/-!
# ROM Collision Resistance — Union Bound Approach

Following the SNARGs textbook (Thaler, Lemma rom-cr), we prove:

> For every t-query algorithm A, the probability that A's query trace contains
> a collision (two distinct inputs with the same output) is ≤ t(t-1)/(2·|C|).

## Proof (textbook, Section 4)

Let q₁,...,qₜ be the queries. For each pair (i,j) with i ≠ j, define
  E_{i,j} = "qᵢ ≠ qⱼ AND H(qᵢ) = H(qⱼ)".

Then:
- Pr[E_{i,j}] ≤ 1/|C| (if qᵢ = qⱼ then E doesn't hold; if qᵢ ≠ qⱼ then
  the outputs are independent uniform, so Pr[equal] = 1/|C|).
- Collision = ∃ (i,j) with i ≠ j such that E_{i,j}.
- Union bound: Pr[collision] ≤ ∑ Pr[E_{i,j}] ≤ C(t,2)/|C| = t(t-1)/(2|C|).

## Status

The per-pair bound `Pr[E_{i,j}] ≤ 1/|C|` and the union bound over pairs are
the two key steps. Both are stated; the per-pair bound requires showing that
`loggingOracle` outputs at distinct positions are independent uniform draws,
which is the core ROM property.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0,0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-! ## Collision Predicates -/

/-- A query log has a collision: two entries at distinct positions with
distinct inputs but HEq-equal outputs. -/
def LogHasCollision (log : QueryLog spec) : Prop :=
  ∃ (i j : Fin log.length), i ≠ j ∧
    log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2

/-- A cache has a collision: two distinct inputs map to the same output. -/
def CacheHasCollision (cache : QueryCache spec) : Prop :=
  ∃ (t₁ t₂ : spec.Domain) (u₁ : spec.Range t₁) (u₂ : spec.Range t₂),
    t₁ ≠ t₂ ∧ cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ HEq u₁ u₂

/-! ## Gauss Sum Arithmetic -/

/-- The Gauss sum `∑_{k=0}^{n-1} k/N ≤ n²/(2N)`, the arithmetic core of the birthday bound. -/
private lemma gauss_sum_inv_le (n : ℕ) (N : ℝ≥0∞) (_hN : 0 < N) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ ≤
      (n ^ 2 : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  -- Key inequality in ℕ: 2 * ∑_{k<n} k = n*(n-1) ≤ n^2
  have hnat : 2 * (∑ k ∈ range n, k) ≤ n ^ 2 := by
    have := Finset.sum_range_id_mul_two n; nlinarith [Nat.sub_le n 1]
  -- Lift to ENNReal
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num,
      show (n : ℝ≥0∞) ^ 2 = ((n ^ 2 : ℕ) : ℝ≥0∞) from by push_cast; ring,
      ← Nat.cast_mul]
    exact_mod_cast hnat
  -- From 2 * sum ≤ n^2, derive sum ≤ n^2 / 2
  have hle : (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
    rwa [mul_comm]
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      ≤ ((n : ℝ≥0∞) ^ 2 / 2) * N⁻¹ := mul_le_mul_left hle N⁻¹
    _ = (n : ℝ≥0∞) ^ 2 / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

/-! ## Total Query Bound -/

/-- A total query bound: the computation makes at most `n` queries total
(across all oracle indices). -/
def IsTotalQueryBound {α : Type} (oa : OracleComp spec α) (n : ℕ) : Prop :=
  IsQueryBound oa n (fun _ b => 0 < b) (fun _ b => b - 1)

lemma isTotalQueryBound_query_bind_iff {α : Type} {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound (liftM (query t) >>= mx) n ↔
      0 < n ∧ ∀ u, IsTotalQueryBound (mx u) (n - 1) := by
  simp [IsTotalQueryBound, IsQueryBound, OracleComp.construct_query_bind]

/-- Updating one index and summing gives sum minus one. -/
private lemma sum_update_pred [Fintype ι] {qb : ι → ℕ} {t : ι} (ht : 0 < qb t) :
    ∑ i, Function.update qb t (qb t - 1) i = (∑ i, qb i) - 1 := by
  have hsub : ∑ i, Function.update qb t (qb t - 1) i + 1 = (∑ i, qb i) := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => Function.update qb t (qb t - 1) i)
      (Finset.mem_univ t)]
    simp only [Function.update_self]
    conv_rhs => rw [← Finset.add_sum_erase Finset.univ qb (Finset.mem_univ t)]
    have herase : ∑ x ∈ Finset.univ.erase t,
        Function.update qb t (qb t - 1) x = ∑ x ∈ Finset.univ.erase t, qb x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [herase]; omega
  omega

/-- Per-index bound implies total bound (sum over indices). -/
theorem IsTotalQueryBound.of_perIndex [Fintype ι] {α : Type}
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => exact trivial
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    rw [isTotalQueryBound_query_bind_iff]
    have hpos : 0 < ∑ i, qb i :=
      Nat.lt_of_lt_of_le h.1 (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))
    refine ⟨hpos, fun u => ?_⟩
    rw [← sum_update_pred h.1]
    exact ih u (h.2 u)

/-! ## Logging Oracle Run Decomposition -/

/-- When running `loggingOracle` on `query t >>= mx`, the result decomposes as:
a uniform draw `u` from `Range t`, followed by prepending `⟨t, u⟩` to the sub-log. -/
private lemma run_simulateQ_loggingOracle_query_bind {α : Type}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp spec _) >>= fun u =>
        (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def, Function.comp]

/-! ## Per-Pair Collision Bound (Textbook Step 3)

For each pair (i,j) of positions in the log with distinct inputs,
Pr[outputs equal] ≤ 1/|C|. This is because in the evalDist model,
each query returns an independent uniform sample. -/

/-- **ROM uniformity at a log position**: For any `loggingOracle` trace, the
probability that the k-th log entry matches a fixed sigma-typed value `⟨t, v⟩`
is at most `1/|Range t|`. Each query response is an independent uniform draw.

Proof by structural induction on the computation. For `query t >>= mx`:
- The log is `[⟨t, u⟩] ++ sub_log` where `u` is uniform from `Range t`.
- For k = 0: the event is `⟨t, u⟩ = entry`, bounded by `Pr[= v | query t] = 1/|Range t|`.
- For k > 0: the event is `sub_log[k-1]? = entry`, bounded by the inductive hypothesis. -/
private theorem probEvent_log_entry_eq_le {α : Type}
    (oa : OracleComp spec α)
    (k : ℕ) (entry : (t : spec.Domain) × spec.Range t) :
    Pr[fun z => z.2[k]? = some entry |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure _ =>
    -- Pure computation: log is empty, so z.2[k]? = none ≠ some entry.
    simp [loggingOracle, simulateQ_pure]
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    cases k with
    | zero =>
      -- k = 0: The 0-th log entry is ⟨t, u⟩. Decompose, simplify predicate.
      rw [probEvent_bind_eq_tsum]
      simp_rw [probEvent_map, Function.comp_def]
      have hpred : ∀ u : spec.Range t,
          (fun z : α × QueryLog spec =>
            ((⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[0]? = some entry) =
          (fun _ => (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) = entry) := by
        intro u; ext z; simp only [show ((⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[0]? =
          some (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) from rfl, Option.some_inj]
      simp_rw [hpred]
      -- Goal: ∑' u, Pr[= u | query t] * Pr[fun _ => ⟨t,u⟩ = entry | sim.run] ≤ 1/|R|
      -- Replace inner Pr by: 0 (if ⟨t,u⟩ ≠ entry) or ≤ 1 (if ⟨t,u⟩ = entry).
      -- So the sum ≤ Pr[= entry.2 | query t] when t = entry.1, else 0.
      -- Direct bound: each term ≤ Pr[= u | query t] * 1 = 1/|Range t|.
      -- And at most one term is nonzero (the one with ⟨t,u⟩ = entry).
      -- So sum ≤ 1/|Range t| = 1/|Range entry.1| when t = entry.1, else 0.
      -- Use: probOutput_query gives Pr[= u | query t] = 1/|Range t|.
      -- Substitute and bound.
      -- Case split on whether t = entry.1
      by_cases ht : t = entry.1
      · -- t = entry.1: Range t = Range entry.1, so card⁻¹ match.
        subst ht
        simp_rw [probOutput_query]
        rw [ENNReal.tsum_mul_left]
        apply le_of_le_of_eq (mul_le_mul' le_rfl _) (mul_one _)
        -- Need: ∑' u, Pr[fun _ => ⟨entry.1, u⟩ = entry | sim.run] ≤ 1
        -- Only u = entry.2 can satisfy ⟨entry.1, u⟩ = entry.
        -- For u ≠ entry.2, the Sigma can't be equal (same fst, different snd).
        -- Reduce Sigma equality to component equality
        -- entry = ⟨entry.1, entry.2⟩ and t was subst'd to entry.1
        -- So ⟨entry.1, u⟩ = entry ↔ u = entry.2
        have hsigma : ∀ w : spec.Range entry.1,
            (⟨entry.1, w⟩ : (i : spec.Domain) × spec.Range i) = entry ↔ w = entry.2 := by
          intro w; constructor
          · intro h; exact eq_of_heq (Sigma.mk.inj h).2
          · intro h; subst h; exact Sigma.eta entry
        simp_rw [show ∀ w : spec.Range entry.1,
            (fun _ : α × QueryLog spec =>
              (⟨entry.1, w⟩ : (i : spec.Domain) × spec.Range i) = entry) =
            fun _ => w = entry.2 from fun w => by ext; exact hsigma w]
        exact le_trans
          (ENNReal.tsum_le_tsum fun w => by
            by_cases hw : w = entry.2
            · exact le_trans probEvent_le_one (by simp [hw])
            · exact le_of_eq_of_le (probEvent_eq_zero fun _ _ => hw) (by simp [hw]))
          (le_of_eq (tsum_ite_eq entry.2 (fun _ => (1 : ℝ≥0∞))))
      · -- t ≠ entry.1: ⟨t, u⟩ ≠ entry for all u, so inner Pr = 0.
        have hne : ∀ u : spec.Range t,
            ¬ (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) = entry :=
          fun _ h => ht (by cases h; rfl)
        have hzero : ∀ u : spec.Range t,
            Pr[fun _ => (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) = entry |
              (simulateQ loggingOracle (mx u)).run] = 0 :=
          fun u => probEvent_eq_zero fun _ _ => hne u
        simp only [hzero, mul_zero, tsum_zero]
        exact zero_le _
    | succ k' =>
      -- k > 0: decompose with probEvent_bind_eq_tsum, use ih.
      rw [probEvent_bind_eq_tsum]
      simp_rw [probEvent_map, Function.comp_def, List.getElem?_cons_succ]
      calc ∑' u, Pr[= u | (query t : OracleComp spec _)] *
            Pr[fun z => z.2[k']? = some entry | (simulateQ loggingOracle (mx u)).run]
        ≤ ∑' u, Pr[= u | (query t : OracleComp spec _)] *
            (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (ih u k')
        _ = (∑' u, Pr[= u | (query t : OracleComp spec _)]) *
            (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_mul_right
        _ ≤ 1 * (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ :=
          mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := one_mul _

/-- **Per-pair collision bound**: For any two positions in a `loggingOracle` trace
with distinct inputs, the probability that their outputs are HEq-equal is ≤ 1/|C|.

This is the core ROM property: distinct oracle inputs yield independent uniform outputs.
In the `evalDist` model, each `query` call returns a fresh uniform sample.

The proof decomposes via `probEvent_bind_eq_tsum`: condition on the i-th entry, then
the j-th output is uniform by `probEvent_log_entry_eq_le`, matching any fixed value
with probability 1/|C|. -/
theorem probEvent_pair_collision_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n)
    (i j : Fin n) (hij : i ≠ j) :
    Pr[fun z => z.2.length > i.val ∧ z.2.length > j.val ∧
        z.2[i]?.bind (fun ei => z.2[j]?.map (fun ej =>
          ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  -- The collision event E_{i,j} implies the j-th entry matches some fixed sigma value.
  -- By probEvent_mono, weaken to "z.2[j]? = some entry" and apply probEvent_log_entry_eq_le.
  -- The key subtlety: we don't know entry ahead of time, so we bound via tsum decomposition.
  --
  -- Expand Pr[E_{i,j}] = ∑_z (if E_{i,j}(z) then Pr[=z] else 0).
  -- For each z with E_{i,j}(z), z.2[j]? = some ej for a specific ej.
  -- Group by ej: Pr[E_{i,j}] = ∑_{ej} Pr[z.2[j]? = some ej ∧ E_{i,j}(z)].
  -- Since events are disjoint: ≤ ∑_{ej that participate} Pr[z.2[j]? = some ej].
  -- But this sum ≤ 1, not 1/|C|. Need a tighter argument.
  --
  -- Correct approach: use probEvent_mono to weaken to just the j-th entry matching,
  -- then apply probEvent_log_entry_eq_le. The collision condition constrains the output,
  -- so the weakened event has the same bound.
  --
  -- Actually, the simplest approach: Pr[E_{i,j}] ≤ Pr[z.2[j]? = some entry] for ANY
  -- fixed entry, by probEvent_mono. Choose entry = ⟨default, default⟩.
  -- But E_{i,j} does NOT imply z.2[j]? = some ⟨default, default⟩.
  --
  -- The correct proof requires structural induction on oa.
  sorry

/-! ## Union Bound Birthday (Textbook Steps 4-5)

Collision = ∃ pair with collision. Union bound over C(n,2) pairs gives n²/(2|C|). -/

/-- **Birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ n²/(2|C|).

Proof: express collision as ∃ pair (i,j), then union bound using
`probEvent_pair_collision_le` for each pair. -/
theorem probEvent_logCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Strategy: express LogHasCollision as ∃ (i,j) ∈ Fin n × Fin n with i < j,
  -- then apply union bound, bounding each pair by 1/|C|.
  -- Step 1: LogHasCollision z.2 implies there exist indices i < j < n
  -- (assuming the log length is ≤ n from the query bound)
  -- Step 2: Union bound over pairs
  -- Step 3: Each pair contributes ≤ 1/|C| by probEvent_pair_collision_le
  -- Step 4: Number of pairs × 1/|C| = gauss_sum_inv_le
  let C := Fintype.card (spec.Range default)
  -- Bound by union over pairs using probEvent_pair_collision_le
  calc Pr[fun z => LogHasCollision z.2 | (simulateQ loggingOracle oa).run]
      ≤ ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
          (C : ℝ≥0∞)⁻¹ := by
        -- Step A: Log length ≤ n for elements in support
        have hlog_le : ∀ z ∈ support ((simulateQ loggingOracle oa).run),
            z.2.length ≤ n := by
          -- By induction on oa: pure gives empty log, query_bind appends one entry
          suffices h : ∀ (β : Type) (ob : OracleComp spec β) (m : ℕ),
              IsTotalQueryBound ob m → ∀ z ∈ support ((simulateQ loggingOracle ob).run),
              z.2.length ≤ m from h α oa n hbound
          intro β ob m hm
          induction ob using OracleComp.inductionOn generalizing m with
          | pure x =>
            intro z hz
            simp [simulateQ_pure] at hz
            subst hz; simp
          | query_bind t mx ih =>
            intro z hz
            rw [isTotalQueryBound_query_bind_iff] at hm
            obtain ⟨hpos, hrest⟩ := hm
            simp only [simulateQ_bind, simulateQ_query] at hz
            rw [show ((query t).cont <$> loggingOracle (query t).input >>=
              fun x => simulateQ loggingOracle (mx x) :
              WriterT (QueryLog spec) (OracleComp spec) β).run =
              ((query t).cont <$> loggingOracle (query t).input).run >>=
              fun p => Prod.map id (p.2 ++ ·) <$>
                (simulateQ loggingOracle (mx p.1)).run
              from WriterT.run_bind' _ _] at hz
            rw [support_bind] at hz
            simp only [Set.mem_iUnion] at hz
            obtain ⟨qu, hqu, hz⟩ := hz
            rw [support_map] at hz
            obtain ⟨z', hz', rfl⟩ := hz
            simp only [Prod.map]
            -- The log is qu.2 ++ z'.2
            show (qu.2 ++ z'.2).length ≤ m
            -- Analyze the query step to get qu.2.length = 1
            have hqu_log : qu.2.length = 1 := by
              -- The query oracle step maps (loggingOracle t).run through (query t).cont = id
              simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query] at hqu
              -- (loggingOracle t).run = liftM (query t) >>= fun u => pure (u, [⟨t, u⟩])
              -- via the WriterT unfolding
              have hrun : (loggingOracle (spec := spec) t).run =
                  (query t : OracleComp spec _) >>= fun u =>
                    pure (u, [⟨t, u⟩]) := by
                simp [loggingOracle, QueryImpl.withLogging_apply,
                  WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
                  map_pure, Prod.map]
              rw [hrun] at hqu
              simp only [support_bind, support_pure, Set.mem_iUnion,
                Set.mem_singleton_iff] at hqu
              obtain ⟨u, _, rfl⟩ := hqu
              simp
            -- Bound continuation log length by IH
            have hz'_len : z'.2.length ≤ m - 1 :=
              ih qu.1 (m - 1) (hrest qu.1) z' hz'
            -- Combine: qu.2 ++ z'.2 has length ≤ 1 + (m-1) = m
            simp only [List.length_append]
            omega
        -- Step B: Define the per-pair collision event (matching probEvent_pair_collision_le)
        let E : Fin n × Fin n → α × QueryLog spec → Prop := fun ij z =>
          z.2.length > ij.1.val ∧ z.2.length > ij.2.val ∧
            z.2[ij.1]?.bind (fun ei => z.2[ij.2]?.map (fun ej =>
              ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true
        let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
        -- Step C: probEvent_mono + union bound + per-pair bound
        apply le_trans (probEvent_mono (q := fun z => ∃ ij ∈ pairs, E ij z) ?_)
        · apply le_trans (probEvent_exists_finset_le_sum pairs _ E)
          apply Finset.sum_le_sum
          intro ⟨i, j⟩ hij
          simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact probEvent_pair_collision_le oa n hbound i j (Fin.ne_of_lt hij)
        · -- Show LogHasCollision z.2 → ∃ pair in pairs, E pair z
          intro z hz hcoll
          obtain ⟨i, j, hij, hdist, heq⟩ := hcoll
          have hlen := hlog_le z hz
          have hi_lt : i.val < n := Nat.lt_of_lt_of_le i.isLt hlen
          have hj_lt : j.val < n := Nat.lt_of_lt_of_le j.isLt hlen
          -- Helper: reduce getElem? for Fin n index when val < list length
          have getElem?_fin (l : QueryLog spec) (k : Fin n) (hk : k.val < l.length) :
              l[k]? = some l[k.val] := by
            simp [List.getElem?_eq_getElem, hk]
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · refine ⟨(⟨i.val, hi_lt⟩, ⟨j.val, hj_lt⟩), ?_, ?_⟩
            · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt
            · refine ⟨i.isLt, j.isLt, ?_⟩
              rw [getElem?_fin _ _ i.isLt, getElem?_fin _ _ j.isLt]
              change some _ = some _
              congr 1; exact propext ⟨fun _ => rfl, fun _ => ⟨hdist, heq⟩⟩
          · refine ⟨(⟨j.val, hj_lt⟩, ⟨i.val, hi_lt⟩), ?_, ?_⟩
            · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hgt
            · refine ⟨j.isLt, i.isLt, ?_⟩
              rw [getElem?_fin _ _ j.isLt, getElem?_fin _ _ i.isLt]
              change some _ = some _
              congr 1; exact propext ⟨fun _ => rfl, fun _ => ⟨Ne.symm hdist, heq.symm⟩⟩
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * C) := by
        -- The sum of constant C⁻¹ over pairs = |pairs| * C⁻¹
        rw [Finset.sum_const, nsmul_eq_mul]
        -- Suffices to show |pairs| * C⁻¹ ≤ n²/(2C)
        -- |pairs| = n*(n-1)/2, and n*(n-1)/2 ≤ n²/2
        -- We use gauss_sum_inv_le: ∑ k < n, k * C⁻¹ ≤ n²/(2C)
        -- Note ∑ k < n, k = n*(n-1)/2 = |pairs|
        -- So it suffices to show |pairs| ≤ ∑ k < n, k ... actually they're equal!
        -- |{(i,j) : Fin n × Fin n | i < j}| = ∑_{j<n} j = n(n-1)/2
        have hcard_eq : ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card : ℝ≥0∞)
            = ∑ k ∈ range n, (k : ℝ≥0∞) := by
          -- |{(i,j) | i < j}| = ∑_{j<n} j = n*(n-1)/2
          -- |{(i,j) : Fin n × Fin n | i < j}| = ∑_{k<n} k
          -- Proved as a separate lemma for clarity.
          have hcard_nat : ∀ m : ℕ,
              (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card =
                ∑ k ∈ range m, k := by
            intro m; induction m with
            | zero => simp
            | succ k ih =>
              rw [Finset.sum_range_succ, ← ih]
              -- Split the set of pairs in Fin (k+1) into:
              -- (1) pairs (i,j) with both < k (embedded from Fin k), and
              -- (2) pairs (i, last k) for i < last k
              -- Count: |old pairs| + k
              have hsplit :
                  (Finset.univ.filter (fun p : Fin (k+1) × Fin (k+1) => p.1 < p.2)).card =
                  (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).card + k := by
                -- Define the embedding from Fin k pairs to Fin (k+1) pairs
                let emb : Fin k × Fin k ↪ Fin (k+1) × Fin (k+1) :=
                  ⟨fun p => (p.1.castSucc, p.2.castSucc), fun a b h => by
                    simp [Prod.ext_iff, Fin.castSucc_inj] at h; exact Prod.ext h.1 h.2⟩
                -- Define the embedding for new pairs (i, last k)
                let newEmb : Fin k ↪ Fin (k+1) × Fin (k+1) :=
                  ⟨fun i => (i.castSucc, Fin.last k), fun a b h => by
                    simp [Prod.ext_iff, Fin.castSucc_inj] at h; exact h⟩
                -- The filtered set splits as a disjoint union
                have hunion :
                    Finset.univ.filter (fun p : Fin (k+1) × Fin (k+1) => p.1 < p.2) =
                    (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb ∪
                    Finset.univ.map newEmb := by
                  ext ⟨i, j⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_union, Finset.mem_map, emb, newEmb,
                    Function.Embedding.coeFn_mk]
                  constructor
                  · intro hij
                    by_cases hj : j = Fin.last k
                    · subst hj; right
                      exact ⟨i.castPred (Fin.ne_last_of_lt hij), by
                        ext <;> simp [Fin.castSucc_castPred]⟩
                    · left
                      have hj' : j ≠ Fin.last k := hj
                      have hi' : i ≠ Fin.last k :=
                        Fin.ne_last_of_lt (lt_trans hij (lt_of_le_of_ne (Fin.le_last j) hj'))
                      refine ⟨(i.castPred hi', j.castPred hj'), ?_, ?_⟩
                      · exact Fin.castPred_lt_castPred hij hj'
                      · ext <;> simp [Fin.castSucc_castPred]
                  · intro hij
                    rcases hij with ⟨⟨a, b⟩, hab, heq⟩ | ⟨a, heq⟩
                    · have h1 := congr_arg Prod.fst heq
                      have h2 := congr_arg Prod.snd heq
                      simp only at h1 h2
                      rw [← h1, ← h2]
                      exact Fin.castSucc_lt_castSucc_iff.mpr hab
                    · have h1 := congr_arg Prod.fst heq
                      have h2 := congr_arg Prod.snd heq
                      simp only at h1 h2
                      rw [← h1, ← h2]
                      exact Fin.castSucc_lt_last a
                have hdisj : Disjoint
                    ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb)
                    (Finset.univ.map newEmb) := by
                  rw [Finset.disjoint_left]
                  intro ⟨x, y⟩ hmem1 hmem2
                  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                    emb, newEmb, Function.Embedding.coeFn_mk] at hmem1 hmem2
                  obtain ⟨⟨a, b⟩, _, heq1⟩ := hmem1
                  obtain ⟨c, heq2⟩ := hmem2
                  have h1 := congr_arg Prod.snd heq1
                  have h2 := congr_arg Prod.snd heq2
                  simp only at h1 h2
                  rw [← h1] at h2
                  exact absurd h2.symm (Fin.castSucc_ne_last b)
                rw [hunion, Finset.card_union_of_disjoint hdisj,
                  Finset.card_map, Finset.card_map, Finset.card_univ, Fintype.card_fin]
              omega
          have := hcard_nat n; push_cast [this]; rfl
        rw [hcard_eq, Finset.sum_mul]
        exact gauss_sum_inv_le n C (by exact_mod_cast hC)

/-- On the support of `cachingOracle.withLogging`, every cache entry appears in the log.
Starting from initial cache `cache₀`, if the final cache maps `t ↦ some u`
and `cache₀ t = none`, then `⟨t, u⟩` is in the accumulated log `z.1.2`. -/
private lemma cache_subset_log_of_withLogging
    {α : Type} (oa : OracleComp spec α) (cache₀ : QueryCache spec)
    (z : (α × QueryLog spec) × QueryCache spec)
    (hz : z ∈ support (((simulateQ cachingOracle.withLogging oa).run).run cache₀))
    (t : spec.Domain) (u : spec.Range t) (htu : z.2 t = some u)
    (hnotinit : cache₀ t = none) :
    ⟨t, u⟩ ∈ z.1.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    -- For pure, the cache doesn't change: z.2 = cache₀
    simp only [simulateQ_pure] at hz
    -- z = ((a, []), cache₀), so z.2 = cache₀
    have h2 : z.2 = cache₀ := by
      have := congr_arg Prod.snd (show z = _ from hz)
      simpa using this
    simp [h2, hnotinit] at htu
  | query_bind t' oa ih =>
    -- Unfold simulateQ for query_bind
    simp only [simulateQ_query_bind, OracleQuery.input_query,
      OracleQuery.cont_query, id_eq] at hz
    -- WriterT.run distributes over bind (appending logs)
    change z ∈ support (((liftM (cachingOracle.withLogging t') >>=
        fun x => simulateQ cachingOracle.withLogging (oa x) :
        WriterT (QueryLog spec) (StateT (QueryCache spec) (OracleComp spec)) α)).run.run
        cache₀) at hz
    rw [WriterT.run_bind', StateT.run_bind] at hz
    -- Decompose support of bind at the OracleComp level
    rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨⟨u', w₁⟩, cache₁⟩, hstep1, hrest⟩
    -- u' : spec.Range t', w₁ : QueryLog spec, cache₁ : QueryCache spec
    -- hstep1 : ((u', w₁), cache₁) ∈ support of first step
    -- hrest has a match that reduces with the concrete pattern
    simp only at hrest
    -- Now hrest involves (Prod.map id (w₁ ++ ·) <$> ...).run cache₁
    rw [StateT.run_map] at hrest
    rw [support_map] at hrest
    obtain ⟨z', hz', rfl⟩ := hrest
    -- z = ((z'.1.1, w₁ ++ z'.1.2), z'.2)
    simp only [Prod.map, Function.id_comp] at htu ⊢
    -- htu : z'.2 t = some u
    -- Goal: ⟨t, u⟩ ∈ w₁ ++ z'.1.2
    rw [List.mem_append]
    -- Case split: is t already cached in cache₁ (the cache after the first step)?
    by_cases hstep : cache₁ t = none
    · -- t not cached after first step: entry came from continuation
      right; exact ih u' cache₁ z' hz' htu hstep
    · -- t cached after first step but not initially: the first step introduced it.
      -- Need to show ⟨t, u⟩ ∈ w₁ (the log from the first step).
      -- The first step is cachingOracle.withLogging t', which logs ⟨t', result⟩.
      -- Since cache₀ t = none and cache₁ t ≠ none, the first step cached t,
      -- meaning t = t' and it was a cache miss.
      -- withCaching preserves existing cache entries (cache only grows),
      -- so z'.2 t = cache₁ t = some u_cached.
      -- Therefore u equals the value cached in step 1.
      -- The first step logs ⟨t', u'⟩ giving w₁ = [⟨t', u'⟩].
      -- Since cache₀ t = none but cache₁ t ≠ none, the step cached t → t = t'.
      -- By cache monotonicity z'.2 t = cache₁ t = some u', so u = u'.
      left; sorry

/-- **Birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n²/(2|C|). -/
theorem probEvent_cacheCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n)
    (_hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Derive from log version via combined logging+caching oracle.
  -- The combined oracle `cachingOracle.withLogging` both caches and logs.
  -- Projecting out the log recovers cachingOracle (fst_map_run_withLogging).
  -- CacheHasCollision cache → LogHasCollision log pointwise since every
  -- distinct cache entry (t, u) has a corresponding log entry ⟨t, u⟩.
  -- The log collision probability is then bounded by the birthday bound.
  let combined := ((simulateQ cachingOracle.withLogging oa).run).run ∅
  have hproj : (fun z : (α × QueryLog spec) × QueryCache spec => (z.1.1, z.2)) <$>
      combined = (simulateQ cachingOracle oa).run ∅ :=
    congrArg (·.run ∅) (QueryImpl.fst_map_run_withLogging cachingOracle oa)
  rw [← hproj, probEvent_map]
  change Pr[fun z => CacheHasCollision z.2 | combined] ≤ _
  -- Step 1: CacheHasCollision z.2 → LogHasCollision z.1.2 on support of combined.
  -- Every cache entry (t, u) with cache t = some u was logged by withLogging,
  -- so two distinct cache inputs with HEq outputs appear in the log.
  have hcache_to_log : ∀ z ∈ support combined,
      CacheHasCollision z.2 → LogHasCollision z.1.2 := by
    sorry
  -- Step 2: Monotonicity of probEvent
  calc Pr[fun z => CacheHasCollision z.2 | combined]
      ≤ Pr[fun z => LogHasCollision z.1.2 | combined] :=
        probEvent_mono hcache_to_log
    _ = Pr[fun w => LogHasCollision w.2 | Prod.fst <$> combined] := by
        exact probEvent_comp combined Prod.fst (fun w => LogHasCollision w.2)
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
        -- Prod.fst <$> combined is the log distribution from cachingOracle.withLogging.
        -- The log collision probability for the caching oracle's log is ≤ than for the
        -- pure logging oracle's log, since caching only reduces collision opportunities
        -- (repeated queries return cached values with same input, not contributing to
        -- LogHasCollision which requires distinct inputs).
        sorry

/-! ## Per-Index Bound Versions -/

/-- Birthday bound for `cachingOracle` with per-index query bound. -/
theorem probEvent_cacheCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal := IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  have h := probEvent_cacheCollision_le_birthday_total oa _ htotal hC
  simp only [Nat.cast_mul] at h; exact h

/-- Birthday bound for single-index oracle specs (typical ROM case: `t²/(2|C|)`). -/
theorem probEvent_cacheCollision_le_birthday' {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have h := probEvent_cacheCollision_le_birthday oa hbound hC
  simp only [Fintype.card_unique, Nat.cast_one, one_mul] at h
  exact h

/-! ## Unpredictability -/

section Unpredictability

variable {spec' : OracleSpec.{0,0} ι} [spec'.DecidableEq] [spec'.Fintype] [spec'.Inhabited]

omit [spec'.DecidableEq] in
/-- **Fresh query uniformity**: querying `cachingOracle` at an uncached point
yields each value with probability `1/|C|`. -/
theorem probOutput_fresh_cachingOracle_query
    (t : spec'.Domain) (u : spec'.Range t)
    (cache₀ : QueryCache spec') (hfresh : cache₀ t = none) :
    Pr[= (u, cache₀.cacheQuery t u) | (cachingOracle t).run cache₀] =
      (Fintype.card (spec'.Range t) : ℝ≥0∞)⁻¹ := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hfresh]
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.run_lift, bind_assoc,
    pure_bind]
  simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, StateT.run]
  rw [show (do let x ← PFunctor.FreeM.lift (query t); pure (x, cache₀.cacheQuery t x)) =
    (fun x => (x, cache₀.cacheQuery t x)) <$> PFunctor.FreeM.lift (query t) from by
      simp [Functor.map, bind_pure_comp]]
  rw [probOutput_map_injective _ (fun a b hab => by exact Prod.ext_iff.mp hab |>.1)]
  exact probOutput_query t u

omit [spec'.DecidableEq] in
/-- **Unpredictability bound**: `Pr[cache miss] * 1/|C| ≤ 1/|C|`. -/
theorem probEvent_unqueried_match_le {α : Type} {t : ℕ}
    (oa : OracleComp spec' α)
    (_hbound : IsPerIndexQueryBound oa (fun _ => t))
    (predict : spec'.Domain) (_target : spec'.Range predict) :
    Pr[fun z => z.2 predict = none |
      (simulateQ cachingOracle oa).run ∅] *
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ ≤
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := by
  calc Pr[fun z => z.2 predict = none | (simulateQ cachingOracle oa).run ∅] *
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ :=
        mul_le_mul' probEvent_le_one le_rfl
    _ = (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := one_mul _

end Unpredictability

/-! ## Collision-Based Win Bound -/

/-- If winning implies a cache collision, the win probability is bounded by the birthday bound. -/
theorem probEvent_collision_win_le {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (win : α × QueryCache spec → Prop)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default))
    (hwin : ∀ z ∈ support ((simulateQ cachingOracle oa).run ∅),
      win z → CacheHasCollision z.2) :
    Pr[win | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
  le_trans (probEvent_mono hwin) (probEvent_cacheCollision_le_birthday' oa hbound hC)

end OracleComp
