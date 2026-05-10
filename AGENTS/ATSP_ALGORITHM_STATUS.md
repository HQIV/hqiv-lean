# Directed Torus ATSP: Algorithm Status and Proof Boundary

This note summarizes the current ATSP algorithm family in `scripts/directed_torus_atsp_oracle.py`, what is formally proved in Lean, and what is still heuristic.

## 1) Algorithm Family (Python)

Current optimizer modes:

- `golden-section`
  - Direct 1D minimization on the narrow arc chart.
- `spiral`
  - Golden-angle style sampling on the narrow arc.
- `anchored-spiral`
  - Arc sampling around annulus anchors from directed city pairs.
- `anchored-intercept`
  - Intersections between anchor families (near-coincident permutations).
- `recursive-intercept`
  - Multi-level anchor/intercept expansion with beam budget.
- `reverse-flip-prune`
  - Start from recursive candidates, remove overlap-heavy and rapidity-dominated edge signatures while keeping a local best-cost witness.
- `iterative-peel-anneal`
  - Repeats:
    1. peel ladder in arity (`k = start_arity .. n`, i.e., arity +1 each stage),
    2. merge/dedupe candidate pool at each macro round,
    3. optional early-stop if round-best cost does not improve.

Additional research script:

- `scripts/rapidity_first_atsp_oracle.py`
  - Shell-ordered rapidity ladder inspired by `SpatialSliceRapidityScaffold` /
    `RapidityArcPatchBridge`,
  - finite periodic slot families per shell,
  - OSHoracle-style flip-prune between shell snapshots,
  - optional lightweight local completion (`2opt`, `relocate`, `both`),
  - shell-periodicity telemetry for 1D rapidity traces.
- `scripts/benchmark_rapidity_first_atsp.py`
  - Benchmarks rapidity-first search against the directed-torus baseline,
  - supports cache-backed exact references keyed by matrix hash,
  - intended for one-time exact 11/12-city solves that can be reused across
    later tuning runs.

Scoring channels in use include:

- root-distance term,
- normalized tour cost,
- associator term,
- optional tau term,
- optional roughness penalties.

Rapidity-based prune scale policy supports:

- `fixed`,
- `sqrt-n`,
- `sqrt-n-over-arity` (currently implemented as `sqrt(k)` behavior so peel side is mild and `k=n` settles at `sqrt(n)`).

## 1b) Physical uniqueness vs algorithmic channel freedom

For agents working across the HQIV physics and ATSP/QC-sim notes, keep the distinction sharp:

- The physical HQIV curvature imprint is the canonical octonionic slot `6^7 * sqrt(3)`, not an arbitrary rapidity/manifold choice.
- The quaternionic `6^3 * sqrt(3)` comparison is useful as a contrast channel, but it is not the canonical shell-imprint normalization in the current Lean corpus.
- In the ATSP / oracle / QC-sim setting, arbitrary manifold parameterizations, chart choices, or rapidity schedules may still be useful as **algorithmic superposition-channel selectors**.
- That freedom is heuristic and task-facing: it helps choose which candidate families, interference patterns, or prune channels are emphasized during search.
- It should **not** be described as changing the physical HQIV curvature slot itself.

## 2) Lean-Proved vs Heuristic Boundary

## Lean-proved (in repository)

From `Hqiv/Geometry/GeneralizedGeometricOracle.lean`:

- `tsp_optimal_candidate_exists`
  - Any nonempty candidate list has a tour-cost minimizer.
- `prune_preserves_optimal_if_witness_kept`
  - If prune keeps an optimal witness and prune result is a subset, optimality is preserved in pruned list.
- `unit_witness_optimal_of_lower_bound`
  - If a witness has cost `n` and every candidate cost is at least `n`, that witness is globally optimal.
- `prune_boundary_safe_of_unit_witness`
  - Proof-first prune boundary: pruning by `tourCost ≤ n` is safe when a cost-`n` witness exists and `n` is a global lower bound.
- `recursive_pipeline_deterministic`
  - Recursive pipeline construction is deterministic.
- `recursive_level_count_bounded`, `recursiveCandidateBudget`, related bounds
  - Recursive candidate counts are budget-bounded under stated step hypotheses.
- `annulus_candidate_optimal_exists`, `intercept_candidate_optimal_exists`
  - Existence of optimal candidate in those candidate families (nonempty case).
- `root_closest_candidate_minimizes_tourCost`
  - Root-minimal implies cost-minimal **under explicit monotonicity hypothesis**.
- `directed_torus_effective_minimizes_tourCost`
  - Effective-score minimization implies cost minimization **under explicit alignment hypothesis**.

From `Hqiv/Geometry/EuclideanAxisBounds.lean`:

- `euclideanDist_le_sqrt_two_of_axisDiff_le_one`
- `euclideanDist_le_sqrt_three_of_axisDiff_le_one`
- `euclideanDist_le_sqrt_dim_of_axisDiff_le_one`
- `euclideanDist_le_two_mul_sqrt_dim_of_axisDiff_le_two`
- `l1Dist_le_two_mul_dim_of_axisDiff_le_two`

These are geometric norm bounds, not combinatorial optimal-tour guarantees.

## Not proved (currently heuristic / empirical)

- Global optimality of Python ATSP solver at moderate/large `n`.
- Safety of rapidity-dominated-edge pruning as a theorem for all inputs.
- Claim that `sqrt(n)` rapidity prune captures all optimal tours.
  - Empirically promising on tested nonnegative random cases; still unproved.
- Claim that `sqrt(2)` is universally safe.
  - Not true in general symmetric matrices; only meaningful under planar Euclidean assumptions, and still needs a prune-rule-specific proof.
- Any polynomial-time guarantee for arbitrary dense ATSP.
- Any theorem that a particular manifold embedding or rapidity schedule is the uniquely correct search channel for arbitrary ATSP instances.
  - Those are currently heuristic design choices for selecting a useful superposition/emphasis channel, not physically forced constants.

## 2b) Big-O / certification ledger (current honesty state)

This records asymptotic claims as **certified** only when they are backed by Lean theorems in-repo.

- **Rapidity factor candidate scan (`RapidityPolarFactorOracle`)**
  - Claim: constant candidate scan budget.
  - Lean status: **certified** via `allCandidates_length`, `factorPair_candidate_scan_le_budget`, `factorPair_from_3spiral_is_O1`.
  - Concrete bound: filtered scan inspects at most `7` candidate entries (`3` projection + `4` anchors).
  - Generic scan-cost certificate: `Bridge.firstValidDivisor_scanCost_le_length` (O(k) in input-list length), specialized to current curvature-candidate list by `Bridge.allCandidatesWithCurvature_length` + `Bridge.pickFromCandidates_scanCost_le_seven` (constant `≤ 7` in this scaffold).
- **Recursive SAT/ATSP explored-level bounds (`GeneralizedGeometricOracle`)**
  - Claim: bounded explored levels under beam/topk/depth hypotheses.
  - Lean status: **certified (conditional)** via `recursive_level_count_bounded`, `recursiveCandidateBudget`, and slack/gap variants.
  - Asymptotic reading: exponential/factorial-style upper envelopes depending on certificate hypotheses, not global polynomial-time guarantees.
- **Ribbon-cover residual envelope (`SATRapidityPlaneBridge`)**
  - Claim: residual budget can be pushed to a natural root-envelope bound.
  - Lean status: **certified (conditional)** via `ribbon_cover_collapse_hasPolynomialResidualBudget` and `ribbon_cover_collapse_implies_nat_root_envelope`.
- **Python ATSP solvers (`directed_torus_atsp_oracle.py`, edge-space variants)**
  - Claim: practical runtime scaling can be benchmarked, but global complexity class for arbitrary dense ATSP remains open.
  - Lean status: **not certified** as polynomial-time for general instances.

## 3) What “best tours exist on an arc” means right now

Formal status:

- Lean proves minimizers exist in nonempty candidate families.
- It does **not** currently prove that arc-generated families are globally complete for ATSP.

Operational status:

- Python generates arc-based candidates and returns the best found.
- For small `n` where exact check is enabled, we can measure exact gap.
- For larger `n`, output is heuristic best-found.

## 4) Current empirical signal (small exact-checked targets)

Recent small-target checks (`n=8..10`) showed:

- iterative peel/anneal and baseline reverse mode currently produce similar best-cost quality,
- no exact hit in that measured slice,
- typical mean relative gap roughly in the ~20% range for those seeds/configs.

Interpretation:

- framework is stable and structured,
- but current prune/anneal settings are not yet closing exactness on small hard instances.

## 5) Additional Improvements (high priority)

1. **Certified prune mode (hybrid)**
   - Keep rapidity prune, but add local exact witness checks before committing aggressive prunes.
2. **Two-stage completion**
   - Use geometric solver for top-K candidate seeds, then exact neighborhood search (2-opt/3-opt/exact micro-branch) per seed.
3. **Euclidean-specific prune ledger**
   - Separate metric assumptions:
     - symmetric only,
     - metric,
     - planar Euclidean embedding.
   - Use stronger certified inequalities only in matching regime.
4. **Adaptive iterative scheduler**
   - Start with broad candidate reservoir at low arity; tighten only when round improvement stalls.
   - Keep early-stop gate and add “re-expand” gate when stagnation is detected.
5. **Proof-track extension in Lean**
   - Formalize degeneracy barrier (uniform-cost case => all tours tie).
   - Formalize stronger sufficient conditions under which rapidity prune is witness-safe.

## 6) Practical command patterns

Iterative peel/anneal with arity ladder and early stop:

- `python3 scripts/directed_torus_atsp_oracle.py --optimizer iterative-peel-anneal --iterative-rounds 4 --iterative-arity-start 2 --iterative-stage-topk 12 --iterative-early-stop-patience 1 --iterative-early-stop-tol 1e-9 --rapidity-prune --rapidity-prune-scale 1.0 --rapidity-prune-scale-mode sqrt-n-over-arity --demo-cities 10 --exact-if-at-most 10`

Rapidity prune falsification harness:

- `python3 scripts/check_rapidity_prune_safety.py --n-min 7 --n-max 8 --trials 100 --scales "1.0,1.4142135623730951,2.0,2.5"`

Step-down runtime harness:

- `python3 scripts/benchmark_atsp_stepdown.py --n-min 8 --n-max 12 --trials 10 --optimizer golden-section --floor-n 7`

## 7) Edge-space Tensor Phase-2 (proof-aware truncation)

Implemented in `scripts/edge_space_atsp_oracle.py`:

- Tensor truncation now emits explicit residual telemetry:
  - `trunc_residual` (dropped absolute channel mass),
  - `trunc_residual_ratio`,
  - `trunc_error_bound_empirical` (observed dropped contribution),
  - `trunc_error_bound_certified` (proof-channel bound).
- Candidate payload and aggregate payload now report these channels.
- Local amplitudes are clamped to `[0, 1]` so the certified bound hypothesis is explicit in runtime behavior.

Lean proof channel added in `Hqiv/Geometry/TensorTruncationBounds.lean`:

- `weightedPriority_split`
- `weightedPriority_error_eq_dropped`
- `abs_weightedPriority_error_le_dropped_abs`
- `abs_weightedPriority_error_le_droppedWeightMass_of_unit_amp`

Interpretation:

- The certified bound states that if local amplitudes are unit-bounded, the truncation-induced weighted-priority error is at most dropped weight mass.
- This gives a proof-aligned residual ledger for later boundary coupling (Phase 3), while keeping hard witness safety logic unchanged.

## 8) Edge-space Tensor Phase-3 (boundary coupling)

Implemented in `scripts/edge_space_atsp_oracle.py`:

- Hard boundary remains unchanged and witness-safe (`cost <= ub` with UB witness retention in soft gate path).
- Soft boundary now uses residual-gated coupling:
  - compute residual metric from truncation channel (`trunc_residual_ratio` by default, or certified absolute residual),
  - only allow boundary shrink (`alpha_eff < 1`) when residual metric is below `residual_gate_threshold`,
  - above gate, soft boundary is relaxed to `UB` (`alpha_eff = 1`) so no residual-driven over-tightening occurs.
- New CLI controls:
  - `--residual-gate-threshold`
  - `--residual-gate-strength`
  - `--residual-gate-use-ratio` / `--no-residual-gate-use-ratio`
- New telemetry:
  - `soft_alpha_effective` in trace rows,
  - `soft_coupling_trigger_count`, `soft_coupling_total_count`, `soft_coupling_trigger_rate` in payload.

## 9) Edge-space Tensor Phase-4 (optional topological channel)

Implemented in `scripts/edge_space_atsp_oracle.py` as a score-only regularizer:

- Added a lightweight local cycle-circulation proxy:
  - compares forward vs reverse local directed 3-cycle costs around tour windows,
  - reports marker mean, absolute mean, and jitter.
- Integrated only into `effective_score` via optional weight:
  - `topology_regularizer = w_top * (abs_mean + w_jitter * jitter)`
  - no hard/soft prune condition uses this channel.

CLI controls:

- `--topology-regularizer-weight` (default `0.0`, disabled by default)
- `--topology-jitter-weight` (default `0.5`)
- `--topology-window` (default `3`, requires `>= 3`)

Telemetry:

- Candidate-level:
  - `topology_marker_mean`
  - `topology_marker_abs_mean`
  - `topology_marker_jitter`
  - `topology_regularizer`
- Payload means:
  - `mean_topology_marker_mean`
  - `mean_topology_marker_abs_mean`
  - `mean_topology_marker_jitter`
  - `mean_topology_regularizer`

## 10) Edge-space Tensor Phase-5 (topology calibration + adaptive policy)

Implemented in `scripts/edge_space_atsp_oracle.py`:

- Added topology weighting policies (still score-only, non-pruning):
  - `off`
  - `fixed`
  - `residual-gated`
  - `arity-ramp`
  - `residual-arity`
- Added adaptive controls:
  - `topology_residual_floor` (fallback scale when residual gate fails)
  - `topology_arity_exponent` (shape of arity ramp)
  - `topology_max_weight` (applied-weight cap)
- Added candidate and trace telemetry:
  - candidate: `topology_weight_applied`
  - trace: `topology_weight_mean`, `soft_alpha_effective_mean`
  - payload: `mean_topology_weight_applied`, selected topology policy parameters.

Added calibration harness in `scripts/benchmark_edge_topology_calibration.py`:

- Sweeps topology policy/weights/windows/jitter weights on exact-checkable instances.
- Reports:
  - mean exact gap,
  - delta vs topology-off baseline,
  - mean runtime,
  - mean applied topology weight.
- Intended as the Phase-5 decision surface for selecting robust defaults.

## 11) Certified hybrid prune + seeded completion (current extension)

Lean proof-track additions:

- In `Hqiv/Geometry/TensorTruncationBounds.lean`:
  - `abs_weightedPriority_error_le_gate_of_unit_amp_of_droppedWeightMass_le`
    (gate form of the tensor residual certificate).
- In `Hqiv/Geometry/GeneralizedGeometricOracle.lean`:
  - `rapidityDominatedEdgeSafe`
  - `prune_preserves_optimal_if_witness_kept_hybrid`
  - `prune_boundary_safe_of_unit_witness_hybrid`
  - `uniform_cost_effective_order_iff_geometric_order`
  - `degenerate_uniform_cost_yields_near_optimal_tour`

Interpretation:

- The hybrid prune theorem carries:
  - witness-preservation core,
  - tensor residual gate side condition,
  - rapidity-dominated-edge safety side condition.
- This gives a formal sufficient-condition scaffold for certified hybrid pruning.

Two-stage completion (Python):

- `scripts/edge_space_atsp_oracle.py` now runs seeded local completion after the
  geometric stage:
  - top-K seeds from geometric pool,
  - deterministic 2-opt best-improvement,
  - optional sampled 3-opt-style reconnections,
  - improved tours merged back into candidate pool.
- New controls:
  - `--seeded-local-search`
  - `--seeded-local-topk`
  - `--seeded-local-rounds`
  - `--seeded-use-3opt`
  - `--seeded-three-opt-trials`
- New telemetry:
  - `seeded_local_candidates_added`
  - `seeded_local_improvements`

Degenerate uniform-cost detector (Python):

- Added `detect_uniform_cost_matrix` in `scripts/edge_space_atsp_oracle.py`.
- New controls:
  - `--degenerate-uniform-tol`
  - `--degenerate-short-circuit`
- New payload telemetry:
  - `degenerate_uniform_detected`
  - `degenerate_uniform_spread`
  - `degenerate_short_circuit`
- If short-circuit is enabled and uniform-cost is detected, the solver emits a
  direct geometric-regularized witness without running full peel loops.

## 12) Worst-case certified behavior envelope (Lean)

Added module: `Hqiv/Geometry/ATSPWorstCaseCertified.lean` (imported in `HQIVLEAN.lean`).

Core certified statements:

- `approximationRatio`
- `exact_degenerate_ratio_eq_one`
- `exact_degenerate_ratio_le_nat_root_envelope`
- `additive_gap_implies_ratio_bound`
- `near_degenerate_ratio_le_nat_root_envelope`
- `worst_case_certified_behavior_nat_root_envelope`
- `random_poly_search_hits_nat_root_envelope_of_certificate`

Interpretation:

- Exact uniform-cost degeneracy gives ratio exactly `1`.
- Near-degenerate additive gap assumptions yield a certified multiplicative
  envelope of form `1 + n^(1/n)`.
- Random/poly-search claims are exposed through explicit certificate hypotheses
  (no hidden probabilistic assumptions).

Finite-sample empirical certificate wiring:

- Lean-side certificate objects:
  - `EnvelopeCertificate`
  - `validEnvelopeCertificate`
  - `validEnvelopeBatch`
  - `validEnvelopeCertificate_implies_bound`
  - `validEnvelopeBatch_member_implies_bound`
- Python exporter:
  - `scripts/export_worst_case_envelope_certificate.py`
  - emits JSON rows with `(n, oracleCost, optimalCost, ratio, bound, valid)` plus
    batch summary and pass-rate for Lean/verification handoff.

Bridge roadmap (top-priority theorem target):

- `Hqiv/Geometry/ATSPWorstCaseCertified.lean` now includes
  `OracleBridgeAssumptions` and bridge theorems:
  - `oracle_bridge_implies_nat_root_envelope`
  - `oracle_bridge_exact_degenerate_implies_envelope`
- This provides the formal contract for the remaining proof obligations:
  1. projection/truncation residual -> additive gap contribution,
  2. seeded local completion monotonicity,
  3. global additive gap aggregation into `ε ≤ OPT * n^(1/n)`.

Progress update:

- `Hqiv/Geometry/ATSPWorstCaseCertified.lean` now includes
  `local_completion_preserves_additive_gap`, and the bridge contract has been
  tightened so `oracle_bridge_implies_nat_root_envelope` *derives* global gap
  from:
  - seed additive gap (`hSeedGap`),
  - local completion monotonicity (`hLocalCompletion : oracleCost ≤ seedCost`).

Further progress (projection/residual channel integrated):

- Added `projection_residual_implies_seed_gap` in
  `Hqiv/Geometry/ATSPWorstCaseCertified.lean`.
- `OracleBridgeAssumptions` now carries explicit certified error channels:
  - `tensorResidualErr`
  - `rapidityErr`
  - `axisErr`
  with assumptions:
  - `hProjResidual : seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr`
  - `hResidualBudget : tensorResidualErr + rapidityErr + axisErr ≤ ε`
- `oracle_bridge_implies_nat_root_envelope` now *derives*:
  1. seed additive gap from residual channels,
  2. global additive gap via local completion monotonicity,
  then applies the `1 + n^(1/n)` envelope theorem.

Geometric-first route (`n = 3`) added:

- Lean (`Hqiv/Geometry/ATSPWorstCaseCertified.lean`):
  - `envelope3`
  - `n3_exact_degenerate_ratio_eq_one`
  - `n3_exact_degenerate_ratio_le_envelope`
  - `n3_additive_perturbation_ratio_bound`
  - `n3_additive_perturbation_within_envelope`
- Python probe:
  - `scripts/n3_geometric_degeneracy_probe.py`
  - demonstrates degenerate baseline and additive perturbation path with exact
    checks against the `1 + 3^(1/3)` envelope.

`3 + 1` and successor generalization added (Lean):

- In `Hqiv/Geometry/ATSPWorstCaseCertified.lean`:
  - `envelope4`
  - `n4_exact_degenerate_ratio_eq_one`
  - `n4_exact_degenerate_ratio_le_envelope`
  - `n4_additive_perturbation_within_envelope`
  - `envelopeSucc`
  - `succ_exact_degenerate_ratio_le_envelope`
  - `succ_near_degenerate_ratio_le_envelope`
  - `succ_hybrid_channels_and_local_monotone_imply_envelope`

This now gives an explicit route:
`n = 3` baseline -> `n = 4` (3+1) -> generic successor (`n+1`) theorem family.

## 13) Post-audit roadmap update (SAT/rapidity cross-thread progress)

This section records concrete progress from the Lean corpus audit and the next execution targets.

### Progress recorded now

- The SAT rapidity collapse chain and the rapidity-polar factor-oracle soundness chain are now indexed in `AGENTS/THEOREMS.md` (so they are no longer hidden in module-level exploration).
- The roadmap layer now treats `SATRapidityPlaneBridge` collapse theorems as first-class inputs for arithmetic/search-envelope reasoning, rather than isolated SAT geometry facts.
- The factor-oracle theorem chain is now explicitly recognized as certificate-oriented (`factorPair_from_3spiral_correct`, `pickFromCandidates_sound`, `chart_bridge_and_picker_sound`, `factorTree_prod_eq`) and not merely script heuristic guidance.
- Concrete cross-language progress landed:
  - Python `geometric_factorization_solver.py` now emits `one_step_pick_certificate` payload fields for nontrivial divisor picks.
  - Lean `RapidityPolarFactorOracle` now packages the same hypothesis shape via `Bridge.OneStepPickCertificate` with theorem outputs `OneStepPickCertificate.sound` and `OneStepPickCertificate.pair_product`.
- Generalized SAT oracle wiring now landed:
  - `scripts/generalized_geometric_oracle.py` emits normalized bridge payload `factor_pick_bridge` (schema `hqiv.one-step-pick-bridge.v1`).
  - In `--mode sat` and `--mode sat-competition`, payload now includes `sat_bridge_certificates.one_step_pick` by default.
  - The normalized object carries Lean target metadata (`Hqiv.Geometry.Bridge.OneStepPickCertificate`) and theorem consumers (`OneStepPickCertificate.sound`, `OneStepPickCertificate.pair_product`) plus runtime checks (`is_nontrivial`, `divides`, `pair_product_ok`) and `theorem_ready`.
- Factorization solver alignment progress landed (`scripts/geometric_factorization_solver.py`):
  - removed trial-division-derived stop budget dependency from the main loop;
  - moved to SAT/ATSP-style pipeline: register candidate generation -> bit-flip neighborhood expansion -> step-level prune trace;
  - register width is now posed by the shell search window (`bit_length(floor(sqrt(n)))`);
  - preserves Lean-facing one-step certificate payload.
  - now supports recursive cofactor peeling (`--prime-factorization`) to produce a full prime-factor list when splits succeed, with a trace log and product-verification flag (`verified_product`), without requiring prime inputs.
- Runtime benchmark note (10s break test by increasing bit length):
  - old trial-division-style version broke around `~58-60` bits;
  - refactored generate/flip/prune version showed **no 10s break** up to `512` bits on probable-prime track (with fixed `max_steps=120`), and remained sub-`0.05s` in sampled runs.

### Immediate execution milestones (next edits/scripts)

1. **ATSP-SAT bridge contract (docs + assumptions)**
   - Add a compact bridge contract to `ASSUMPTIONS.md` tying SAT ribbon-cover certificates to `ATSPWorstCaseCertified.OracleBridgeAssumptions` fields (`tensorResidualErr`, `rapidityErr`, `axisErr`) without overclaiming automatic implication.

2. **Certificate-emitting oracle payload (script progress target)**
   - Extend geometric oracle outputs so candidate picks carry:
     - candidate family used,
     - divisor-witness fields for `pickFromCandidates_sound`,
     - optional shell-lock witness metadata when available.
   - Goal: make script runs directly consumable by Lean-side witness checkers.

3. **Root-envelope handshake path**
   - Add a thin handoff script that maps SAT/ribbon residual telemetry to the JSON shape expected by `export_worst_case_envelope_certificate.py`, so the SAT channel can be benchmarked against the same `1 + n^(1/n)` envelope ledger.

4. **Transport-budget unification pass**
   - Reuse one budget naming path (`shellIndexFromTimeAngle` / `accessibleModeBudgetUpToPhiTime`) across SAT/ATSP scheduling knobs where appropriate, and mark any non-equivalent budget as explicitly heuristic.

### Non-overclaim guardrails

- No claim that SAT geometric certificates alone solve dense ATSP globally.
- No claim that rapidity pruning is universally witness-safe without theorem hypotheses.
- No claim that script-side payloads are proofs until hypotheses are instantiated in Lean.

