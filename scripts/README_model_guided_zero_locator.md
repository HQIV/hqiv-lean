# Model-guided zero locator

Hybrid geometric + classical ζ-zero locator (Option 1), with Lean certificates for the
geometric chart and an Option 2 scaffold for deviation bounds.

## Geometric chart (Lean, proved)

- Model candidates: `t_k = 3π/4 + kπ` (`balanceCandidateHeight` in
  `Hqiv/Story/S3ModelGuidedZeroLocator.lean`).
- Critical amplitude `A(θ) = cos(θ − π/4)` vanishes exactly on `{ t_k }`.
- Cumulative harmonic phase sum `∑ (2π/n) H_n · A(θ)` vanishes on the same locus for
  any `N > 0` (exact factorization through `A(θ)`).
- Antipodal pairs cancel unconditionally; locator is robust to that symmetry.

## Scaling (honest)

| Weight | Growth |
|--------|--------|
| `∑_{n≤N} Λ(n)` | Θ(`N`) (PNT) |
| `2π ∑_{n≤N} H_n/n` | Θ(`(log N)²`) |
| `Δ_N` (difference) | dominated by linear Λ term at large `N` |

The parallel is structural (shared `A(θ)`, cancellation), not term-by-term numerical
matching. Model candidates are spaced by `π`; true zero spacing is ≈ `2π/log t`.

## Python hybrid locator

```bash
python3 scripts/model_guided_zero_locator.py --T 50 --window 1.0 --compare 10
```

Functions:

- `model_candidates_up_to(T)` — arithmetic candidate ladder
- `locate_zeros_near(candidate, window)` — Hardy `Z(t)` sign changes (`mpmath.siegelz`)
- `model_guided_zero_locator(T, window)` — combined search

Output: `data/model_guided_zero_locator.json`

Tests: `python3 -m unittest scripts.test_model_guided_zero_locator`

## Option 2 (deviation theorem scaffold)

`Hqiv/Story/S3ModelGuidedLocationBound.lean`:

- `distanceToNearestBalanceCandidate t` — always `≤ π/2` (unconditional)
- Under `RollingZetaIdentificationAtCriticalLine`, zeros are **exactly** at candidates
- `ModelGuidedLocationBound` + `ZetaZeroNearModelCandidate` — target for remainder-driven
  bounds using `weightDifference N` / `WeightDifferenceAsymptoticSlot`
- Deviation bounds are expected to **grow with `T`** (model spacing `π` vs classical
  `2π/log t`)

`Hqiv/Story/S3CumulativeHarmonicPhase.lean` (Option A):

- `weightDifferenceLeadingTerm N = Λ_N − π(log(N+1))²`
- `weightDifferenceAsymptoticSketch` — exact decomposition + named remainder bound
- Classical leading terms: `Λ_N ~ N`, `W_N ~ π(log N)²` (documented, not proved)

Theorem target (Option B): `ModelGuidedZeroLocationTheoremTarget` — if
`|Δ_N|/Λ_N ≤ ε`, then `|γ − t_k| ≤ f(ε,T)` with coarse envelope `π/2 + ε·T`.
Prove via `ExplicitFormulaLocationInput` + Hardy-`Z` / argument variation.

## Goldbach holomorphic geometric-mean bridge

`Hqiv/Story/S3GoldbachHolomorphicWeightBridge.lean`:

- Midpoint partitions `p + q = 2N` with geometric mean `√{pq} ≤ N` (proved)
- On `Re s = 1/2`: `√{pq} · ‖(pq)^{−s}‖ = 1` (proved)
- `GoldbachHolomorphicWeightBridge N` — named input: holomorphic GM regularity
  bounds `weightDifferenceEulerMaclaurinRemainder` after exact main term `Λ_N − π(log N)²`
- Feeds `WeightDifferenceRemainderBound` → `ModelGuidedLocationBound`

`Hqiv/Story/S3GoldbachPartitionGeneratingFunction.lean`:

- `GoldbachPartitionGeneratingFunction` — `F(z)` + holomorphy domain + midpoint GM readout
- `HolomorphicMeanControlsWeightRemainder N` — explicit implication
  `IsHolomorphicGoldbachPartition → |euler tail| ≤ bound`
- `GoldbachHolomorphicRegularityCertificate` — witnessed holomorphy + implication
- Proved wiring: certificate → `WeightDifferenceAsymptoticSlot` → `ModelGuidedLocationBound`

## Path A Perron Cauchy error probe

```bash
python3 scripts/hqiv_perron_cauchy_error_probe.py --M 50 200 1000 --T 1 2
```

Coupling / smoother sweep (center offset + Fejér vs Gaussian):

```bash
python3 scripts/hqiv_perron_cauchy_error_probe.py --M 200 --T 1 2 4 8 \
  --coupling-sweep --sweep-only
# custom offsets: --center-offsets -10,-5,0,5,10
# smoothers only: --smoothers gaussian,fejer
```

Writes `data/perron_cauchy_error_probe.json` (Path A grid) and, with `--coupling-sweep`,
`data/perron_coupling_sweep_probe.json` (structural coupling only — no σ₀ dependence).
`goldbachSmoothedPerronCauchyRectangleErrorTotalBound` at `x = 1`.

**Numerical takeaway (mid `σ₀`, `σ = σ₀ + 0.5`):** tail bookkeeping is negligible;
left-edge error dominates and is ~99% **A₂ smoothed** (not the `8×` FMPlusOne term).
Within A₂, **aggregate coupling** `|∑ K_T(N;M)(a_N−1)|` is the largest sub-term.
Path 2 (sharp A₂.1) is low priority unless that balance changes.

**Fejér hybrid left-edge** (partial Path A; probe + Lean):
`goldbachFejerGaussianHybridLeftEdgeMellinLinkError` = Fejér coupling bound +
Gaussian-chart A₂ kernel slack + `8×` FMPlusOne. At `M=200`, `center=M`, Fejér coupling
is ~35–58% of Gaussian (compact support); hybrid left-edge savings track coupling delta
while Mellin slack stays on the Gaussian normalisation until a full Fejér Mellin route exists.

Lean bridge: `Hqiv/Story/S3ExplicitFormulaLocationBridge.lean` — **proved**
`perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate`:
identification + Path A certificate ⇒ `PerronToWeightDifferenceBridge.em_remainder_le`.
Instantiate identification via `GoldbachExplicitFormulaEulerMaclaurinContourDuality`.

## References

- `S3CumulativeHarmonicPhase.lean` — cumulative sum, `Δ_N`, von Mangoldt parallel
- `S3CriticalCirclePhaseCancellation.lean` — Euler phase cancellation parallel
