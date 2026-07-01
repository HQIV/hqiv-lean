import Hqiv.Story.S3ZeroHolonomyGoldbachChain
import Hqiv.Story.S3CumulativeHarmonicPhase
import Hqiv.Story.S3ModelGuidedZeroLocator
import Hqiv.Story.S3ConstructionsEquivalent
import Hqiv.Story.S3MidpointEckmannHiltonSoe
import Hqiv.Story.S3MidpointSO4DeltaOrbit
import Hqiv.Story.S3SO4SquareOrbitCollision
import Hqiv.Story.S3OrbitEnergyNonExtinctionBridge
import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Hqiv.Story.S3PolarProjectionCollapse
import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3DeltaHarmonicDischargeBridge
import Hqiv.Story.S3PhysicsInvarianceDischargeBridge
import Hqiv.Story.S3HarmonicMulModHolonomy
import Hqiv.Story.S3TwinMulModTwiddleBridge
import Hqiv.Story.S3DeltaHolonomyMulModAnchorBridge
import Hqiv.Story.S3PlasticRatioTwinTwiddleAnchor
import Hqiv.Story.S3GoldbachGapOneActivationBudget
import Hqiv.Story.S3SquareOrbitGapOneBridge
import Hqiv.Story.S3GoldbachGapOneDensityPressure
import Hqiv.Story.S3HeatFlowArrowNoBackprojection
import Hqiv.Story.S3OctonionS7TorsionCancellation

/-!
# RH–Goldbach geometric bridge — status capstone

This module is the **single review entry point** for the RH–Goldbach joint bridge.
It collects what is proved, what is open, and how the geometric reformulations relate
to Mathlib's `RiemannHypothesis` and the repo's Goldbach predicates.

---

## 1. What is already a theorem (packaging)

The informal "bridge hypothesis" often conflates two claims.  The first is **proved**:

> **`SO8ProjectedHalfSlopeBridge 2` ↔ `RiemannHypothesis ∧ GoldbachParity`**

See `rh_goldbach_bridge_equivalence_is_theorem` (re-exporting
`so8_projected_half_slope_two_iff_rh_and_goldbach_parity` from
`S3ExplicitFormulaDualitySlot`).

The SO(8) bridge packages two explicit fields:

| Bridge field | Classical content |
|--------------|-------------------|
| `critical_line` (`WeilPositivityForcesCriticalLine`) | Mathlib `RiemannHypothesis` |
| `midpoint_pairs` (`SO4ZetaHolonomyForcesMidpointPairs 2`) | `GoldbachParity` |

**Channel separation** (`rh_goldbach_bridge_channels_separated`): the two fields are
*independently* equivalent to RH and Goldbach — no cross-channel leakage.

**Master recharacterization** (`rh_goldbach_joint_bridge_master_iff`): the same bridge
is also equivalent to polar collapse ∧ Goldbach, square-root spectral weights ∧ Goldbach,
and Fourier/harmonic balancing ∧ Goldbach.  These are packaging equivalences, not
stronger claims.

After the carrier is built, the equivalence feels almost definitional: the shared
normalized `1/2` readout is the critical-line lock on the ζ channel and the midpoint
slope `N/(p+q) = 1/2` on the additive channel (`so4_orthogonal_tangent_midpoint_slope_eq_half`).

---

## 2. What remains open (discharge)

The second claim — that the geometric balancing condition **holds unconditionally**
from octonion/Fano/SO(4) structure alone — is **open**:

> **`GeometricHalfSlopeDischarge` := `SO8ProjectedHalfSlopeBridge 2`**

`bridge_discharge_iff_millennium` proves discharging the bridge is **provably exactly as
hard** as `RiemannHypothesis ∧ GoldbachParity`.  This repository does **not** claim
to prove either classical conjecture.

The Δ-from-`H_n` architecture (`S3DeltaHarmonicDischargeBridge`) makes the same
honest split explicit in four layers: harmonic split + equator factor + G₂ seed
(**proved**, `DeltaHarmonicUnconditionalCarrier`); ζ zero activation and Goldbach pair
existence (**hypotheses** ≡ RH ∧ Goldbach); discharge
(`DeltaHarmonicBalancingForcesBridge` = `SO8ProjectedHalfSlopeBridge 2`, **open**).
See `delta_harmonic_discharge_iff_geometric_discharge` and
`delta_harmonic_discharge_iff_millennium`.

**Physics mining (Layer P).**  HQIV rapidity/Lorentz closure, covariant O-Maxwell
(`√(-g)` cancellation, flat-jet Christoffel drop), and S₃ twiddle multiset
invariance are bundled in `S3PhysicsInvarianceDischargeBridge` as
`PhysicsInvarianceUnconditionalCarrier`.  They explain *why* the balancing
geometries align; global discharge still equals RH ∧ Goldbach
(`GlobalCovarianceForcesDischarge`).

**Strip–rapidity lock (proved).**  `rapidityNormalizedJetCoeff` equals `(2σ−1)/√2`
under the canonical chart in `S3StripRapidityEquatorIdentification`
(`rapidity_jet_coeff_eq_equator_factor`, `flat_jet_covariant_div_eq_equator_times_surrogate`).

### ζ channel (RH)

Every geometric locator (Weil positivity, polar collapse, square-root spectral weights,
interior factorization, …) is **equivalent to RH**, not stronger — see
`S3ConstructionsEquivalent` and `S3SpectralResonanceChanneling`.

Recent RH-side faces are also recorded without strengthening the target:
heat-flow vaporization (`VaporizationForcesCriticalLine`) and S⁷ torsion
cancellation at nontrivial zeros are both **equivalent to RH**.

### Goldbach channel

The constructive target localizes to **EH forward collapse** at composite midpoints:

`EckmannHiltonForwardCollapse N` ↔ `CompositeMidpointHasSurvivor N`

Global discharge requires either:

* **`EckmannHiltonCardinalityObstruction N`** — duplicate reflect crossings force a stack
  survivor (pigeonhole route, `GoldbachG2Parity`); or
* **`SO4DeltaOrbitObstruction N`** — same conclusion from SO(4) gap-orbit collision data
  (`S3MidpointSO4DeltaOrbit`).

Both global obstructions remain **open for general composite `N`**.

---

## 3. Classical Goldbach statement used here

The bridge uses **`GoldbachParity`**: every even `n > 2` is a sum of two primes
(diagonal pairs allowed, e.g. `4 = 2 + 2`).

This is logically equivalent to the standard **`ClassicalEvenGoldbach`** statement
(every even `n ≥ 4`, same pair predicate) — see
`classical_even_goldbach_iff_goldbach_parity` in `GoldbachG2Parity`.

Midpoint form: `GoldbachMidpointPair N p q` means `p + q = 2N` with `p ≤ N ≤ q`;
equivalent to even Goldbach at `n = 2N` via `midpoint_goldbach_two_iff_goldbach_parity`.

---

## 4. Fourier / harmonic balancing — why the linkage feels natural

The carrier factorizes at the spectral line (`S3LogPhaseEdge.log_edge_decoupling`):

`n^{−s} = n^{−σ} · exp(−i t log n)`  (modulus × phase).

* **Modulus channel** (`σ = Re s`): norm readouts see only `σ`.  Every locator of this
  type is equivalent to RH (`so4SpectralLine_sq_weight`, `polar_collapse_iff_RH`).
  The phase `t` is erased.

* **Phase / log channel** (`t = Im s`): multiplication becomes addition (`linePhase_mul`).
  Goldbach midpoint pairs supply **additive curvature** on the Goldbach circle
  (`goldbach_pair_circle` in `S3LogPhaseEdge`).

The **shared half-slope** unification lives at the **harmonic/Fourier layer**, not in
raw modulus comparison:

* ζ side: `A(θ) = cos(θ − π/4)` vanishes on `t_k = 3π/4 + kπ`
  (`zeta_fourier_balance_locus`); cumulative harmonic phase factors through `A(θ)`.
* Goldbach side: certified pairs have slope `N/(p+q) = 1/2` unconditionally.

`FourierHarmonicHalfSlopeBalancing` names the joint payload (Weil/RH field + holonomy/
Goldbach field).  Equivalence to the bridge is proved in
`fourier_harmonic_balancing_iff_bridge`.

Coupling σ and t at actual ζ-zeros requires the **analytic** explicit-formula /
identification layer — that is the open RH content, not the finite symmetry layer.

---

## 5. Unconditional carrier content (proved in this stack)

* `(2,2,2)` twiddle address, shell `8`, π/4 slot, `28` cumulative slots;
* `cumulativeHarmonicPhaseSum N θ = A(θ) · W_N`;
* midpoint slope `1/2` and Hopf holonomy for every *certified* pair;
* `zero_contains_pair_holonomy`: every nontrivial zero activates every midpoint pair.

---

## 6. Partial Goldbach progress (small composite midpoints)

Explicit SoE/midpoint **witnesses** (not via global cardinality obstruction) for
`N ∈ {4, 6, 8, 9, 10, 15}`: `composite_midpoint_has_survivor_small_composites` in
`GoldbachG2Parity`.  Re-exported here as `eckmann_hilton_forward_collapse_certified_midpoints`.

**Still open:** `EckmannHiltonCardinalityObstruction N` and `SO4DeltaOrbitObstruction N`
for general composite `N ≥ 4`.

### Gap-one (twin) vantage inside global budget

Twin primes are **not** a separate circle geometry — they are gap-one Goldbach annulus
sweeps at `N = p + 1` with full `2π` partner sweep and the proved `ln 2` dyadic ladder
step (`S3GoldbachGapOneActivationBudget`, `S3GoldbachAnnulusTwinPrimeSweep`).

| Claim | Status |
|-------|--------|
| Twin ↔ gap-one midpoint pair | **Theorem** (`twin_prime_iff_goldbach_gap_one_midpoint`) |
| Twin sweep package (`2π` + ladder) | **Theorem** (`goldbach_twin_gap_one_sweep_package`) |
| Gap-one activation mass ≤ cap term | **Theorem** (`goldbach_gap_one_activation_mass_le_cap_term`) |
| Gap-one subseries summable inside cap | **Theorem** (`tsum_goldbach_gap_one_activation_le_cap_series`) |
| Infinitely many twins / dyadic pressure | **Open** (`GoldbachDyadicGapOneSweepPressure`) |
| Square diff prime ⇒ unit `m − n` at `N = m²` | **Theorem** (`square_diff_prime_forces_unit_mn_at_square_midpoint`) |
| Ng-square + `g = 1` ⇒ gap-one activation | **Theorem** (`square_diff_prime_forces_twin_annulus_sweep`) |
| Twin arms hit by mul-mod sweep on `2N` | **Theorem** (`twin_mul_mod_twiddle_arm_hits_capstone`) |
| Certified twin mul-mod shells `N = 4, 6` | **Theorem** (`twin_mul_mod_twiddle_certified_shells_capstone`) |
| Δ plaquette holonomy ↔ mul-mod at `N = 4` | **Theorem** (`delta_holonomy_mul_mod_anchor_certificate_capstone`) |
| Δ twin ladder `N = 4, 6` + zero activation | **Theorem** (`delta_holonomy_twin_ladder_certificate_capstone`) |
| Plastic ratio ↔ first twin ↔ twiddle shell `8` | **Theorem** (`plastic_ratio_twin_twiddle_anchor_capstone`) |
| Plastic ratio **not** global for all twins | **Theorem** (`plasticP_five_ne_twin_small_prime`, `plasticQ_six_ne_second_twin_shell`) |

---

## 7. Pythagorean inradius lattice — candidate holonomy loop label (NOTE, not yet a theorem)

*Recorded for future agents working the holonomy side of this bridge. This is a
structural observation about a candidate base space + loop label; it is **not** a
holonomy proof and adds **no** Lean theorem.*

**Identity.** Every primitive Pythagorean triple comes from Euclid parameters
`m > n > 0`, `gcd(m,n) = 1`, opposite parity, with
`A = m² − n²`, `B = 2mn`, `C = m² + n²`. The incircle radius is the integer

> `r = (A + B − C)/2 = n(m − n)`,

and non-primitive scalings by `k ≥ 2` give `r = k·r₀`. So `r` is an intrinsic
**integer defect** attached to each right-triangle cell, not merely "an integer".

**Rigid integer coordinates.** Reparametrize by the leg gap `g = m − n` (then `g` is
odd and `gcd(n, g) = 1`). With the semiperimeter `s = m(m + n)`:

> `r = n·g`,  `s = m(m + n)`,  `Area = r·s`,  `C = s − r`.

So `(r, s)` is a rigid integral coordinate system on the cell, more informative than
`r` alone — exactly the kind of discrete label a transport/monodromy story needs.

**Surjectivity + divisor fibers.** Every `r ∈ ℕ⁺` is realized: `(m,n) = (r+1, r)` gives
triple `(2r+1, 2r(r+1), 2r²+2r+1)` with inradius `r`. Fixing `r` reduces classification
to a **divisor problem**: primitive triples of inradius `r` ↔ factorizations `r = n·g`
with `gcd(n,g) = 1`, `g` odd. Prime `r` forces `g = 1` — i.e. primes sit on the
gap-one boundary `m − n = 1` of this lattice.

**Why this is relevant here, and where it is already touched.** The bridge's additive
channel is the **square-midpoint / gap-one** vantage: §6's
`square_diff_prime_forces_unit_mn_at_square_midpoint` already lives on the same `m − n`
unit edge that `r = n·g` flags as the prime boundary, and the certified
`midpoint_slope_half` (`N/(p+q) = 1/2`) is the half-slope readout on the additive side.
The inradius gives an arithmetic-to-geometry labeling of those cells.

**Honest gap (what this does NOT give).** `r` (or `(r,s)`) is a scalar **loop label /
defect charge**, not a holonomy. Holonomy needs a *transport law* under loop
composition — a phase or operator with `H(γ₁γ₂) = H(γ₁)·H(γ₂)` — defined on this base.
This note supplies the **base space** (Euclid lattice fibered by the inradius map
`(n,g) ↦ n·g`) and a candidate discrete charge; the connection/transport operator and
its composition law remain **open** and are the actual holonomy content.

**Suggested next lemma chain (for whoever picks this up):**
`Euclid lattice` → `inradius fiber map (n,g) ↦ n·g` → `divisor fibers (gcd, g odd)` →
`candidate holonomy operator on cell composition`, then prove the composition law.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Geometric carrier: unconditional spine -/

/--
The shared geometric carrier for the RH–Goldbach bridge.

Fields marked unconditional are discharged from existing Story/Geometry modules.
The two `Prop` fields are the classical payloads; proving them from bare finite
symmetry alone is **not** claimed here.
-/
structure GeometricHalfSlopeCarrier where
  /-- Unconditional: `(2,2,2)` address, shell `8`, π/4 slot, partition = Gram energy. -/
  theta_address : ThetaPartitionTwiddleAddressBundle
  /-- Unconditional: `∑ (2π/n) H_n · A(θ) = A(θ) · W_N`. -/
  amplitude_factorization :
    ∀ N θ, 0 < N →
      cumulativeHarmonicPhaseSum N θ = criticalAmplitudeAt θ * totalArcHarmonicWeight N
  /-- Unconditional: certified midpoint pairs have slope `N/(p+q) = 1/2`. -/
  midpoint_slope_half :
    ∀ N p q, 0 < N → GoldbachMidpointPair N p q →
      SO4OrthogonalTangentMidpointSlope N p q = (1 / 2 : ℝ)
  /-- Unconditional: Hopf holonomy support for every certified midpoint pair. -/
  midpoint_holonomy_support :
    ∀ N p q, 0 < N → GoldbachMidpointPair N p q →
      HopfFiberMidpointHolonomySupport N p q
  /-- Classical ζ payload (equivalent to RH — not proved from carrier alone). -/
  zeta_channel : WeilPositivityForcesCriticalLine
  /-- Classical Goldbach payload (equivalent to parity — not proved from carrier alone). -/
  goldbach_channel : SO4ZetaHolonomyForcesMidpointPairs 2

/-- Default carrier: unconditional geometry + explicit classical payloads. -/
noncomputable def geometricHalfSlopeCarrierOfBridge (B : SO8ProjectedHalfSlopeBridge 2) :
    GeometricHalfSlopeCarrier where
  theta_address := thetaPartitionTwiddleAddressBundle
  amplitude_factorization _ _ _ := cumulative_harmonic_phase_sum_eq _ _
  midpoint_slope_half _ _ _ hN hPair :=
    so4_orthogonal_tangent_midpoint_slope_eq_half hN hPair
  midpoint_holonomy_support _ _ _ hN hPair :=
    hopf_fiber_midpoint_holonomy_support_of_midpoint_pair hN hPair
  zeta_channel := B.critical_line
  goldbach_channel := B.midpoint_pairs

/--
Rebuild the SO(8) bridge from a carrier that supplies both classical payloads.
This is the converse direction showing the carrier captures **all** bridge content.
-/
theorem so8_bridge_of_geometric_half_slope_carrier (C : GeometricHalfSlopeCarrier) :
    SO8ProjectedHalfSlopeBridge 2 where
  critical_line := C.zeta_channel
  midpoint_pairs := C.goldbach_channel

theorem geometric_carrier_fields_are_bridge (C : GeometricHalfSlopeCarrier) :
    (so8_bridge_of_geometric_half_slope_carrier C).critical_line = C.zeta_channel ∧
      (so8_bridge_of_geometric_half_slope_carrier C).midpoint_pairs = C.goldbach_channel :=
  ⟨rfl, rfl⟩

theorem geometric_half_slope_carrier_of_bridge_roundtrip
    (B : SO8ProjectedHalfSlopeBridge 2) :
    (so8_bridge_of_geometric_half_slope_carrier (geometricHalfSlopeCarrierOfBridge B)) =
      B := by
  cases B
  rfl

/-! ## Classical Goldbach ↔ bridge Goldbach -/

/--
The bridge's `GoldbachParity` is the standard even Goldbach conjecture in parity form.
-/
theorem bridge_goldbach_is_classical_even_goldbach :
    GoldbachParity ↔ ClassicalEvenGoldbach :=
  classical_even_goldbach_iff_goldbach_parity.symm

/-! ## Fourier/harmonic shared `1/2` readout -/

/--
Fourier-level ζ-channel balancing: the critical amplitude vanishes exactly on the
arithmetic balance ladder `t_k = 3π/4 + kπ`.
-/
theorem zeta_fourier_balance_locus (t : ℝ) :
    criticalAmplitudeAt t = 0 ↔ ∃ k : ℤ, t = balanceCandidateHeight k :=
  critical_amplitude_at_eq_zero_iff_balance t

/--
Joint Fourier/harmonic balancing at the shared half-slope: the two classical
payloads packaged as a conjunction (the SO(8) bridge fields, not a separate
hypothesis).
-/
def FourierHarmonicHalfSlopeBalancing : Prop :=
  WeilPositivityForcesCriticalLine ∧ SO4ZetaHolonomyForcesMidpointPairs 2

theorem fourier_harmonic_half_slope_balancing_iff_bridge :
    FourierHarmonicHalfSlopeBalancing ↔ SO8ProjectedHalfSlopeBridge 2 := by
  constructor
  · rintro ⟨hZ, hG⟩
    exact so8_bridge_of_geometric_half_slope_carrier
      { theta_address := thetaPartitionTwiddleAddressBundle
        amplitude_factorization := fun _ _ _ => cumulative_harmonic_phase_sum_eq _ _
        midpoint_slope_half := fun _ _ _ hN hPair =>
          so4_orthogonal_tangent_midpoint_slope_eq_half hN hPair
        midpoint_holonomy_support := fun _ _ _ hN hPair =>
          hopf_fiber_midpoint_holonomy_support_of_midpoint_pair hN hPair
        zeta_channel := hZ
        goldbach_channel := hG }
  · intro B
    exact ⟨B.critical_line, B.midpoint_pairs⟩

/-! ## Capstone: the bridge equivalence is a theorem, not a hypothesis -/

/--
**Capstone (packaging).**  The SO(8) projected half-slope bridge at threshold `2`
*is* `RiemannHypothesis ∧ GoldbachParity` — machine-checked in both directions.
The bridge hypothesis in the sense of "does the geometric payload match the
classical conjunction?" is **discharged as a theorem** here.
-/
theorem rh_goldbach_bridge_equivalence_is_theorem :
    SO8ProjectedHalfSlopeBridge 2 ↔ (RiemannHypothesis ∧ GoldbachParity) :=
  so8_projected_half_slope_two_iff_rh_and_goldbach_parity

theorem fourier_harmonic_balancing_iff_rh_and_goldbach :
    FourierHarmonicHalfSlopeBalancing ↔ (RiemannHypothesis ∧ GoldbachParity) := by
  rw [fourier_harmonic_half_slope_balancing_iff_bridge,
    rh_goldbach_bridge_equivalence_is_theorem]

/-! ## Recent RH-side faces: still equivalences, not discharge -/

/--
The S⁷ torsion face of RH, named locally so the capstone can cite it as a
single predicate.  It is deliberately just the zero-by-zero torsion cancellation
payload from `S3OctonionS7TorsionCancellation`.
-/
def ZeroTorsionCancellationAtZeros : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ a b c : ℕ, 2 ≤ a → 0 < b → 0 < c →
    octTorsionDefect a b c ρ = 0

theorem zero_torsion_cancellation_iff_rh_capstone :
    ZeroTorsionCancellationAtZeros ↔ RiemannHypothesis := by
  dsimp [ZeroTorsionCancellationAtZeros]
  exact RH_iff_zero_torsion_cancellation.symm

theorem heat_flow_vaporization_iff_rh_capstone :
    VaporizationForcesCriticalLine ↔ RiemannHypothesis :=
  vaporization_iff_RiemannHypothesis

theorem heat_flow_bridge_iff_rh_capstone (W : Hqiv.Physics.TempLadderFiniteWindowConcrete) :
    Nonempty HeatFlowVaporizationBridge ↔ RiemannHypothesis :=
  vaporizationBridge_iff_RiemannHypothesis W

/--
The single open step: inhabiting the bridge.  Equivalent to both classical
problems together — provably so, not heuristically.
-/
def GeometricHalfSlopeDischarge : Prop :=
  SO8ProjectedHalfSlopeBridge 2

theorem bridge_discharge_iff_millennium :
    GeometricHalfSlopeDischarge ↔ (RiemannHypothesis ∧ GoldbachParity) :=
  rh_goldbach_bridge_equivalence_is_theorem

theorem bridge_discharge_iff_fourier_balancing :
    GeometricHalfSlopeDischarge ↔ FourierHarmonicHalfSlopeBalancing := by
  exact fourier_harmonic_half_slope_balancing_iff_bridge.symm

theorem delta_harmonic_discharge_iff_geometric_discharge :
    DeltaHarmonicBalancingForcesBridge ↔ GeometricHalfSlopeDischarge := by
  rw [delta_harmonic_discharge_iff_millennium, bridge_discharge_iff_millennium]

/-- Discharge implies the unconditional Layer-A carrier; the converse is **not** proved. -/
theorem delta_discharge_implies_unconditional_carrier :
    DeltaHarmonicBalancingForcesBridge → Nonempty DeltaHarmonicUnconditionalCarrier :=
  fun _ => unconditional_carrier_exists

/-! ## Master recharacterization chain (all packaging, all proved) -/

/--
Every known geometric face of the bridge is equivalent to the same proposition.
There is no logical gap *between* these packagings — only supplying the inhabitant
remains open.
-/
theorem rh_goldbach_joint_bridge_master_iff :
    (SO8ProjectedHalfSlopeBridge 2 ↔ RiemannHypothesis ∧ GoldbachParity) ∧
      (SO8ProjectedHalfSlopeBridge 2 ↔
        PolarProjectionCollapsesOnZeros ∧ GoldbachParity) ∧
      (SO8ProjectedHalfSlopeBridge 2 ↔
        (∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ n : ℕ, 2 ≤ n →
            ‖so4SpectralLine n ρ‖ ^ 2 = (n : ℝ)⁻¹) ∧ GoldbachParity) ∧
      (FourierHarmonicHalfSlopeBalancing ↔ RiemannHypothesis ∧ GoldbachParity) ∧
      (WeilPositivityForcesCriticalLine ↔ RiemannHypothesis) ∧
      (SO4ZetaHolonomyForcesMidpointPairs 2 ↔ GoldbachParity) ∧
      (GoldbachParity ↔ ClassicalEvenGoldbach) := by
  refine ⟨rh_goldbach_bridge_equivalence_is_theorem, ?_⟩
  refine ⟨bridge_iff_polar_collapse_and_parity, ?_⟩
  refine ⟨bridge_iff_spectral_weights_and_parity, ?_⟩
  refine ⟨fourier_harmonic_balancing_iff_rh_and_goldbach, ?_⟩
  refine ⟨weilPositivity_iff_RiemannHypothesis, ?_⟩
  refine ⟨so4_zeta_holonomy_bridge_two_iff_goldbach_parity, ?_⟩
  exact bridge_goldbach_is_classical_even_goldbach

/--
Channel separation: ζ and Goldbach are independent faces of the same bridge —
no leakage between channels.
-/
theorem rh_goldbach_bridge_channels_separated :
    (WeilPositivityForcesCriticalLine ↔ RiemannHypothesis) ∧
      (SO4ZetaHolonomyForcesMidpointPairs 2 ↔ GoldbachParity) :=
  bridge_channels_are_rh_and_goldbach

/-! ## Unconditional holonomy chain (holds at every zero, every pair) -/

/--
Every nontrivial zero contains the holonomy of every midpoint pair — proved
without RH or Goldbach.  This is the unconditional geometric spine behind the
zero–holonomy–Goldbach chain.
-/
theorem unconditional_zero_contains_pair_holonomy {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ)
    {N p q : ℕ} (hN : 0 < N) (hPair : GoldbachMidpointPair N p q) :
    HopfFiberMidpointHolonomySupport N p q :=
  (zero_contains_pair_holonomy hzz hN hPair).2.2.2

/-! ## Goldbach midpoint = EH forward collapse (same open target) -/

/--
The additive Goldbach midpoint target is exactly the EH forward collapse /
finite-stack extinction obstruction — not a separate conjecture once the carrier
is fixed.
-/
theorem goldbach_midpoint_iff_eh_forward_collapse (N : ℕ) :
    CompositeMidpointHasSurvivor N ↔ EckmannHiltonForwardCollapse N :=
  (eckmann_hilton_forward_collapse_iff_composite N).symm

/-- Goldbach parity yields a composite midpoint survivor once `N ≥ 2` is composite. -/
theorem goldbach_parity_implies_composite_midpoint_survivor (hG : GoldbachParity) (N : ℕ)
    (_hc : ¬ Nat.Prime N) (hN : 2 ≤ N) : MidpointSieveSurvivorExists N := by
  obtain ⟨p, q, hp, hq, hsum⟩ := hG (2 * N) (by omega) ⟨N, by ring⟩
  rcases midpoint_pair_of_goldbach_pair_two_mul (N := N) (p := p) (q := q)
      ⟨hp, hq, hsum⟩ with ⟨p', q', hMid⟩
  exact ⟨p', goldbachMidpointPair_to_dual_survivor hMid⟩

theorem goldbach_parity_implies_eh_forward_collapse (hG : GoldbachParity) (N : ℕ)
    (hN : 2 ≤ N) : EckmannHiltonForwardCollapse N :=
  (goldbach_midpoint_iff_eh_forward_collapse N).mp (by
    intro hc
    exact goldbach_parity_implies_composite_midpoint_survivor hG N hc hN)

/-! ## Partial progress: certified small composite midpoints -/

/--
Re-export: explicit midpoint/SoE witnesses for `N ∈ {4, 6, 8, 9, 10, 15}`.

These are **constructive certificates** (`dualMidpointSurvivor`), not proofs of the
global obstructions `EckmannHiltonCardinalityObstruction` or `SO4DeltaOrbitObstruction`.
-/
theorem composite_midpoint_certified_midpoints :
    CompositeMidpointHasSurvivor 4 ∧ CompositeMidpointHasSurvivor 6 ∧
      CompositeMidpointHasSurvivor 8 ∧ CompositeMidpointHasSurvivor 9 ∧
      CompositeMidpointHasSurvivor 10 ∧ CompositeMidpointHasSurvivor 15 :=
  composite_midpoint_has_survivor_small_composites

theorem eckmann_hilton_forward_collapse_certified_midpoints :
    EckmannHiltonForwardCollapse 4 ∧ EckmannHiltonForwardCollapse 6 ∧
      EckmannHiltonForwardCollapse 8 ∧ EckmannHiltonForwardCollapse 9 ∧
      EckmannHiltonForwardCollapse 10 ∧ EckmannHiltonForwardCollapse 15 :=
  eckmann_hilton_forward_collapse_small_composites

/-! ## Gap-one (twin) activation inside associator cap -/

/--
Re-export: every twin pair is a gap-one sweep package with `ln 2` ladder step and
full `2π` partner sweep.
-/
theorem twin_prime_gap_one_sweep_vantage (p : ℕ) (h : TwinPrimePair p) :
    GoldbachTwinGapOneSweepPackage p h :=
  goldbach_twin_gap_one_sweep_package p h

/--
Re-export: the twin / gap-one activation channel is a summable sub-budget of the
global π-annulus associator cap series.
-/
theorem goldbach_gap_one_activation_inside_global_cap :
    Summable (fun n : ℕ => goldbachGapOneActivationMass (n + 2)) ∧
      ∑' n : ℕ, goldbachGapOneActivationMass (n + 2) ≤
        goldbachAnnulusAssociatorCapSeries :=
  ⟨goldbach_gap_one_activation_subseries_summable,
    tsum_goldbach_gap_one_activation_le_cap_series⟩

/--
Recent twiddle-ladder refinement: a certified twin midpoint on shell `2N` has
constructive mul-mod preimages for both gap-one arms.  This is local arm access,
not a global multiplier law or a twin-density claim.
-/
theorem twin_mul_mod_twiddle_arm_hits_capstone {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q)
    (h : goldbachMidpointSupportsTwinPrime N) :
    ∃ (xL xR : ℕ), xL < B.shell ∧ xR < B.shell ∧
      scaleOrbitMulMod B.shell B.multiplier xL = N - 1 ∧
      scaleOrbitMulMod B.shell B.multiplier xR = N + 1 :=
  twin_harmonic_mul_mod_arm_hits B h

theorem twin_mul_mod_twiddle_axis_offsets_capstone {N : ℕ}
    (h : goldbachMidpointSupportsTwinPrime N) :
    goldbachLeftArmAngle N (N - 1) (twin_midpoint_pos h)
        (by simpa using twin_arm_left_lt_shell h) =
          Real.pi - Real.pi / N ∧
      goldbachLeftArmAngle N (N + 1) (twin_midpoint_pos h)
        (by simpa using twin_arm_right_lt_shell h) =
          Real.pi + Real.pi / N ∧
      goldbachLeftArmAngle N (N - 1) (twin_midpoint_pos h)
          (by simpa using twin_arm_left_lt_shell h) +
          goldbachLeftArmAngle N (N + 1) (twin_midpoint_pos h)
            (by simpa using twin_arm_right_lt_shell h) =
        2 * Real.pi :=
  ⟨twin_left_arm_angle_eq h, twin_right_arm_angle_eq h, twin_arm_sweep_angles_sum_two_pi h⟩

theorem twin_anchor_twiddle_pole_depth_capstone :
    (2 * 4 : ℕ) = twiddleAddressShellDepth twiddleAddress222 ∧
      symmetricTwiddleAddress 2 = twiddleAddress222 :=
  twin_anchor_shell_eq_twiddle_pole_depth

theorem twin_mul_mod_twiddle_certified_shells_capstone :
    (∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
      scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) xL = 3 ∧
      scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) xR = 5) ∧
    (∃ (xL xR : ℕ), xL < 12 ∧ xR < 12 ∧
      scaleOrbitMulMod 12 (harmonicOrbitMulModMultiplier 12) xL = 5 ∧
      scaleOrbitMulMod 12 (harmonicOrbitMulModMultiplier 12) xR = 7) :=
  ⟨twin_harmonic_mul_mod_arm_hits_four, twin_harmonic_mul_mod_arm_hits_six⟩

/-! ## Δ plaquette holonomy ↔ mul-mod at square anchor `N = 4` -/

theorem so4_seed_commutator_eq_delta_generator_capstone :
    ⁅Hqiv.Algebra.planeGen (0 : Fin 4) (1 : Fin 4) (by decide),
      Hqiv.Algebra.planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      so4DeltaGenerator :=
  so4_seed_commutator_eq_so4_delta_generator

theorem delta_holonomy_mul_mod_anchor_certificate_capstone :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 8 = 5 ∧
      (2 * 4 : ℕ) = twiddleAddressShellDepth twiddleAddress222 ∧
      ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
        scaleOrbitMulMod 8 5 xL = 3 ∧
        scaleOrbitMulMod 8 5 xR = 5 :=
  delta_holonomy_mul_mod_anchor_certificate

theorem delta_anchor_at_zero_certificate_capstone {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      HopfFiberMidpointHolonomySupport 4 3 5 ∧
      (∀ k : ℕ, 0 < k → k < 8 →
        ∃ x : ℕ, x < 8 ∧ scaleOrbitMulMod 8 5 x = k) ∧
      ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
        scaleOrbitMulMod 8 5 xL = 3 ∧
        scaleOrbitMulMod 8 5 xR = 5 :=
  delta_anchor_at_zero_certificate hzz

theorem delta_holonomy_twin_ladder_certificate_capstone :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      Nonempty (DeltaHolonomyTwinShellPack 6 5 7) ∧
      harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 8 = 5 ∧
      harmonicOrbitMulModMultiplier 12 = 5 ∧
      (2 * 4 : ℕ) = twiddleAddressShellDepth twiddleAddress222 ∧
      (∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
        scaleOrbitMulMod 8 5 xL = 3 ∧ scaleOrbitMulMod 8 5 xR = 5) ∧
      (∃ (xL xR : ℕ), xL < 12 ∧ xR < 12 ∧
        scaleOrbitMulMod 12 5 xL = 5 ∧ scaleOrbitMulMod 12 5 xR = 7) ∧
      (goldbachLeftArmAngle 4 3 (by decide) (by decide) = Real.pi - Real.pi / 4 ∧
        goldbachLeftArmAngle 4 5 (by decide) (by decide) = Real.pi + Real.pi / 4 ∧
        goldbachLeftArmAngle 6 5 (by decide) (by decide) = Real.pi - Real.pi / 6 ∧
        goldbachLeftArmAngle 6 7 (by decide) (by decide) = Real.pi + Real.pi / 6) :=
  delta_holonomy_twin_ladder_certificate

theorem plastic_ratio_twin_twiddle_anchor_capstone :
    PlasticRatioTwinTwiddleAnchorCert :=
  plastic_ratio_twin_twiddle_anchor_certificate

/--
**Open (documented).**  Dyadic gap-one sweep pressure: infinitely many twin midpoints
along the ladder.  Implied by infinitely many twins, not proved here.
-/
def GoldbachDyadicGapOneSweepPressureOpen : Prop :=
  GoldbachDyadicGapOneSweepPressure

theorem infinitely_many_twins_implies_dyadic_gap_one_pressure
    (h : ∀ p, ∃ q > p, TwinPrimePair q) :
    GoldbachDyadicGapOneSweepPressure :=
  goldbach_dyadic_gap_one_sweep_pressure_of_infinitely_many_twins h

/-! ## Square-orbit → gap-one activation bridge -/

theorem square_diff_prime_forces_twin_annulus_sweep_capstone {N g : ℕ} (hg : g ≤ N)
    (hPair : GoldbachMidpointPair N (N - g) (N + g))
    (hNg : MidpointGapNgSquare N g) (hg1 : g = 1) :
    0 < goldbachGapOneActivationMass N :=
  square_diff_prime_forces_twin_annulus_sweep hg hPair hNg hg1

theorem square_midpoint_ng_square_forces_unit_mn_capstone {m n : ℕ} (hn : n < m)
    (hNg : MidpointGapNgSquare (m * m) (n * n))
    (hSym : symmetricPrimeReflectionAtGap (m * m) (n * n)) :
    m - n = 1 :=
  square_midpoint_ng_square_symmetric_forces_unit_mn hn hNg hSym

theorem so4_delta_obstruction_square_ladder_discharge_chain_capstone
    (hRoute : SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair)
    (m : ℕ) (hm : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    0 < goldbachGapOneActivationMass (m * m) :=
  (so4_delta_obstruction_square_ladder_discharge_chain hRoute m hm hOb).1

theorem so4_delta_orbit_obstruction_at_four_capstone :
    SO4DeltaOrbitObstruction 4 :=
  so4_delta_orbit_obstruction_at_four

theorem so4_delta_obstruction_forces_gap_one_at_anchor_capstone :
    symmetricPrimeReflectionAtGap 4 1 ∧ MidpointGapNgSquare 4 1 :=
  so4_delta_obstruction_forces_gap_one_symmetric_square_pair_at_anchor so4_delta_orbit_obstruction_at_four

theorem so4_delta_orbit_anchor_four_discharge_capstone :
    0 < goldbachGapOneActivationMass 4 ∧
      GoldbachTwinGapOneSweepPackage 3 ⟨nat_prime_three, nat_prime_five⟩ :=
  so4_delta_orbit_anchor_four_discharge

theorem goldbach_non_square_twin_pressure_capstone
    (h : GoldbachDyadicGapOneSweepPressure) :
    GoldbachNonSquareTwinSweepPressure :=
  goldbach_dyadic_gap_one_sweep_forces_non_square_twin_pressure h

theorem goldbach_non_square_activation_pressure_capstone
    (h : GoldbachDyadicGapOneSweepPressure) :
    GoldbachNonSquareGapOneActivationPressure :=
  goldbach_dyadic_gap_one_sweep_forces_non_square_activation_pressure h

theorem goldbach_gap_one_cap_split_capstone :
    (∑' n : ℕ, goldbachGapOneActivationMass (n + 2)) =
      goldbachGapOneSquareSubladderMass + goldbachGapOneNonSquareSubladderMass :=
  goldbach_gap_one_series_eq_square_subladder_plus_non_square

theorem so4_delta_obstruction_symmetric_square_pair_at_nine_capstone :
    ∃ g, symmetricPrimeReflectionAtGap 9 g :=
  ⟨2, symmetricPrimeReflectionAtGap_nine_two⟩

theorem so4_delta_obstruction_forces_gap_one_symmetric_square_pair_refuted :
    ¬ SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair :=
  so4_delta_obstruction_forces_gap_one_symmetric_square_pair_false

/--
**Open (documented).**  Global EH cardinality obstruction: turning pigeonhole duplicate
reflect crossings into a stack survivor for every composite `N ≥ 4`.  Proved infrastructure:
`eckmann_hilton_forward_collapse_of_cardinality_obstruction`, `composite_eh_extinction_reflect_cross_pigeonhole`.
Small-`N` witnesses above bypass this route.
-/
def EckmannHiltonCardinalityObstructionOpen (N : ℕ) : Prop :=
  EckmannHiltonCardinalityObstruction N

/--
**Open (documented).**  SO(4)/Δ-orbit obstruction: same conclusion from gap-orbit collision
geometry (`S3MidpointSO4DeltaOrbit`).  Equivalent strength to EH cardinality once the
spectral closing step is proved.
-/
def SO4DeltaOrbitObstructionOpen (N : ℕ) : Prop :=
  SO4DeltaOrbitObstruction N

theorem so4_delta_obstruction_implies_eh_cardinality {N : ℕ}
    (h : SO4DeltaOrbitObstruction N) : EckmannHiltonCardinalityObstruction N :=
  so4_delta_orbit_obstruction_implies_cardinality h

/-!
## Quick reference (maintainers)

| Status | Name | Location |
|--------|------|----------|
| **Theorem** | Bridge ↔ RH ∧ Goldbach | `rh_goldbach_bridge_equivalence_is_theorem` |
| **Theorem** | Classical even Goldbach ↔ `GoldbachParity` | `bridge_goldbach_is_classical_even_goldbach` |
| **Theorem** | Heat-flow vaporization face ↔ RH | `heat_flow_vaporization_iff_rh_capstone` |
| **Theorem** | S⁷ torsion cancellation at zeros ↔ RH | `zero_torsion_cancellation_iff_rh_capstone` |
| **Theorem** | Unconditional zero–pair holonomy | `unconditional_zero_contains_pair_holonomy` |
| **Theorem** | Small composite midpoint witnesses | `composite_midpoint_certified_midpoints` |
| **Open** | Inhabiting the bridge | `GeometricHalfSlopeDischarge` |
| **Open** | EH cardinality / SO(4) Δ-orbit | `EckmannHiltonCardinalityObstructionOpen`, `SO4DeltaOrbitObstructionOpen` |
| **Open** | Δ-harmonic discharge (= RH ∧ Goldbach) | `DeltaHarmonicBalancingForcesBridge` in `S3DeltaHarmonicDischargeBridge` |
| **Open** | Global covariance discharge (= same) | `GlobalCovarianceForcesDischarge` in `S3PhysicsInvarianceDischargeBridge` |
| **Proved** | Physics invariance carrier (Layer P) | `PhysicsInvarianceUnconditionalCarrier` |
| **Proved** | Rapidity jet coeff = equator factor on strip | `S3StripRapidityEquatorIdentification` |
| **Proved** | Harmonic `6/5` → mul-mod on certified shells | `harmonic_mul_mod_bundles_small_composites`, `S3HarmonicMulModHolonomy` |
| **Proved** | Zero holonomy + harmonic sweep (N=4…15) | `zero_holonomy_harmonic_mul_mod_small_composites` |
| **Open** | Global harmonic mul-mod coprimality | `HarmonicMulModMultiplierCoprimeObstruction` (fails at `n=770`) |
| **Proved** | Square-orbit collision closes at `N = m²` (Ng-square) | `SO4SquareOrbitCollisionCloses_square_midpoint` in `S3SO4SquareOrbitCollision` |
| **Proved** | Ng-square collision forbidden when square-orbit closes | `square_orbit_collision_extinction_contradiction` |
| **Proved** | Orbit energy unifies RH deviation + Ng-square defect | `orbit_energy_unifies_rh_and_goldbach_channels` in `S3OrbitEnergyNonExtinctionBridge` |
| **Proved** | Certified square midpoints `N ∈ {4, 9, 16}` | `delta_orbit_non_extinction_certified_square_midpoints` |
| **Proved** | Twin ↔ gap-one sweep package | `twin_prime_gap_one_sweep_vantage` in `S3GoldbachGapOneActivationBudget` |
| **Proved** | Gap-one activation subseries inside cap | `goldbach_gap_one_activation_inside_global_cap` |
| **Proved** | Twin arm mul-mod hits on any certified `2N` sweep | `twin_mul_mod_twiddle_arm_hits_capstone` |
| **Proved** | Certified twin mul-mod shells `N = 4, 6` | `twin_mul_mod_twiddle_certified_shells_capstone` |
| **Proved** | Δ plaquette holonomy ↔ mul-mod at `N = 4` | `delta_holonomy_mul_mod_anchor_certificate_capstone` |
| **Proved** | Δ anchor activated at every nontrivial zero | `delta_anchor_at_zero_certificate_capstone` |
| **Proved** | Δ twin ladder `N = 4, 6` with `m = 5` | `delta_holonomy_twin_ladder_certificate_capstone` |
| **Proved** | Plastic ratio ↔ first twin ↔ twiddle shell `8` | `plastic_ratio_twin_twiddle_anchor_capstone` |
| **Proved** | Plastic ratio not global for all twins | `plasticQ_six_ne_second_twin_shell` |
| **Proved** | Dyadic `ln 2` ladder on every midpoint | `goldbach_dyadic_sweep_ln_two_normalization` |
| **Open** | Dyadic gap-one sweep pressure (twin frequency) | `GoldbachDyadicGapOneSweepPressureOpen` |
| **Proved** | Square diff prime ⇒ unit `m − n` at square midpoint | `square_midpoint_ng_square_forces_unit_mn_capstone` |
| **Proved** | Ng-square + `g = 1` ⇒ twin activation mass | `square_diff_prime_forces_twin_annulus_sweep_capstone` |
| **Proved** | Certified square-orbit twin at `N = 4` | `square_midpoint_twin_at_four` in `S3SquareOrbitGapOneBridge` |
| **Proved** | Unit `m−n` Ng-square pair on ladder (`m = 2`, `n = 1`) | `square_ladder_unit_mn_ng_square_certified` |
| **Proved** | `SO4DeltaOrbitObstruction 4` (anchor) | `so4_delta_orbit_obstruction_at_four` |
| **Proved** | Obstruction at `4` ⇒ gap-one symmetric pair | `so4_delta_obstruction_forces_gap_one_at_anchor_capstone` |
| **Proved** | Anchor discharge: activation + twin sweep at `N = 4` | `so4_delta_orbit_anchor_four_discharge_capstone` |
| **Proved** | No gap-one twins on square midpoints for `m > 2` | `no_twin_on_square_midpoint_for_m_gt_two` |
| **Proved** | Twin on square midpoint forces `N = 4` | `goldbach_midpoint_twin_on_square_midpoint_eq_four` |
| **Proved** | Global gap-one symmetric forcing is false | `so4_delta_obstruction_forces_gap_one_symmetric_square_pair_false` |
| **Proved** | Dyadic pressure at `N₀ ≥ 5` uses non-square midpoints | `goldbach_dyadic_pressure_from_non_square_midpoint` |
| **Proved** | Square subladder gap-one mass = anchor only | `goldbach_gap_one_square_subladder_mass_eq_anchor` |
| **Proved** | Non-square twin sweep pressure from dyadic shells | `goldbach_non_square_twin_pressure_capstone` |
| **Proved** | Non-square activation pressure from dyadic shells | `goldbach_non_square_activation_pressure_capstone` |
| **Proved** | Gap-one series = square anchor + non-square tail | `goldbach_gap_one_cap_split_capstone` |
| **Proved** | Wider symmetric pair at square anchor `N = 9` | `so4_delta_obstruction_symmetric_square_pair_at_nine_capstone` |
| **Open** | Δ-orbit ⇒ unit `m−n` Ng-square on square ladder (global) | `SO4DeltaOrbitObstructionForcesUnitMnNgSquarePair` |
| **Refuted** | Δ-orbit ⇒ gap-one symmetric at all `m²` | `SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair` |
| **Open** | Δ-orbit ⇒ symmetric pair at all `m²` (any gap `g`) | `SO4DeltaOrbitObstructionForcesSymmetricSquarePair` |
| **Proved** | Conditional: gap-one route ⇒ activation | `so4_delta_obstruction_square_ladder_discharge_chain` |
| **Open** | Global Δ-orbit non-extinction | `DeltaOrbitNonExtinctionObstruction` |
| **Open** | Rolling explicit-formula orbit-energy discharge (RH) | `RollingExplicitFormulaOrbitEnergyDischarge` |
-/

end

end Hqiv.Story
