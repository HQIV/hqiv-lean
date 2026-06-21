import Hqiv.Story.S3DeltaHarmonicDischargeBridge
import Hqiv.Story.S3StripRapidityEquatorIdentification
import Hqiv.Story.S3QuaternionZetaTwiddleMultisetInvariance
import Hqiv.Geometry.RapidityLorentzClosure
import Hqiv.Physics.RapidityZetaPhaseBridge
import Hqiv.Physics.CovariantSolution

/-!
# Physics invariance / covariance → pure-math discharge bridge

HQIV physics already formalizes **what must be true** for a readout to be
coordinate- or gauge-independent.  This module mines that machinery for the
RH–Goldbach / Δ-harmonic story:

| Physics (HQIV) | Pure math (S³ / ζ / Goldbach) |
|----------------|-------------------------------|
| Rapidity boost equivariance of null-lattice chart | Critical-line deviation is the **boost-invariant** scalar locus |
| `φ` Lorentz-scalar → polar phase unchanged | `zetaHQIVTerm` phase = `polarAngleFromRapidity` (same exponent) |
| `√(-g)` cancels in covariant divergence | Equator factor separates **pure harmonic** from **Δ correction** |
| Vanishing metric jets → Christoffels drop | Flat jet: covariant div = coeff × pure surrogate |
| **Strip chart lock** | `rapidityNormalizedJetCoeff = (2σ−1)/√2` (`S3StripRapidityEquatorIdentification`) |
| S₃ leg permutation = gauge on twiddle cell | Product shell / geometric-mean orbit **multiset-invariant** |

## Proved now

Layer **P** (physics invariance carrier) is inhabited without RH or Goldbach.
It **extends** Layer A of `S3DeltaHarmonicDischargeBridge` with covariance facts.

## Open (same as discharge)

**Global** invariance forcing **every** residual to vanish (zeros + all midpoint
pairs) is **not** proved from Layer P alone — it is equivalent to
`DeltaHarmonicBalancingForcesBridge` (hence RH ∧ Goldbach).

Local invariance (flat jet, vacuum solution, multiset gauge) is the **correct
mining target**: it explains *why* the balancing loci align, not *that* they
hold everywhere unconditionally.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry Hqiv.Physics

noncomputable section

/-! ## 1. Rapidity / Lorentz invariance ↔ critical-line gauge -/

/--
**Boost invariance of polar phase.**  Auxiliary `φ` is a Lorentz scalar on the
flat null slice; the polar-angle readout used in `zetaHQIVTerm` is unchanged
under rapidity relabeling of `φ`.
-/
theorem polar_angle_readout_boost_invariant (η φ t : ℝ) (m : ℕ) :
    polarAngleFromRapidity (phiLorentzScalarBoost η φ) t m = polarAngleFromRapidity φ t m :=
  polarAngleFromRapidity_invariant_under_phi_scalar_boost η φ t m

/--
**Zeta shell phase uses the same boost-invariant polar angle** (`RapidityZetaPhaseBridge`).
-/
theorem zeta_shell_phase_is_polar_angle (φ t : ℝ) (m : ℕ) :
    I * φ * t * delta_theta_prime (m : ℝ) = I * (polarAngleFromRapidity φ t m : ℂ) :=
  zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity φ t m

/--
**45° equator = critical-line deviation locus.**  The SO(4) projection is a
fixed coordinate change on the functional-equation pair; vanishing free coordinate
is exactly vanishing `criticalLineDeviation` — the same scalar singled out by
boost-invariant polar readouts on the strip.
-/
theorem equator_vanishes_iff_critical_line_deviation (s : ℂ) :
    rot45Free (functionalPair s.re) = 0 ↔ criticalLineDeviation s = 0 :=
  rot45Free_re_pair_eq_zero_iff_deviation_zero s

theorem equator_balancing_is_gauge_fixed_critical_line (s : ℂ) :
    rot45Free (functionalPair s.re) = 0 ↔ s.re = (1 / 2 : ℝ) :=
  rot45Free_re_pair_eq_zero_iff s

/-! ## 2. Covariance: volume element cancels; flat jet drops connection -/

/--
**Covariant divergence is independent of `√(-g)`** at a frozen chart point — the
volume factor in `(1/√g) ∂(√g F)` cancels (`CovariantSolution`).
This is the physics-side analogue of "only the raised-field content survives
after normalization."
-/
theorem covariant_divergence_independent_of_volume_element
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
    (a : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g ≠ 0) :
    covariant_div_F_O F sqrt_neg_g gInv a ν =
      ∑ μ : Fin 4, raisedFieldStrength_O F gInv a μ ν :=
  covariant_div_F_O_eq_sum_raised F sqrt_neg_g gInv a ν hsqrt

/--
On HQVM data with **vanishing metric jets**, the Christoffel connection contribution
to the covariant divergence vanishes; only the antisymmetric raised-field surrogate
remains (`covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate`).

This parallels the harmonic story: at the **flat jet**, the Δ / curvature connection
term drops and the **pure harmonic surrogate** is visible — the same split as
`pureHarmonicChannel` vs `deltaCorrectionChannel` in the discharge bridge.
-/
theorem flat_metric_jet_covariant_is_pure_surrogate
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ)
    (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariant_div_F_O_HQVM_Christoffel F
      (frozenFirstIndexJet_raisedChannel F N aScale Φ b) N aScale Φ dN da dPhi b ν =
      covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν :=
  covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate F N aScale Φ dN da dPhi b ν hF hN ha hΦ

/-! ## 3. Multiset gauge invariance ↔ geometric-mean orbit -/

/--
**S₃ leg permutation is gauge** on the Euler twiddle cell: the product shell
depth `a·b·c` — the multiplicative orbit level — is unchanged.
This is the discrete origin of "geometric mean as orbit coordinate."
-/
theorem geometric_orbit_shell_multiset_invariant (σ : Equiv.Perm (Fin 3))
    (addr : TwiddleFactorAddress) :
    twiddleAddressShellDepth (permuteTwiddleAddress σ addr) = twiddleAddressShellDepth addr :=
  twiddle_address_shell_depth_perm σ addr

theorem partition_weight_multiset_invariant (addr : TwiddleFactorAddress)
    (σ : Equiv.Perm (Fin 3)) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    twiddleCellPartitionWeight (permuteTwiddleAddress σ addr) hn k =
      twiddleCellPartitionWeight addr hn k :=
  quaternion_zeta_partition_weight_on_orbit addr σ hn k

/-! ## 4. Physics invariance carrier (Layer P) -/

/--
Layer **P**: physics covariance + gauge invariance facts that align with the
Δ-harmonic / equator / multiset orbit story — **without** RH or Goldbach.
-/
structure PhysicsInvarianceUnconditionalCarrier where
  rapidity_lorentz : Nonempty RapidityLorentzClosure
  polar_boost_invariant :
    ∀ η φ t (mShell : ℕ),
      polarAngleFromRapidity (phiLorentzScalarBoost η φ) t mShell = polarAngleFromRapidity φ t mShell
  zeta_phase_polar :
    ∀ φ t (mShell : ℕ),
      I * φ * t * delta_theta_prime (mShell : ℝ) = I * (polarAngleFromRapidity φ t mShell : ℂ)
  equator_deviation : ∀ s : ℂ, rot45Free (functionalPair s.re) = 0 ↔ criticalLineDeviation s = 0
  volume_cancels :
    ∀ (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
      (a : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g ≠ 0),
      covariant_div_F_O F sqrt_neg_g gInv a ν =
        ∑ μ : Fin 4, raisedFieldStrength_O F gInv a μ ν
  flat_jet_pure_surrogate :
    ∀ (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ)
      (b : Fin 8) (ν : Fin 4),
      (∀ c μ ρ, F c μ ρ = -F c ρ μ) → (∀ κ, dN κ = 0) → (∀ κ, da κ = 0) → (∀ κ, dPhi κ = 0) →
        covariant_div_F_O_HQVM_Christoffel F
            (frozenFirstIndexJet_raisedChannel F N aScale Φ b) N aScale Φ dN da dPhi b ν =
          covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν
  multiset_shell :
    ∀ (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress),
      twiddleAddressShellDepth (permuteTwiddleAddress σ addr) = twiddleAddressShellDepth addr
  harmonic_delta : DeltaHarmonicUnconditionalCarrier

noncomputable def physicsInvarianceUnconditionalCarrier : PhysicsInvarianceUnconditionalCarrier where
  rapidity_lorentz := rapidity_lorentz_closure_discharged
  polar_boost_invariant := fun η φ t mShell => polar_angle_readout_boost_invariant η φ t mShell
  zeta_phase_polar := fun φ t mShell => zeta_shell_phase_is_polar_angle φ t mShell
  equator_deviation := equator_vanishes_iff_critical_line_deviation
  volume_cancels := fun F sqrt_neg_g gInv a ν hsqrt =>
    covariant_divergence_independent_of_volume_element F sqrt_neg_g gInv a ν hsqrt
  flat_jet_pure_surrogate := fun F N aScale Φ dN da dPhi b ν hF hN ha hΦ =>
    flat_metric_jet_covariant_is_pure_surrogate F N aScale Φ dN da dPhi b ν hF hN ha hΦ
  multiset_shell := fun σ addr => geometric_orbit_shell_multiset_invariant σ addr
  harmonic_delta := deltaHarmonicUnconditionalCarrier

theorem physics_invariance_carrier_exists :
    Nonempty PhysicsInvarianceUnconditionalCarrier :=
  ⟨physicsInvarianceUnconditionalCarrier⟩

/-! ## 5. Global covariance discharge (open = same as Δ-harmonic) -/

/--
**Global covariance discharge.**  Requiring that **every** ζ residual and **every**
midpoint pair be forced by the invariance/covariance bundle is **definitionally**
the same obligation as the geometric half-slope bridge — not a strictly weaker
physics-flavored conjecture.
-/
def GlobalCovarianceForcesDischarge : Prop :=
  DeltaHarmonicBalancingForcesBridge

theorem global_covariance_discharge_iff_delta_harmonic :
    GlobalCovarianceForcesDischarge ↔ DeltaHarmonicBalancingForcesBridge :=
  Iff.rfl

theorem global_covariance_discharge_iff_millennium :
    GlobalCovarianceForcesDischarge ↔ (RiemannHypothesis ∧ GoldbachParity) :=
  delta_harmonic_discharge_iff_millennium

/--
Discharge implies the physics invariance carrier; the converse is **open**
(equivalent to RH ∧ Goldbach).
-/
theorem delta_discharge_implies_physics_invariance_carrier :
    DeltaHarmonicBalancingForcesBridge → Nonempty PhysicsInvarianceUnconditionalCarrier :=
  fun _ => physics_invariance_carrier_exists

/-!
**Mining summary.**  HQIV physics supplies **local** invariance and **covariance**
identities that explain why the critical line, equator factor, multiset orbit, and
harmonic/Δ split are the **same balancing geometry** in different charts.  Closing
the discharge gap still requires a **global** existence theorem — provably as hard as
RH ∧ Goldbach — not merely more invariance lemmas at the flat-jet level.
-/

end

end Hqiv.Story
