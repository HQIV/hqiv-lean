import Hqiv.Story.S3ZeroProducingOrbits
import Hqiv.Story.S3InteriorPathE

/-!
# Pathway E ↔ zero-producing orbits

Links the non-degenerate even channel (`evenStripChannelPathE`) with the S³
zero-orbit classification (`ZeroProducingOrbit`).

**Strip level.** Path E channels are functions of `s : ℂ`; orbit classification
lives on `QuaternionCoords` inside `ScaledS3Sample`.  The bridge is explicit:
`ZetaEqualsS3ResidualAt s P` identifies `ζ(s)` with the S³ residual readout.

Under that bridge on the open strip:

* `ζ(s) = 0` ↔ `ZeroProducingOrbit P.coords` ↔ even/odd Path E balance
  (`even = −odd_residual`).

**Honesty.** This strengthens the zero *picture* (harmonic–Δ even term cancelled
by the odd residual) but does not prove the RH capstone.
-/

namespace Hqiv.Story

/-! ## Naming alias -/

/-- User-facing alias for the Path E odd residual channel. -/
noncomputable abbrev oddResidualPathE (s : ℂ) : ℂ :=
  oddStripChannelPathE s

@[simp] theorem oddResidualPathE_eq_oddStripChannelPathE (s : ℂ) :
    oddResidualPathE s = oddStripChannelPathE s :=
  rfl

/-! ## Strip-level balance predicate -/

/-- Path E channel balance: odd residual cancels the harmonic–Δ even term. -/
def PathEChannelBalanceAt (s : ℂ) : Prop :=
  oddResidualPathE s = -evenStripChannelPathE s

theorem pathE_channel_balance_even_neg_odd
    {s : ℂ} :
    PathEChannelBalanceAt s ↔ evenStripChannelPathE s = -oddResidualPathE s := by
  dsimp [PathEChannelBalanceAt, oddResidualPathE]
  constructor
  · intro h
    simpa [neg_neg] using (congrArg Neg.neg h).symm
  · intro h
    simpa [neg_neg] using (congrArg Neg.neg h).symm

theorem pathE_channel_balance_iff_numerator_zero
    {s : ℂ} :
    PathEChannelBalanceAt s ↔ evenStripChannelPathE s + oddResidualPathE s = 0 := by
  dsimp [PathEChannelBalanceAt, oddResidualPathE]
  constructor
  · intro h
    calc evenStripChannelPathE s + oddStripChannelPathE s
        = evenStripChannelPathE s + (-evenStripChannelPathE s) := by rw [h]
      _ = 0 := by ring
  · intro hsum
    exact eq_neg_of_add_eq_zero_right hsum

theorem zeta_zero_iff_pathE_channel_balance
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s = 0 ↔ PathEChannelBalanceAt s := by
  dsimp [PathEChannelBalanceAt, oddResidualPathE]
  constructor
  · intro hζ
    simpa [PathEChannelBalanceAt, oddResidualPathE] using
      pathE_channels_cancel_at_zeta_zero h0 h1 hζ
  · intro h
    exact (pathE_numerator_zero_iff_zeta_zero h0 h1).mp
      (pathE_channel_balance_iff_numerator_zero.mp h)

theorem zeta_zero_iff_pathE_even_neg_odd
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s = 0 ↔ evenStripChannelPathE s = -oddResidualPathE s := by
  rw [← pathE_channel_balance_even_neg_odd, zeta_zero_iff_pathE_channel_balance h0 h1]

/-! ## ζ–S³ bridge -/

/--
At a zero-producing orbit (under the zeta/S³ identification), Path E channels
cancel: `even = −odd_residual`.
-/
theorem even_channel_eq_neg_odd_residual_of_zero_producing_bridge
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hOrbit : ZeroProducingOrbit P.coords) :
    evenStripChannelPathE s = -oddResidualPathE s := by
  have hζ : riemannZeta s = 0 :=
    (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mpr hOrbit
  exact (zeta_zero_iff_pathE_even_neg_odd h0 h1).mp hζ

/--
Conversely, Path E channel balance together with the bridge forces a
zero-producing orbit on the sample.
-/
theorem zero_producing_orbit_of_pathE_balance_bridge
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hBal : PathEChannelBalanceAt s) :
    ZeroProducingOrbit P.coords :=
  (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mp
    ((zeta_zero_iff_pathE_channel_balance h0 h1).mpr hBal)

theorem zeta_zero_implies_pathE_channel_cancellation
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ : riemannZeta s = 0) :
    evenStripChannelPathE s + oddResidualPathE s = 0 :=
  (pathE_numerator_zero_iff_zeta_zero h0 h1).mpr hζ

theorem zeta_zero_implies_pathE_even_neg_odd
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ : riemannZeta s = 0) :
    evenStripChannelPathE s = -oddResidualPathE s :=
  (pathE_channel_balance_even_neg_odd).mp
    ((zeta_zero_iff_pathE_channel_balance h0 h1).mp hζ)

theorem zero_producing_bridge_implies_pathE_cancellation
    {s : ℂ} (_P : ScaledS3Sample)
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (_hEq : ZetaEqualsS3ResidualAt s _P) (hζ : riemannZeta s = 0) :
    evenStripChannelPathE s + oddResidualPathE s = 0 :=
  zeta_zero_implies_pathE_channel_cancellation h0 h1 hζ

/-! ## Unified classification (Path E strengthened) -/

/--
**Path E strengthened classification** (conditional on `ZetaEqualsS3ResidualAt`).

A zero-producing orbit is exactly balanced imaginary geometry on `P.coords`
together with Path E even/odd cancellation at `s`.
-/
theorem zero_producing_orbit_classification_pathE
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZeroProducingOrbit P.coords ↔
      BalancedImag P.coords ∧ PathEChannelBalanceAt s := by
  constructor
  · intro hOrbit
    refine ⟨(zero_producing_orbit_iff_balanced P.coords).mp hOrbit, ?_⟩
    exact (zeta_zero_iff_pathE_channel_balance h0 h1).mp
      ((zeta_zero_iff_zero_producing_orbit_of_eq hEq).mpr hOrbit)
  · intro ⟨_, hPathE⟩
    exact (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mp
      ((zeta_zero_iff_pathE_channel_balance h0 h1).mpr hPathE)

theorem zero_producing_orbit_iff_pathE_balance
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZeroProducingOrbit P.coords ↔ PathEChannelBalanceAt s := by
  constructor
  · intro hOrbit
    exact (zeta_zero_iff_pathE_channel_balance h0 h1).mp
      ((zeta_zero_iff_zero_producing_orbit_of_eq hEq).mpr hOrbit)
  · intro hPathE
    exact (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mp
      ((zeta_zero_iff_pathE_channel_balance h0 h1).mpr hPathE)

/--
Off `σ = 1/2`, a `ζ`-zero forces `interiorStripH_PathE = 0` via factorization
(the critical factor is nonzero, so the assembly quotient vanishes).
-/
theorem interiorStripH_PathE_zero_of_zeta_zero_off_line
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hζ : riemannZeta s = 0) :
    interiorStripH_PathE s = 0 := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hdiv := interiorStripH_PathE_eq_zeta_div_critical_on_strip h0 h1 hσ
  rw [hdiv, hζ, zero_div]

/-!
## Status

* Zeros ↔ zero-producing orbits ↔ `BalancedImag` (bridge layer).
* Path E adds: zeros ↔ `evenStripChannelPathE = −oddResidualPathE`.
* Capstone unchanged: `interior_pathE_capstone_iff_original_capstone`.
-/

end Hqiv.Story
