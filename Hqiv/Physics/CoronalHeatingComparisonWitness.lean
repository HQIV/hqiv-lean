import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.SolarDynamics

/-!
# Coronal heating comparison witness (HQIV vs wave / nanoflare scalings)

**Purpose:** formal comparison layer for the longitudinal EM programme review:
dimensionless and absolute flux ratios between the proved HQIV footpoint boundary
channel and schematic Alfvén-wave / nanoflare heating proxies.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex` §MHD interaction;
Python: `scripts/hqiv_solar_dynamics.py`.

## Proof status (all `Prop` / definitional, zero `sorry`)

* **§1.** Schematic Alfvén Poynting / wave-dissipation flux proxy `∝ ρ v_A³`.
* **§2.** Schematic nanoflare flux proxy `E_event · rate / area`.
* **§3.** HQIV boundary flux aliases and shell-gap form.
* **§4.** Length-scaling discriminants (HQIV footpoint-only vs wave `L^α`).
* **§5.** Ratio witnesses and comparison bundle.
* **§6.** Discharged honesty ledger.

**Not claimed:** unique coronal `$n,T,B$` assignment; measured wave amplitudes;
Parker nanoflare rates; quadrature superposition of independent heat sources;
derivation of `$v_A$` from HQIV shells.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Alfvén-wave heating flux proxy
-/

/-- Schematic energy-flux density from Alfvén-wave dissipation:
`F_A = f_damp · ρ · v_A³` (Withington–Marsch / Parker-type scaling slot).

`dampingFraction` packages net dissipation efficiency in `(0,1]` at the readout layer. -/
def alfvenWaveHeatingFluxDensity (rho vAlfven dampingFraction : ℝ) : ℝ :=
  dampingFraction * rho * vAlfven ^ 3

theorem alfvenWaveHeatingFluxDensity_zero_of_zero_damping
    (rho vAlfven : ℝ) :
    alfvenWaveHeatingFluxDensity rho vAlfven 0 = 0 := by
  unfold alfvenWaveHeatingFluxDensity; ring

theorem alfvenWaveHeatingFluxDensity_zero_of_zero_rho
    (vAlfven dampingFraction : ℝ) :
    alfvenWaveHeatingFluxDensity 0 vAlfven dampingFraction = 0 := by
  unfold alfvenWaveHeatingFluxDensity; ring

theorem alfvenWaveHeatingFluxDensity_nonneg
    {rho vAlfven dampingFraction : ℝ}
    (hr : 0 ≤ rho) (hv : 0 ≤ vAlfven) (hd : 0 ≤ dampingFraction) :
    0 ≤ alfvenWaveHeatingFluxDensity rho vAlfven dampingFraction := by
  unfold alfvenWaveHeatingFluxDensity
  exact mul_nonneg (mul_nonneg hd hr) (pow_nonneg hv 3)

/-- Loop-length scaling often used for wave/reconnection channels:
`F(L) = F_ref · (L / L_ref)^lengthExponent`. -/
def waveHeatingFluxWithLength
    (fluxRef loopLength lengthRef lengthExponent : ℝ) : ℝ :=
  fluxRef * (loopLength / lengthRef) ^ lengthExponent

theorem waveHeatingFluxWithLength_eq_ref_at_ref_length
    (fluxRef lengthRef lengthExponent : ℝ) (h : lengthRef ≠ 0) :
    waveHeatingFluxWithLength fluxRef lengthRef lengthRef lengthExponent = fluxRef := by
  unfold waveHeatingFluxWithLength
  field_simp [h]
  simp

theorem waveHeatingFluxWithLength_linear_in_length
    (fluxRef loopLength lengthRef : ℝ) (h : lengthRef ≠ 0) :
    waveHeatingFluxWithLength fluxRef loopLength lengthRef 1 =
      fluxRef * loopLength / lengthRef := by
  unfold waveHeatingFluxWithLength
  simp [pow_one]
  ring

/-!
## §2. Nanoflare heating flux proxy
-/

/-- Schematic nanoflare steady flux:
`F_N = (E_event · eventRate) / crossSection`.

`eventRate` is events per second over the loop ensemble; `crossSection` is the
footpoint / cross-sectional area used for area-normalised comparison. -/
def nanoflareHeatingFluxDensity (eventEnergy eventRate crossSection : ℝ) : ℝ :=
  if crossSection = 0 then 0 else eventEnergy * eventRate / crossSection

theorem nanoflareHeatingFluxDensity_eq_div
    (eventEnergy eventRate crossSection : ℝ) (h : crossSection ≠ 0) :
    nanoflareHeatingFluxDensity eventEnergy eventRate crossSection =
      eventEnergy * eventRate / crossSection := by
  unfold nanoflareHeatingFluxDensity
  simp [h]

theorem nanoflareHeatingFluxDensity_zero_of_zero_rate
    (eventEnergy crossSection : ℝ) :
    nanoflareHeatingFluxDensity eventEnergy 0 crossSection = 0 := by
  unfold nanoflareHeatingFluxDensity
  split_ifs <;> ring

theorem nanoflareHeatingFluxDensity_nonneg
    {eventEnergy eventRate crossSection : ℝ}
    (he : 0 ≤ eventEnergy) (hr : 0 ≤ eventRate) (ha : 0 < crossSection) :
    0 ≤ nanoflareHeatingFluxDensity eventEnergy eventRate crossSection := by
  unfold nanoflareHeatingFluxDensity
  have hsec : crossSection ≠ 0 := ne_of_gt ha
  simp [hsec]
  exact div_nonneg (mul_nonneg he hr) (le_of_lt ha)

/-!
## §3. HQIV boundary flux aliases
-/

/-- HQIV footpoint boundary heating flux (area-normalised). -/
def hqivBoundaryHeatingFluxDensity
    (nq Estar couplingLog vParallel phiPhoto phiCorona : ℝ) : ℝ :=
  coronalHeatingFluxBoundary nq Estar couplingLog vParallel phiPhoto phiCorona

theorem hqivBoundaryHeatingFluxDensity_eq_solar_alias
    (nq Estar couplingLog vParallel phiPhoto phiCorona : ℝ) :
    hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona =
      coronalHeatingFluxBoundary nq Estar couplingLog vParallel phiPhoto phiCorona := rfl

theorem hqivBoundaryHeatingFluxDensity_shells
    (nq Estar couplingLog vParallel : ℝ) (cols : CoronalColumnShells) :
    hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel
        (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona) =
      solarFluxTubeHeatingBoundaryShells nq Estar couplingLog vParallel cols := by
  unfold hqivBoundaryHeatingFluxDensity solarFluxTubeHeatingBoundaryShells
  rfl

theorem hqivBoundaryHeatingFluxDensity_zero_of_equal_phi
    (nq Estar couplingLog vParallel phi : ℝ) :
    hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phi phi = 0 :=
  coronalHeatingFluxBoundary_zero_of_phi_equal nq Estar couplingLog vParallel phi

/-!
## §4. Length-scaling discriminants
-/

/-- HQIV boundary flux is **independent of bulk loop length** at fixed footpoints:
changing `L` leaves `Q/A` unchanged (coronal spine §8). -/
theorem hqivBoundaryFlux_length_independent
    (nq Estar couplingLog vParallel phiPhoto phiCorona L1 L2 : ℝ) :
    hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona =
      hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona := rfl

/-- Witness packaging the length-independence discriminant for two loop lengths. -/
structure HqivFootpointOnlyFluxDiscriminant
    (nq Estar couplingLog vParallel phiPhoto phiCorona loopLength1 loopLength2 flux1 flux2 : ℝ) : Prop where
  flux1_eq :
    flux1 = hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona
  flux2_eq :
    flux2 = hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona
  lengths_distinct : loopLength1 ≠ loopLength2

theorem HqivFootpointOnlyFluxDiscriminant.fluxes_equal
    {nq Estar couplingLog vParallel phiPhoto phiCorona loopLength1 loopLength2 flux1 flux2 : ℝ}
    (h : HqivFootpointOnlyFluxDiscriminant nq Estar couplingLog vParallel phiPhoto phiCorona
      loopLength1 loopLength2 flux1 flux2) :
    flux1 = flux2 := by
  rw [h.flux1_eq, h.flux2_eq]

/-- Wave channel with distinct loop lengths may differ when supplied as a witness. -/
structure WaveLengthScalingDiscriminant
    (fluxRef loopLength1 loopLength2 lengthRef lengthExponent flux1 flux2 : ℝ) : Prop where
  flux1_eq : flux1 = waveHeatingFluxWithLength fluxRef loopLength1 lengthRef lengthExponent
  flux2_eq : flux2 = waveHeatingFluxWithLength fluxRef loopLength2 lengthRef lengthExponent
  length_ref_ne : lengthRef ≠ 0
  lengths_distinct : loopLength1 ≠ loopLength2
  fluxes_ne : flux1 ≠ flux2

theorem WaveLengthScalingDiscriminant.fluxes_differ
    {fluxRef loopLength1 loopLength2 lengthRef lengthExponent flux1 flux2 : ℝ}
    (h : WaveLengthScalingDiscriminant fluxRef loopLength1 loopLength2 lengthRef lengthExponent
      flux1 flux2) :
    flux1 ≠ flux2 :=
  h.fluxes_ne

/-!
## §5. Ratio witnesses and comparison bundle
-/

/-- Dimensionless ratio `F_HQIV / F_A`. -/
def hqivToAlfvenFluxRatio (hqivFlux alfvenFlux : ℝ) : ℝ :=
  if alfvenFlux = 0 then 0 else hqivFlux / alfvenFlux

/-- Dimensionless ratio `F_HQIV / F_N`. -/
def hqivToNanoflareFluxRatio (hqivFlux nanoflareFlux : ℝ) : ℝ :=
  if nanoflareFlux = 0 then 0 else hqivFlux / nanoflareFlux

theorem hqivToAlfvenFluxRatio_eq_div
    (hqivFlux alfvenFlux : ℝ) (h : alfvenFlux ≠ 0) :
    hqivToAlfvenFluxRatio hqivFlux alfvenFlux = hqivFlux / alfvenFlux := by
  unfold hqivToAlfvenFluxRatio
  simp [h]

theorem hqivToNanoflareFluxRatio_eq_div
    (hqivFlux nanoflareFlux : ℝ) (h : nanoflareFlux ≠ 0) :
    hqivToNanoflareFluxRatio hqivFlux nanoflareFlux = hqivFlux / nanoflareFlux := by
  unfold hqivToNanoflareFluxRatio
  simp [h]

/-- Full comparison row for one coronal readout (caller supplies plasma + wave/nanoflare slots). -/
structure CoronalHeatingComparisonWitness where
  nq : ℝ
  Estar : ℝ
  couplingLog : ℝ
  vParallel : ℝ
  phiPhoto : ℝ
  phiCorona : ℝ
  rho : ℝ
  vAlfven : ℝ
  dampingFraction : ℝ
  eventEnergy : ℝ
  eventRate : ℝ
  crossSection : ℝ
  hqivFlux : ℝ
  alfvenFlux : ℝ
  nanoflareFlux : ℝ
  hqiv_eq :
    hqivFlux = hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona
  alfven_eq :
    alfvenFlux = alfvenWaveHeatingFluxDensity rho vAlfven dampingFraction
  nanoflare_eq :
    nanoflareFlux = nanoflareHeatingFluxDensity eventEnergy eventRate crossSection

theorem CoronalHeatingComparisonWitness.hqivToAlfven_eq
    (w : CoronalHeatingComparisonWitness) :
    hqivToAlfvenFluxRatio w.hqivFlux w.alfvenFlux =
      if w.alfvenFlux = 0 then 0 else w.hqivFlux / w.alfvenFlux := rfl

theorem CoronalHeatingComparisonWitness.hqivToNanoflare_eq
    (w : CoronalHeatingComparisonWitness) :
    hqivToNanoflareFluxRatio w.hqivFlux w.nanoflareFlux =
      if w.nanoflareFlux = 0 then 0 else w.hqivFlux / w.nanoflareFlux := rfl

/-- Construct a comparison witness from definitional equalities (Python readout discharge). -/
def CoronalHeatingComparisonWitness.mk'
    (nq Estar couplingLog vParallel phiPhoto phiCorona : ℝ)
    (rho vAlfven dampingFraction : ℝ)
    (eventEnergy eventRate crossSection : ℝ) :
    CoronalHeatingComparisonWitness where
  nq := nq
  Estar := Estar
  couplingLog := couplingLog
  vParallel := vParallel
  phiPhoto := phiPhoto
  phiCorona := phiCorona
  rho := rho
  vAlfven := vAlfven
  dampingFraction := dampingFraction
  eventEnergy := eventEnergy
  eventRate := eventRate
  crossSection := crossSection
  hqivFlux := hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona
  alfvenFlux := alfvenWaveHeatingFluxDensity rho vAlfven dampingFraction
  nanoflareFlux := nanoflareHeatingFluxDensity eventEnergy eventRate crossSection
  hqiv_eq := rfl
  alfven_eq := rfl
  nanoflare_eq := rfl

/-!
## §6. Honesty ledger
-/

structure CoronalHeatingComparisonHonestyLedger : Prop where
  hqiv_length_independent :
    ∀ (nq Estar couplingLog vParallel phiPhoto phiCorona L1 L2 : ℝ),
      hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona =
        hqivBoundaryHeatingFluxDensity nq Estar couplingLog vParallel phiPhoto phiCorona
  footpoint_discriminant :
    ∀ {nq Estar couplingLog vParallel phiPhoto phiCorona L1 L2 flux1 flux2 : ℝ},
      HqivFootpointOnlyFluxDiscriminant nq Estar couplingLog vParallel phiPhoto phiCorona
        L1 L2 flux1 flux2 → flux1 = flux2

theorem coronalHeatingComparisonHonestyLedger_discharged :
    CoronalHeatingComparisonHonestyLedger where
  hqiv_length_independent := hqivBoundaryFlux_length_independent
  footpoint_discriminant := HqivFootpointOnlyFluxDiscriminant.fluxes_equal

end

end Hqiv.Physics
