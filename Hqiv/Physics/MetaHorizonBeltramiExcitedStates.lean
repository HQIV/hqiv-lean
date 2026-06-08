import Hqiv.Geometry.QuaternionMaxwellS3OMaxwellS4Spectral
import Hqiv.Physics.FanoSectorSpectralMassEmergence
import Hqiv.Physics.MetaHorizonExcitedStates
import Hqiv.Topology.HopfShellComplex

namespace Hqiv.Physics

open Hqiv.Geometry
open Hqiv.Topology

/-!
# Meta-horizon excited masses from Beltrami / Laplace–Beltrami spectra

The synthesis paper (`papers/tuft_hqiv_dynamic_mass_spectrum`) records the operational
meta-horizon catalog as a **readout layer** whose naive composite-trace channel has the
wrong sign for the first radial step.  This module supplies the **first-principles
spectral derivation** of that catalog:

* **Radial (`n`) excitations** on the lock-in drum are the scalar **`S⁴` Laplace–Beltrami**
  ladder (`λ_ℓ = ℓ(ℓ+3)` from `QuaternionMaxwellS3OMaxwellS4Spectral`).  The discrete
  shell area law `S(m) = (m+1)(m+2)` is exactly `λ_m + 2` on that chart.
* **Orbital (`ℓ`) excitations** are **detuned sector-Gaussian** steps — the leading term
  of the TUFT contact-Beltrami (`B = ⋆d`) sector determinant on the strong Hopf shell
  (`FanoSectorSpectralMassEmergence` / `tuftSectorZetaDet`).

The main closure theorem is `metaHorizonExcitedMassReadout_eq_beltramiSpectralReadout`:
the calculator/catalog mass equals the Beltrami-spectral assembly proved here.
-/

/-! ## Shell area = `S⁴` Laplace eigenvalue + 2 -/

theorem shellSurface_eq_laplaceBeltramiEigenvalueS4_plus_two (m : ℕ) :
    shellSurface m = laplaceBeltramiEigenvalueS4 m + 2 := by
  unfold shellSurface laplaceBeltramiEigenvalueS4
  ring

theorem laplaceBeltramiEigenvalueS4_nonneg (m : ℕ) : 0 ≤ laplaceBeltramiEigenvalueS4 m := by
  unfold laplaceBeltramiEigenvalueS4
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm3 : (0 : ℝ) ≤ (m : ℝ) + 3 := by linarith
  exact mul_nonneg hm hm3

theorem laplaceBeltramiEigenvalueS4_add_two_pos (m : ℕ) : 0 < laplaceBeltramiEigenvalueS4 m + 2 := by
  linarith [laplaceBeltramiEigenvalueS4_nonneg m]

theorem shellSurface_eq_laplaceBeltrami_plus_two (m : ℕ) :
    internalSurfaceArea m = laplaceBeltramiEigenvalueS4 m + 2 := by
  rw [internalSurfaceArea_eq_shellSurface, shellSurface_eq_laplaceBeltramiEigenvalueS4_plus_two]

/-! ## Radial excitation = `S⁴` Beltrami eigenvalue ratio -/

/-- Radial meta-horizon increment from the scalar `S⁴` Laplace–Beltrami ladder. -/
noncomputable def metaHorizonBeltramiRadialDelta (n : ℕ) : ℝ :=
  derivedProtonMass *
    (laplaceBeltramiEigenvalueS4 (referenceM + n) + 2) /
      (laplaceBeltramiEigenvalueS4 referenceM + 2) - derivedProtonMass

theorem metaHorizonBeltramiRadialDelta_zero :
    metaHorizonBeltramiRadialDelta 0 = 0 := by
  unfold metaHorizonBeltramiRadialDelta
  field_simp [Nat.add_zero, ne_of_gt (laplaceBeltramiEigenvalueS4_add_two_pos referenceM)]
  ring

theorem metaHorizonBeltramiRadialDelta_eq_radialOperational (n : ℕ) :
    metaHorizonBeltramiRadialDelta n = radialExcitationDeltaOperational n := by
  unfold metaHorizonBeltramiRadialDelta radialExcitationDeltaOperational
  rw [← shellSurface_eq_laplaceBeltrami_plus_two (referenceM + n),
    ← shellSurface_eq_laplaceBeltrami_plus_two referenceM,
    internalSurfaceArea_eq_shellSurface, internalSurfaceArea_eq_shellSurface]
  field_simp [ne_of_gt (shellSurface_pos referenceM)]

theorem radialExcitationDeltaOperational_eq_s4BeltramiRatio (n : ℕ) :
    radialExcitationDeltaOperational n =
      derivedProtonMass *
        (laplaceBeltramiEigenvalueS4 (referenceM + n) + 2) /
          (laplaceBeltramiEigenvalueS4 referenceM + 2) - derivedProtonMass := by
  rw [← metaHorizonBeltramiRadialDelta_eq_radialOperational n, metaHorizonBeltramiRadialDelta]

theorem resonanceDropK_eq_s4BeltramiRatio (step : Fin 2) :
    resonanceDropK step =
      (laplaceBeltramiEigenvalueS4 (top_at_lockin + step.val.succ) + 2) /
        (laplaceBeltramiEigenvalueS4 (top_at_lockin + step.val) + 2) := by
  fin_cases step <;>
    simp [resonanceDropK, top_at_lockin, internalSurfaceArea_eq_shellSurface,
      shellSurface_eq_laplaceBeltramiEigenvalueS4_plus_two, referenceM_eq_four_local]

/-! ## Orbital excitation = sector-Gaussian / contact-Beltrami leading term -/

/-- Strong-sector Hopf shell (`n = 2`) carrying the meta-horizon `S⁴` chart. -/
noncomputable def metaHorizonStrongHopfShell : HopfShell :=
  mkIntegrable 2 (Or.inr (Or.inl rfl))

theorem metaHorizonStrongHopfShell_integrable : metaHorizonStrongHopfShell.integrable := by
  simp [metaHorizonStrongHopfShell, mkIntegrable]

/-- Canonical contact Beltrami (`B = ⋆d`) data on the strong Hopf shell. -/
noncomputable def metaHorizonContactBeltrami : ContactBeltrami metaHorizonStrongHopfShell :=
  mkContactBeltrami metaHorizonStrongHopfShell metaHorizonStrongHopfShell_integrable

/-- Inverse-square weight from the coexact Beltrami spectrum at harmonic level `ℓ`. -/
noncomputable def contactBeltramiStarWeight (ℓ : ℕ) : ℝ :=
  (metaHorizonContactBeltrami.spectrum ℓ + 1)⁻¹

theorem metaHorizonContactBeltrami_spectrum_pos (ℓ : ℕ) :
    0 < metaHorizonContactBeltrami.spectrum ℓ + 1 := by
  unfold metaHorizonContactBeltrami mkContactBeltrami
  simp only
  linarith

theorem contactBeltramiStarWeight_pos (ℓ : ℕ) : 0 < contactBeltramiStarWeight ℓ := by
  unfold contactBeltramiStarWeight
  exact inv_pos.mpr (metaHorizonContactBeltrami_spectrum_pos ℓ)

/-- Orbital increment from the sector-Gaussian / TUFT determinant leading term. -/
noncomputable def metaHorizonBeltramiOrbitalDelta (ℓ : ℕ) : ℝ :=
  derivedProtonMass *
    max 0 (sectorGaussianLeadingWeight (referenceM + ℓ) / sectorGaussianLeadingWeight referenceM - 1)

theorem metaHorizonBeltramiOrbitalDelta_zero :
    metaHorizonBeltramiOrbitalDelta 0 = 0 := by
  unfold metaHorizonBeltramiOrbitalDelta
  simp [Nat.add_zero, div_self (ne_of_gt (sectorGaussianLeadingWeight_pos referenceM)), sub_self, mul_zero]

theorem metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational (ℓ : ℕ) :
    metaHorizonBeltramiOrbitalDelta ℓ = orbitalExcitationDeltaOperational ℓ := by
  unfold metaHorizonBeltramiOrbitalDelta orbitalExcitationDeltaOperational
  have hstep :
      geometricResonanceStep (referenceM + ℓ) referenceM =
        sectorGaussianLeadingWeight (referenceM + ℓ) / sectorGaussianLeadingWeight referenceM := by
    rw [geometricResonanceStep_eq_sectorGaussianLeading_ratio]
  rw [hstep]

theorem orbitalExcitationDeltaOperational_eq_sectorGaussianDelta (ℓ : ℕ) :
    orbitalExcitationDeltaOperational ℓ =
      derivedProtonMass *
        max 0 (sectorGaussianLeadingWeight (referenceM + ℓ) / sectorGaussianLeadingWeight referenceM - 1) := by
  rw [← metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational ℓ, metaHorizonBeltramiOrbitalDelta]

theorem orbitalExcitationDeltaOperational_eq_tuftZetaLeadingRatio (ℓ : ℕ) :
    orbitalExcitationDeltaOperational ℓ =
      derivedProtonMass *
        max 0
          ((tuftSectorZetaDet metaHorizonStrongHopfShell metaHorizonStrongHopfShell_integrable).leadingTerm
              (referenceM + ℓ) /
            (tuftSectorZetaDet metaHorizonStrongHopfShell metaHorizonStrongHopfShell_integrable).leadingTerm
              referenceM -
          1) := by
  rw [orbitalExcitationDeltaOperational_eq_sectorGaussianDelta]
  simp [tuftSectorZetaDet, sectorGaussianLeadingWeightForHopfShell]

/-! ## Full excited mass from Beltrami spectra -/

/-- Excited baryon mass from the `S⁴` radial + sector-Gaussian orbital Beltrami readouts. -/
noncomputable def metaHorizonExcitedMassFromBeltramiSpectrum (n ℓ : ℕ) : ℝ :=
  derivedProtonMass + metaHorizonBeltramiRadialDelta n + metaHorizonBeltramiOrbitalDelta ℓ

theorem metaHorizonExcitedMassFromBeltramiSpectrum_ground :
    metaHorizonExcitedMassFromBeltramiSpectrum 0 0 = derivedProtonMass := by
  simp [metaHorizonExcitedMassFromBeltramiSpectrum, metaHorizonBeltramiRadialDelta_zero,
    metaHorizonBeltramiOrbitalDelta_zero]

/-- **Main closure:** catalog readout equals the Beltrami-spectral assembly. -/
theorem metaHorizonExcitedMassReadout_eq_beltramiSpectralReadout (n ℓ : ℕ) :
    metaHorizonExcitedMassReadout n ℓ = metaHorizonExcitedMassFromBeltramiSpectrum n ℓ := by
  unfold metaHorizonExcitedMassReadout metaHorizonExcitedMassFromBeltramiSpectrum
  rw [metaHorizonBeltramiRadialDelta_eq_radialOperational,
    metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational]

theorem metaHorizonExcitedMassReadout_eq_s4Radial_plus_sectorGaussianOrbital (n ℓ : ℕ) :
    metaHorizonExcitedMassReadout n ℓ =
      derivedProtonMass +
        derivedProtonMass *
          (laplaceBeltramiEigenvalueS4 (referenceM + n) + 2) /
            (laplaceBeltramiEigenvalueS4 referenceM + 2) - derivedProtonMass +
        derivedProtonMass *
          max 0 (sectorGaussianLeadingWeight (referenceM + ℓ) / sectorGaussianLeadingWeight referenceM - 1) := by
  rw [metaHorizonExcitedMassReadout_eq_beltramiSpectralReadout,
    metaHorizonExcitedMassFromBeltramiSpectrum, metaHorizonBeltramiRadialDelta,
    metaHorizonBeltramiOrbitalDelta]
  ring

/-! ## Witness packaging -/

/-- Bundled certificate: operational excited masses are Beltrami-spectral, not ad hoc. -/
structure MetaHorizonBeltramiExcitationWitness where
  radial_eq_s4_beltrami : ∀ n, radialExcitationDeltaOperational n = metaHorizonBeltramiRadialDelta n
  orbital_eq_sector_gaussian : ∀ ℓ, orbitalExcitationDeltaOperational ℓ = metaHorizonBeltramiOrbitalDelta ℓ
  readout_eq_beltrami_spectrum : ∀ n ℓ, metaHorizonExcitedMassReadout n ℓ =
    metaHorizonExcitedMassFromBeltramiSpectrum n ℓ
  shell_area_eq_s4_eigenvalue : ∀ m, shellSurface m = laplaceBeltramiEigenvalueS4 m + 2
  orbital_eq_tuft_zeta_leading : ∀ ℓ, orbitalExcitationDeltaOperational ℓ =
    derivedProtonMass *
      max 0
        ((tuftSectorZetaDet metaHorizonStrongHopfShell metaHorizonStrongHopfShell_integrable).leadingTerm
            (referenceM + ℓ) /
          (tuftSectorZetaDet metaHorizonStrongHopfShell metaHorizonStrongHopfShell_integrable).leadingTerm
            referenceM -
        1)

theorem metaHorizonBeltramiExcitationWitness_default : MetaHorizonBeltramiExcitationWitness where
  radial_eq_s4_beltrami := fun n => (metaHorizonBeltramiRadialDelta_eq_radialOperational n).symm
  orbital_eq_sector_gaussian := fun ℓ => (metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational ℓ).symm
  readout_eq_beltrami_spectrum := metaHorizonExcitedMassReadout_eq_beltramiSpectralReadout
  shell_area_eq_s4_eigenvalue := shellSurface_eq_laplaceBeltramiEigenvalueS4_plus_two
  orbital_eq_tuft_zeta_leading := orbitalExcitationDeltaOperational_eq_tuftZetaLeadingRatio

end Hqiv.Physics
