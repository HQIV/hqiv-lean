import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Physics.FanoResonance
import Hqiv.QuantumChemistry.CurvatureBondContact
import Hqiv.QuantumChemistry.PhaseGeometryDensity

/-!
# Phase geometry → material response (n, ε_r, k_th, σ slot)

Structural readouts extending `PhaseGeometryDensity` — no fitted potentials:

* **Polarizability** from covalent binding softness and lattice α.
* **Clausius–Mossotti** → refractive index n, dielectric ε_r ≈ n².
* **Phonon thermal conductivity** k_th from binding stiffness, ρ, G_eff contact.
* **Ionic conductivity** σ slot (carrier fraction explicit; pure media → 0).
* **Molar heat capacity** C_p from contact-mode DOF × `B_hom`.
* **Latent heat** L_fusion from melt cohesive × tetrahedral shell release.
* **Dynamic viscosity** η (Eyring slot; solid → ∞).
* **Birefringence** Δn from hexagonal c/a CM split (ice Ih).

Python mirror: `scripts/hqiv_phase_material_response.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Algebra
open Hqiv.Physics
open Real

noncomputable section

/-- Shell-opening factor φ(3)/6 = 4/3 for oriented ice Ih (tetrahedral water). -/
noncomputable def phaseOrientationCmFactorH2OIceIh : ℝ := (4 : ℝ) / 3

theorem phaseOrientationCmFactorH2OIceIh_eq_phaseLiftCoeff_three :
    phaseOrientationCmFactorH2OIceIh = phaseLiftCoeff 3 := by
  rw [phaseOrientationCmFactorH2OIceIh]
  rw [Hqiv.Algebra.phaseLiftCoeff, Hqiv.phi_of_shell_closed_form, Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

/-- Liquid H₂O local-field divisor: 1 − c_Rindler = 1 − γ/2 = 4/5. -/
noncomputable def liquidLocalFieldDivisorH2O : ℝ := 1 - c_rindler_shared

theorem liquidLocalFieldDivisorH2O_eq_four_fifths :
    liquidLocalFieldDivisorH2O = (4 : ℝ) / 5 := by
  rw [liquidLocalFieldDivisorH2O, c_rindler_shared_eq_one_fifth]
  norm_num

/--
HQIV dimensionless polarizability scale (before Å³ conversion in Python):

α_scale ∝ α · (4/8) · (r_span/a₀)³ · (E_Ryd/E_bond) · (1 + ρ·α_lattice).
-/
noncomputable def hqivPolarizabilityScale
    (rSpanRatio eBondEv ρ_curv : ℝ) : ℝ :=
  alpha * strongChannelFraction * rSpanRatio ^ 3 *
    (13.605693122994 / max eBondEv 0.05) * (1 + ρ_curv * alpha)

/--
Clausius–Mossotti ratio (n²−1)/(n²+2) from mass density, formula weight, polarizability
volume [Å³ in Python; here a positive structural slot α_mol], and local-field divisor.
-/
noncomputable def clausiusMossottiRatio
    (ρ_g_cm3 mw_amu α_mol_angstrom3 coordDiv : ℝ) : ℝ :=
  let raw := (ρ_g_cm3 / mw_amu) * avogadroNumber * (α_mol_angstrom3 * angstromToCm ^ 3) / 3
  raw / max coordDiv 1e-6

/-- Oriented ice Ih CM factor on top of raw ratio. -/
noncomputable def clausiusMossottiRatioH2OIceIh (ρ_g_cm3 α_mol : ℝ) : ℝ :=
  clausiusMossottiRatio ρ_g_cm3 18.015 α_mol 1 * phaseOrientationCmFactorH2OIceIh

/-- Liquid local-field divisor from phase participation η = θ/θ₀: ``1 − c_Rindler·η``. -/
noncomputable def localFieldDivisorFromEta (η : ℝ) : ℝ :=
  1 - c_rindler_shared * η

theorem localFieldDivisorFromEta_eq_four_fifths_at_unit :
    localFieldDivisorFromEta 1 = liquidLocalFieldDivisorH2O := by
  rw [localFieldDivisorFromEta, liquidLocalFieldDivisorH2O, mul_one]

/-- ``G_eff(η) = η^α`` on optical phase participation (``CurvatureBondContact`` spine). -/
noncomputable def gEffFromPhaseParticipation (η : ℝ) : ℝ := η ^ alpha

/-- Solid apolar / pyramidal Onsager slot: ``n_domains · phaseLiftCoeff(n−1) / G_eff(η)``. -/
noncomputable def solidOnsagerLocalFieldDivisor (nDomains : ℕ) (η : ℝ) : ℝ :=
  let n := max nDomains 1
  let m := max (n - 1) 1
  (n : ℝ) * phaseLiftCoeff m / max (gEffFromPhaseParticipation η) 1e-6

/-- Oriented ice-Ih CM factor: ``phaseLiftCoeff(n−1) · G_eff(η) · (1 + γ/4)``. -/
noncomputable def phaseOrientationCmFactorTetrahedralIh (nDomains : ℕ) (η : ℝ) : ℝ :=
  let m := max (nDomains - 1) 1
  phaseLiftCoeff m * gEffFromPhaseParticipation η * (1 + gamma_HQIV / 4)

/-- Pyramidal liquid local-field slot: ``base · n²/4``. -/
noncomputable def liquidLocalFieldDivisorPyramidal (nDomains : ℕ) (η : ℝ) : ℝ :=
  let base := localFieldDivisorFromEta η
  let n := max nDomains 1
  max (base * (n : ℝ) ^ 2 / 4) 1e-6

/-- Linear-chain liquid slot: ``base · (1 + γ)``. -/
noncomputable def liquidLocalFieldDivisorLinearChain (η : ℝ) : ℝ :=
  max (localFieldDivisorFromEta η * (1 + gamma_HQIV)) 1e-6

/-- Apolar liquid slot: ``base · (1 + (n−1)γ)``. -/
noncomputable def liquidLocalFieldDivisorApolar (nDomains : ℕ) (η : ℝ) : ℝ :=
  let base := localFieldDivisorFromEta η
  let n := max nDomains 1
  max (base * (1 + (max (n - 1) 0 : ℝ) * gamma_HQIV)) 1e-6

/-- Solid linear-chain Onsager slot: ``n_contacts / (2 G_eff(η))``. -/
noncomputable def solidLocalFieldDivisorLinearChain (nContacts : ℕ) (η : ℝ) : ℝ :=
  max ((max nContacts 1 : ℝ) / (2 * max (gEffFromPhaseParticipation η) 1e-6)) 1e-6

noncomputable def clausiusMossottiRatioH2OLiquid (α_mol : ℝ) : ℝ :=
  clausiusMossottiRatio 1 18.015 α_mol liquidLocalFieldDivisorH2O

/-- n² from CM; valid when `cm < 1`. -/
noncomputable def refractiveIndexSquaredFromCM (cm : ℝ) : ℝ :=
  if cm < 1 then (1 + 2 * cm) / (1 - cm) else 1

noncomputable def refractiveIndexFromCM (cm : ℝ) : ℝ :=
  Real.sqrt (max 1 (refractiveIndexSquaredFromCM cm))

noncomputable def dielectricConstantFromRefractiveIndex (n : ℝ) : ℝ := n ^ 2

theorem dielectricConstantFromRefractiveIndex_eq_n_sq (n : ℝ) :
    dielectricConstantFromRefractiveIndex n = n ^ 2 := rfl

theorem refractiveIndexSquaredFromCM_ge_one
    (cm : ℝ) (hcm : 0 ≤ cm ∧ cm < 1) :
    1 ≤ refractiveIndexSquaredFromCM cm := by
  unfold refractiveIndexSquaredFromCM
  by_cases h : cm < 1
  · have hden : 0 < 1 - cm := sub_pos.mpr hcm.2
    simp [h]
    rw [one_le_div_iff]
    exact Or.inl ⟨hden, by nlinarith [hcm.1]⟩
  · simp [h]

theorem refractiveIndexFromCM_ge_one
    (cm : ℝ) (hcm : 0 ≤ cm ∧ cm < 1) :
    1 ≤ refractiveIndexFromCM cm := by
  have h1 := refractiveIndexSquaredFromCM_ge_one cm hcm
  dsimp [refractiveIndexFromCM]
  rw [one_le_sqrt]
  exact le_max_left 1 (refractiveIndexSquaredFromCM cm)

/--
Phonon thermal conductivity slot [W/(m·K) structural units in Python]:

k_th = (1/3) ρ c_spec v_s ℓ G_eff(θ) B_hom.
-/
noncomputable def phononThermalConductivitySlot
    (ρ_kg c_spec v_s ell geff b_hom : ℝ) : ℝ :=
  (1 / 3 : ℝ) * ρ_kg * c_spec * v_s * ell * geff * b_hom

theorem phononThermalConductivitySlot_pos
    (ρ_kg c_spec v_s ell geff b_hom : ℝ)
    (hρ : 0 < ρ_kg) (hc : 0 < c_spec) (hv : 0 < v_s) (hℓ : 0 < ell)
    (hg : 0 < geff) (hb : 0 < b_hom) :
    0 < phononThermalConductivitySlot ρ_kg c_spec v_s ell geff b_hom := by
  unfold phononThermalConductivitySlot
  positivity

/--
Ionic conductivity slot: zero without explicit carriers (pure-water limit).
-/
noncomputable def ionicConductivitySlot (carrierFraction : ℝ) (σ_scale : ℝ) : ℝ :=
  carrierFraction * σ_scale

theorem ionicConductivitySlot_zero_of_zero_carrier (σ_scale : ℝ) :
    ionicConductivitySlot 0 σ_scale = 0 := by
  unfold ionicConductivitySlot
  ring

/-- Dielectric from phase-derived CM at ice Ih (structural composition). -/
noncomputable def dielectricConstantH2OIceIhFromCM (cm : ℝ) : ℝ :=
  dielectricConstantFromRefractiveIndex (refractiveIndexFromCM cm)

theorem dielectricConstantH2OIceIhFromCM_eq_n_sq (cm : ℝ) :
    dielectricConstantH2OIceIhFromCM cm =
      refractiveIndexFromCM cm ^ 2 := by
  unfold dielectricConstantH2OIceIhFromCM dielectricConstantFromRefractiveIndex
  ring

/-- Thermal slot dressed by homogeneous curvature at bulk H₂O contact ξ. -/
noncomputable def thermalConductivityH2OBulkSlot
    (ξ ρ_curv ρ_kg c_spec v_s ell θ : ℝ) : ℝ :=
  phononThermalConductivitySlot ρ_kg c_spec v_s ell
    (outsideContactCoupling θ) (homogeneousCurvatureBudgetFromPhase ξ ρ_curv)

/-- Molar heat capacity slot: (3 n_atoms) R × (1 + α·𝟙_solid) × B_hom. -/
noncomputable def molarHeatCapacitySlot (nAtoms b_hom : ℝ) (solid : Bool) : ℝ :=
  let dof := 3 * nAtoms * (if solid then 1 + alpha else 1)
  dof * 8.314462618 * b_hom

/-- Squared shell-opening factor on latent heat (φ(3)/6)² / (1+α). -/
noncomputable def latentHeatShellReleaseFactor : ℝ :=
  phaseOrientationCmFactorH2OIceIh ^ 2 / (1 + alpha)

/-- Latent heat slot L_f = E_melt · N_A · n_inter · releaseFactor (structural units). -/
noncomputable def latentHeatFusionSlot (eMeltEv nInter : ℝ) : ℝ :=
  eMeltEv * 96485.33212 * nInter * latentHeatShellReleaseFactor

/-- Hexagonal c/a split for CM birefringence: ±(c/a − 1)·c_Rindler/20 on isotropic CM. -/
noncomputable def hexagonalCmSplitFactor (cOverA : ℝ) : ℝ :=
  (cOverA - 1) * c_rindler_shared / 20

noncomputable def hexagonalCmFactors (cOverA : ℝ) : ℝ × ℝ :=
  let s := hexagonalCmSplitFactor cOverA
  (1 + s, max (1 - s) 1e-6)

/-- Birefringence Δn slot = |n(f₊) − n(f₋)| (Python evaluates n from CM). -/
noncomputable def birefringenceDeltaNSlot (nOrdinary nExtraordinary : ℝ) : ℝ :=
  |nOrdinary - nExtraordinary|

theorem birefringenceDeltaNSlot_nonneg (nOrdinary nExtraordinary : ℝ) :
    0 ≤ birefringenceDeltaNSlot nOrdinary nExtraordinary := abs_nonneg _

/-- Dynamic viscosity slot (Pa·s): zero for solid flag, positive for liquid inputs. -/
noncomputable def dynamicViscositySlot (solid : Bool) (η_liquid : ℝ) : ℝ :=
  if solid then 0 else η_liquid

theorem dynamicViscositySlot_zero_of_solid (η_liquid : ℝ) :
    dynamicViscositySlot true η_liquid = 0 := by
  unfold dynamicViscositySlot
  simp

end

end Hqiv.QuantumChemistry
