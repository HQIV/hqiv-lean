import Hqiv.QuantumChemistry.PhaseGeometryDensity
import Hqiv.Physics.HQIVNuclei
import Mathlib.Tactic

/-!
# Phase elasticity and fracture-scale candidates

Bulk stiffness and Griffith-type fracture readouts from lattice contact binding and
coordination — witnesses only, not fitted moduli.

Python mirror: ``scripts/hqiv_crystal_fracture_witness.py``.

No tabulated Young's modulus or K_IC inputs; no `sorry`.

Ethics note: these are **scale witnesses**.  They deliberately do not claim a
production material handbook value for toughness; crystal anisotropy, crack geometry,
plasticity, grain boundaries, and semiconductor defects remain outside this first
contact-network scaffold.
-/

namespace Hqiv.QuantumChemistry

open Real
open Hqiv.Physics

noncomputable section

/-- Contact binding stiffness proxy ``E_bind / d³`` with ``d`` in metres (Pa scale). -/
noncomputable def contactBindingStiffnessPa (bindingEv contactDistAng : ℝ) : ℝ :=
  if contactDistAng ≤ 0 then 0
  else
    let dM := contactDistAng * 1e-10
    bindingEv * 1.602176634e-19 / max (dM ^ 3) 1e-36

/-- Isotropic bulk-modulus proxy from contact stiffness × coordination. -/
noncomputable def bulkModulusProxyPa (bindingEv contactDistAng nCoord : ℝ) : ℝ :=
  contactBindingStiffnessPa bindingEv contactDistAng * max nCoord 1

/-- Young's modulus proxy ``3 B`` (isotropic scaffold). -/
noncomputable def youngModulusProxyPa (bindingEv contactDistAng nCoord : ℝ) : ℝ :=
  3 * bulkModulusProxyPa bindingEv contactDistAng nCoord

/-- Griffith cohesive energy release rate ``G_c ≈ bind × n_coord / d`` [J/m²]. -/
noncomputable def griffithCohesiveEnergyReleaseJPerM2
    (bindingEv contactDistAng nCoord : ℝ) : ℝ :=
  if contactDistAng ≤ 0 then 0
  else
    bindingEv * 1.602176634e-19 * max nCoord 1 / (contactDistAng * 1e-10)

/-- Griffith-scale toughness witness ``K_scale = sqrt(2 E G_c)`` [Pa·√m]. -/
noncomputable def fractureToughnessCandidatePaSqrtM
    (bindingEv contactDistAng nCoord : ℝ) : ℝ :=
  Real.sqrt (
    2 * youngModulusProxyPa bindingEv contactDistAng nCoord *
      griffithCohesiveEnergyReleaseJPerM2 bindingEv contactDistAng nCoord)

theorem fractureToughnessCandidatePaSqrtM_nonneg
    (bindingEv contactDistAng nCoord : ℝ) :
    0 ≤ fractureToughnessCandidatePaSqrtM bindingEv contactDistAng nCoord :=
  Real.sqrt_nonneg _

/-! ## Strain ↔ stiffness fixed point

External / wall stress σ drives dimensionless strain ε.  Contact length responds
as `r = r₀ · (1 + ε)`, stiffness falls as `k ∝ 1/r³`, and the mechanical balance

`ε' = clamp01( σ / k(r(ε)) · k₀ )`

is iterated to a bounded fixed point.  No residual-inferred strain; no molecule case.
-/

/-- Length response under dimensionless strain. -/
noncomputable def contactLengthFromStrain (r0 strain : ℝ) : ℝ :=
  r0 * (1 + strain)

/-- Stiffness ratio `(r₀/r)³` under strain (binding held). -/
noncomputable def stiffnessRatioFromStrain (strain : ℝ) : ℝ :=
  (1 / max (1 + strain) 1e-12) ^ 3

/-- One strain update: `ε' = clamp01( σ · (k₀/k) · strongChannelFraction )`. -/
noncomputable def strainFromStressStiffness
    (stressPa k0Pa : ℝ) (strain : ℝ) : ℝ :=
  let k := k0Pa * stiffnessRatioFromStrain strain
  min 1 (max 0 (stressPa / max k 1e-30 * strongChannelFraction))

/-- Piezo↔stiffness equilibrium seed: thermal Lindemann strain plus one stress update.
At zero external stress the fixed point is the thermal seed (identity path). -/
noncomputable def piezoStiffnessEquilibriumStrain
    (thermalStrain stressPa k0Pa : ℝ) : ℝ :=
  if stressPa = 0 then thermalStrain
  else
    let eps := strainFromStressStiffness stressPa k0Pa thermalStrain
    min 1 (max 0 (thermalStrain + (1 - thermalStrain) * strongChannelFraction *
      (stressPa / max (k0Pa * stiffnessRatioFromStrain eps) 1e-30)))

theorem piezoStiffnessEquilibriumStrain_zero_stress (thermalStrain k0Pa : ℝ) :
    piezoStiffnessEquilibriumStrain thermalStrain 0 k0Pa = thermalStrain := by
  unfold piezoStiffnessEquilibriumStrain
  simp

/-! ## Contact force / Hessian / discrete phonon (DFT-slot readouts)

Same matrix spine as molecular spectra: binding depth \(D\) and contact length \(r\)
already determine the Morse backbone \(k = 2D/r^{2}\).  The force and phonon
readouts are log-derivatives of that dress product — not a new XC functional.

Python: ``scripts/hqiv_contact_force_readout.py``.
-/

/-- Electron-volt → joule (CODATA exact). -/
def electronVoltJoule : ℝ := 1.602176634e-19

/-- Ångström → metre. -/
def angstromMetre : ℝ := 1e-10

/-- Morse-backbone log-length derivative magnitude:
`k = 2 D / r²` ⇒ `|∂ log D / ∂ log r| = 2` at fixed well shape. -/
def morseBackboneLogLengthDeriv : ℝ := 2

/-- Characteristic contact force [N] from the log-dress:
`F = strong · (D / r) · |∂log E / ∂log r|`.
At the Morse backbone this is `strong · 2 D / r`. -/
noncomputable def contactForceFromLogDress
    (bindingEv contactDistAng logDeriv : ℝ) : ℝ :=
  if contactDistAng ≤ 0 then 0
  else
    strongChannelFraction *
      (bindingEv * electronVoltJoule) / (contactDistAng * angstromMetre) *
        |logDeriv|

/-- Morse-backbone contact force [N]. -/
noncomputable def contactForceMorseBackbone
    (bindingEv contactDistAng : ℝ) : ℝ :=
  contactForceFromLogDress bindingEv contactDistAng morseBackboneLogLengthDeriv

/-- Contact Hessian [N/m] = length-scaled force constant `2 D / r²`
(Lean ``lengthScaledForceConstant`` in SI units). -/
noncomputable def contactHessianNm
    (bindingEv contactDistAng : ℝ) : ℝ :=
  if contactDistAng ≤ 0 then 0
  else
    2 * (bindingEv * electronVoltJoule) /
      (contactDistAng * angstromMetre) ^ 2

/-- Discrete phonon angular frequency [rad/s] from Hessian and reduced mass [amu]. -/
noncomputable def discretePhononOmegaRad
    (hessianNm reducedMassAmu : ℝ) : ℝ :=
  if hessianNm ≤ 0 ∨ reducedMassAmu ≤ 0 then 0
  else
    let muKg := reducedMassAmu * 1.66053906660e-27
    Real.sqrt (hessianNm / muKg)

/-- Discrete phonon wavenumber [cm⁻¹] — same SI bridge as molecular `ωₑ`. -/
noncomputable def discretePhononWavenumberCm1
    (hessianNm reducedMassAmu : ℝ) : ℝ :=
  if hessianNm ≤ 0 ∨ reducedMassAmu ≤ 0 then 0
  else
    discretePhononOmegaRad hessianNm reducedMassAmu /
      (2 * Real.pi * 2.99792458e10)

/-- Minimal 1D acoustic dispersion on a Morse contact chain:
``ω(k) = 2 √(k_spring/μ) · |sin(k a / 2)|`` with dimensionless ``ka``.
At the zone boundary ``ka = π`` this is ``2 · ω_Γ`` of the single-contact
optical slot (DFT-slot band edge on the same Hessian). -/
noncomputable def discretePhononDispersionOmegaRad
    (hessianNm reducedMassAmu ka : ℝ) : ℝ :=
  if hessianNm ≤ 0 ∨ reducedMassAmu ≤ 0 then 0
  else
    2 * discretePhononOmegaRad hessianNm reducedMassAmu *
      |Real.sin (ka / 2)|

/-- Zone-boundary edge in wavenumber units [cm⁻¹]. -/
noncomputable def discretePhononDispersionWavenumberCm1
    (hessianNm reducedMassAmu ka : ℝ) : ℝ :=
  if hessianNm ≤ 0 ∨ reducedMassAmu ≤ 0 then 0
  else
    discretePhononDispersionOmegaRad hessianNm reducedMassAmu ka /
      (2 * Real.pi * 2.99792458e10)

/-- Optical / lattice phonon softener on the Morse Hessian:
``s = (4/8)·γ / max(CN_eff, 1)`` with
``CN_eff = 1`` for metal hydrides (anion Z=1) and ``CN`` otherwise.

Ionic / hydride solids take this lattice softener; pass ``apply = false``
(covalent / metallic) to keep identity.  Applied to ``k`` so ``ω`` scales
as ``√s``. -/
noncomputable def opticalPhononHessianSoftener
    (nCoord : ℝ) (hydride : Bool) : ℝ :=
  let cnEff := if hydride then (1 : ℝ) else max nCoord 1
  strongChannelFraction * gamma_HQIV / cnEff

/-- Dressed contact Hessian [N/m] for optical phonon / TO slot. -/
noncomputable def contactHessianOpticalNm
    (bindingEv contactDistAng nCoord : ℝ) (hydride applySoftener : Bool) : ℝ :=
  let k0 := contactHessianNm bindingEv contactDistAng
  if applySoftener then
    k0 * opticalPhononHessianSoftener nCoord hydride
  else
    k0

/-- Packing disorder score for glass / amorphous gate:
``S = γ · [(1 − w_periodic) + Var(CN)/⟨CN⟩ + open²]``.

Prefer amorphous packing when ``S > α``. -/
noncomputable def packingDisorderScore
    (periodicWeight meanCoord coordVariance openFraction : ℝ) : ℝ :=
  let w := max 0 (min 1 periodicWeight)
  let cn := max meanCoord 1e-9
  let varTerm := max 0 coordVariance / cn
  let openSq := (max 0 openFraction) ^ 2
  gamma_HQIV * ((1 - w) + varTerm + openSq)

/-- Contact-network allotrope ranking score:
``w_c · inc · p · (1 + γ · (4/8) · δ)`` with bond order ``p``, periodic
increment ``inc``, contact weight ``w_c``, and ionic character ``δ``. -/
noncomputable def contactNetworkAllotropeScore
    (bondOrder periodicIncrement contactWeight ionicCharacter : ℝ) : ℝ :=
  let δ := max 0 (min 1 ionicCharacter)
  contactWeight * periodicIncrement * bondOrder *
    (1 + gamma_HQIV * strongChannelFraction * δ)

theorem contactForceFromLogDress_nonpos_length
    (bindingEv logDeriv : ℝ) :
    contactForceFromLogDress bindingEv 0 logDeriv = 0 := by
  unfold contactForceFromLogDress; simp

theorem contactHessianNm_nonpos_length (bindingEv : ℝ) :
    contactHessianNm bindingEv 0 = 0 := by
  unfold contactHessianNm; simp

theorem contactForceMorseBackbone_eq
    (bindingEv contactDistAng : ℝ) (h : 0 < contactDistAng) :
    contactForceMorseBackbone bindingEv contactDistAng =
      strongChannelFraction * 2 *
        (bindingEv * electronVoltJoule) / (contactDistAng * angstromMetre) := by
  unfold contactForceMorseBackbone contactForceFromLogDress
    morseBackboneLogLengthDeriv
  have : ¬ contactDistAng ≤ 0 := not_le.mpr h
  simp [this]
  ring

end

end Hqiv.QuantumChemistry
