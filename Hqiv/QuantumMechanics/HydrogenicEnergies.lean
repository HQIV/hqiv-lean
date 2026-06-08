/-
Closed-form hydrogenic energy scales used by `Schrodinger.lean` and `QuantumComputing/DigitalQuantumSimulation`.
Factored out so the digital simulation layer need not import the full patch Schrödinger development
(operators, wavefunctions, calculus).
-/

import Hqiv.Physics.Forces
import Hqiv.Physics.SM_GR_Unification
import Hqiv.Geometry.AuxiliaryField

namespace Hqiv

/-- Expected ground-state energy for a hydrogenic system in the HQIV effective description
(same formula as the former inline definition in `Schrodinger.lean`). -/
noncomputable def expectedGroundEnergy (Z : ℕ) (μ : ℝ) : ℝ :=
  - μ * (Z : ℝ) ^ 2 * (alpha_EM_at_MZ ^ 2) / 2

/-- Expected energy for principal quantum number `n ≥ 1` (Rydberg-style `∝ 1/n²`). -/
noncomputable def expectedEnergy (n : ℕ) (Z : ℕ) (μ : ℝ) : ℝ :=
  if hn : 0 < n then
    - μ * ((Z : ℝ) ^ 2) * (alpha_EM_at_MZ ^ 2) /
        (2 * (n : ℝ) ^ 2)
  else
    0

/-- Shell-resolved hydrogenic ground-state energy using the same `α_eff(m)` ladder
that appears in the bound-state mass modules. -/
noncomputable def expectedGroundEnergyAtShell (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ := 1) : ℝ :=
  - μ * (Z : ℝ) ^ 2 * ((one_over_alpha_eff (phi_of_shell m) c)⁻¹ ^ 2) / 2

/-- Principal-shell energy on the same convention as `expectedGroundEnergy`. -/
noncomputable def expectedEnergyAtLevel (n : ℕ) (Z : ℕ) (μ : ℝ) : ℝ :=
  if hn : 0 < n then
    expectedGroundEnergy Z μ / (n : ℝ) ^ 2
  else
    0

theorem expectedEnergy_eq_expectedEnergyAtLevel (n : ℕ) (Z : ℕ) (μ : ℝ) :
    expectedEnergy n Z μ = expectedEnergyAtLevel n Z μ := by
  by_cases hn : 0 < n
  · simp [expectedEnergy, expectedEnergyAtLevel, hn, expectedGroundEnergy]
    ring
  · simp [expectedEnergy, expectedEnergyAtLevel, hn]

end Hqiv
