import HqivSpine.Chemistry.Molecule
import HqivSpine.Physics.Shell

/-!
# `HqivSpine.Chemistry.BondedHorizon` — joint vs separated mode surplus

Golfed from legacy `BondedHorizonCasimir`: the **bond surplus**
`E_joint − E_frag₁ − E_frag₂` on the separated-atom zero-point ladder from
`Chemistry.Molecule`, without importing the full `S⁷` metahorizon perturbation stack.

Honest scope: structural **non-additivity** bookkeeping on `siteModeEnergy` — not a fitted
eV anchor or Hartree–Fock replacement.
-/

namespace HqivSpine.Chemistry.BondedHorizon

open HqivSpine.Chemistry.Molecule
open HqivSpine.Physics

/-- **Dimensionless bond surplus** on shell indices `(m_total, m₁, m₂)`. -/
noncomputable def bondModeSurplus (m_total m₁ m₂ : ℕ) : ℝ :=
  siteModeEnergy m_total - siteModeEnergy m₁ - siteModeEnergy m₂

/-- Ionic-style split: `m_total = m₁ + m₂` narrative (same formula). -/
noncomputable def ionicBondSurplus (m₁ m₂ : ℕ) : ℝ :=
  bondModeSurplus (m₁ + m₂) m₁ m₂

/-- Covalent H₂-style witness: joint shell `1`, fragments `0`. -/
noncomputable def h2BondSurplus : ℝ := bondModeSurplus 1 0 0

theorem h2BondSurplus_eq : h2BondSurplus = siteModeEnergy 1 - siteModeEnergy 0 - siteModeEnergy 0 := rfl

/-- Binding convention: negative surplus = joint lower than separated parts. -/
noncomputable def bindingEnergyFromSurplus (surplus : ℝ) : ℝ := -surplus

theorem bindingEnergyFromSurplus_neg (surplus : ℝ) :
    bindingEnergyFromSurplus surplus = -surplus := rfl

end HqivSpine.Chemistry.BondedHorizon
