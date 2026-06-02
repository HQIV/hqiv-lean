import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.ChargedLeptonResonance
import Hqiv.Physics.QuarkResonanceMassFunctional

/-!
# Quark sector from electroweak outer closure (blank-slate scaffold)

This module **does not** import `QuarkMetaResonance` or any top/bottom GeV anchors.

**Design (parallel to the EM / W story):**

* **Triality generations** — `Hqiv.Algebra.So8RepIndex` (`Fin 3`) labels the three inequivalent
  eight-dimensional slots, exactly as in the Spin(8) / triality narrative.
* **Mass ratios** — reuse `resonanceProduct` from `ChargedLeptonResonance` (same Fano / detuned
  surface ladder that drives the charged-lepton functional in `SM_GR_Unification.smMassFromGeometry`).
* **Absolute normalization (W-sector anchor)** — use `vacuumExpectationValueGauge`, the **same**
  outer-horizon geometric scale that enters `M_W_derived = su2CouplingDerived * vacuumExpectationValueGauge`.

So quark masses here are literally “**weak closure vev / generation resonance product**”, with the
heavy triality slot equal to the full vev (so that slot times `su2CouplingDerived` reproduces `M_W_derived`).

**EM-sector dressing (optional second track):** divide by `phi_of_shell referenceM`, the same auxiliary
field readout used throughout the φ–α ladder (`AuxiliaryField`), without importing the full bound-state
library.
-/

namespace Hqiv.Physics

open Hqiv.Algebra Hqiv

/-- Blank-slate quark mass: outer gauge vev divided by the lepton-matched resonance product. -/
noncomputable def quarkMassFromGaugeVevResonance (ρ : So8RepIndex) : ℝ :=
  vacuumExpectationValueGauge / resonanceProduct ρ

theorem vacuumExpectationValueGauge_pos : 0 < vacuumExpectationValueGauge := by
  have hcalc : vacuumExpectationValueGauge = (1176 / 5 : ℝ) := by
    have hMW : M_W_derived = (392 : ℝ) / 5 := boson_witness_M_W
    have hdef : M_W_derived = (1 / 3 : ℝ) * vacuumExpectationValueGauge := by
      simp [M_W_derived, gaugeBosonMassFromVevGauge, su2CouplingDerived, trialityOrder]
    have := hdef.symm.trans hMW
    field_simp at this
    linarith
  rw [hcalc]
  norm_num

theorem quarkMassFromGaugeVevResonance_pos (ρ : So8RepIndex) :
    0 < quarkMassFromGaugeVevResonance ρ := by
  unfold quarkMassFromGaugeVevResonance
  exact div_pos vacuumExpectationValueGauge_pos (resonanceProduct_pos ρ)

/-- Gram-style identity: mass times resonance product recovers the single outer closure scale. -/
theorem quarkMassFromGaugeVevResonance_mul_resonance (ρ : So8RepIndex) :
    quarkMassFromGaugeVevResonance ρ * resonanceProduct ρ = vacuumExpectationValueGauge := by
  unfold quarkMassFromGaugeVevResonance
  rw [div_mul_cancel₀ vacuumExpectationValueGauge (ne_of_gt (resonanceProduct_pos ρ))]

/-- The heavy triality slot carries the full vev (`resonanceProduct` is `1` there). -/
theorem quarkMass_heavyTriality_eq_vev :
    quarkMassFromGaugeVevResonance rep8SMinus = vacuumExpectationValueGauge := by
  simp [quarkMassFromGaugeVevResonance, resonanceProduct, rep8SMinus]

/-- Same slot as above: multiplying by `su2CouplingDerived` reproduces `M_W_derived`. -/
theorem quarkMass_heavyTriality_mul_su2_eq_MW :
    quarkMassFromGaugeVevResonance rep8SMinus * su2CouplingDerived = M_W_derived := by
  simp [quarkMassFromGaugeVevResonance, resonanceProduct, rep8SMinus, M_W_derived,
    gaugeBosonMassFromVevGauge, mul_comm]

/-- Packaged certificate: positivity, trace-like product law, and W mass contact on the heavy slot. -/
theorem quark_ew_sector_mass_certificate :
    (∀ ρ : So8RepIndex, 0 < quarkMassFromGaugeVevResonance ρ) ∧
      (∀ ρ : So8RepIndex,
        quarkMassFromGaugeVevResonance ρ * resonanceProduct ρ = vacuumExpectationValueGauge) ∧
      quarkMassFromGaugeVevResonance rep8SMinus * su2CouplingDerived = M_W_derived :=
  ⟨quarkMassFromGaugeVevResonance_pos, quarkMassFromGaugeVevResonance_mul_resonance,
    quarkMass_heavyTriality_mul_su2_eq_MW⟩

/-! ### EM dressing via φ(lock-in) (same object as the O–Maxwell / α_eff ladder) -/

noncomputable def quarkMassFromGaugeVevPhiDress (ρ : So8RepIndex) : ℝ :=
  quarkMassFromGaugeVevResonance ρ / phi_of_shell referenceM

theorem phi_lockin_pos : 0 < phi_of_shell referenceM :=
  phi_of_shell_pos referenceM

theorem quarkMassFromGaugeVevPhiDress_pos (ρ : So8RepIndex) :
    0 < quarkMassFromGaugeVevPhiDress ρ := by
  unfold quarkMassFromGaugeVevPhiDress
  exact div_pos (quarkMassFromGaugeVevResonance_pos ρ) phi_lockin_pos

/-! ### Comparison to the τ-resonance track (`QuarkResonanceMassFunctional`) -/

theorem m_tau_Pl_ne_zero : (m_tau_Pl : ℝ) ≠ 0 := by norm_num [m_tau_Pl]

theorem quarkMass_ew_track_over_tau_track (ρ : So8RepIndex) :
    quarkMassFromGaugeVevResonance ρ / quarkLikeMassFromTauResonance ρ =
      vacuumExpectationValueGauge / m_tau_Pl := by
  unfold quarkMassFromGaugeVevResonance quarkLikeMassFromTauResonance
  field_simp [m_tau_Pl_ne_zero, (resonanceProduct_pos ρ).ne']

end Hqiv.Physics
