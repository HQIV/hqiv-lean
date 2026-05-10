import Hqiv.Geometry.HQVMCLASSBridge

namespace Hqiv

/-!
# HQVM ↔ FLRW-minded “main paper” node alignment (single chart)

This module does **not** formalize a complete \(k=0\) FLRW spacetime with Boltzmann sources,
gauge-fixed Einstein constraints, or a ΛCDM likelihood. It **packages** equivalences that are
already proved elsewhere so a manuscript can cite a **small** set of Lean names when equating:

* gravitational stationarity `S_HQVM_grav = 0` with the HQVM Friedmann constraint;
* that constraint with the **CLASS-style** \(H^2\) rescaling and `ρ_crit = 8πρ_tot/3`;
* the fixed rational prefactor **`15/13`** at `γ = 2/5`;
* the textbook flat normalization identity `3H² = 8πρ` ↔ `H² = ρ_crit` at `G = 1`.

**Primary references:** `Hqiv.Physics.Action` (`S_HQVM_grav`, `S_HQVM_grav_zero_iff_Friedmann`),
`Hqiv.Geometry.HQVMetric` (`HQVM_Friedmann_eq`, `G_eff`, `H_of_phi_eq`, `rho_total`),
`Hqiv.Geometry.HQVMCLASSBridge` (`HQVM_Friedmann_eq_iff_CLASS_H_squared_rational`, Picard / conformal
sections for deeper CLASS-facing algebra).
-/

/-- Stationarity of the HQVM gravitational action density ↔ `HQVM_Friedmann_eq`. -/
theorem paper_FLRW_node_Sgrav_iff_Friedmann (φ rho_m rho_r : ℝ) :
    S_HQVM_grav φ rho_m rho_r = 0 ↔ HQVM_Friedmann_eq φ rho_m rho_r :=
  S_HQVM_grav_zero_iff_Friedmann φ rho_m rho_r

/-- `S_grav = 0` iff the CLASS-rescaled squared-Hubble identity with rational **`15/13`**. -/
theorem paper_FLRW_node_Sgrav_iff_CLASS_H2_rational (φ rho_m rho_r : ℝ) :
    S_HQVM_grav φ rho_m rho_r = 0 ↔
      φ ^ 2 = (15 / 13 : ℝ) * G_eff φ * HQVM_CLASS_rhoCrit (rho_total rho_m rho_r) := by
  rw [paper_FLRW_node_Sgrav_iff_Friedmann, HQVM_Friedmann_eq_iff_CLASS_H_squared_rational]

/-- Same chain with `G_eff φ = φ^α` for `φ ≥ 0` (`G_eff_eq`). -/
theorem paper_FLRW_node_Sgrav_iff_CLASS_H2_rational_Geff_power (φ rho_m rho_r : ℝ) (hφ : 0 ≤ φ) :
    S_HQVM_grav φ rho_m rho_r = 0 ↔
      φ ^ 2 = (15 / 13 : ℝ) * (φ ^ alpha) * HQVM_CLASS_rhoCrit (rho_total rho_m rho_r) := by
  rw [paper_FLRW_node_Sgrav_iff_CLASS_H2_rational, G_eff_eq φ hφ]

/-- Textbook flat FRW at `G = 1`: `3H² = 8πρ` ↔ `H² = HQVM_CLASS_rhoCrit ρ`. -/
theorem paper_standard_flat_GR_H2_iff_CLASS_rhoCrit (H rho : ℝ) :
    3 * H ^ 2 = 8 * Real.pi * rho ↔ H ^ 2 = HQVM_CLASS_rhoCrit rho :=
  HQVM_CLASS_GR_flat_H_sq_iff H rho

/-- Vacuum node: `S_grav = 0` with vanishing densities forces `φ = 0`. -/
theorem paper_FLRW_node_Sgrav_vacuum_iff_phi_zero (φ : ℝ) :
    S_HQVM_grav φ 0 0 = 0 ↔ φ = 0 := by
  rw [paper_FLRW_node_Sgrav_iff_Friedmann, HQVM_Friedmann_eq_vacuum_iff]

end Hqiv
