import HqivSpine.Physics.Binding

/-!
# `HqivSpine.Physics.TrappedCasimir` — strong binding as trapped zero-point × trace selection

The gluon-curvature note's central HQIV claim: network binding is **not** an
independent gluon-exchange sector. Each shell's binding cell factors exactly as

`binding cell(m) = trapped zero-point budget(m) × normalised SO(8) selection(m)`,

where

* the **per-mode zero-point** is `φ(m)/2`;
* the **available mode count** is `4 · latticeSimplexCount(m)`, so the **trapped
  zero-point budget** is `availableModes(m) · φ(m)/2`;
* the **normalised SO(8) trace selection** is `α_eff(m) / (φ(m)/2)`.

The `φ(m)/2` cancels, so the trapped Casimir cell is exactly `α_eff(m)` and the
binding coupling is `latticeSimplexCount(m) · α_eff(m)` — the spine's
`bindingCouplingAtShell`, now read as trapped radiative zero-point filtered by
composite-trace selection on the `so(8)` generators. No extra strong-sector
parameter enters.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **Per-mode Casimir zero-point** at shell `m`: `φ(m)/2`. -/
noncomputable def casimirPerMode (m : ℕ) : ℝ := (phi m : ℝ) / 2

/-- **Available trapped modes** at shell `m`: `4 · latticeSimplexCount(m)`. -/
def availableModes (m : ℕ) : ℕ := 4 * latticeSimplexCount m

/-- **Normalised SO(8) trace selection:** `α_eff(m) / (φ(m)/2)`. -/
noncomputable def normalizedSelection (m : ℕ) (c : ℝ := 1) : ℝ :=
  alphaEffAtShell m c / casimirPerMode m

/-- **Trapped Casimir coupling cell:** per-mode zero-point times normalised selection. -/
noncomputable def trappedCasimirCell (m : ℕ) (c : ℝ := 1) : ℝ :=
  casimirPerMode m * normalizedSelection m c

/-- **Trapped zero-point budget:** `availableModes(m) · φ(m)/2`. -/
noncomputable def trappedCasimirEnergy (m : ℕ) : ℝ :=
  (availableModes m : ℝ) * casimirPerMode m

theorem casimirPerMode_pos (m : ℕ) : 0 < casimirPerMode m := by
  unfold casimirPerMode
  have hphi : 0 < phi m := by unfold phi; omega
  have : (0 : ℝ) < (phi m : ℝ) := by exact_mod_cast hphi
  positivity

/-- **The trapped Casimir cell is exactly `α_eff(m)`** — the `φ(m)/2` cancels, so no
new strong-sector scale is hiding in the factorisation. -/
theorem trappedCasimirCell_eq_alphaEff (m : ℕ) (c : ℝ) :
    trappedCasimirCell m c = alphaEffAtShell m c := by
  unfold trappedCasimirCell normalizedSelection
  field_simp [ne_of_gt (casimirPerMode_pos m)]

/-- **Binding coupling = lattice × trapped Casimir cell.** -/
theorem bindingCouplingAtShell_eq_lattice_trappedCell (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c = (latticeSimplexCount m : ℝ) * trappedCasimirCell m c := by
  unfold bindingCouplingAtShell
  rw [← trappedCasimirCell_eq_alphaEff]

/-- **Binding coupling = (availableModes/4) × trapped Casimir cell.** -/
theorem bindingCouplingAtShell_eq_availableModes_quarter_trappedCell
    (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c = (availableModes m : ℝ) / 4 * trappedCasimirCell m c := by
  rw [bindingCouplingAtShell_eq_lattice_trappedCell]
  unfold availableModes
  push_cast; ring

/-- **The headline factorisation:** binding coupling = trapped zero-point budget / 4 ×
normalised SO(8) selection. Strong binding is trapped Casimir zero-point filtered by
composite-trace selection — not an independent gluon exchange. -/
theorem bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection
    (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c =
      trappedCasimirEnergy m / 4 * normalizedSelection m c := by
  rw [bindingCouplingAtShell_eq_availableModes_quarter_trappedCell]
  unfold trappedCasimirCell trappedCasimirEnergy normalizedSelection
  field_simp [ne_of_gt (casimirPerMode_pos m)]

/-- **Network binding is the weight sum times one trapped Casimir cell** (per lattice
site) — every generator's contribution is the same trapped zero-point object. -/
theorem E_bind_from_network_eq_sum_trappedCells (m : ℕ) (w : NetworkWeight) (c : ℝ) :
    E_bind_from_network m w c =
      (∑ k : So8Index, w k) * trappedCasimirCell m c * (latticeSimplexCount m : ℝ) := by
  unfold E_bind_from_network
  simp_rw [bindingCouplingAtShell_eq_lattice_trappedCell]
  rw [← Finset.sum_mul]
  ring

end HqivSpine.Physics
