import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.Physics.BoundStates

/-!
# Bond-state network traces

This module is the structural Lean counterpart of
`scripts/hqiv_bond_state_network.py` and `Hqiv.QuantumChemistry.CurvatureBondContact`.

Binding energy lives in the same curvature slot as hadron mass (inside trapped
ratio vs outside contact `G_eff·θ^α`); the network trace is the bookkeeping layer
for separated / edge / hyperclosure weights before eV projection.

The point is deliberately not a scalar shortcut.  A molecule is represented by:

* separated node traces (nuclei / local electron states),
* edge closure traces (geometry brought close enough to share Casimir boundary data),
* an optional graph-level hyperclosure trace for multi-bond molecules.

The chemistry number is a projection of the **closed network trace**.  The main
identity proved here is the bookkeeping invariant:

`closed network - separated network = edge closure + hyperclosure`.

No empirical numbers or fitted potentials are introduced.
-/

namespace Hqiv.QuantumChemistry

open scoped BigOperators
open Finset
open Hqiv.Physics

noncomputable section

/-- A molecular bond-state network with `nodeCount` local fragment states and
`edgeCount` explicit bond-closure states. -/
structure BondStateNetwork (nodeCount edgeCount : ℕ) where
  /-- Separated fragment / nucleus / local electronic trace weights. -/
  nodeWeight : Fin nodeCount → NetworkWeight
  /-- Bond closure trace weights: geometry-near Casimir overlap channels. -/
  edgeWeight : Fin edgeCount → NetworkWeight
  /-- Higher-order graph closure trace (zero for pure dimers). -/
  hyperWeight : NetworkWeight

/-- Sum of separated node traces. -/
noncomputable def separatedWeight {nodeCount edgeCount : ℕ}
    (net : BondStateNetwork nodeCount edgeCount) : NetworkWeight :=
  fun k => ∑ i : Fin nodeCount, net.nodeWeight i k

/-- Sum of explicit edge-closure traces. -/
noncomputable def edgeClosureWeight {nodeCount edgeCount : ℕ}
    (net : BondStateNetwork nodeCount edgeCount) : NetworkWeight :=
  fun k => ∑ e : Fin edgeCount, net.edgeWeight e k

/-- The bond-state surplus trace before projection to an observable. -/
noncomputable def bondStateSurplusWeight {nodeCount edgeCount : ℕ}
    (net : BondStateNetwork nodeCount edgeCount) : NetworkWeight :=
  fun k => edgeClosureWeight net k + net.hyperWeight k

/-- Closed molecular trace: separated fragments plus bond closure plus graph closure. -/
noncomputable def closedNetworkWeight {nodeCount edgeCount : ℕ}
    (net : BondStateNetwork nodeCount edgeCount) : NetworkWeight :=
  fun k => separatedWeight net k + bondStateSurplusWeight net k

theorem closedNetworkWeight_eq_separated_add_surplus {nodeCount edgeCount : ℕ}
    (net : BondStateNetwork nodeCount edgeCount) (k : So8Index) :
    closedNetworkWeight net k =
      separatedWeight net k + bondStateSurplusWeight net k := rfl

/-- Projection of a network trace through the existing 8×8 shell binding map. -/
noncomputable def networkTraceEnergyAtShell (m : ℕ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  E_bind_from_network m w c

theorem networkTraceEnergyAtShell_eq_bind (m : ℕ) (w : NetworkWeight) (c : ℝ) :
    networkTraceEnergyAtShell m w c = E_bind_from_network m w c := rfl

/-- Linearity of the shell projection over pointwise-added network traces. -/
theorem networkTraceEnergyAtShell_add
    (m : ℕ) (w₁ w₂ : NetworkWeight) (c : ℝ := 1) :
    networkTraceEnergyAtShell m (fun k => w₁ k + w₂ k) c =
      networkTraceEnergyAtShell m w₁ c + networkTraceEnergyAtShell m w₂ c := by
  unfold networkTraceEnergyAtShell E_bind_from_network
  simp [add_mul, Finset.sum_add_distrib]

/-- Closed molecular trace energy splits into separated + bond-state surplus energy. -/
theorem closedNetworkEnergy_eq_separated_add_surplus
    {nodeCount edgeCount : ℕ} (m : ℕ)
    (net : BondStateNetwork nodeCount edgeCount) (c : ℝ := 1) :
    networkTraceEnergyAtShell m (closedNetworkWeight net) c =
      networkTraceEnergyAtShell m (separatedWeight net) c +
        networkTraceEnergyAtShell m (bondStateSurplusWeight net) c := by
  simpa [closedNetworkWeight] using
    networkTraceEnergyAtShell_add m (separatedWeight net) (bondStateSurplusWeight net) c

/-- The projected bond-state surplus is exactly closed energy minus separated energy. -/
noncomputable def projectedBondStateSurplus
    {nodeCount edgeCount : ℕ} (m : ℕ)
    (net : BondStateNetwork nodeCount edgeCount) (c : ℝ := 1) : ℝ :=
  networkTraceEnergyAtShell m (closedNetworkWeight net) c -
    networkTraceEnergyAtShell m (separatedWeight net) c

theorem projectedBondStateSurplus_eq_surplus_energy
    {nodeCount edgeCount : ℕ} (m : ℕ)
    (net : BondStateNetwork nodeCount edgeCount) (c : ℝ := 1) :
    projectedBondStateSurplus m net c =
      networkTraceEnergyAtShell m (bondStateSurplusWeight net) c := by
  unfold projectedBondStateSurplus
  have h :=
    closedNetworkEnergy_eq_separated_add_surplus
      (nodeCount := nodeCount) (edgeCount := edgeCount) m net c
  rw [h]
  ring

/-- eV projection is a final readout layer, not part of the bond-state definition. -/
noncomputable def projectedBondStateSurplusEv
    {nodeCount edgeCount : ℕ} (m : ℕ)
    (net : BondStateNetwork nodeCount edgeCount) (evPerLambda : ℝ) (c : ℝ := 1) : ℝ :=
  projectedBondStateSurplus m net c * evPerLambda

theorem projectedBondStateSurplusEv_eq
    {nodeCount edgeCount : ℕ} (m : ℕ)
    (net : BondStateNetwork nodeCount edgeCount) (evPerLambda c : ℝ) :
    projectedBondStateSurplusEv m net evPerLambda c =
      networkTraceEnergyAtShell m (bondStateSurplusWeight net) c * evPerLambda := by
  unfold projectedBondStateSurplusEv
  have h :=
    projectedBondStateSurplus_eq_surplus_energy
      (nodeCount := nodeCount) (edgeCount := edgeCount) m net c
  rw [h]

end

end Hqiv.QuantumChemistry
