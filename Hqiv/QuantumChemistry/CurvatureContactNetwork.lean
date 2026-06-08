import Hqiv.QuantumChemistry.CurvatureBondContact
import Hqiv.QuantumChemistry.DynamicBindingChart
import Hqiv.QuantumChemistry.BondStateNetwork

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Curvature contact network (geometry + phase rules)

Precise bookkeeping for how **cluster mass deficits** and **contact curvature**
propagate through a finite graph before the TUFT vev geometric mean and eV readout.

This is the Lean spine for `scripts/hqiv_curvature_contact_network.py` and for
extensions to condensed phases (liquid coordination, solid periodic images).

## Network rule (conceptual)

* **Nodes** — fragments / nuclei with bound cluster mass `clusterMassMeV m A`.
* **Contacts** (typed):
  * `clusterDeficit` — node self: lowers effective mass (D, T, … valley memory).
  * `covalentBond` — attractive edge: outside `G_eff(θ)` closure (same as `CurvatureBondContact`).
  * `stericRepulsion` — repulsive edge (e.g. peripheral H–H): adds curvature mass back.
  * `hyperclosure` — graph-level multi-bond closure (`BondStateNetwork.hyperWeight`).
  * `periodicImage` — lattice repeat for solid/liquid scaffolds (coordination-weighted).

* **Phase** — derived from **(T, P)** and material cohesive scales (Python:
  `hqiv_thermodynamic_phase_from_tp`); not supplied as `solid` / `liquid` inputs.

* **Vev geometric mean** — networked node factors × steric multiplier × derived
  coordination / persistence; chemistry surplus and `η_p` downstream (`DynamicBindingChart`).

Structural theorems only; numerics live in Python witnesses.
-/

namespace Hqiv.QuantumChemistry

open scoped BigOperators
open Finset
open Hqiv
open Hqiv.Physics

noncomputable section

/-- Laboratory / simulation box: temperature and pressure only (phase is derived). -/
structure ThermodynamicEnvironment where
  temperatureK : ℝ
  pressurePa : ℝ

/-- Phase readout from (T, P) + material scales (Python witness). -/
inductive DerivedPhase
  | gas
  | molecularCluster
  | liquid
  | solid
  | supercritical
  deriving DecidableEq, Repr

/-- Typed contact on the curvature network. -/
inductive ContactKind
  | clusterDeficit
  | covalentBond
  | stericRepulsion
  | hyperclosure
  | periodicImage
  deriving DecidableEq, Repr

/-- One fragment node on the network. -/
structure NetworkNode where
  index : ℕ
  Z : ℕ
  massNumber : ℕ
  nuclearShell : ℕ
  valenceSShell : ℕ
  valencePShell : Option ℕ
  comptonShell : ℕ

/-- One contact (edge or node self-term). `j = none` for node-only contacts. -/
structure NetworkContact where
  kind : ContactKind
  i : ℕ
  j : Option ℕ
  contactsAtI : ℕ
  contactsAtJ : ℕ
  undirectedPoints : ℕ

/-- Finite curvature-contact network before eV projection. -/
structure CurvatureContactNetwork where
  derivedPhase : DerivedPhase
  nodes : List NetworkNode
  contacts : List NetworkContact
  comptonTriplet : DynamicComptonTriplet
  /-- Coordination number per node index (liquid/solid weighting). -/
  coordination : ℕ → ℕ

/-- Count peripheral hydrogens when a heavy fragment is present. -/
def peripheralHydrogenCount (nH nHeavy : ℕ) : ℕ :=
  if nHeavy = 0 then 0 else nH

theorem peripheralHHRepulsiveContactPoints_ch4 :
    peripheralHHRepulsiveContactPoints 4 = 4 := by
  native_decide

/-- Steric repulsion multiplier scaffold (parameter-free spine; Python evaluates `G_eff`). -/
noncomputable def stericRepulsionMultiplierScaffold (contactPoints : ℕ) : ℝ :=
  if contactPoints = 0 then 1 else
    1 + (gamma_HQIV * strongChannelFraction) * (contactPoints : ℝ) / 3

/-- Phase coordination factor from derived phase and local coordination. -/
noncomputable def phaseCoordinationFactor (ph : DerivedPhase) (z : ℕ) (zMax : ℕ) : ℝ :=
  match ph with
  | .gas | .molecularCluster => 1
  | .liquid | .solid | .supercritical => (z : ℝ) / (zMax : ℝ)

/-- Network vev uses the same networked cluster factor as `tuftVevFactorNetworkedAtCluster`. -/
noncomputable def nodeNetworkedVevFactor (m A : ℕ) (c : ℝ := 1) : ℝ :=
  tuftVevFactorNetworkedAtCluster m A c

end

end Hqiv.QuantumChemistry
