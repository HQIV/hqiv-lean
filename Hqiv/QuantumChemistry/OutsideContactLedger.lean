import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.QuantumChemistry.MacroRicciFlowDynamics
import Hqiv.QuantumChemistry.SecondOrderEffects
import HqivSpine.Chemistry.Spectroscopy
import HqivSpine.Physics.GeneratorDependentCoupling

/-!
# Outside-contact G_eff ledger (multi-channel bookkeeping)

The live chemistry chart previously folded several outside environments into a
single `outsideGeffSurplus` scalar.  Condensed-phase / interface work needs those
channels kept separate:

* **grav** — Ricci / gravitational outside support (`outsideGravityGeffModulator`);
* **em** — electric / curvature-dielectric concentration (`curvatureConcentrationWeight`);
* **bulk** — medium density ρ (`scaleOutsideCouplingForMediumDensity` on a bulk factor);
* **localDefect** — nucleation / wall / interface defect (`localCurvatureDefectExcess`);
* **contact** — bond-summed outside `G_eff` participation (`outsideGeffSurplus`).

The product `M_out = grav · em · bulk · localDefect · contact` is the ledger dress.
At dilute-gas assay (`φ = 0`, dielectric `n = 1`, `ρ_bulk = 0`, `δ_coord = 0`) the
first four channels are exactly `1`, so the chart recovers the previous
`outsideGeffSurplus`-only behaviour with no fitted coefficient.

Foundation anchors: `α = 3/5`, `γ = 2/5`, `strongChannelFraction = 4/8`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open HqivSpine.Chemistry
open HqivSpine.Physics.GeneratorDependentCoupling

noncomputable section

/-- Electric / dielectric outside channel:
`1 + (4/8)·curvatureConcentrationWeight n`.  At `n = 1` (no contrast) this is `1`. -/
def outsideEmChannel (nDielectric : ℝ) : ℝ :=
  1 + strongChannelFraction * Spectroscopy.curvatureConcentrationWeight nDielectric

theorem outsideEmChannel_unit :
    outsideEmChannel 1 = 1 := by
  unfold outsideEmChannel
  rw [Spectroscopy.curvatureConcentrationWeight_unit]
  ring

/-- Bulk medium-density channel: interpolates a bulk target by `ρ_bulk`.
Uses the proved `scaleOutsideCouplingForMediumDensity` (ρ=0 → 1). -/
def outsideBulkChannel (bulkTarget ρBulk : ℝ) : ℝ :=
  scaleOutsideCouplingForMediumDensity bulkTarget ρBulk

theorem outsideBulkChannel_dilute (bulkTarget : ℝ) :
    outsideBulkChannel bulkTarget 0 = 1 :=
  scaleOutsideCouplingForMediumDensity_unity bulkTarget

/-- Local nucleation / wall / interface channel:
`1 + localCurvatureDefectExcess δ`.  Zero coordination excess → `1`. -/
def outsideLocalDefectChannel (coordinationExcess : ℝ) : ℝ :=
  1 + localCurvatureDefectExcess coordinationExcess

theorem outsideLocalDefectChannel_zero :
    outsideLocalDefectChannel 0 = 1 := by
  unfold outsideLocalDefectChannel localCurvatureDefectExcess
  simp

/-- Bond-contact participation channel (legacy `outsideGeffSurplus`). -/
abbrev outsideContactChannel := outsideGeffSurplus

/-- Multi-channel outside-contact ledger. -/
structure OutsideContactLedger where
  /-- Ricci / gravitational outside support. -/
  grav : ℝ := 1
  /-- Electric / dielectric concentration channel. -/
  em : ℝ := 1
  /-- Bulk medium-density channel. -/
  bulk : ℝ := 1
  /-- Local nucleation / wall / interface channel. -/
  localDefect : ℝ := 1
  /-- Bond-summed contact `G_eff` participation. -/
  contact : ℝ := 1

/-- Product dress from the ledger. -/
def outsideContactLedgerDress (L : OutsideContactLedger) : ℝ :=
  L.grav * L.em * L.bulk * L.localDefect * L.contact

/-- Dilute-gas ledger: environment channels at identity; contact carries the bond sum. -/
def diluteGasOutsideContactLedger (geffSum surplus : ℝ) : OutsideContactLedger where
  grav := 1
  em := outsideEmChannel 1
  bulk := outsideBulkChannel 1 0
  localDefect := outsideLocalDefectChannel 0
  contact := outsideContactChannel geffSum surplus

theorem diluteGasOutsideContactLedger_em :
    (diluteGasOutsideContactLedger 0 1).em = 1 := by
  unfold diluteGasOutsideContactLedger
  exact outsideEmChannel_unit

theorem diluteGasOutsideContactLedger_bulk :
    (diluteGasOutsideContactLedger 0 1).bulk = 1 := by
  unfold diluteGasOutsideContactLedger
  exact outsideBulkChannel_dilute 1

theorem diluteGasOutsideContactLedger_local :
    (diluteGasOutsideContactLedger 0 1).localDefect = 1 := by
  unfold diluteGasOutsideContactLedger
  exact outsideLocalDefectChannel_zero

/-- Dilute-gas dress equals the legacy bond-contact surplus factor. -/
theorem diluteGasOutsideContactLedger_dress
    (geffSum surplus : ℝ) :
    outsideContactLedgerDress (diluteGasOutsideContactLedger geffSum surplus) =
      outsideGeffSurplus geffSum surplus := by
  unfold outsideContactLedgerDress diluteGasOutsideContactLedger
  rw [outsideEmChannel_unit, outsideBulkChannel_dilute, outsideLocalDefectChannel_zero]
  ring

/-- Build a full ledger from explicit channel inputs (n-body / condensed ready). -/
def outsideContactLedgerFromChannels
    (phiEpsilon nDielectric bulkTarget ρBulk coordinationExcess geffSum surplus : ℝ) :
    OutsideContactLedger where
  grav := outsideGravityGeffModulator ⟨phiEpsilon⟩
  em := outsideEmChannel nDielectric
  bulk := outsideBulkChannel bulkTarget ρBulk
  localDefect := outsideLocalDefectChannel coordinationExcess
  contact := outsideContactChannel geffSum surplus

/-- Promoted n-body second-order factor with multi-channel outside ledger. -/
def nBodyPromotedSecondOrderFactorLedger
    (L : OutsideContactLedger) (eta g : ℝ) : ℝ :=
  outsideContactLedgerDress L * preferredAxisPlaneLocalDress eta g

/-- Dilute-gas promoted factor recovers the previous `outsideGeff × preferredAxis` form. -/
theorem nBodyPromotedSecondOrderFactorLedger_dilute
    (geffSum surplus eta g : ℝ) :
    nBodyPromotedSecondOrderFactorLedger
        (diluteGasOutsideContactLedger geffSum surplus) eta g =
      outsideGeffSurplus geffSum surplus * preferredAxisPlaneLocalDress eta g := by
  unfold nBodyPromotedSecondOrderFactorLedger
  rw [diluteGasOutsideContactLedger_dress]

end

end Hqiv.QuantumChemistry
