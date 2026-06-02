import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.MassFromSpinorRho
import Hqiv.Physics.ContinuousXiPath

/-!
# Lapse-normalized mass readouts

This module factors the common pattern behind the existing nucleon lapse
theorems into a small reusable interface:

* a **raw shell mass** is evaluated on the fixed null-lattice readout coordinate
  `m : ℕ`;
* observation divides that raw energy by the HQVM lapse
  `HQVM_lapse Φ (phi_of_shell m) t`;
* continuous readouts should use the `ContinuousXiPath` aliases (`xiOfShell`,
  `phi_xi`) and then return to shells through the chart lemmas below;
* Furey/Clifford data may supply a **state/channel** and a shell-support score,
  but it is not treated as an automatic MeV table;
* hadron readouts stay on the constituent-minus-8×8-network path;
* the KK-style option is recorded as a shell spectral tower, not as a literal
  compactification theorem.
-/

namespace Hqiv.Physics

open BigOperators

/-! ## Generic lapse readout -/

/-- A raw mass assignment over the HQIV shell readout coordinate. -/
abbrev RawShellMass := ℕ → ℝ

/-- HQVM lapse evaluated on the auxiliary field attached to shell `m`. -/
noncomputable def shellLapse (m : ℕ) (Φ t : ℝ) : ℝ :=
  HQVM_lapse Φ (Hqiv.phi_of_shell m) t

/-- Observable mass readout: raw shell energy divided by the HQVM lapse. -/
noncomputable def lapseMassReadout (raw : RawShellMass) (m : ℕ) (Φ t : ℝ) : ℝ :=
  raw m / shellLapse m Φ t

theorem shellLapse_eq_HQVM_lapse (m : ℕ) (Φ t : ℝ) :
    shellLapse m Φ t = HQVM_lapse Φ (Hqiv.phi_of_shell m) t := rfl

theorem shellLapse_eq_one_add_phi_t (m : ℕ) (Φ t : ℝ) :
    shellLapse m Φ t = 1 + Φ + Hqiv.phi_of_shell m * t := rfl

/-- Lapse readout on the continuous ξ chart, routed through `ContinuousXiPath.phi_xi`. -/
noncomputable def shellLapse_xi (ξ : ℝ) (Φ t : ℝ) : ℝ :=
  HQVM_lapse Φ (ContinuousXiPath.phi_xi ξ) t

theorem shellLapse_xi_eq_HQVM_lapse (ξ : ℝ) (Φ t : ℝ) :
    shellLapse_xi ξ Φ t = HQVM_lapse Φ (ContinuousXiPath.phi_xi ξ) t := rfl

theorem shellLapse_xi_chart (m : ℕ) (Φ t : ℝ) :
    shellLapse_xi (xiOfShell m) Φ t = shellLapse m Φ t := by
  unfold shellLapse_xi shellLapse
  rw [ContinuousXiPath.phi_xi_chart]

theorem lapseMassReadout_eq_raw_div_lapse
    (raw : RawShellMass) (m : ℕ) (Φ t : ℝ) :
    lapseMassReadout raw m Φ t = raw m / shellLapse m Φ t := rfl

/-- Constant raw mass family, useful when an existing module already computes a
single lock-in mass and the shell dependence is carried by the chosen readout. -/
noncomputable def constantRawShellMass (M : ℝ) : RawShellMass :=
  fun _ => M

theorem lapseMassReadout_constantRawShellMass
    (M : ℝ) (m : ℕ) (Φ t : ℝ) :
    lapseMassReadout (constantRawShellMass M) m Φ t = M / shellLapse m Φ t := rfl

/-- The generic shell lapse recovers the existing lock-in lapse at `referenceM`. -/
theorem shellLapse_referenceM_eq_lockinHQVMLapse (Φ t : ℝ) :
    shellLapse referenceM Φ t = lockinHQVMLapse Φ t := rfl

/-- The generic readout recovers the existing raw-divided-by-lapse proton pattern. -/
theorem lapseMassReadout_constant_proton_referenceM
    (Φ t : ℝ) :
    lapseMassReadout (constantRawShellMass derivedProtonMass) referenceM Φ t =
      derivedProtonMass_lapseCorrected Φ t := by
  rw [derivedProtonMass_lapseCorrected_eq_raw_div_lapse]
  rfl

/-- The generic readout recovers the existing raw-divided-by-lapse neutron pattern. -/
theorem lapseMassReadout_constant_neutron_referenceM
    (Φ t : ℝ) :
    lapseMassReadout (constantRawShellMass derivedNeutronMass) referenceM Φ t =
      derivedNeutronMass_lapseCorrected Φ t := by
  rw [derivedNeutronMass_lapseCorrected_eq_raw_div_lapse]
  rfl

/-! ## Furey / spinor-ρ state-to-shell bridge -/

/--
A state/channel selector for Furey- or Clifford-shaped bookkeeping.

`score` is deliberately abstract: it can be instantiated by norms, traces,
eigenvalue proxies, or other invariants of `MassFromSpinorRho.manifoldMassOp8`.
The structure only records that the channel chooses a support shell or shell
band; it does not assert a particle mass table.
-/
structure ShellSupportSelector (StateLabel : Type) where
  supportShell : StateLabel → ℕ
  score : StateLabel → ℕ → ℝ

/-- A shell band around the representative support shell. -/
structure ShellSupportBand where
  center : ℕ
  radius : ℕ

/-- Membership in the integer shell band `|m - center| ≤ radius`, written without
subtraction so it stays simple over `ℕ`. -/
def ShellSupportBand.Contains (band : ShellSupportBand) (m : ℕ) : Prop :=
  m ≤ band.center + band.radius ∧ band.center ≤ m + band.radius

/-- Upgrade an exact selector to a zero-radius shell band. -/
def ShellSupportSelector.exactBand {StateLabel : Type}
    (selector : ShellSupportSelector StateLabel) (state : StateLabel) : ShellSupportBand :=
  { center := selector.supportShell state, radius := 0 }

theorem ShellSupportSelector.supportShell_mem_exactBand {StateLabel : Type}
    (selector : ShellSupportSelector StateLabel) (state : StateLabel) :
    (selector.exactBand state).Contains (selector.supportShell state) := by
  constructor <;> simp [ShellSupportSelector.exactBand]

/-- Baseline spinor-ρ score: sum of row-diagonal entries of `manifoldMassOp8 m`.

This is a conservative invariant hook for selecting shells. It is a spectral
proxy, not a MeV normalization.
-/
noncomputable def spinorRhoTraceScore (m : ℕ) : ℝ :=
  ∑ i : Fin 8, MassFromSpinorRho.manifoldMassOp8 m i i

/-- A generic selector can be read as a raw mass family after a calibration map
from score to energy has been supplied. -/
noncomputable def rawShellMassFromSelector {StateLabel : Type}
    (selector : ShellSupportSelector StateLabel) (calibrate : ℝ → ℝ)
    (state : StateLabel) : RawShellMass :=
  fun m => calibrate (selector.score state m)

/-- Lapse readout for a Furey/Clifford channel once a score-to-energy calibration
has been supplied. -/
noncomputable def selectedLapseMassReadout {StateLabel : Type}
    (selector : ShellSupportSelector StateLabel) (calibrate : ℝ → ℝ)
    (state : StateLabel) (Φ t : ℝ) : ℝ :=
  lapseMassReadout (rawShellMassFromSelector selector calibrate state)
    (selector.supportShell state) Φ t

theorem selectedLapseMassReadout_eq_score_at_support {StateLabel : Type}
    (selector : ShellSupportSelector StateLabel) (calibrate : ℝ → ℝ)
    (state : StateLabel) (Φ t : ℝ) :
    selectedLapseMassReadout selector calibrate state Φ t =
      calibrate (selector.score state (selector.supportShell state)) /
        shellLapse (selector.supportShell state) Φ t := rfl

/-! ## Network-only hadron readouts -/

/-- Raw hadron mass from constituent energy minus an 8×8 network binding term. -/
noncomputable def rawHadronMassFromNetwork
    (m : ℕ) (constituentMass : ℝ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  constituentMass - E_bind_from_network m w c

/-- Lapse-normalized hadron mass, still using only constituent mass plus the
8×8 network binding functional. -/
noncomputable def hadronLapseMassReadoutFromNetwork
    (m : ℕ) (constituentMass : ℝ) (w : NetworkWeight) (Φ t : ℝ) (c : ℝ := 1) : ℝ :=
  rawHadronMassFromNetwork m constituentMass w c / shellLapse m Φ t

theorem hadronLapseMassReadoutFromNetwork_eq_raw_div_lapse
    (m : ℕ) (constituentMass : ℝ) (w : NetworkWeight) (Φ t : ℝ) (c : ℝ := 1) :
    hadronLapseMassReadoutFromNetwork m constituentMass w Φ t c =
      rawHadronMassFromNetwork m constituentMass w c / shellLapse m Φ t := rfl

/-- Raw hadron mass from explicit 8×8 composite trace data. -/
noncomputable def rawHadronMassFromCompositeTrace
    (m : ℕ) (constituentMass : ℝ) (diag : So8TraceDiagonal) (ψ : OctonionState)
    (c : ℝ := 1) : ℝ :=
  constituentMass - E_bind_from_composite_trace m diag ψ c

/-- Lapse-normalized hadron mass from explicit 8×8 composite trace data. -/
noncomputable def hadronLapseMassReadoutFromCompositeTrace
    (m : ℕ) (constituentMass : ℝ) (diag : So8TraceDiagonal) (ψ : OctonionState)
    (Φ t : ℝ) (c : ℝ := 1) : ℝ :=
  rawHadronMassFromCompositeTrace m constituentMass diag ψ c / shellLapse m Φ t

theorem rawHadronMassFromCompositeTrace_eq_network
    (m : ℕ) (constituentMass : ℝ) (diag : So8TraceDiagonal) (ψ : OctonionState)
    (c : ℝ := 1) :
    rawHadronMassFromCompositeTrace m constituentMass diag ψ c =
      rawHadronMassFromNetwork m constituentMass
        (networkWeightFromCompositeTrace diag ψ) c := rfl

theorem nucleonSharedBinding_uses_composite_trace_only :
    nucleonSharedBinding_MeV =
      E_bind_from_composite_trace referenceM nucleonTraceDiagonal nucleonTraceState := rfl

theorem proton_raw_hadron_mass_from_composite_trace :
    rawHadronMassFromCompositeTrace referenceM protonConstituentEnergy
        nucleonTraceDiagonal nucleonTraceState =
      derivedProtonMass := rfl

theorem neutron_raw_hadron_mass_from_composite_trace :
    rawHadronMassFromCompositeTrace referenceM neutronConstituentEnergy
        nucleonTraceDiagonal nucleonTraceState =
      derivedNeutronMass := rfl

/-- The proton anchor is a target readout condition, not an input to the generic
network/lapse formula. -/
def ProtonAnchorCondition (Φ t : ℝ) : Prop :=
  shellLapse referenceM Φ t * protonAnchorMass_MeV = derivedProtonMass

theorem proton_anchor_condition_discharge
    (Φ t : ℝ) (hanchor : ProtonAnchorCondition Φ t)
    (hlapseNz : shellLapse referenceM Φ t ≠ 0) :
    lapseMassReadout (constantRawShellMass derivedProtonMass) referenceM Φ t =
      protonAnchorMass_MeV := by
  unfold ProtonAnchorCondition at hanchor
  rw [lapseMassReadout_constantRawShellMass, ← hanchor]
  field_simp [hlapseNz]

/-! ## KK-style shell tower, without compactification -/

/--
A KK-style HQIV tower: shells are spectral levels of the null-lattice readout,
with masses obtained by the same lapse rule. This is intentionally not a
compactification or extra-dimension theorem.
-/
structure ShellSpectralTower where
  levelShell : ℕ → ℕ
  rawLevelMass : ℕ → ℝ

/-- Lapse readout of one level in an HQIV shell spectral tower. -/
noncomputable def ShellSpectralTower.levelMassReadout
    (tower : ShellSpectralTower) (level : ℕ) (Φ t : ℝ) : ℝ :=
  tower.rawLevelMass level / shellLapse (tower.levelShell level) Φ t

/-- The tower readout is definitionally the same `raw / shellLapse` rule. -/
theorem ShellSpectralTower.levelMassReadout_eq_raw_div_lapse
    (tower : ShellSpectralTower) (level : ℕ) (Φ t : ℝ) :
    tower.levelMassReadout level Φ t =
      tower.rawLevelMass level / shellLapse (tower.levelShell level) Φ t := rfl

/-- A shell tower is HQIV-native when its levels are only shell readouts. This
empty predicate is a naming guard against reading the tower as a compactified
spatial dimension. -/
def ShellSpectralTower.HQIVNative (_tower : ShellSpectralTower) : Prop := True

theorem ShellSpectralTower.hqivNative_no_compactification_claim
    (tower : ShellSpectralTower) :
    tower.HQIVNative := trivial

end Hqiv.Physics
