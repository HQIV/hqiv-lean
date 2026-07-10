import Hqiv.QuantumChemistry.DynamicBindingChart
import Hqiv.QuantumChemistry.AtomElectronicBinding
import Hqiv.QuantumChemistry.CurvatureBondContact
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge
import Hqiv.QuantumComputing.OSHoracle
import Hqiv.Physics.BoundStates

/-!
# Molecular energy bridge: dissociation (eV) ↔ total energy (Hartree) ↔ OSH oracle

Lean counterpart of the classical / quantum-chemistry observable chain used when
comparing HQIV to hardware QPE papers (e.g. H₂ STO-3G ground-state energy in Hartree).

**Inputs (already proved elsewhere):**

* `DynamicBindingChart.dynamicBindingEnergyEv` — chemist dissociation / atomization BE (eV, positive when bound),
* `AtomElectronicBinding.hartreeToEvBridge` — eV ↔ Hartree reporting bridge,
* `BoundStates.expectedGroundEnergyAtShell` — atomic fragment energies (Hartree a.u.),
* `AtomEnergyOSHoracleBridge` + `OSHoracle` — sparse octonion register on fragment shells.

**Outputs (this module):**

* thermochemical identity `E_mol = Σ E_atom − D_e` with consistent units,
* H₂ packaging on `dynamicComptonTripletH2`,
* OSH diagonal energy observable as the sparse phase-estimation target.

Structural theorems only — no numeric fit to experiment, no QEC circuit certificate.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Hqiv.Geometry
open Hqiv.ProteinResearch
open Hqiv.QuantumComputing

noncomputable section

/-! ## Unit bridges -/

/-- Chemist dissociation energy (eV, positive when bound) → Hartree atomic units. -/
def chemistDissociationEvToHartree (dEv : ℝ) : ℝ :=
  dEv / hartreeToEvBridge

/-- Inverse: Hartree binding increment → eV chemist convention. -/
def chemistDissociationHartreeToEv (dHa : ℝ) : ℝ :=
  dHa * hartreeToEvBridge

theorem chemistDissociationEvToHartree_pos (dEv : ℝ) (h : 0 < dEv) :
    0 < chemistDissociationEvToHartree dEv := by
  unfold chemistDissociationEvToHartree
  exact div_pos h (by unfold hartreeToEvBridge; norm_num)

theorem hartreeToEvBridge_ne_zero : hartreeToEvBridge ≠ 0 := by
  unfold hartreeToEvBridge
  norm_num

theorem chemistDissociation_roundtrip_ev (dEv : ℝ) :
    chemistDissociationHartreeToEv (chemistDissociationEvToHartree dEv) = dEv := by
  unfold chemistDissociationHartreeToEv chemistDissociationEvToHartree
  field_simp [hartreeToEvBridge_ne_zero]

theorem chemistDissociation_roundtrip_hartree (dHa : ℝ) :
    chemistDissociationEvToHartree (chemistDissociationHartreeToEv dHa) = dHa := by
  unfold chemistDissociationHartreeToEv chemistDissociationEvToHartree
  field_simp [hartreeToEvBridge_ne_zero]

/-! ## Thermochemical total energy from dissociation -/

/--
Total **electronic** energy of a homonuclear diatomic (Hartree a.u.) from one
fragment atomic energy and chemist dissociation energy (eV).

`E_total = 2 · E_atom − D_e`  (two equivalent fragments).
-/
noncomputable def homonuclearDiatomicTotalEnergyHartree (eAtomHa dEvChemist : ℝ) : ℝ :=
  2 * eAtomHa - chemistDissociationEvToHartree dEvChemist

/-- General two-fragment total from distinct atomic energies. -/
noncomputable def diatomicTotalEnergyHartree (eAtom1Ha eAtom2Ha dEvChemist : ℝ) : ℝ :=
  eAtom1Ha + eAtom2Ha - chemistDissociationEvToHartree dEvChemist

theorem homonuclearDiatomicTotalEnergy_dissociation_sum
    (eAtomHa dEvChemist : ℝ) :
    homonuclearDiatomicTotalEnergyHartree eAtomHa dEvChemist +
        chemistDissociationEvToHartree dEvChemist =
      2 * eAtomHa := by
  unfold homonuclearDiatomicTotalEnergyHartree
  ring

theorem diatomicTotalEnergy_dissociation_sum
    (eAtom1Ha eAtom2Ha dEvChemist : ℝ) :
    diatomicTotalEnergyHartree eAtom1Ha eAtom2Ha dEvChemist +
        chemistDissociationEvToHartree dEvChemist =
      eAtom1Ha + eAtom2Ha := by
  unfold diatomicTotalEnergyHartree
  ring

/-! ## H₂ dynamic binding packaging (canonical chart) -/

/-- H₂ Compton triplet fragment shells for OSH preload (both H at shell `1`). -/
def h2DiatomicFragmentShells : List ℕ :=
  [dynamicComptonTripletH2.m0, dynamicComptonTripletH2.m1]

theorem h2DiatomicFragmentShells_eq_one_one :
    h2DiatomicFragmentShells = [1, 1] := by
  unfold h2DiatomicFragmentShells dynamicComptonTripletH2
  rfl

noncomputable def h2DynamicBindingCoreDimless (ηp surplus vevGeom : ℝ) : ℝ :=
  dynamicBindingCoreDimless ηp surplus vevGeom dynamicComptonTripletH2

theorem h2DynamicBindingCoreDimless_eq
    (ηp surplus vevGeom : ℝ) :
    h2DynamicBindingCoreDimless ηp surplus vevGeom =
      dynamicBindingCoreDimlessAtXi ηp surplus vevGeom (dynamicComptonXiMean dynamicComptonTripletH2) := by
  unfold h2DynamicBindingCoreDimless dynamicBindingCoreDimless dynamicComptonXiMean
  simp [dynamicComptonTripletH2]

/-- H₂ chemist dissociation energy (eV) on the dynamic binding chart. -/
noncomputable def h2DissociationBindingEv (ηp surplus vevGeom : ℝ) : ℝ :=
  dynamicBindingEnergyEv (h2DynamicBindingCoreDimless ηp surplus vevGeom)

theorem h2DissociationBindingEv_eq_core_times_anchor
    (ηp surplus vevGeom : ℝ) :
    h2DissociationBindingEv ηp surplus vevGeom =
      h2DynamicBindingCoreDimless ηp surplus vevGeom * eVPerLambdaUnit_S7HydrogenAnchor := by
  unfold h2DissociationBindingEv dynamicBindingEnergyEv
  rfl

noncomputable def h2CovalentSurplusDimless (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  covalentDimerTwoElectronSurplusDimless cfg

theorem h2CovalentSurplus_eq_diatomicBondSurplus (cfg : NuclearTorusConfig) :
    h2CovalentSurplusDimless cfg = diatomicBondSurplusDimless 2 1 1 cfg := rfl

/--
H₂ total electronic energy (Hartree) from HQIV atomic shell energy + dynamic binding D_e.

Python witness: combine `hqiv_dynamic_binding_chart` H₂ row with
`hqiv_molecular_hamiltonian.example_h2_sto3g_fci` for classical cross-check.
-/
noncomputable def h2TotalEnergyHartreeFromBinding
    (m : ℕ) (μ c : ℝ) (ηp surplus vevGeom : ℝ) : ℝ :=
  homonuclearDiatomicTotalEnergyHartree
    (expectedGroundEnergyAtShell m 1 μ c)
    (h2DissociationBindingEv ηp surplus vevGeom)

/-! ## OSH oracle: sparse quantum energy observable -/

/--
Diagonal molecular energy observable on the OSH sparse register: sum of per-ket
`latticeFullModeEnergy` weights (same indices as `sparseRegisterOfShells`).

This is the **target observable** for sparse phase estimation on the HQIV octonion
carrier — not a full QPE convergence theorem.
-/
noncomputable def oshSparseMolecularEnergyObservable (shells : List ℕ) : ℝ :=
  listLatticeEnergySum shells

theorem oshSparseMolecularEnergyObservable_eq_list_sum (shells : List ℕ) :
    oshSparseMolecularEnergyObservable shells = listLatticeEnergySum shells := rfl

theorem oshH2SparseRegister_norm (L : ℕ) :
    sparseNormSq (sparseRegisterOfShells L h2DiatomicFragmentShells) = 2 := by
  rw [sparseRegisterOfShells_normSq, h2DiatomicFragmentShells_eq_one_one]
  norm_num

theorem oshH2SparseRegister_length (L : ℕ) :
    (sparseRegisterOfShells L h2DiatomicFragmentShells).length = 2 := by
  rw [sparseRegisterOfShells_length, h2DiatomicFragmentShells_eq_one_one]
  decide

/--
Structural QPE target: total Hartree energy from homonuclear binding readout.

Hardware papers report this quantity (within a basis set); HQIV supplies D_e from
`dynamicBindingEnergyEv` and atomic fragments from `expectedGroundEnergyAtShell`.
-/
noncomputable def qpeTargetHomonuclearTotalEnergyHartree
    (eAtomHa dEvChemist : ℝ) : ℝ :=
  homonuclearDiatomicTotalEnergyHartree eAtomHa dEvChemist

theorem qpeTarget_eq_h2Total_when_same_inputs
    (m : ℕ) (μ c : ℝ) (ηp surplus vevGeom : ℝ) :
    qpeTargetHomonuclearTotalEnergyHartree
        (expectedGroundEnergyAtShell m 1 μ c)
        (h2DissociationBindingEv ηp surplus vevGeom) =
      h2TotalEnergyHartreeFromBinding m μ c ηp surplus vevGeom := rfl

/-- OSH gate evolution preserves register norm — prerequisite for coherent phase accumulation. -/
theorem oshGate_preserves_normSq {L : Nat} (G : SparseCertifiedGate L) (f : DiscreteState L) :
    discreteNormSq (G.gate.toEquiv f) = discreteNormSq f :=
  G.preserves_discreteNormSq f

/-! ## Lab outside closure + bond curvature quantification -/

/-- Earth-lab GMTKN assay scale: ``support_ratio / K_mass_chart`` (parameter inputs from outside closure audit). -/
noncomputable def labGmtknBindingScale (kMass supportRatio : ℝ) : ℝ :=
  supportRatio / kMass

/-- Lab-corrected chemist dissociation (eV) from the dilute ρ = 0 chart row. -/
noncomputable def labCorrectedBindingEv (chartEv kMass supportRatio : ℝ) : ℝ :=
  chartEv * labGmtknBindingScale kMass supportRatio

theorem labGmtknBindingScale_identity (chartEv : ℝ) :
    labCorrectedBindingEv chartEv 1 1 = chartEv := by
  unfold labCorrectedBindingEv labGmtknBindingScale
  ring

/-- Intrinsic covalent bond flatness vs saturated unity: ``G_eff(θ/θ₀)``. -/
noncomputable def bondCurvatureFlatnessRatio (θ : ℝ) : ℝ :=
  outsideContactCoupling θ

/-- γ/2 partial stacked-line breathing on tertiary Cα contacts (protein spine). -/
noncomputable def proteinStackedContactBreathingScale (θ : ℝ) : ℝ :=
  1 + gamma_HQIV / 2 * (outsideContactCoupling θ - 1)

/-- GMTKN lab row with bond-corridor relic-ν dress after outside closure. -/
noncomputable def labBindingEvWithBondCorridor
    (chartEv kMass supportRatio ξ φ η : ℝ) : ℝ :=
  labCorrectedBindingEv chartEv kMass supportRatio * bondCorridorNeutrinoDress ξ φ η

theorem labBindingEvWithBondCorridor_eq_chart_when_eta_zero
    (chartEv kMass supportRatio ξ φ : ℝ) :
    labBindingEvWithBondCorridor chartEv kMass supportRatio ξ φ 0 =
      labCorrectedBindingEv chartEv kMass supportRatio := by
  unfold labBindingEvWithBondCorridor
  rw [bondCorridorNeutrinoDress_eq_one_when_eta_zero]
  ring

theorem labBindingEvWithBondCorridor_ge_labCorrected
    (chartEv kMass supportRatio ξ φ η : ℝ)
    (h : 0 ≤ labCorrectedBindingEv chartEv kMass supportRatio) :
    labCorrectedBindingEv chartEv kMass supportRatio ≤
      labBindingEvWithBondCorridor chartEv kMass supportRatio ξ φ η := by
  unfold labBindingEvWithBondCorridor labCorrectedBindingEv labGmtknBindingScale
  calc chartEv * (supportRatio / kMass)
      = chartEv * (supportRatio / kMass) * 1 := by ring
    _ ≤ chartEv * (supportRatio / kMass) * bondCorridorNeutrinoDress ξ φ η :=
        mul_le_mul_of_nonneg_left (bondCorridorNeutrinoDress_ge_one ξ φ η) h

end

end Hqiv.QuantumChemistry
