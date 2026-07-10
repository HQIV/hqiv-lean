import Hqiv.Physics.DynamicCentreGeometry
import Hqiv.QuantumChemistry.FoundationChemistry

/-!
# Peptide backbone geometry (derived slots, no tabulated Å)

Python mirrors:
  • ``hqiv_lab/derived_bond_geometry.py`` — diamond-node Θ and bond lengths
  • ``hqiv_lab/peptide_geometry.py`` — layer Bravais + Cα contact scales
  • ``hqiv_lab/miniprotein_backbone.py`` — Ramachandran + centre angles

Bond lengths use the diamond-node spine (PROtien / pyhqiv fallback); centre angles
reuse ``DynamicCentreGeometry`` (VSEPR + strong-channel bent dress).
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Real

/-- Diamond-node scale exponent (null-lattice monogamy dress on Θ₀). -/
noncomputable def diamondNodeAlpha : ℝ := 0.91

noncomputable def diamondNodeTheta0 : ℝ :=
  1.53 * (6 : ℝ) ^ diamondNodeAlpha * (2 : ℝ) ^ ((1 : ℝ) / 3)

noncomputable def diamondThetaLocal (z coordination : ℕ) : ℝ :=
  if z = 0 ∨ coordination = 0 then 0
  else diamondNodeTheta0 * (z : ℝ) ^ (-diamondNodeAlpha) / (coordination : ℝ) ^ ((1 : ℝ) / 3)

noncomputable def bondLengthAngstromMinTheta (z_i z_j coord_i coord_j : ℕ) (monogamy : ℝ) : ℝ :=
  min (diamondThetaLocal z_i coord_i) (diamondThetaLocal z_j coord_j) * monogamy

/-- N–Cα peptide bond (N sp², Cα sp³). -/
noncomputable def peptideBondLengthN_CA : ℝ := bondLengthAngstromMinTheta 7 6 2 4 1

/-- Cα–C peptide bond (both sp³). -/
noncomputable def peptideBondLengthCA_C : ℝ := bondLengthAngstromMinTheta 6 6 4 4 1

/-- C–N peptide bond (both sp²). -/
noncomputable def peptideBondLengthC_N : ℝ := bondLengthAngstromMinTheta 6 7 2 2 1

/-- C=O partial-double slot: C–O single · (1 − strongChannelFraction/4). -/
noncomputable def peptideBondLengthC_O : ℝ :=
  bondLengthAngstromMinTheta 6 8 2 1 1 * (1 - strongChannelFraction / 4)

/-- Bound-system growth coordinate: partial chain occupancy clamped to ``[0,1]``. -/
noncomputable def boundSystemParticipation (nResidues boundCount : ℕ) : ℝ :=
  if nResidues = 0 then 1
  else ((min (max boundCount 1) nResidues : ℕ) : ℝ) / (nResidues : ℝ)

/-- Spectator σ dress grows as the peptide system coagulates. -/
noncomputable def peptideSigmaDressAtBound (nResidues boundCount : ℕ) : ℝ :=
  1 + gamma_HQIV / 2 * boundSystemParticipation nResidues boundCount

/-- Cα sp³ exocyclic dress grows with the bound-system participation. -/
noncomputable def peptideCA_CSp3DressAtBound (nResidues boundCount : ℕ) : ℝ :=
  Real.sqrt (1 + strongChannelFraction / 4 * boundSystemParticipation nResidues boundCount)

/-- Dynamic N–Cα peptide bond at a partial bound-chain stage. -/
noncomputable def dynamicPeptideBondLengthN_CA (nResidues boundCount : ℕ) : ℝ :=
  bondLengthAngstromMinTheta 7 6 2 4 (peptideSigmaDressAtBound nResidues boundCount)

/-- Dynamic Cα–C peptide bond at a partial bound-chain stage. -/
noncomputable def dynamicPeptideBondLengthCA_C (nResidues boundCount : ℕ) : ℝ :=
  bondLengthAngstromMinTheta 6 6 4 4
    (peptideSigmaDressAtBound nResidues boundCount *
      peptideCA_CSp3DressAtBound nResidues boundCount)

/-- N–Cα–C angle at Cα (sp³ tetrahedral domain). -/
noncomputable def peptideAngleN_CA_C : ℝ := dynamicCentreAngleRad 6 4

/-- Cα–C–N angle: π − bent(C,3)/2. -/
noncomputable def peptideAngleCA_C_N : ℝ :=
  Real.pi - dynamicCentreAngleRad 6 3 / 2

/-- C–N–Cα angle at peptide N (sp² + lone pair). -/
noncomputable def peptideAngleC_N_CA : ℝ := dynamicCentreAngleRad 7 3

/-- Bundled derived peptide backbone geometry (Python ``PeptideBondGeometry``). -/
structure PeptideBondGeometry where
  n_ca : ℝ
  ca_c : ℝ
  c_n : ℝ
  c_o : ℝ
  n_ca_c : ℝ
  ca_c_n : ℝ
  c_n_ca : ℝ

noncomputable def hqivPeptideBondGeometry : PeptideBondGeometry where
  n_ca := peptideBondLengthN_CA
  ca_c := peptideBondLengthCA_C
  c_n := peptideBondLengthC_N
  c_o := peptideBondLengthC_O
  n_ca_c := peptideAngleN_CA_C
  ca_c_n := peptideAngleCA_C_N
  c_n_ca := peptideAngleC_N_CA

/-- Bundled dynamic peptide geometry at a partial bound-chain stage. -/
noncomputable def dynamicPeptideBondGeometry (nResidues boundCount : ℕ) : PeptideBondGeometry where
  n_ca := dynamicPeptideBondLengthN_CA nResidues boundCount
  ca_c := dynamicPeptideBondLengthCA_C nResidues boundCount
  c_n := peptideBondLengthC_N
  c_o := peptideBondLengthC_O
  n_ca_c := peptideAngleN_CA_C
  ca_c_n := peptideAngleCA_C_N
  c_n_ca := peptideAngleC_N_CA

/-- Equilibrated full-bound geometry: the growth endpoint for an ``n``-residue chain. -/
noncomputable def fullBoundPeptideBondGeometry (nResidues : ℕ) : PeptideBondGeometry :=
  dynamicPeptideBondGeometry nResidues nResidues

/-- Mean backbone bond length along N–Cα–C–N path. -/
noncomputable def peptideBackboneMeanBond (g : PeptideBondGeometry) : ℝ :=
  (g.n_ca + g.ca_c + g.c_n) / 3

theorem peptide_backbone_mean_bond_pos (g : PeptideBondGeometry)
    (hn : 0 < g.n_ca) (hc : 0 < g.ca_c) (hcn : 0 < g.c_n) :
    0 < peptideBackboneMeanBond g := by
  unfold peptideBackboneMeanBond
  have h3 : 0 < (3 : ℝ) := by norm_num
  apply div_pos
  · nlinarith
  · exact h3

theorem boundSystemParticipation_full {n : ℕ} (hn : 0 < n) :
    boundSystemParticipation n n = 1 := by
  unfold boundSystemParticipation
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hmax : max n 1 = n := max_eq_left hn
  simp [hn0, hmax]

theorem peptideSigmaDressAtBound_full {n : ℕ} (hn : 0 < n) :
    peptideSigmaDressAtBound n n = 1 + gamma_HQIV / 2 := by
  unfold peptideSigmaDressAtBound
  rw [boundSystemParticipation_full hn]
  ring

theorem peptideCA_CSp3DressAtBound_full {n : ℕ} (hn : 0 < n) :
    peptideCA_CSp3DressAtBound n n =
      Real.sqrt (1 + strongChannelFraction / 4) := by
  unfold peptideCA_CSp3DressAtBound
  rw [boundSystemParticipation_full hn]
  ring_nf

theorem dynamicPeptideBondLengthN_CA_full {n : ℕ} (hn : 0 < n) :
    dynamicPeptideBondLengthN_CA n n =
      bondLengthAngstromMinTheta 7 6 2 4 (1 + gamma_HQIV / 2) := by
  unfold dynamicPeptideBondLengthN_CA
  rw [peptideSigmaDressAtBound_full hn]

theorem dynamicPeptideBondLengthCA_C_full {n : ℕ} (hn : 0 < n) :
    dynamicPeptideBondLengthCA_C n n =
      bondLengthAngstromMinTheta 6 6 4 4
        ((1 + gamma_HQIV / 2) * Real.sqrt (1 + strongChannelFraction / 4)) := by
  unfold dynamicPeptideBondLengthCA_C
  rw [peptideSigmaDressAtBound_full hn, peptideCA_CSp3DressAtBound_full hn]

theorem fullBoundPeptideBondGeometry_n_ca {n : ℕ} (hn : 0 < n) :
    (fullBoundPeptideBondGeometry n).n_ca =
      bondLengthAngstromMinTheta 7 6 2 4 (1 + gamma_HQIV / 2) := by
  unfold fullBoundPeptideBondGeometry dynamicPeptideBondGeometry
  exact dynamicPeptideBondLengthN_CA_full hn

theorem fullBoundPeptideBondGeometry_ca_c {n : ℕ} (hn : 0 < n) :
    (fullBoundPeptideBondGeometry n).ca_c =
      bondLengthAngstromMinTheta 6 6 4 4
        ((1 + gamma_HQIV / 2) * Real.sqrt (1 + strongChannelFraction / 4)) := by
  unfold fullBoundPeptideBondGeometry dynamicPeptideBondGeometry
  exact dynamicPeptideBondLengthCA_C_full hn

theorem centre_lone_pair_count_c_alpha_sp3 : centreLonePairCount 6 4 = 0 := by decide

theorem steric_domain_count_c_alpha_sp3 : stericDomainCount 4 (centreLonePairCount 6 4) = 4 := by decide

theorem peptide_angle_n_ca_c_eq_dynamic_centre :
    peptideAngleN_CA_C = dynamicCentreAngleRad 6 4 := rfl

theorem peptide_angle_c_n_ca_eq_dynamic_centre :
    peptideAngleC_N_CA = dynamicCentreAngleRad 7 3 := rfl

theorem peptide_angle_ca_c_n_uses_bent_dress :
    peptideAngleCA_C_N = Real.pi - dynamicCentreAngleRad 6 3 / 2 := rfl

theorem dynamicCentreAngleRad_c_alpha_sp3_eq_bent :
    dynamicCentreAngleRad 6 4 =
      centreAngleBentDress (centreAngleRadFromDomains 4) 0 4 := by
  dsimp [dynamicCentreAngleRad, centreLonePairCount, stericDomainCount, period2ValenceElectronCount,
    centreAngleBentDress, centreAngleRadFromDomains]
  norm_num

theorem dynamicCentreAngleRad_c_alpha_sp3_eq_tetrahedral :
    dynamicCentreAngleRad 6 4 = centreAngleRadFromDomains 4 := by
  rw [dynamicCentreAngleRad_c_alpha_sp3_eq_bent]
  dsimp [centreAngleBentDress, centreAngleRadFromDomains]
  norm_num

/-- Peptide backbone diameter factor ``2(1 + α + γ/8)`` (sheet layer). -/
noncomputable def peptideBackboneDiameterFactor : ℝ := 2 * (1 + alpha + gamma_HQIV / 8)

/-- Peptide layer open cell ``1 + γ/8`` (Foundation ``peptideLayerOpenCell``). -/
noncomputable def peptideBackboneOpenFactor : ℝ := peptideLayerOpenCell

/-- Sheet short-axis closure ``(1+γ/8)/(1+α/4) / (1 + γ/(n²+2))``. -/
noncomputable def peptideSheetShortAxisFactor (nBackbone : ℕ) : ℝ :=
  let n := max nBackbone 1
  let closure := 1 + gamma_HQIV / ((n : ℝ) ^ 2 + 2)
  (1 + gamma_HQIV / 8) / (1 + alpha / 4) / closure

/-- Exocyclic / inter-strand dress ``√(1 + (4/8)·n/4)``. -/
noncomputable def peptideBackboneExocyclicDressFactor (nInter : ℕ) : ℝ :=
  Real.sqrt (1 + strongChannelFraction * (max nInter 1 : ℝ) / 4)

/-- Mean backbone bond × diameter × open × dress (relative to supplied mean bond [Å]). -/
noncomputable def peptideBackboneContactDistance (meanBond : ℝ) (nInter : ℕ) : ℝ :=
  meanBond * peptideBackboneDiameterFactor * peptideBackboneOpenFactor *
    peptideBackboneExocyclicDressFactor (max nInter 1)

theorem peptide_backbone_diameter_factor_rational :
    peptideBackboneDiameterFactor = 33 / 10 := by
  rw [peptideBackboneDiameterFactor, alpha_eq_3_5, gamma_eq_2_5]
  norm_num

theorem peptide_backbone_open_factor_eq_layer_cell :
    peptideBackboneOpenFactor = peptideLayerOpenCell := rfl

theorem peptide_backbone_open_factor_rational :
    peptideBackboneOpenFactor = 21 / 20 := by
  rw [peptideBackboneOpenFactor, peptideLayerOpenCell, gamma_eq_2_5]
  norm_num

theorem peptide_exocyclic_dress_factor_four_contacts :
    peptideBackboneExocyclicDressFactor 4 = Real.sqrt (3 / 2) := by
  rw [peptideBackboneExocyclicDressFactor, strongChannelFraction_eq_four_eighths]
  norm_num

/-- Helix Cα_i–Cα_{i+3} scale relative to adjacent Cα step. -/
noncomputable def helixCaIi3DistanceScale : ℝ := 1 + alpha + gamma_HQIV / 4

/-- Helix Cα_i–Cα_{i+4} one-turn scale relative to i+3 slot. -/
noncomputable def helixCaIi4DistanceScale : ℝ := 1 + gamma_HQIV / 8

/-- In-strand β Cα_i–Cα_{i+2} scale relative to adjacent Cα step. -/
noncomputable def sheetCaIi2DistanceScale : ℝ := 1 + gamma_HQIV / 4

theorem helix_ca_i_i3_scale_rational :
    helixCaIi3DistanceScale = 17 / 10 := by
  rw [helixCaIi3DistanceScale, alpha_eq_3_5, gamma_eq_2_5]
  norm_num

theorem helix_ca_i_i4_scale_rational :
    helixCaIi4DistanceScale = 21 / 20 := by
  rw [helixCaIi4DistanceScale, gamma_eq_2_5]
  norm_num

theorem sheet_ca_i_i2_scale_rational :
    sheetCaIi2DistanceScale = 11 / 10 := by
  rw [sheetCaIi2DistanceScale, gamma_eq_2_5]
  norm_num

theorem carbonyl_bond_length_slot :
    peptideBondLengthC_O =
      bondLengthAngstromMinTheta 6 8 2 1 1 * (7 / 8) := by
  unfold peptideBondLengthC_O bondLengthAngstromMinTheta
  rw [strongChannelFraction_eq_four_eighths]
  ring

theorem carbonyl_bond_length_factor_lt_one : (7 : ℝ) / 8 < 1 := by norm_num

theorem carbonyl_bond_length_scaled (r : ℝ) (hr : 0 < r) :
    r * (7 / 8) < r := by nlinarith [carbonyl_bond_length_factor_lt_one, hr]

end Hqiv.QuantumChemistry
