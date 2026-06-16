import Hqiv.ProteinResearch.MiniproteinSecondaryStructure

/-!
# Tertiary Cα contact counting (sequence-derived graph)

Python mirror: ``hqiv_lab/miniprotein_contacts.build_tertiary_contact_graph``.

Counts mirror the Python graph builder; Trp-cage totals are pinned by ``native_decide``.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QuantumChemistry

def helixPairAt (ss : List SecondaryStructure) (i sep : ℕ) : Bool :=
  match ss[i]?, ss[i + sep]? with
  | some h1, some h2 => h1 == .helix && h2 == .helix
  | _, _ => false

def countHelixContacts (ss : List SecondaryStructure) (sep : ℕ) : ℕ :=
  (List.range ss.length).filter (fun i => helixPairAt ss i sep) |>.length

def sheetPairAt (ss : List SecondaryStructure) (i : ℕ) : Bool :=
  match ss[i]?, ss[i + 2]? with
  | some h1, some h2 => h1 == .strand && h2 == .strand
  | _, _ => false

def countSheetI2Contacts (ss : List SecondaryStructure) : ℕ :=
  (List.range ss.length).filter (fun i => sheetPairAt ss i) |>.length

def helixSheetRegisterPair (ss : List SecondaryStructure) (si hi minSep maxSep : ℕ) : Bool :=
  match ss[si]?, ss[hi]? with
  | some .strand, some .helix =>
    minSep ≤ hi - si ∧ hi - si ≤ maxSep
  | _, _ => false

def countHelixSheetContacts (ss : List SecondaryStructure) (minSep maxSep : ℕ) : ℕ :=
  let sheetTail := ss.zipIdx.filter (fun p => p.1 == .strand) |>.map Prod.snd
  let helixHead := ss.zipIdx.filter (fun p => p.1 == .helix) |>.map Prod.snd
  let lastSheet := sheetTail.reverse.take 2 |>.reverse
  let firstHelix := helixHead.take 3
  Id.run do
    let mut total := 0
    for si in lastSheet do
      for hi in firstHelix do
        if helixSheetRegisterPair ss si hi minSep maxSep then
          total := total + 1
    return total

def hydrophobicWindow (n : ℕ) : ℕ :=
  max (n / 2) 5

def countHydrophobicContacts (seq : String) (minSep : ℕ) : ℕ :=
  let chars := seq.toList
  let n := chars.length
  let hi := hydrophobicWindow n
  Id.run do
    let mut total := 0
    for i in [0:n] do
      match chars[i]? with
      | none => continue
      | some ci =>
        if !isHydrophobicResidue ci then continue
        for j in [i + minSep : min (i + hi + 1) n] do
          match chars[j]? with
          | none => continue
          | some cj =>
            if isHydrophobicResidue cj then
              total := total + 1
    return total

def countTerminusContacts (n : ℕ) (includeTerminus : Bool) : ℕ :=
  if includeTerminus && n ≥ tertiaryTerminusMinResidues then 1 else 0

def countTertiaryContacts (seq : String) (ss : List SecondaryStructure) : ℕ :=
  countHelixContacts ss 3 +
    countHelixContacts ss 4 +
    countSheetI2Contacts ss +
    countHelixSheetContacts ss 3 5 +
    countHydrophobicContacts seq hydrophobicMinSeparation +
    countTerminusContacts ss.length true

theorem trp_cage_helix_i3_contacts :
    countHelixContacts trpCageSecondaryStructure 3 = 8 := by native_decide

theorem trp_cage_helix_i4_contacts :
    countHelixContacts trpCageSecondaryStructure 4 = 7 := by native_decide

theorem trp_cage_sheet_i2_contacts :
    countSheetI2Contacts trpCageSecondaryStructure = 1 := by native_decide

theorem trp_cage_helix_sheet_contacts :
    countHelixSheetContacts trpCageSecondaryStructure 3 5 = 5 := by native_decide

theorem trp_cage_hydrophobic_contacts :
    countHydrophobicContacts trpCageSequence hydrophobicMinSeparation = 3 := by native_decide

theorem trp_cage_terminus_contact :
    countTerminusContacts trpCageSequence.length true = 1 := by decide

theorem trp_cage_total_tertiary_contacts :
    countTertiaryContacts trpCageSequence trpCageSecondaryStructure = 25 := by native_decide

theorem protein_scaffold_contact_count_ge_three (n : ℕ) (h : 3 ≤ n) :
    proteinScaffoldContactCount n = 2 * n := by
  unfold proteinScaffoldContactCount
  have h1 : ¬ n ≤ 1 := by omega
  have h2 : ¬ n = 2 := by omega
  simp [h1, h2]

theorem protein_scaffold_contact_count_monotone (n : ℕ) (h : 2 ≤ n) :
    proteinScaffoldContactCount n ≤ 2 * n := by
  unfold proteinScaffoldContactCount
  by_cases hn1 : n ≤ 1
  · omega
  by_cases hn2 : n = 2
  · subst hn2; norm_num
  · simp [hn1, hn2]

/-- Derived helix i+3 target distance from adjacent Cα step. -/
noncomputable def helixCaIi3Distance (caStep : ℝ) : ℝ :=
  caStep * helixCaIi3DistanceScale

/-- Derived helix i+4 target from i+3 slot. -/
noncomputable def helixCaIi4Distance (caStep i3 : ℝ) : ℝ :=
  i3 * helixCaIi4DistanceScale

/-- Derived sheet i+2 target from adjacent Cα step. -/
noncomputable def sheetCaIi2Distance (caStep : ℝ) : ℝ :=
  caStep * sheetCaIi2DistanceScale

theorem helix_ca_i_i3_distance_scale (caStep : ℝ) :
    helixCaIi3Distance caStep = caStep * (17 / 10) := by
  unfold helixCaIi3Distance
  rw [helix_ca_i_i3_scale_rational]

theorem sheet_ca_i_i2_distance_scale (caStep : ℝ) :
    sheetCaIi2Distance caStep = caStep * (11 / 10) := by
  unfold sheetCaIi2Distance
  rw [sheet_ca_i_i2_scale_rational]

end Hqiv.ProteinResearch
