import Hqiv.Physics.FanoOmaxwellSpectrum
import Hqiv.Physics.FanoLineRapidityChoice
import Hqiv.Physics.QuarkOMaxwellBridge

namespace Hqiv.Physics

open Hqiv

/-!
# Unified Fano vertex / line / O-Maxwell selectors (all seven vertices)

The SM-facing narrative in this repo uses:

- **one EM / charged-lepton axis** (vertex `0`, matrix index `1` in the octonion slotting),
- **three up-type quark directions** (vertices `1..3`),
- **three down-type quark directions** (vertices `4..6`).

The Higgs / colour-into-`e₇` story uses the **Fano vertex `6`**, the same as the third down-type
corner of the up/down `Fin 3` bookkeeping (`HiggsPhaseFiberScaffold` / phase-lift on the
`e₁`–`e₇` Fano line).

`FanoVertexLineSelectors` packages the same **three** combinatorial hooks used everywhere else:

* canonical tag line: `FanoLine.ofTag v` (lowest incident standard index),
* shell/triality-fibrated line: `fanoLineFromVertexShell v m` (`FanoLineRapidityChoice`),
* an `FanoOmaxwellSpectralMode` for detuning: built from either line, same `shell` readout as in
  `FanoOmaxwellSpectrum` / `spectralFanoRindler1Jet` (per-line 1-jet is line-independent in the
  current **proved** affine scaffold: `spectralFanoRindler1Jet_eq_rindler`).

All **mass** ratios that already use `detunedShellSurface` / `geometricResonanceStep` keep using
`ResonanceAxis.anchorShell` in the quark and lepton modules; this file does **not** introduce new
MeV numbers—it only unifies the **Fano** bookkeeping so every sector can cite the same line/mode
API.
-/

section named_vertices

/-- Fano `0` — EM / charged lepton; same tag as `canonicalSpectralTag` in `FanoDetuningFirstOrder`. -/
def emLeptonFanoVertex : FanoVertex := ⟨0, by decide⟩

/-- Fano `1,2,3` — up-type quark colours (families) in `FanoResonance` (`upQuarkAxis`). -/
def upTypeFanoVertex (g : Fin 3) : FanoVertex :=
  ⟨g.val + 1, by have := g.2; omega⟩

/-- Fano `4,5,6` — down-type quark colours. -/
def downTypeFanoVertex (g : Fin 3) : FanoVertex :=
  ⟨g.val + 4, by have := g.2; omega⟩

/-- Fano `6` — down-type `g = 2` and the same vertex used for the Higgs / `e₇` Fano line scaffold. -/
def scalarHiggsFanoVertex : FanoVertex := ⟨6, by decide⟩

theorem upTypeFanoVertex_edge (g : Fin 3) (hg : g.val = 0) : upTypeFanoVertex g = (⟨1, by decide⟩ : FanoVertex) := by
  ext
  simp [upTypeFanoVertex, hg]

theorem downTypeFanoVertex_edge (g : Fin 3) (hg : g.val = 0) : downTypeFanoVertex g = (⟨4, by decide⟩ : FanoVertex) := by
  ext
  simp [downTypeFanoVertex, hg]

theorem upTypeFanoVertex_last : upTypeFanoVertex ⟨2, by decide⟩ = (⟨3, by decide⟩ : FanoVertex) := by
  native_decide

theorem downTypeFanoVertex_last : downTypeFanoVertex ⟨2, by decide⟩ = scalarHiggsFanoVertex := by
  native_decide

/-- List of the seven Fano plane vertices in label order. -/
def fanoVerticesInOrder : List FanoVertex :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]

theorem fanoVerticesInOrder_length : fanoVerticesInOrder.length = 7 := rfl

end named_vertices

section axis_vertices

theorem leptonAxis_vertex (anchorShell : ℕ) : (leptonAxis anchorShell).vertex = emLeptonFanoVertex := by
  simp [leptonAxis, emLeptonFanoVertex]

theorem upQuarkAxis_vertex (g : Fin 3) (anchorShell : ℕ) :
    (upQuarkAxis g anchorShell).vertex = upTypeFanoVertex g := by
  simp [upQuarkAxis, upTypeFanoVertex]

theorem downQuarkAxis_vertex (g : Fin 3) (anchorShell : ℕ) :
    (downQuarkAxis g anchorShell).vertex = downTypeFanoVertex g := by
  simp [downQuarkAxis, downTypeFanoVertex]

end axis_vertices

section quark_resonance_bridge

theorem upTypeFanoVertex_gen0_eq_upResonanceAxis :
    upTypeFanoVertex ⟨0, by decide⟩ = upResonanceAxis.vertex := by
  rw [upResonanceAxis_vertex_eq]
  native_decide

theorem downTypeFanoVertex_gen0_eq_downResonanceAxis :
    downTypeFanoVertex ⟨0, by decide⟩ = downResonanceAxis.vertex := by
  rw [downResonanceAxis_vertex_eq]
  native_decide

theorem upResonanceAxis_eq_upTypeFanoFirstGen : upResonanceAxis.vertex = upTypeFanoVertex ⟨0, by decide⟩ := by
  rw [upTypeFanoVertex_gen0_eq_upResonanceAxis]

theorem downResonanceAxis_eq_downTypeFanoFirstGen : downResonanceAxis.vertex = downTypeFanoVertex ⟨0, by decide⟩ := by
  rw [downTypeFanoVertex_gen0_eq_downResonanceAxis]

end quark_resonance_bridge

/-!
### Shared line + O-Maxwell mode bundle
-/

/-- Per-vertex Fano line choices and O-Maxwell mode hooks (one API for all sectors). -/
structure FanoVertexLineSelectors (v : FanoVertex) : Type where
  /-- Lowest-index incident line (`FanoLine.ofTag`). -/
  canonicalLine : FanoLine
  /-- Line from shell readout: triality tick on the three lines through `v` (`fanoLineFromVertexShell`). -/
  lineFromReadoutShell (m : ℕ) : FanoLine
  /-- Spectral mode on the **tag** line and shell `shell`. -/
  omaxwellModeOnTag (shell : ℕ) : FanoOmaxwellSpectralMode
  /-- Spectral mode on the **shell-fibrated** line and the same `shell` index (readout). -/
  omaxwellModeOnShellFibration (readout : ℕ) : FanoOmaxwellSpectralMode

/-- The canonical `FanoVertexLineSelectors` for vertex `v`. -/
def fanoLineSelectors (v : FanoVertex) : FanoVertexLineSelectors v where
  canonicalLine := FanoLine.ofTag v
  lineFromReadoutShell m := fanoLineFromVertexShell v m
  omaxwellModeOnTag shell := ⟨FanoLine.ofTag v, shell⟩
  omaxwellModeOnShellFibration readout := ⟨fanoLineFromVertexShell v readout, readout⟩

theorem fanoLineSelectors_canonicalLine (v : FanoVertex) : (fanoLineSelectors v).canonicalLine = FanoLine.ofTag v :=
  rfl

theorem fanoLineSelectors_lineFromReadoutShell (v : FanoVertex) (m : ℕ) :
    (fanoLineSelectors v).lineFromReadoutShell m = fanoLineFromVertexShell v m := rfl

theorem fanoLineSelectors_omaxwellModeOnTag (v : FanoVertex) (shell : ℕ) :
    (fanoLineSelectors v).omaxwellModeOnTag shell = (⟨FanoLine.ofTag v, shell⟩ : FanoOmaxwellSpectralMode) := rfl

/-!
### `ResonanceAxis` view
-/

/-- Line selectors for the Fano tag carried by a resonance axis (anchor ignored for **line** only). -/
def fanoLineSelectorsForAxis (a : ResonanceAxis) : FanoVertexLineSelectors a.vertex :=
  fanoLineSelectors a.vertex

theorem fanoLineSelectorsForAxis_eq (a : ResonanceAxis) (m : ℕ) :
    (fanoLineSelectorsForAxis a).lineFromReadoutShell m = fanoLineFromVertexShell a.vertex m := rfl

/-!
### The seven defaults (named accessors)
-/

def emLeptonFanoLineSelectors : FanoVertexLineSelectors emLeptonFanoVertex :=
  fanoLineSelectors emLeptonFanoVertex

def upFanoLineSelectors (g : Fin 3) : FanoVertexLineSelectors (upTypeFanoVertex g) :=
  fanoLineSelectors (upTypeFanoVertex g)

def downFanoLineSelectors (g : Fin 3) : FanoVertexLineSelectors (downTypeFanoVertex g) :=
  fanoLineSelectors (downTypeFanoVertex g)

def scalarHiggsFanoLineSelectors : FanoVertexLineSelectors scalarHiggsFanoVertex :=
  fanoLineSelectors scalarHiggsFanoVertex

end Hqiv.Physics
