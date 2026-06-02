import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Sort
import Hqiv.Physics.FanoResonance

namespace Hqiv.Physics

/-!
# FanoLine — minimal incidence structure

A `FanoLine` is a 3-point line in the Fano plane (the projective plane over \( \mathbb{F}_2 \)).
Each line is stored as a `Finset` of three distinct `FanoVertex` values so equality and
membership are decidable.

Two distinct tag stories coexist in the repo:

- a **line-label** view, where `Fin 7` indexes the seven standard projective lines, and
- a **vertex-incidence** view, where a `FanoVertex` chooses one incident line by convention.

The public default is now the **vertex-incidence** interpretation:
`FanoLine.ofTag` chooses a canonical incident line for a `FanoVertex` (lowest
standard line index through that vertex, same as `FanoLine.ofVertexChoice v 0`).

The old line-label lookup is kept under the explicit name `FanoLine.ofLineLabel`.

**Programmatic choice:** `FanoLine.ofVertexChoice v j` (with `j : Fin 3`) cycles over the
three lines incident to `v` in sorted label order, so you can treat `j` as a
triality/sector index or drive it from a shell readout; see
`Hqiv.Physics.FanoLineRapidityChoice` for a shell-`% 3` hook that composes with the
`rapidityCPBias` / `omega_k` story.
-/

/-- A line: three distinct collinear points (Fano incidence is checked at the table level). -/
structure FanoLine where
  pts : Finset FanoVertex
  size_three : pts.card = 3

namespace FanoLine

/-- The three vertices of the line, listed in increasing order (`Finset.sort` default `≤` on `Fin 7`). -/
def vertices (L : FanoLine) (i : Fin 3) : FanoVertex :=
  let l := L.pts.sort
  have hl : l.length = 3 := by
    rw [Finset.length_sort, L.size_three]
  l.get ⟨i, by rw [hl]; exact i.is_lt⟩

/-- Membership predicate for the combinatorial line. -/
def contains (L : FanoLine) (v : FanoVertex) : Prop := v ∈ L.pts

theorem contains_iff_mem (L : FanoLine) (v : FanoVertex) : L.contains v ↔ v ∈ L.pts := Iff.rfl

end FanoLine

/-! ## Standard PG(2,2) lines (0-based labels 0..6) -/

open Finset
/-- The seven lines of a standard labeling (each is a 3-point line of the Fano plane). -/
def fanoStandardLine (i : Fin 7) : Finset FanoVertex :=
  match i with
  | ⟨0, _⟩ => insert (⟨2, by decide⟩ : FanoVertex) (insert (⟨1, by decide⟩ : FanoVertex) {⟨0, by decide⟩})
  | ⟨1, _⟩ => insert (⟨4, by decide⟩ : FanoVertex) (insert (⟨3, by decide⟩ : FanoVertex) {⟨0, by decide⟩})
  | ⟨2, _⟩ => insert (⟨6, by decide⟩ : FanoVertex) (insert (⟨5, by decide⟩ : FanoVertex) {⟨0, by decide⟩})
  | ⟨3, _⟩ => insert (⟨5, by decide⟩ : FanoVertex) (insert (⟨3, by decide⟩ : FanoVertex) {⟨1, by decide⟩})
  | ⟨4, _⟩ => insert (⟨6, by decide⟩ : FanoVertex) (insert (⟨4, by decide⟩ : FanoVertex) {⟨1, by decide⟩})
  | ⟨5, _⟩ => insert (⟨6, by decide⟩ : FanoVertex) (insert (⟨3, by decide⟩ : FanoVertex) {⟨2, by decide⟩})
  | ⟨6, _⟩ => insert (⟨5, by decide⟩ : FanoVertex) (insert (⟨4, by decide⟩ : FanoVertex) {⟨2, by decide⟩})

theorem fanoStandardLine_card (i : Fin 7) : (fanoStandardLine i).card = 3 := by
  fin_cases i <;> native_decide

/-- Line indexed by `i : Fin 7` in the standard table. -/
def ofIndex (i : Fin 7) : FanoLine where
  pts := fanoStandardLine i
  size_three := fanoStandardLine_card i

/-- Explicit line-label API: `Fin 7` as the index of one of the seven standard lines. -/
def FanoLine.ofLineLabel (i : Fin 7) : FanoLine := ofIndex i

theorem FanoLine.ofLineLabel_eq_ofIndex (i : Fin 7) : FanoLine.ofLineLabel i = ofIndex i := rfl

/-- Standard-line labels incident to a given vertex. -/
def incidentLineLabels (v : FanoVertex) : Finset (Fin 7) :=
  Finset.univ.filter fun i => v ∈ fanoStandardLine i

theorem incidentLineLabels_card (v : FanoVertex) : (incidentLineLabels v).card = 3 := by
  fin_cases v <;> native_decide

/-- Canonical incidence choice: lowest-index standard line containing the vertex. -/
def incidentLineLabelLowest (v : FanoVertex) : Fin 7 :=
  match v with
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨3, _⟩ => ⟨1, by decide⟩
  | ⟨4, _⟩ => ⟨1, by decide⟩
  | ⟨5, _⟩ => ⟨2, by decide⟩
  | ⟨6, _⟩ => ⟨2, by decide⟩

/-- Incidence-driven API: choose one canonical incident line for the given vertex. -/
def FanoLine.ofIncidentVertex (v : FanoVertex) : FanoLine := ofIndex (incidentLineLabelLowest v)

/-- Public tag API: interpret a `FanoVertex` tag as a vertex and choose the canonical incident line. -/
def FanoLine.ofTag (t : FanoVertex) : FanoLine := ofIncidentVertex t

theorem FanoLine.ofTag_eq_ofIncidentVertex (t : FanoVertex) :
    FanoLine.ofTag t = ofIncidentVertex t := rfl

theorem incidentLineLabelLowest_mem_incidentLineLabels (v : FanoVertex) :
    incidentLineLabelLowest v ∈ incidentLineLabels v := by
  fin_cases v <;> native_decide

theorem ofIncidentVertex_mem_pts (v : FanoVertex) :
    v ∈ (FanoLine.ofIncidentVertex v).pts := by
  fin_cases v <;> native_decide

theorem ofIncidentVertex_contains (v : FanoVertex) :
    (FanoLine.ofIncidentVertex v).contains v := by
  simpa [FanoLine.contains] using ofIncidentVertex_mem_pts v

/-!
### Incident line choice: sorted labels per vertex (Fin 3 fibration)
-/

/-- The three standard line labels through `v`, sorted by `Fin 7` order (deterministic, reusable). -/
def incidentLineLabelsSorted (v : FanoVertex) : List (Fin 7) :=
  sort (incidentLineLabels v)

theorem incidentLineLabelsSorted_length (v : FanoVertex) :
    (incidentLineLabelsSorted v).length = 3 := by
  unfold incidentLineLabelsSorted
  rw [Finset.length_sort, incidentLineLabels_card]

/-- `j = 0` is the same incident line as `incidentLineLabelLowest` (the `ofTag` / `ofIncident` pick). -/
def incidentLineAt (v : FanoVertex) (j : Fin 3) : Fin 7 :=
  (incidentLineLabelsSorted v).get
    (Fin.cast (incidentLineLabelsSorted_length v).symm j)

theorem incidentLineAt_zero_eq_lowest (v : FanoVertex) :
    incidentLineAt v 0 = incidentLineLabelLowest v := by
  fin_cases v <;> native_decide

theorem incidentLineAt_mem_incidentLineLabels (v : FanoVertex) (j : Fin 3) :
    incidentLineAt v j ∈ incidentLineLabels v := by
  -- The seven vertices × three incident lines are finite: decide.
  fin_cases v <;> fin_cases j <;> native_decide

/-- Pick the `j`-th incident line to `v` (sorted by standard line index `0..6`). -/
def FanoLine.ofVertexChoice (v : FanoVertex) (j : Fin 3) : FanoLine := ofIndex (incidentLineAt v j)

theorem FanoLine.ofTag_eq_ofVertexChoice_zero (t : FanoVertex) :
    FanoLine.ofTag t = FanoLine.ofVertexChoice t 0 := by
  simp [FanoLine.ofTag, FanoLine.ofIncidentVertex, FanoLine.ofVertexChoice, ofIndex,
    incidentLineAt_zero_eq_lowest]

theorem ofVertexChoice_mem_lineLabel (v : FanoVertex) (j : Fin 3) :
    incidentLineAt v j ∈ incidentLineLabels v :=
  incidentLineAt_mem_incidentLineLabels v j

theorem ofVertexChoice_contains_vertex (v : FanoVertex) (j : Fin 3) :
    v ∈ (FanoLine.ofVertexChoice v j).pts := by
  have hL : incidentLineAt v j ∈ incidentLineLabels v := ofVertexChoice_mem_lineLabel v j
  unfold incidentLineLabels at hL
  have hv : v ∈ fanoStandardLine (incidentLineAt v j) := (Finset.mem_filter.1 hL).2
  simpa [FanoLine.ofVertexChoice, ofIndex] using hv

theorem ofVertexChoice_contains (v : FanoVertex) (j : Fin 3) :
    (FanoLine.ofVertexChoice v j).contains v :=
  ofVertexChoice_contains_vertex v j

end Hqiv.Physics
