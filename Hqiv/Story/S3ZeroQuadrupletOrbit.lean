import Hqiv.Story.S3DeltaOrbitOffStrip
import Hqiv.Story.S3OrbitVsPointwiseGap
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Functional-equation + Schwarz quadruplet orbits for ζ-zeros

Nontrivial zeros come in FE pairs `{s, 1-s}` (`zeta_zero_fe_pair`).  The full
Schwarz quadruplet `{s, 1-s, conj s, conj (1-s)}` is discharged when the
conjugation identity `ζ(conj t) = conj ζ(t)` on all orbit points is available
(`zeta_zero_quadruplet`).  On the critical line the two reflections coincide;
see `S3OrbitVsPointwiseGap` for the σ-orbit packaging.
-/

namespace Hqiv.Story

noncomputable section

open Complex ComplexConjugate

def schwarzReflect (s : ℂ) : ℂ := starRingEnd ℂ s

theorem one_sub_schwarzReflect (s : ℂ) : 1 - schwarzReflect s = schwarzReflect (1 - s) := by
  simp [schwarzReflect, map_one, map_sub]

theorem schwarzReflect_zero : schwarzReflect (0 : ℂ) = 0 := by
  simp [schwarzReflect, map_zero]

def zetaZeroQuadruplet (s : ℂ) : Finset ℂ :=
  {s, 1 - s, schwarzReflect s, 1 - schwarzReflect s}

theorem zeta_zero_fe_pair (s : ℂ) (h : IsNontrivialZetaZero s) :
    riemannZeta (1 - s) = 0 :=
  riemannZeta_zero_reflects s (nontrivial_zero_fe_slot s h) h.2.2 h.1

theorem zeta_zero_quadruplet
    (s : ℂ) (h : IsNontrivialZetaZero s)
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    ∀ z ∈ zetaZeroQuadruplet s, riemannZeta z = 0 := by
  intro z hz
  simp only [zetaZeroQuadruplet, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | hz
  · exact h.1
  · rcases hz with rfl | hz
    · exact zeta_zero_fe_pair s h
    · rcases hz with rfl | hz
      · rw [hconj s, h.1, schwarzReflect_zero]
      · subst hz
        rw [one_sub_schwarzReflect s, hconj (1 - s), zeta_zero_fe_pair s h, schwarzReflect_zero]

end

end Hqiv.Story
