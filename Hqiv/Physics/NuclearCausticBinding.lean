import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Physics.MetaHorizonTrappedPlanckMass
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.NuclearCurvatureBinding

/-!
# Nuclear binding from hierarchical Casimir caustics

Each nucleon carries a **spherical Fresnel caustic** (`fresnelCaustic`, radius `R_m`).
When nucleons bind:

1. **Pair overlap** — two caustics fit; `valleyPotential` / `deuteronBindingScale`.
2. **Barbell torus** — toroidal ring caustic one shell higher (`toroidal_ring_closure`).
3. **Tetrahedral closure** — deepest cooperative spot completing ⁴He.

All active caustics **deepen the binding well together** (additive structural stack).

Python: `scripts/hqiv_nuclear_caustic_binding.py`.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Horizon ratio scale for a caustic layer at shell `m` (matches `deuteronBindingScale`). -/
noncomputable def causticHorizonScale (m : ℕ) : ℝ :=
  deuteronBindingScale m

/-- Barbell torus scale at shell `m`: `γ · new_modes(m+1) / R_{m+1}`. -/
noncomputable def barbellTorusCausticScale (m : ℕ) : ℝ :=
  gamma_HQIV * Hqiv.new_modes (m + 1) / R_m (m + 1)

theorem barbellTorusCausticScale_eq (m : ℕ) :
    barbellTorusCausticScale m = gamma_HQIV * Hqiv.new_modes (m + 1) / R_m (m + 1) := rfl

theorem barbellTorusCausticScale_eq_eight_gamma (m : ℕ) :
    barbellTorusCausticScale m = 8 * gamma_HQIV := by
  unfold barbellTorusCausticScale R_m
  rw [toroidal_ring_closure m]
  have hden : ((m + 1 : ℕ) + 1 : ℝ) = (↑m + 2) := by
    push_cast
    ring
  rw [hden]
  field_simp

/-- Deepest tetrahedral closure scale two shells above the binding drum. -/
noncomputable def tetrahedralClosureCausticScale (m : ℕ) : ℝ :=
  gamma_HQIV * modes (m + 2) / R_m (m + 2)

theorem tetrahedralClosureCausticScale_eq (m : ℕ) :
    tetrahedralClosureCausticScale m =
      gamma_HQIV * Hqiv.available_modes (m + 2) / R_m (m + 2) := by
  unfold tetrahedralClosureCausticScale modes
  rfl

/-- Pair-sphere overlap layer (two nucleons, A ≥ 2). -/
noncomputable def pairSphereCausticBinding (m : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  causticHorizonScale m * nuclearOutsideContactCoupling θ * bbnNucleonTraceBinding m c

/-- Barbell torus layer (A ≥ 2). -/
noncomputable def barbellTorusCausticBinding (m : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  barbellTorusCausticScale m * nuclearOutsideContactCoupling θ * bbnNucleonTraceBinding m c

/-- Tetrahedral closure layer (A ≥ 4). -/
noncomputable def tetrahedralCausticBinding (m : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  tetrahedralClosureCausticScale m * nuclearOutsideContactCoupling θ * bbnNucleonTraceBinding m c

/-- Cumulative outside caustic binding for mass number A ≥ 2 (pair + torus; + tetra when A ≥ 4). -/
noncomputable def nuclearOutsideCausticBinding (m : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  if A ≤ 1 then 0
  else
    pairSphereCausticBinding m θ c + barbellTorusCausticBinding m θ c +
      (if 4 ≤ A then tetrahedralCausticBinding m θ c else 0)

/-- Full nuclear cluster binding: inside trapped curvature + cumulative caustics. -/
noncomputable def nuclearClusterBindingCaustic
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearInsideBindingAtShell m m_cluster A c + nuclearOutsideCausticBinding m A θ c

theorem nuclearClusterBindingCaustic_add_inside_outside
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ) :
    nuclearClusterBindingCaustic m m_cluster A θ c =
      nuclearInsideBindingAtShell m m_cluster A c +
        nuclearOutsideCausticBinding m A θ c := by
  unfold nuclearClusterBindingCaustic
  ring

end

end Hqiv.Physics
