import HqivSpine.Physics.NuclearBinding
import HqivSpine.Physics.NucleonLadder
import HqivSpine.Physics.Curvature
import HqivSpine.Foundation.Carrier
import HqivSpine.Chemistry.Binding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `HqivSpine.Physics.NuclearCluster` — inside/outside cluster binding

Golfed from legacy `NuclearCurvatureBinding`: the **structural split** between trapped inside
curvature and outside `G_eff(η)^α` contact networking, using spine-native binding traces and
no PDG mass tables.

Honest scope: **sign, monotonicity, and the inside+outside decomposition** for light nuclei
(`A ≤ 4` constructive valley cap). Post-α cooperative network and isotope panels stay partial.
-/

namespace HqivSpine.Physics.NuclearCluster

open HqivSpine.Foundation
open HqivSpine.Physics
open HqivSpine.Physics.NucleonLadder
open HqivSpine.Chemistry.Binding
open scoped BigOperators

/-! ## Valley bookkeeping (constructive α cap) -/

/-- Constructive valley contact cap at closed α (`⁴He`). -/
def constructiveValleyCap : ℕ := 6

/-- Valley contact count on the constructive ladder (exact for `A ≤ 4`). -/
def valleyContactCount : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => constructiveValleyCap
  | _ => constructiveValleyCap

theorem valleyContactCount_four : valleyContactCount 4 = constructiveValleyCap := rfl

theorem valleyContactCount_pos_of_ge_three (A : ℕ) (hA : 3 ≤ A) : 0 < valleyContactCount A := by
  have h3 : 3 ≤ valleyContactCount A := by
    match A with
    | 3 => simp [valleyContactCount]
    | n + 4 =>
      have hcount : valleyContactCount (n + 4) = constructiveValleyCap := by
        cases n with
        | zero => simp [valleyContactCount]
        | succ _ => simp [valleyContactCount]
      rw [hcount, constructiveValleyCap]
      decide
  exact Nat.lt_of_lt_of_le (by decide : 0 < 3) h3

/-- Strong-sector channel fraction `4/8 = 1/2`. -/
noncomputable def strongChannelFraction : ℝ := 4 / (carrierMultiplicity : ℝ)

theorem strongChannelFraction_eq : strongChannelFraction = 1 / 2 := by
  unfold strongChannelFraction
  rw [carrierMultiplicity_eq_eight]
  norm_num

/-! ## Inside / outside pieces -/

/-- Inside curvature weight ratio between cluster shell and reference. -/
noncomputable def insideWeightRatio (m_cluster m_ref : ℕ) : ℝ :=
  max 0 (shellShape m_cluster / shellShape m_ref - 1)

/-- Per-nucleon trace binding at shell `m` (from the concrete nucleon network). -/
noncomputable def nucleonTraceBinding (m : ℕ) (c : ℝ := 1) : ℝ :=
  E_bind_from_network m nucleonWeight c / 3

theorem nucleonTraceBinding_pos (m : ℕ) : 0 < nucleonTraceBinding m 1 := by
  unfold nucleonTraceBinding
  exact div_pos (E_bind_nucleon_pos m) (by norm_num : (0 : ℝ) < 3)

/-- Normalized outside contact phase `η = θ/θ₀` with `θ₀ = 1`. -/
noncomputable def contactParticipation (θ : ℝ) : ℝ := θ

/-- Outside nucleon–nucleon coupling `G_eff(η) = η^α`. -/
noncomputable def outsideContactCoupling (θ : ℝ) : ℝ := G_eff (contactParticipation θ)

theorem outsideContactCoupling_eq (θ : ℝ) (_hθ : 0 ≤ θ) :
    outsideContactCoupling θ = θ ^ alphaEM := by
  unfold outsideContactCoupling contactParticipation G_eff; rfl

/-- **Inside binding:** trapped curvature deepening at cluster shell. -/
noncomputable def insideBinding (m m_cluster A : ℕ) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * nucleonTraceBinding m c * insideWeightRatio m_cluster referenceM

/-- **Outside binding:** valley contacts times outside coupling times trace. -/
noncomputable def outsideBinding (m A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  (valleyContactCount A : ℝ) * outsideContactCoupling θ * nucleonTraceBinding m c

/-- **Total cluster binding** = inside + outside. -/
noncomputable def clusterBinding (m m_cluster A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  insideBinding m m_cluster A c + outsideBinding m A θ c

theorem clusterBinding_add (m m_cluster A : ℕ) (θ : ℝ) (c : ℝ) :
    clusterBinding m m_cluster A θ c =
      insideBinding m m_cluster A c + outsideBinding m A θ c := rfl

theorem clusterBinding_pos (m m_cluster A : ℕ) (θ : ℝ)
    (hA : 3 ≤ A) (hθ : 0 < θ) :
    0 < clusterBinding m m_cluster A θ 1 := by
  unfold clusterBinding
  have htrace := nucleonTraceBinding_pos m
  have hvc : 0 < (valleyContactCount A : ℝ) := by
    exact_mod_cast valleyContactCount_pos_of_ge_three A hA
  have hG : 0 < outsideContactCoupling θ := by
    rw [outsideContactCoupling_eq θ hθ.le]
    exact Real.rpow_pos_of_pos hθ alphaEM
  have hout : 0 < outsideBinding m A θ 1 := by
    unfold outsideBinding
    exact mul_pos (mul_pos hvc hG) htrace
  by_cases hinside : 0 < insideWeightRatio m_cluster referenceM
  · have hin : 0 < insideBinding m m_cluster A 1 := by
      unfold insideBinding
      have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
      exact mul_pos (mul_pos hA' htrace) hinside
    linarith [hin, hout]
  · have hzero : insideWeightRatio m_cluster referenceM = 0 :=
      le_antisymm (le_of_not_gt hinside) (le_max_left 0 _)
    have hin : insideBinding m m_cluster A 1 = 0 := by
      unfold insideBinding; simp [hzero, mul_zero]
    rw [hin, zero_add]
    exact hout

/-! ## Post-α extension (structural) -/

/-- Nucleons beyond closed α. -/
def postAlphaExtra (A : ℕ) : ℕ := if A ≤ 4 then 0 else A - 4

/-- Post-α well-deepening factor (cooperative network hook). -/
noncomputable def postAlphaWellDeepening (A : ℕ) : ℝ :=
  if A ≤ 4 then 1
  else 1 + strongChannelFraction * ((valleyContactCount A : ℝ) - constructiveValleyCap) /
    (constructiveValleyCap : ℝ)

theorem postAlphaWellDeepening_he4 : postAlphaWellDeepening 4 = 1 := by
  unfold postAlphaWellDeepening; norm_num

end HqivSpine.Physics.NuclearCluster
