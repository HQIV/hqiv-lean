import Hqiv.Physics.CompactObjectRotatingCrustScaffold
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gravitational-wave ringdown + tail scaffold (Lean ↔ Python witness)

Packages **named scaling slots** for Kerr (2,2,0) ringdown mass inference from measured
``f₂₂₀`` and ``τ₂₂₀``.  Python treats those as **detection inputs** and infers remnant mass
as **output** (standard Kerr inversion vs HQIV-unmapped Kerr inversion).

**GR inference:** spin from ``2π f τ``; mass from ``τ`` and ``f`` via tabulated ``M ω``.

**HQIV inference:** unmap ``f → f / freqScale`` and ``τ → τ / dampScale`` (plus HMNS mass-tail
fixed point) then apply the same Kerr inversion.

**Forward map (synthetic detections):** true ``M_f`` implies higher measured ``f`` and shifted
``τ`` through the slots below.

* ``freqScale = √(G_eff(ε)) / lapse(ε)^α`` with ``ε = 1/2``, ``lapse = 1 − ε``, ``α = 3/5``.
* ``dampScale = lapse(ε) / G_eff(ε) × (1 + η/η_lock)`` with ``η = inductionResistivityEta``.

**HQIV tail index slot:** ``ν_tail = ν_GR + γ(1 − lapse) + α(G_eff − 1)`` with ``ν_GR = 4``.

**Mass tail:** charmed-core extension from the compact-object gradient-collapse layer
(Python `gradient_collapse_hypothesis` / `charmed_tail_mass_oblate`) for HMNS-class remnants.

Python: `scripts/hqiv_gw_ringdown.py`.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Schwarzschild-surface gravitational slot (``GM/(Rc²) = 1/2``). -/
def gwHorizonEpsilon : ℝ := 1 / 2

theorem gwHorizonEpsilon_eq_half : gwHorizonEpsilon = (1 / 2 : ℝ) := rfl

/-- HQVM lapse at the horizon slot: ``N = 1 − ε``. -/
noncomputable def gwHorizonLapse : ℝ := 1 - gwHorizonEpsilon

theorem gwHorizonLapse_eq_half : gwHorizonLapse = (1 / 2 : ℝ) := by
  unfold gwHorizonLapse gwHorizonEpsilon
  norm_num

/-- Outside gravity modulator at the horizon slot. -/
noncomputable def gwHorizonGeffModulator : ℝ :=
  outsideGravityGeffModulator ⟨gwHorizonEpsilon⟩

/-- GR Price-tail baseline exponent for the leading ``l = 2`` multipole (witness label). -/
def gwGrTailExponent : ℝ := 4

/-- HQIV frequency scaling slot at the horizon. -/
noncomputable def gwRingdownFrequencyScale : ℝ :=
  Real.sqrt gwHorizonGeffModulator / gwHorizonLapse ^ alpha

/-- HQIV damping-time scaling slot (induction factor applied in Python). -/
noncomputable def gwRingdownDampingScaleBase : ℝ :=
  gwHorizonLapse / gwHorizonGeffModulator

/-- HQIV power-law tail exponent slot above the GR baseline. -/
noncomputable def gwTailExponentOffset (geffMod : ℝ) : ℝ :=
  gamma_HQIV * (1 - gwHorizonLapse) + alpha * (geffMod - 1)

noncomputable def gwTailExponent (geffMod : ℝ) : ℝ :=
  gwGrTailExponent + gwTailExponentOffset geffMod

theorem gwTailExponent_gt_gr (geffMod : ℝ) (hgeff : 1 ≤ geffMod) :
    gwGrTailExponent < gwTailExponent geffMod := by
  unfold gwTailExponent gwTailExponentOffset gwGrTailExponent
  have hlapse : gwHorizonLapse = (1 / 2 : ℝ) := gwHorizonLapse_eq_half
  rw [hlapse, gamma_eq_2_5, alpha_eq_3_5]
  nlinarith

end

end Hqiv.Physics
