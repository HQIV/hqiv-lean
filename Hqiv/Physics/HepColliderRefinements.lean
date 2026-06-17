import Hqiv.Physics.StrongSectorColliderDischarge

/-!
# HEP collider refinements (differential / MC-level discharge)

Extends `StrongSectorColliderDischarge` with refinement readouts cited by the HEP programme:
parton-shower iteration, thrust distribution width, ggH $p_T$ spectrum, QGP $v_2$ / $R_{AA}$,
and Bjorken-$x$ gluon PDF shape.

Python mirror: `scripts/hqiv_hep_collider_refinements.py`.
-/

namespace Hqiv.Physics

open Hqiv Real

/-!
## Thrust distribution + parton shower
-/

/-- Mean thrust at `n` visible axes (same spine as discharge). -/
noncomputable def thrustFromVisibleAxes (nVisibleAxes : ℕ) (alpha_s : ℝ) : ℝ :=
  max 0 (1 - (minStrongEmissionStepsBeyondDipole nVisibleAxes : ℝ) * gamma_HQIV *
    alpha_s / Real.pi * colourCasimirFundamental 3)

/-- RMS thrust fluctuation width from strong-channel count. -/
noncomputable def thrustDistributionWidth (alpha_s : ℝ) : ℝ :=
  gamma_HQIV * alpha_s / Real.pi * Real.sqrt (strongOctonionComponents.card : ℝ)

/-- Per-step shower emission probability (LO, capped). -/
noncomputable def partonShowerEmissionProbability (alpha_s : ℝ) : ℝ :=
  min 0.95 (alpha_s / Real.pi * colourCasimirFundamental 3 * strongChannelFraction)

/-- Non-abelian per-step damp $C_F/C_A$. -/
noncomputable def partonShowerStepDamp : ℝ :=
  colourCasimirFundamental 3 / colourCasimirAdjoint

theorem partonShowerStepDamp_eq_CF_over_CA :
    partonShowerStepDamp = (4 : ℝ) / 9 := by
  rw [partonShowerStepDamp, colourCasimirAdjoint_eq_three, colourCasimirFundamental_three]
  norm_num

/-!
## Higgs $p_T$ spectrum
-/

noncomputable def ggHpTFalloffGeV : ℝ := gamma_HQIV * 125.11 / (1 + gamma_HQIV)

/-!
## QGP transport refinements
-/

/-- Elliptic-flow slot from $\eta/s$ discharge. -/
noncomputable def qgpV2Discharge : ℝ :=
  gamma_HQIV * qgpEtaOverSDischarge

/-- Jet-quenching weight at transverse momentum `ptGeV`. -/
noncomputable def qgpRAAWeightAtPT (ptGeV : ℝ) : ℝ :=
  Real.exp (-ptGeV / (gamma_HQIV * derivedProtonMass / 100))

theorem qgpRAAWeightAtPT_pos (ptGeV : ℝ) : 0 < qgpRAAWeightAtPT ptGeV := by
  unfold qgpRAAWeightAtPT
  exact Real.exp_pos _

/-!
## PDF $x$-shape
-/

/-- Unnormalised gluon PDF slot at Bjorken $x$ (shape exponent from $\gamma$). -/
noncomputable def pdfGluonShapeAtX (x : ℝ) : ℝ :=
  if x ≤ 0 ∨ 1 ≤ x then 0
  else pdfGluonFirstMomentDischarge * Real.rpow x (gamma_HQIV - 1) *
    Real.rpow (1 - x) gamma_HQIV

structure HepColliderRefinementsDischarged where
  shower_damp : partonShowerStepDamp = (4 : ℝ) / 9
  thrust_width_pos : ∀ (alpha_s : ℝ), 0 ≤ alpha_s → 0 ≤ thrustDistributionWidth alpha_s
  raa_pos : ∀ pt, 0 < qgpRAAWeightAtPT pt

noncomputable def hepColliderRefinementsDischarged : HepColliderRefinementsDischarged where
  shower_damp := partonShowerStepDamp_eq_CF_over_CA
  thrust_width_pos := by
    intro alpha_s ha
    unfold thrustDistributionWidth
    rw [gamma_eq_2_5]
    positivity
  raa_pos := qgpRAAWeightAtPT_pos

#check hepColliderRefinementsDischarged
#check thrustDistributionWidth
#check partonShowerEmissionProbability
#check ggHpTFalloffGeV
#check qgpV2Discharge
#check pdfGluonShapeAtX

end Hqiv.Physics
