import Hqiv.Physics.BBNEpochEvolution
import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.NuclearCurvatureBinding
import Hqiv.Physics.NuclearOutsideTemperatureDynamics

/-!
# BBN stoichiometric integrator spine (Lean mirror)

Faithful light-element synthesis at BBN epoch temperatures combines:

* **Partition seeds** (`bbnDHAtEpoch`, `bbnHe3HAtEpoch`, `bbnLi7HAtEpochLadder`) at lock-in Q's;
* **Trimer / multi-α resonance widths** (`trimerResonanceWidthMev`, `multiAlphaResonanceWidthMev`)
  eroding effective Q at finite `T`;
* **`bbnBindingReleaseFactor`** from curvature–temperature separation (`DynamicBBNBaryogenesis`);
* **Stoichiometric D budget** (³He branch width suppression, D return, synthesis-window tail gate,
  strong deposition boost) — numeric integration witness in Python `hqiv_bbn_integrator.py` /
  `data/bbn_integrator.json`;
* **Free-neutron outside curvature** — relic-ν weak-width catalysis and outside-release lifetime
  ratio shift weak freeze-out (`bbnFreeNeutronWeakWidthFactorAtT`, `bbnWeakFreezeoutTempExponent`).

Integrated abundances remain computed witnesses.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Trimer width at epoch `T`, including binding-release compression. -/
noncomputable def trimerResonanceWidthAtT (m : ℕ) (A : ℕ) (clusterTotal T_MeV : ℝ) : ℝ :=
  trimerResonanceWidthMev m A clusterTotal * bbnBindingReleaseFactor T_MeV

/-- Two-α (⁸Be) width at epoch `T`. -/
noncomputable def multiAlphaResonanceWidthAtT (m : ℕ) (nAlpha : ℕ) (clusterTotal T_MeV : ℝ) : ℝ :=
  multiAlphaResonanceWidthMev m nAlpha clusterTotal * bbnBindingReleaseFactor T_MeV

/-- Boltzmann erosion `exp(−Γ/T)` on a trimer channel at `T > 0`. -/
noncomputable def bbnTrimerWidthSuppressAtT (Γ T_MeV : ℝ) : ℝ :=
  Real.exp (-Γ / T_MeV)

/-- Effective trimer binding Q after width erosion at temperature `T`. -/
noncomputable def bbnEffectiveTrimerQAtT (Q_trace Γ T_MeV : ℝ) : ℝ :=
  Q_trace * bbnTrimerWidthSuppressAtT Γ T_MeV

/-- ³He cluster total at lock-in (trace binding × valley factor). -/
noncomputable def bbnHe3ClusterTotalAtLockin (c : ℝ := 1) : ℝ :=
  bbnClusterBinding bbnBindingShell 3 c

/-- Default trimer width for ³He at `T` on the binding shell. -/
noncomputable def bbnHe3TrimerWidthAtT (T_MeV : ℝ) (c : ℝ := 1) : ℝ :=
  trimerResonanceWidthAtT bbnBindingShell 3 (bbnHe3ClusterTotalAtLockin c) T_MeV

/-- Effective ³He Q at `T` after trimer saddle broadening. -/
noncomputable def bbnHe3EffectiveQAtT (T_MeV : ℝ) (c : ℝ := 1) : ℝ :=
  bbnEffectiveTrimerQAtT (bbnClusterBinding bbnBindingShell 3 c)
    (bbnHe3TrimerWidthAtT T_MeV c) T_MeV

structure BBNStoichiometricReadoutAtT where
  T_MeV : ℝ
  trimerWidth_MeV : ℝ
  he3Q_eff_MeV : ℝ
  partition_DH : ℝ
  partition_He3H : ℝ
  partition_Li7H : ℝ

/-- Partition-level readout at `T` (pre-stoichiometric conservation; Python adds D budget). -/
noncomputable def bbnStoichiometricPartitionAtT (η T_MeV : ℝ) (c : ℝ := 1) : BBNStoichiometricReadoutAtT :=
  {
    T_MeV := T_MeV
    trimerWidth_MeV := bbnHe3TrimerWidthAtT T_MeV c
    he3Q_eff_MeV := bbnHe3EffectiveQAtT T_MeV c
    partition_DH := bbnDHAtEpoch η T_MeV
    partition_He3H := bbnHe3HAtEpoch η T_MeV
    partition_Li7H := bbnLi7HAtEpochLadder η T_MeV
  }

theorem bbnTrimerWidthSuppressAtT_pos (Γ T_MeV : ℝ) :
    0 < bbnTrimerWidthSuppressAtT Γ T_MeV := by
  unfold bbnTrimerWidthSuppressAtT
  exact Real.exp_pos _

/-! ## Free-neutron weak freeze-out (outside curvature channel)

Python ``y_p_with_free_neutron_curvature`` mirrors:
* ``localCurvatureWeakWidthFactor`` (relic ν bath catalysis, ≥ 1);
* free-branch outside modulator lifetime ratio vs lock-in (Python
  ``outside_curvature_binding_modulator``);
* ``weak_relax_rate ∝ T^5`` → ``T_eff = T_bare · τ_ratio^(1/5)``.
-/

/-- Weak-width catalysis factor at BBN temperature (free branch, zero gravity φ). -/
noncomputable def bbnFreeNeutronWeakWidthFactorAtT (T_MeV : ℝ) : ℝ :=
  localCurvatureWeakWidthFactor (bbnXiFromT_MeV T_MeV) 0

/-- Exponent for freeze-out shift from ``BBNEpochNetwork.weak_relax_rate ∝ T^5``. -/
def bbnWeakFreezeoutTempExponent : ℝ := 1 / 5

/-- Bare weak freeze-out temperature ``Q_np / log(η₁₀)``. -/
noncomputable def bbnBareFreezeoutTemperatureMeV (η Q_np : ℝ) : ℝ :=
  bbnInternalTemperatureMeV η Q_np

/-- Effective freeze-out temperature with curvature slowdown ``T_bare · τ_ratio^(1/5)``.

``τ_ratio`` is supplied by the Python witness (outside modulator / width factor); the
structural exponent is fixed by the epoch-network weak-rate temperature power.
-/
noncomputable def bbnEffectiveFreezeoutTemperatureMeV (η Q_np τ_ratio : ℝ) : ℝ :=
  bbnBareFreezeoutTemperatureMeV η Q_np * τ_ratio ^ bbnWeakFreezeoutTempExponent

/-- Strong-channel trimer erosion factor (Python ``trimer_width_suppress_at_T``). -/
noncomputable def bbnTrimerWidthStrongSuppressAtT (Γ T_MeV : ℝ) : ℝ :=
  Real.exp (-Γ * gamma_HQIV * strongChannelFraction / T_MeV)

/-! ## Synthesis-window geometry (Python ``hqiv_bbn_condition_decay``)

Shared MeV gate constants, log-weight tail below the ³He mid-gate, and stoichiometric
branch gates mirrored for audit (`scripts/hqiv_integrator_lean_audit.py`).
-/

/-- D/H integration high anchor (Python ``BBN_T_HIGH_MEV``). -/
def bbnSynthesisDWindowHighMeV : ℝ := 1

/-- ³He synthesis band low edge (Python ``HE3_SYNTH_LOW_MEV``). -/
def bbnHe3SynthesisLowMeV : ℝ := 5 / 100

/-- ³He synthesis band high edge (Python ``HE3_SYNTH_HIGH_MEV``). -/
def bbnHe3SynthesisHighMeV : ℝ := 45 / 100

/-- ³He synthesis mid-gate (Python ``HE3_SYNTH_MID_MEV`` / ``he3_synthesis_gate`` apex). -/
def bbnHe3SynthesisMidMeV : ℝ := 18 / 100

/-- Narrow ⁷Be-feed mid-gate (Python ``he3_be7_feed_gate`` apex). -/
def bbnHe3Be7FeedMidMeV : ℝ := 15 / 100

/-- Narrow ⁷Be-feed high edge (Python ``he3_be7_feed_gate``). -/
def bbnHe3Be7FeedHighMeV : ℝ := 35 / 100

/-- D+D→⁴He gate low edge (Python ``dd_fusion_gate`` / ``alpha_synthesis_gate``). -/
def bbnAlphaSynthesisGateLowMeV : ℝ := 35 / 1000

/-- D+D→⁴He gate width (Python ``dd_fusion_gate``). -/
def bbnAlphaSynthesisGateWidthMeV : ℝ := 60 / 1000

/-- Clip to ``[0,1]`` for piecewise synthesis gates. -/
def bbnSynthesisGateClip (x : ℝ) : ℝ :=
  max 0 (min 1 x)

/-- ³He synthesis gate (Python ``he3_synthesis_gate``). -/
noncomputable def bbnHe3SynthesisGate (T_MeV : ℝ) : ℝ :=
  if T_MeV ≤ bbnHe3SynthesisLowMeV ∨ bbnHe3SynthesisHighMeV ≤ T_MeV then 0
  else if bbnHe3SynthesisMidMeV ≤ T_MeV then
    (bbnHe3SynthesisHighMeV - T_MeV) / (bbnHe3SynthesisHighMeV - bbnHe3SynthesisMidMeV)
  else
    (T_MeV - bbnHe3SynthesisLowMeV) / (bbnHe3SynthesisMidMeV - bbnHe3SynthesisLowMeV)

/-- Narrow ³He bath for ⁷Be→⁷Li (Python ``he3_be7_feed_gate``). -/
noncomputable def bbnHe3Be7FeedGate (T_MeV : ℝ) : ℝ :=
  if T_MeV ≤ bbnHe3SynthesisLowMeV ∨ bbnHe3Be7FeedHighMeV ≤ T_MeV then 0
  else if bbnHe3Be7FeedMidMeV ≤ T_MeV then
    (bbnHe3Be7FeedHighMeV - T_MeV) / (bbnHe3Be7FeedHighMeV - bbnHe3Be7FeedMidMeV)
  else
    (T_MeV - bbnHe3SynthesisLowMeV) / (bbnHe3Be7FeedMidMeV - bbnHe3SynthesisLowMeV)

/-- ⁴He lock-in gate (Python ``alpha_synthesis_gate`` / ``dd_fusion_gate``). -/
noncomputable def bbnAlphaSynthesisGate (T_MeV : ℝ) : ℝ :=
  bbnSynthesisGateClip
    ((T_MeV - bbnAlphaSynthesisGateLowMeV) / bbnAlphaSynthesisGateWidthMeV)

/-- C₂ bottleneck — physical end of active n+p / D synthesis (Python ``synthesis_window_end_mev``). -/
noncomputable def bbnSynthesisWindowEndMeV (η : ℝ) : ℝ :=
  bbnDynamicC2BottleneckT_MeV η

/-- D/H integration ladder low bound (through ``T_bn``; not the 10 keV CMB tail). -/
noncomputable def bbnSynthesisDWindowLowMeV (η : ℝ) : ℝ :=
  bbnSynthesisWindowEndMeV η

/-- D/H log-weight tail below the ³He mid-gate (Python ``synthesis_d_window_tail_gate``). -/
noncomputable def bbnSynthesisDWindowTailGate (T_MeV η : ℝ) : ℝ :=
  if T_MeV ≥ bbnHe3SynthesisMidMeV then 1
  else if T_MeV ≤ bbnDynamicC2BottleneckT_MeV η then 0
  else
    (T_MeV - bbnDynamicC2BottleneckT_MeV η)
      / (bbnHe3SynthesisMidMeV - bbnDynamicC2BottleneckT_MeV η)

/-- n+p→D gate: unity above the C₂ bottleneck (Python ``np_to_deuterium_synthesis_gate``). -/
noncomputable def bbnNpToDeuteriumSynthesisGate (T_MeV η : ℝ) : ℝ :=
  if T_MeV ≥ bbnDynamicC2BottleneckT_MeV η then 1
  else max 0 (T_MeV / max (bbnDynamicC2BottleneckT_MeV η) 1e-6)

/-- Strong-channel deposition boost on the D budget (Python ``synthesis_strong_deposition_boost``). -/
noncomputable def bbnSynthesisStrongDepositionBoost (gate_np c2 : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * strongChannelFraction * gamma_HQIV * (1 + gate_np + c2)

/-- ³He/H dedicated integration band (Python ``he3_synthesis_window_bounds_mev``). -/
def bbnHe3SynthesisWindowHighMeV : ℝ := bbnHe3SynthesisHighMeV
def bbnHe3SynthesisWindowLowMeV : ℝ := bbnHe3SynthesisLowMeV

theorem bbnSynthesisWindowEndMeV_eq_bottleneck (η : ℝ) :
    bbnSynthesisWindowEndMeV η = bbnDynamicC2BottleneckT_MeV η := rfl

theorem bbnSynthesisDWindowLowMeV_eq_bottleneck (η : ℝ) :
    bbnSynthesisDWindowLowMeV η = bbnDynamicC2BottleneckT_MeV η := rfl

#check bbnSynthesisDWindowTailGate
#check bbnHe3SynthesisGate
#check bbnHe3Be7FeedGate
#check bbnAlphaSynthesisGate
#check bbnNpToDeuteriumSynthesisGate
#check bbnSynthesisStrongDepositionBoost
#check bbnTrimerWidthStrongSuppressAtT

end

end Hqiv.Physics
