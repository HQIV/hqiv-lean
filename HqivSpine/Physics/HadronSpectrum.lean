import HqivSpine.Physics.MassLadder

/-!
# `HqivSpine.Physics.HadronSpectrum` — meson/baryon ratios off the mass ladder

`MassLadder` built the proton-normalised mass ladder; this module reads off the **structural,
PDG-free ratios** between species. Every hadron ground mass factors as a positive "core"
(`constituent − network binding`) times the closure-rank intrinsic scale:

* **Mass = core × scale.** `hadronGroundMassMeV = (μ − E_bind)·scale(h)` exactly
  (`hadronGroundMassMeV_eq_core`), so a hadron's mass is its shared core times a structural factor.
* **Meson : baryon = 4/9.** The closure-rank ratio is `4/9` independent of the core
  (`intrinsicScale_meson_over_baryon`, `meson_baryon_ratio`), and the baryon is always heavier at a
  positive shared core (`baryon_heavier_than_meson`) — colour confinement built into the network
  weights, never a fitted potential.
* **Lepton Beltrami ladder (chart spectral).** On bare `λ_min(n)=n+1`, `(τ:μ)·(μ:e) = 4/3 · 3/2 = 2`
  (`generation_steps_compose`, `leptonSpectralRatio_tau_e`). Absolute fermion readouts use
  `GenerationResonanceLadder` instead (`LeptonAbsoluteScale`).

All ratios are ratios of the structural integers `{1,2,3}` — no top/bottom anchor, no electroweak
vev, no PDG mass table.

Bundled in `HadronSpectrumClosure` / `hadron_spectrum_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.HadronSpectrum

open HqivSpine.Physics

/-! ## Mass = core × intrinsic scale -/

/-- **Reduced hadron mass:** a shared positive core (`constituent − binding`) scaled by the
closure-rank intrinsic factor `scale(baryon)=1`, `scale(meson)=4/9`. -/
noncomputable def hadronMassFromCore (core : ℝ) (h : HadronStructure) : ℝ :=
  core * hadronIntrinsicScale h

theorem hadronMassFromCore_baryon (core : ℝ) : hadronMassFromCore core .baryon = core := by
  rw [hadronMassFromCore, hadronIntrinsicScale_baryon, mul_one]

theorem hadronMassFromCore_meson (core : ℝ) :
    hadronMassFromCore core .meson = core * (4 / 9) := by
  rw [hadronMassFromCore, hadronIntrinsicScale_meson]

/-- The full ladder mass **is** the core times the intrinsic scale. -/
theorem hadronGroundMassMeV_eq_core
    (m : ℕ) (constituentMeV : ℝ) (h : HadronStructure) (vq : ℕ)
    (diag : So8TraceDiagonal) (state : OctonionState) (c : ℝ) :
    hadronGroundMassMeV m constituentMeV h vq diag state c =
      hadronMassFromCore (constituentMeV - hadronBindingMeV m vq diag state c) h := rfl

/-! ## The meson : baryon ratio -/

/-- **Meson : baryon closure-rank ratio = 4/9.** -/
theorem intrinsicScale_meson_over_baryon :
    hadronIntrinsicScale .meson / hadronIntrinsicScale .baryon = (4 : ℝ) / 9 := by
  rw [hadronIntrinsicScale_meson, hadronIntrinsicScale_baryon, div_one]

/-- The meson : baryon **mass** ratio is `4/9`, independent of the shared core. -/
theorem meson_baryon_ratio {core : ℝ} (h : core ≠ 0) :
    hadronMassFromCore core .meson / hadronMassFromCore core .baryon = (4 : ℝ) / 9 := by
  unfold hadronMassFromCore
  rw [hadronIntrinsicScale_meson, hadronIntrinsicScale_baryon, mul_div_mul_left _ _ h, div_one]

/-- **The baryon is heavier than the meson** at any positive shared core (confinement is built
into the closure rank, not a fitted potential). -/
theorem baryon_heavier_than_meson {core : ℝ} (hc : 0 < core) :
    hadronMassFromCore core .meson < hadronMassFromCore core .baryon := by
  unfold hadronMassFromCore
  rw [hadronIntrinsicScale_meson, hadronIntrinsicScale_baryon, mul_one]
  nlinarith [hc]

/-! ## Lepton generation ladder -/

/-- **τ : e step = 2.** -/
theorem leptonSpectralRatio_tau_e : leptonSpectralRatio 3 1 = 2 := by
  rw [leptonSpectralRatio, beltramiMinEigenvalue_eq_succ, beltramiMinEigenvalue_eq_succ]
  norm_num

theorem generation_steps_compose :
    leptonSpectralRatio 3 2 * leptonSpectralRatio 2 1 = leptonSpectralRatio 3 1 := by
  rw [leptonSpectralRatio_tau_e, leptonSpectralRatio_tau_mu, leptonSpectralRatio_mu_e]
  norm_num

/-! ## Closure -/

/-- **Hadron-spectrum discharge bundle.** -/
structure HadronSpectrumClosure : Prop where
  mass_is_core_times_scale : ∀ (m : ℕ) (μ : ℝ) (h : HadronStructure) (vq : ℕ)
    (diag : So8TraceDiagonal) (state : OctonionState) (c : ℝ),
    hadronGroundMassMeV m μ h vq diag state c =
      hadronMassFromCore (μ - hadronBindingMeV m vq diag state c) h
  meson_baryon_closure_ratio :
    hadronIntrinsicScale .meson / hadronIntrinsicScale .baryon = (4 : ℝ) / 9
  baryon_heavier : ∀ {core : ℝ}, 0 < core →
    hadronMassFromCore core .meson < hadronMassFromCore core .baryon
  generations_compose :
    leptonSpectralRatio 3 2 * leptonSpectralRatio 2 1 = leptonSpectralRatio 3 1

/-- **The hadron spectrum is discharged:** every mass is a core times a structural closure factor,
the meson : baryon ratio is the PDG-free `4/9` with the baryon heavier, and the bare Beltrami
lepton spectral steps compose `(τ:μ)·(μ:e) = (τ:e) = 2`. -/
theorem hadron_spectrum_closure : HadronSpectrumClosure where
  mass_is_core_times_scale := hadronGroundMassMeV_eq_core
  meson_baryon_closure_ratio := intrinsicScale_meson_over_baryon
  baryon_heavier := baryon_heavier_than_meson
  generations_compose := generation_steps_compose

end HqivSpine.Physics.HadronSpectrum
