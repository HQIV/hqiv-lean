import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Spectroscopy` — rovibrational constants from the binding well

Spectroscopic constants are the geometry of the derived binding well, not new physics. Given the
three derived anchors — equilibrium length `rₑ`, well depth `Dₑ` (the dissociation/binding energy),
and reduced mass `μ` — this module records the closed-form maps to the rovibrational constants and
proves the algebraic bridge identities they obey:

* force constants by several routes (Mie, contact-Morse, valley-anchored, accumulated-curvature,
  Born–Landé ionic) and the exact condition for two routes to agree (`forceConstants_agree_iff`);
* harmonic wavenumber `ωₑ` and its monotonicity in stiffness; Morse anharmonicity closure
  `ωₑxₑ·4Dₑ = ωₑ²`; centrifugal distortion, zero-point energy, Pekeris vibration–rotation coupling;
* the VB covalent↔ionic resonance as a convex bracket `k_ion ≤ k_eff ≤ k_cov`, with homonuclear
  bonds carrying zero ionic character.

No fitted coefficients and no empirical spectroscopic inputs. Mathlib-only; no legacy `Hqiv.*`,
no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Spectroscopy

noncomputable section

open Real

/-- Rotational constant `Bₑ = ħ / (4π c μ rₑ²)`. -/
def rotationalConstant (hbar c mu rE : ℝ) : ℝ :=
  hbar / (4 * Real.pi * c * mu * rE ^ 2)

/-- Mie-well force constant `k = n_rep · m_att · Dₑ / rₑ²` (`nRep = referenceM = 4` monogamy-core
hardness, `mAtt` the covalent bond order). -/
def mieForceConstant (nRep mAtt dE rE : ℝ) : ℝ :=
  nRep * mAtt * dE / rE ^ 2

/-- Contact-length Morse force constant: width `a = 1/ℓ_c`, `k = 2 Dₑ a²`. -/
def contactMorseForceConstant (dE a : ℝ) : ℝ :=
  2 * dE * a ^ 2

/-- Valley-anchored force constant `k = Dₑ · curv / depth`. -/
def valleyAnchoredForceConstant (dE curv depth : ℝ) : ℝ :=
  dE * curv / depth

/-- Harmonic wavenumber `ωₑ = (1/2π c) √(k/μ)`. -/
def harmonicWavenumber (c k mu : ℝ) : ℝ :=
  (1 / (2 * Real.pi * c)) * Real.sqrt (k / mu)

/-- The reported `ωₑ` is the geometric mean of the two independent route values. -/
def omegaGeoMean (w1 w2 : ℝ) : ℝ := Real.sqrt (w1 * w2)

/-- Morse anharmonicity closure `ωₑxₑ = ωₑ² / (4 Dₑ)`. -/
def morseAnharmonicity (omegaE dE : ℝ) : ℝ := omegaE ^ 2 / (4 * dE)

/-- Centrifugal distortion `D_J = 4 Bₑ³ / ωₑ²`. -/
def centrifugalDistortion (bE omegaE : ℝ) : ℝ := 4 * bE ^ 3 / omegaE ^ 2

/-- Zero-point energy `½ ωₑ − ¼ ωₑxₑ`. -/
def zeroPointEnergy (omegaE omegaExe : ℝ) : ℝ := omegaE / 2 - omegaExe / 4

/-- Vibration–rotation coupling (Pekeris) `αₑ = 6 √(ωₑxₑ·Bₑ³)/ωₑ − 6 Bₑ²/ωₑ`. -/
def vibrationRotationCoupling (omegaE omegaExe bE : ℝ) : ℝ :=
  6 * Real.sqrt (omegaExe * bE ^ 3) / omegaE - 6 * bE ^ 2 / omegaE

/-! ## Bridge identities -/

/-- Morse closure is exact: `(ωₑxₑ)·(4 Dₑ) = ωₑ²` whenever `Dₑ ≠ 0`. -/
theorem morseAnharmonicity_closure (omegaE dE : ℝ) (hD : dE ≠ 0) :
    morseAnharmonicity omegaE dE * (4 * dE) = omegaE ^ 2 := by
  unfold morseAnharmonicity
  field_simp

/-- Centrifugal distortion is `1/ωₑ²` at fixed `Bₑ`: a stiffer well is more rigid, distorting
four-fold less when `ωₑ` doubles. -/
theorem centrifugalDistortion_quarter_with_double_omega
    (bE omegaE : ℝ) (hw : omegaE ≠ 0) :
    centrifugalDistortion bE (2 * omegaE) = centrifugalDistortion bE omegaE / 4 := by
  unfold centrifugalDistortion
  field_simp
  ring

/-- Pekeris coupling factors through `ωₑ`: `αₑ = (6/ωₑ)(√(ωₑxₑ·Bₑ³) − Bₑ²)`. -/
theorem vibrationRotationCoupling_factor
    (omegaE omegaExe bE : ℝ) (hw : omegaE ≠ 0) :
    vibrationRotationCoupling omegaE omegaExe bE
      = 6 / omegaE * (Real.sqrt (omegaExe * bE ^ 3) - bE ^ 2) := by
  unfold vibrationRotationCoupling
  field_simp

/-- The rotational constant scales as `1/μ` at fixed geometry. -/
theorem rotationalConstant_halves_with_double_mass
    (hbar c mu rE : ℝ) (hc : c ≠ 0) (hmu : mu ≠ 0) (hrE : rE ≠ 0) :
    rotationalConstant hbar c (2 * mu) rE = rotationalConstant hbar c mu rE / 2 := by
  unfold rotationalConstant
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The rotational constant scales as `1/rₑ²` at fixed mass. -/
theorem rotationalConstant_quarters_with_double_length
    (hbar c mu rE : ℝ) (hc : c ≠ 0) (hmu : mu ≠ 0) (hrE : rE ≠ 0) :
    rotationalConstant hbar c mu (2 * rE) = rotationalConstant hbar c mu rE / 4 := by
  unfold rotationalConstant
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The two force-constant routes agree exactly iff the structural relation
`n_rep · m_att / rₑ² = 2 a²` holds. -/
theorem forceConstants_agree_iff
    (nRep mAtt dE rE a : ℝ) (hD : dE ≠ 0) (hrE : rE ≠ 0) :
    mieForceConstant nRep mAtt dE rE = contactMorseForceConstant dE a ↔
      nRep * mAtt / rE ^ 2 = 2 * a ^ 2 := by
  unfold mieForceConstant contactMorseForceConstant
  have hrE2 : rE ^ 2 ≠ 0 := pow_ne_zero 2 hrE
  rw [div_eq_iff hrE2, div_eq_iff hrE2]
  constructor
  · intro h
    have h' : dE * (nRep * mAtt) = dE * (2 * a ^ 2 * rE ^ 2) := by linear_combination h
    exact mul_left_cancel₀ hD h'
  · intro h
    rw [h]; ring

/-- The valley-anchored force constant is linear in the derived depth `Dₑ`. -/
theorem valleyAnchoredForceConstant_linear_in_depthScale
    (t dE curv depth : ℝ) :
    valleyAnchoredForceConstant (t * dE) curv depth =
      t * valleyAnchoredForceConstant dE curv depth := by
  unfold valleyAnchoredForceConstant
  ring

/-- Geometric-mean route is symmetric in its two inputs. -/
theorem omegaGeoMean_comm (w1 w2 : ℝ) : omegaGeoMean w1 w2 = omegaGeoMean w2 w1 := by
  unfold omegaGeoMean; rw [mul_comm]

/-- For nonnegative routes the geometric mean squares back to the product. -/
theorem omegaGeoMean_sq (w1 w2 : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) :
    omegaGeoMean w1 w2 ^ 2 = w1 * w2 := by
  unfold omegaGeoMean
  exact Real.sq_sqrt (mul_nonneg h1 h2)

/-! ## Curvature-concentration bracket -/

/-- Curvature-length force constant at depth `Dₑ` and length scale `ℓ`: `k = 2 Dₑ / ℓ²`. -/
def lengthScaledForceConstant (dE ell : ℝ) : ℝ := 2 * dE / ell ^ 2

/-- Concentrating the well (smaller length scale) never softens it. -/
theorem lengthScaledForceConstant_mono
    (dE ellConc ellDiff : ℝ) (hD : 0 ≤ dE)
    (hConc : 0 < ellConc) (hle : ellConc ≤ ellDiff) :
    lengthScaledForceConstant dE ellDiff ≤ lengthScaledForceConstant dE ellConc := by
  unfold lengthScaledForceConstant
  have hDiff : 0 < ellDiff := lt_of_lt_of_le hConc hle
  have hsq : ellConc ^ 2 ≤ ellDiff ^ 2 := by
    have := mul_le_mul hle hle hConc.le hDiff.le
    simpa [pow_two] using this
  have hcsq : 0 < ellConc ^ 2 := pow_pos hConc 2
  have h2D : 0 ≤ 2 * dE := by positivity
  gcongr

/-! ## Emergent single-generator route -/

/-- Informational-monogamy spectator contact `1 + γ/2`. -/
def monogamySpectatorContact (gamma : ℝ) : ℝ := 1 + gamma / 2

/-- At the HQIV lattice point (`α + γ = 1`, `γ = 2/5`) the monogamy spectator contact coincides
with `2α`. -/
theorem monogamySpectatorContact_eq_twoAlpha
    (alpha gamma : ℝ) (hsum : alpha + gamma = 1) (hg : gamma = 2 / 5) :
    monogamySpectatorContact gamma = 2 * alpha := by
  unfold monogamySpectatorContact
  have ha : alpha = 3 / 5 := by linarith
  rw [ha, hg]; norm_num

theorem monogamySpectatorContact_eq_threeGamma
    (gamma : ℝ) (hg : gamma = 2 / 5) :
    monogamySpectatorContact gamma = 3 * gamma := by
  unfold monogamySpectatorContact; rw [hg]; norm_num

/-- Emergent Morse range `a·rₑ = (1 + γ/2) · C`, `C = ∫₁^{ξ} ρ_curv` the accumulated lattice
curvature to the contact shell. -/
def curvatureIntegralRange (gamma curvatureIntegral : ℝ) : ℝ :=
  monogamySpectatorContact gamma * curvatureIntegral

/-- Morse force constant from the emergent range: `k = 2 Dₑ (a·rₑ / rₑ)²`. -/
def curvatureIntegralForceConstant (dE gamma curvatureIntegral rE : ℝ) : ℝ :=
  2 * dE * (curvatureIntegralRange gamma curvatureIntegral / rE) ^ 2

/-- The emergent stiffness is quadratic in the accumulated curvature `C`. -/
theorem curvatureIntegralForceConstant_scales
    (dE gamma C rE : ℝ) (hrE : rE ≠ 0) :
    curvatureIntegralForceConstant dE gamma (2 * C) rE
      = 4 * curvatureIntegralForceConstant dE gamma C rE := by
  unfold curvatureIntegralForceConstant curvatureIntegralRange
  field_simp
  ring

/-- Pinning to the derived depth keeps the shape fixed: `k` is linear in `Dₑ`. -/
theorem curvatureIntegralForceConstant_linear_in_depth
    (t dE gamma C rE : ℝ) :
    curvatureIntegralForceConstant (t * dE) gamma C rE
      = t * curvatureIntegralForceConstant dE gamma C rE := by
  unfold curvatureIntegralForceConstant curvatureIntegralRange
  ring

/-! ### Occupancy resolution (bond-order term) -/

/-- Occupancy-resolved accumulated contact curvature `C_eff = C + (γ/2)·defect`. -/
def occupancyResolvedContactCurvature (gamma curvatureIntegral defect : ℝ) : ℝ :=
  curvatureIntegral + (gamma / 2) * defect

/-- Occupancy-resolved Morse range `a·rₑ = (1 + γ/2) · C_eff`. -/
def curvatureIntegralRangeResolved (gamma curvatureIntegral defect : ℝ) : ℝ :=
  monogamySpectatorContact gamma * occupancyResolvedContactCurvature gamma curvatureIntegral defect

/-- Maximal closed-shell bonds (`defect = 0`) reduce to the pure accumulated-curvature law. -/
theorem curvatureIntegralRangeResolved_maximal (gamma C : ℝ) :
    curvatureIntegralRangeResolved gamma C 0 = curvatureIntegralRange gamma C := by
  unfold curvatureIntegralRangeResolved occupancyResolvedContactCurvature curvatureIntegralRange
  ring

/-- The occupancy defect adds exactly one amplified spectator step `(1 + γ/2)·(γ/2)`. -/
theorem curvatureIntegralRangeResolved_defect_step (gamma C : ℝ) :
    curvatureIntegralRangeResolved gamma C 1 - curvatureIntegralRangeResolved gamma C 0
      = monogamySpectatorContact gamma * (gamma / 2) := by
  unfold curvatureIntegralRangeResolved occupancyResolvedContactCurvature
  ring

/-- An open channel never softens the well: a genuine spectator only lengthens the range. -/
theorem curvatureIntegralRangeResolved_ge_maximal
    (gamma C : ℝ) (hg : 0 ≤ gamma) :
    curvatureIntegralRange gamma C ≤ curvatureIntegralRangeResolved gamma C 1 := by
  rw [← curvatureIntegralRangeResolved_maximal gamma C]
  unfold curvatureIntegralRangeResolved occupancyResolvedContactCurvature monogamySpectatorContact
  have hpref : 0 ≤ 1 + gamma / 2 := by linarith
  have hstep : 0 ≤ gamma / 2 := by linarith
  nlinarith [mul_nonneg hpref hstep]

/-- Curvature-dielectric concentration weight `s = (n − 1)/(n + 2)` (Clausius–Mossotti). -/
def curvatureConcentrationWeight (n : ℝ) : ℝ := (n - 1) / (n + 2)

theorem curvatureConcentrationWeight_unit :
    curvatureConcentrationWeight 1 = 0 := by
  unfold curvatureConcentrationWeight; norm_num

/-- `s = 1 − 3/(n+2)`. -/
theorem curvatureConcentrationWeight_eq (n : ℝ) (hn : 1 ≤ n) :
    curvatureConcentrationWeight n = 1 - 3 / (n + 2) := by
  unfold curvatureConcentrationWeight
  have hpos : n + 2 ≠ 0 := by linarith
  field_simp
  ring

/-- For any physical dielectric `n ≥ 1` the weight is a genuine bracket fraction: `0 ≤ s < 1`. -/
theorem curvatureConcentrationWeight_mem_Ico (n : ℝ) (hn : 1 ≤ n) :
    0 ≤ curvatureConcentrationWeight n ∧ curvatureConcentrationWeight n < 1 := by
  have hpos : 0 < n + 2 := by linarith
  rw [curvatureConcentrationWeight_eq n hn]
  constructor
  · have : 3 / (n + 2) ≤ 1 := by rw [div_le_one hpos]; linarith
    linarith
  · have : 0 < 3 / (n + 2) := by positivity
    linarith

/-- More curvature contrast ⇒ more concentration: `s` is monotone in the dielectric. -/
theorem curvatureConcentrationWeight_mono
    (n₁ n₂ : ℝ) (h₁ : 1 ≤ n₁) (hle : n₁ ≤ n₂) :
    curvatureConcentrationWeight n₁ ≤ curvatureConcentrationWeight n₂ := by
  rw [curvatureConcentrationWeight_eq n₁ h₁, curvatureConcentrationWeight_eq n₂ (le_trans h₁ hle)]
  have h1 : 0 < n₁ + 2 := by linarith
  have h2 : 0 < n₂ + 2 := by linarith
  have : 3 / (n₂ + 2) ≤ 3 / (n₁ + 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) h1
    linarith
  linarith

/-- Harmonic wavenumber is monotone in the force constant at fixed `c, μ > 0`. -/
theorem harmonicWavenumber_mono_in_k
    (c mu k1 k2 : ℝ) (hc : 0 < c) (hmu : 0 < mu) (_hk1 : 0 ≤ k1) (hle : k1 ≤ k2) :
    harmonicWavenumber c k1 mu ≤ harmonicWavenumber c k2 mu := by
  unfold harmonicWavenumber
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpref : 0 ≤ 1 / (2 * Real.pi * c) := by positivity
  apply mul_le_mul_of_nonneg_left _ hpref
  apply Real.sqrt_le_sqrt
  gcongr

/-! ## Valence-bond covalent↔ionic resonance -/

/-- Born–Landé point-charge ionic curvature `k_ion = (n_rep − 1)·k_C / rₑ³`. -/
def ionicForceConstant (nRep kCoulomb rE : ℝ) : ℝ :=
  (nRep - 1) * kCoulomb / rE ^ 3

/-- Native electron-pull asymmetry `δ = |p_i − p_j|/(p_i + p_j)`. -/
def pullAsymmetry (pI pJ : ℝ) : ℝ := |pI - pJ| / (pI + pJ)

/-- Valence-bond ionic character `w = δ²`. -/
def bondIonicCharacter (pI pJ : ℝ) : ℝ := pullAsymmetry pI pJ ^ 2

/-- VB covalent↔ionic resonance force constant `k_eff = (1 − w)·k_cov + w·k_ion`. -/
def ionicResonanceForceConstant (kCov kIon w : ℝ) : ℝ :=
  (1 - w) * kCov + w * kIon

/-- Homonuclear bonds (`p_i = p_j`) carry zero ionic character. -/
theorem bondIonicCharacter_homonuclear (p : ℝ) : bondIonicCharacter p p = 0 := by
  unfold bondIonicCharacter pullAsymmetry
  simp

/-- Ionic character is always nonnegative (a squared partition fraction). -/
theorem bondIonicCharacter_nonneg (pI pJ : ℝ) : 0 ≤ bondIonicCharacter pI pJ := by
  unfold bondIonicCharacter
  positivity

/-- At zero ionic character the resonance is exactly the covalent force constant. -/
theorem ionicResonanceForceConstant_covalent_at_zero (kCov kIon : ℝ) :
    ionicResonanceForceConstant kCov kIon 0 = kCov := by
  unfold ionicResonanceForceConstant; ring

/-- A homonuclear bond reports the bare covalent generator. -/
theorem ionicResonance_eq_covalent_of_homonuclear (kCov kIon p : ℝ) :
    ionicResonanceForceConstant kCov kIon (bondIonicCharacter p p) = kCov := by
  rw [bondIonicCharacter_homonuclear, ionicResonanceForceConstant_covalent_at_zero]

/-- The resonance is a genuine convex bracket: `k_ion ≤ k_eff ≤ k_cov` for `w ∈ [0,1]` and a softer
ionic well. -/
theorem ionicResonanceForceConstant_brackets
    (kCov kIon w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hle : kIon ≤ kCov) :
    kIon ≤ ionicResonanceForceConstant kCov kIon w ∧
      ionicResonanceForceConstant kCov kIon w ≤ kCov := by
  unfold ionicResonanceForceConstant
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hle)]
  · nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hle)]

end

end HqivSpine.Chemistry.Spectroscopy
