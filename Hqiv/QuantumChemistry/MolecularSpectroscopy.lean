import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Molecular spectroscopy bridge identities

Lean counterpart of `scripts/hqiv_molecular_spectroscopy.py`.

Spectroscopic constants are not new physics — they are the geometry of a binding
well the `nucleon_binding` chemistry engine already derives.  Given the three
HQIV-derived anchors

* equilibrium length `rₑ` (nested-WF covalent radii × monogamy `1 − α/2`),
* well depth `Dₑ` (inside curvature surplus + outside `G_eff(θ)` contact),
* reduced mass `μ` (cluster-mass spine + electron rest mass),

this module records the closed-form maps to the rovibrational constants and proves
the algebraic bridge identities that the Python readout relies on.  No fitted
coefficients and no empirical spectroscopic inputs appear here.
-/

namespace Hqiv.QuantumChemistry.MolecularSpectroscopy

noncomputable section

open Real

/-- Rotational constant `Bₑ = ħ / (4π c μ rₑ²)` (consistent units). -/
def rotationalConstant (hbar c mu rE : ℝ) : ℝ :=
  hbar / (4 * Real.pi * c * mu * rE ^ 2)

/-- Mie-well force constant: curvature `V''(rₑ)` of the monogamy ⊕ `G_eff` well,
`k = n_rep · m_att · Dₑ / rₑ²`.  `nRep = referenceM = 4` is the monogamy-core
hardness; `mAtt` is the covalent bond order (G_eff contacts). -/
def mieForceConstant (nRep mAtt dE rE : ℝ) : ℝ :=
  nRep * mAtt * dE / rE ^ 2

/-- Contact-length Morse force constant: width `a = 1/ℓ_c`, `k = 2 Dₑ a²`. -/
def contactMorseForceConstant (dE a : ℝ) : ℝ :=
  2 * dE * a ^ 2

/-- Primary force constant: curvature of the genuine backbone valley well anchored
to the derived depth, `k = Dₑ · curv / depth`, where `curv = V''(r_min)` and
`depth = |V(r_min)|` come from `valley_fold_energy_bohr` (no imposed Morse/Mie form;
the monogamy-core repulsive power lives inside that well as `(r_m/r)⁴`). -/
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

/-- Vibration–rotation coupling (Pekeris) `αₑ = 6 √(ωₑxₑ · Bₑ³)/ωₑ − 6 Bₑ²/ωₑ`.
A downstream second-order constant: it consumes only the already-derived `Bₑ`, `ωₑ`,
and `ωₑxₑ`, introducing no new input. -/
def vibrationRotationCoupling (omegaE omegaExe bE : ℝ) : ℝ :=
  6 * Real.sqrt (omegaExe * bE ^ 3) / omegaE - 6 * bE ^ 2 / omegaE

/-! ## Bridge identities -/

/-- Morse closure is exact: `(ωₑxₑ)·(4 Dₑ) = ωₑ²` whenever `Dₑ ≠ 0`. -/
theorem morseAnharmonicity_closure (omegaE dE : ℝ) (hD : dE ≠ 0) :
    morseAnharmonicity omegaE dE * (4 * dE) = omegaE ^ 2 := by
  unfold morseAnharmonicity
  field_simp

/-- Centrifugal distortion is `1/ωₑ²` at fixed `Bₑ`: a stiffer (higher `ωₑ`) well is
more rigid, distorting four-fold less when `ωₑ` doubles.  This is the downstream
behaviour the readout reports — `D_J` rides entirely on the derived `Bₑ` and `ωₑ`. -/
theorem centrifugalDistortion_quarter_with_double_omega
    (bE omegaE : ℝ) (hw : omegaE ≠ 0) :
    centrifugalDistortion bE (2 * omegaE) = centrifugalDistortion bE omegaE / 4 := by
  unfold centrifugalDistortion
  field_simp
  ring

/-- Pekeris coupling factors through `ωₑ`: `αₑ = (6/ωₑ)(√(ωₑxₑ·Bₑ³) − Bₑ²)`.  Makes the
single `ωₑ`-dependence of the downstream constant explicit. -/
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
`n_rep · m_att / rₑ² = 2 a²` holds — the internal cross-check the readout reports. -/
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

/-- The valley-anchored force constant is linear in the derived depth `Dₑ`: the
well *shape* (`curv`, `depth`) is fixed by the backbone potential, only the energy
scale rides on `Dₑ`. -/
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

/-! ## Curvature-concentration bracket

The geometry-first valley reads its curvature on the diffuse shell-ladder length
`r_m = m+1`; the same well evaluated on the *contracted* nested-WF contact length
`ℓ_c = R_m/(α_eff Z)` is stiffer.  These two derived readings bracket the measured
`ωₑ`; the in-bracket value is the not-yet-derived concentration flow (no fitted
factor).  The lemmas below record only the bracket *ordering* the readout uses:
shrinking the curvature length raises the stiffness, hence `ωₑ`. -/

/-- Curvature-length force constant at depth `Dₑ` and length scale `ℓ`:
`k = 2 Dₑ / ℓ²` (a width `a = 1/ℓ` Morse curvature). -/
def lengthScaledForceConstant (dE ell : ℝ) : ℝ := 2 * dE / ell ^ 2

/-- Concentrating the well (smaller length scale) never softens it:
for `0 < ℓ_conc ≤ ℓ_diff` and `Dₑ ≥ 0`, `k(ℓ_diff) ≤ k(ℓ_conc)`. -/
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

/-! ## Emergent single-generator route

The whole rovibrational well collapses to one geometric law: the dimensionless Morse
range `a·rₑ` equals the **accumulated lattice curvature** out to the bond contact
shell, scaled by the HQIV lattice constant `α = 3/5`:

`a·rₑ = 2α · ∫₁^{ξ} ρ_curv`.  With `k = 2 Dₑ a²` and `ωₑ ∝ √(k/μ)` every constant
(`ωₑxₑ`, `D_J`, `αₑ`, ZPE) then rides on the single accumulated-curvature input. -/

/-- Informational-monogamy spectator contact `1 + γ/2` (Lean `spectatorHalfMonogamyContact`,
also used in HEP decay routing): one monogamy detuning step dressing a single bond contact. -/
def monogamySpectatorContact (gamma : ℝ) : ℝ := 1 + gamma / 2

/-- At the HQIV lattice point (`α + γ = 1`, `γ = 2/5`) the monogamy spectator contact
coincides with `2α` and `3γ` — the three readings of the same `6/5`. -/
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

/-- Emergent Morse range `a·rₑ = (1 + γ/2) · C`, where `C = ∫₁^{ξ} ρ_curv` is the
accumulated lattice curvature to the contact shell and `1 + γ/2` is the monogamy
spectator contact (= `2α` at the lattice point). -/
def curvatureIntegralRange (gamma curvatureIntegral : ℝ) : ℝ :=
  monogamySpectatorContact gamma * curvatureIntegral

/-- Morse force constant from the emergent range: `k = 2 Dₑ (a·rₑ / rₑ)²`. -/
def curvatureIntegralForceConstant (dE gamma curvatureIntegral rE : ℝ) : ℝ :=
  2 * dE * (curvatureIntegralRange gamma curvatureIntegral / rE) ^ 2

/-- The emergent stiffness is linear in the depth `Dₑ` and quadratic in the
accumulated curvature `C`: doubling the curvature out to contact quadruples `k`. -/
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

/-! ### Occupancy resolution (the foundational bond-order term)

The atomic Compton shell `ξ_contact` is bond-order blind: N₂/O₂/F₂ collapse to the same
contact, yet their wells differ.  The resolution is a **monogamy spectator defect**
`defect ∈ {0,1}`: it is `1` when the net covalent bond order is below the p-shell
shared-channel capacity `2ℓ+1 = 3` (a sub-maximal p-block bond leaves one open channel,
e.g. O₂, F₂) and `0` for maximal closed-shell bonds (N₂/CO triple, H–X single).  A bond is
a single monogamy contact, so at most one spectator half-pair survives — the defect
*saturates* at one `γ/2` step, the same step that dresses the prefactor `1 + γ/2`.  The
accumulated contact curvature is then resolved by occupancy. -/

/-- Occupancy-resolved accumulated contact curvature
`C_eff = C + (γ/2)·defect`: the atomic-shell integral plus one informational-monogamy
spectator step when `defect = 1`. -/
def occupancyResolvedContactCurvature (gamma curvatureIntegral defect : ℝ) : ℝ :=
  curvatureIntegral + (gamma / 2) * defect

/-- Occupancy-resolved Morse range `a·rₑ = (1 + γ/2) · C_eff`. -/
def curvatureIntegralRangeResolved (gamma curvatureIntegral defect : ℝ) : ℝ :=
  monogamySpectatorContact gamma * occupancyResolvedContactCurvature gamma curvatureIntegral defect

/-- Maximal closed-shell bonds (`defect = 0`) reduce exactly to the pure
accumulated-curvature law: the contact sits on its atomic curvature shell. -/
theorem curvatureIntegralRangeResolved_maximal (gamma C : ℝ) :
    curvatureIntegralRangeResolved gamma C 0 = curvatureIntegralRange gamma C := by
  unfold curvatureIntegralRangeResolved occupancyResolvedContactCurvature curvatureIntegralRange
  ring

/-- The occupancy defect adds exactly one amplified spectator step
`(1 + γ/2)·(γ/2)` to the range — independent of `C`, and the *same* `γ/2` that scales the
prefactor.  This is the entire O₂/F₂ ↔ N₂ separation. -/
theorem curvatureIntegralRangeResolved_defect_step (gamma C : ℝ) :
    curvatureIntegralRangeResolved gamma C 1 - curvatureIntegralRangeResolved gamma C 0
      = monogamySpectatorContact gamma * (gamma / 2) := by
  unfold curvatureIntegralRangeResolved occupancyResolvedContactCurvature
  ring

/-- An open channel never softens the well: with `γ ≥ 0` and a genuine spectator
(`defect = 1 ≥ 0`) the resolved range is at least the maximal-bond range. -/
theorem curvatureIntegralRangeResolved_ge_maximal
    (gamma C : ℝ) (hg : 0 ≤ gamma) :
    curvatureIntegralRange gamma C ≤ curvatureIntegralRangeResolved gamma C 1 := by
  rw [← curvatureIntegralRangeResolved_maximal gamma C]
  unfold curvatureIntegralRangeResolved occupancyResolvedContactCurvature monogamySpectatorContact
  have hpref : 0 ≤ 1 + gamma / 2 := by linarith
  have hstep : 0 ≤ gamma / 2 := by linarith
  nlinarith [mul_nonneg hpref hstep]

/-- Curvature-dielectric concentration weight: the outside/inside curvature ratio
`n = ρ_curv(ℓ_in)/ρ_curv(r_m_out)` acts as a dielectric `ε`, and the bracket position
is its Clausius–Mossotti polarization fraction `s = (n − 1)/(n + 2)` — the same
functional the optical refractive-index readout uses. -/
def curvatureConcentrationWeight (n : ℝ) : ℝ := (n - 1) / (n + 2)

/-- An uncontracted contact (`n = 1`, inside as curved as outside) sits exactly on the
diffuse edge: `s = 0`. -/
theorem curvatureConcentrationWeight_unit :
    curvatureConcentrationWeight 1 = 0 := by
  unfold curvatureConcentrationWeight; norm_num

/-- `s = 1 − 3/(n+2)`: the closed form that makes the bracket bounds transparent. -/
theorem curvatureConcentrationWeight_eq (n : ℝ) (hn : 1 ≤ n) :
    curvatureConcentrationWeight n = 1 - 3 / (n + 2) := by
  unfold curvatureConcentrationWeight
  have hpos : n + 2 ≠ 0 := by linarith
  field_simp
  ring

/-- For any physical dielectric `n ≥ 1` the weight is a genuine bracket fraction:
`0 ≤ s < 1`. -/
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

/-- Harmonic wavenumber is monotone in the force constant at fixed `c, μ > 0`:
a stiffer (more concentrated) well reports a higher `ωₑ`. -/
theorem harmonicWavenumber_mono_in_k
    (c mu k1 k2 : ℝ) (hc : 0 < c) (hmu : 0 < mu) (_hk1 : 0 ≤ k1) (hle : k1 ≤ k2) :
    harmonicWavenumber c k1 mu ≤ harmonicWavenumber c k2 mu := by
  unfold harmonicWavenumber
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpref : 0 ≤ 1 / (2 * Real.pi * c) := by positivity
  apply mul_le_mul_of_nonneg_left _ hpref
  apply Real.sqrt_le_sqrt
  gcongr

/-! ## Valence-bond covalent↔ionic resonance (charge-transfer coordinate)

A bond is a superposition `ψ = c_cov ψ_cov + c_ion ψ_ion` of a stiff covalent overlap and a
softer long-range ionic (Coulomb) structure.  The observable force constant is the resonance
average `k_eff = (1 − w)·k_cov + w·k_ion`, where the ionic curvature is the point-charge
Born–Landé value `k_ion = (n_rep − 1)·k_C / rₑ³` with the *same* monogamy-core power
`n_rep = referenceM = 4` (no new constant), and the ionic character `w = δ²` is the squared
native electron-pull asymmetry `δ = |p_i − p_j|/(p_i + p_j)` with
`p = z_eff/(m+1)` the inverse nested-WF contact radius on the correct multi-electron valence
shell (Python `hqiv_atom_construction.valence_electron_pull`).  Homonuclear bonds have `w = 0`,
so the resonance leaves them on the bare covalent generator. -/

/-- Born–Landé point-charge ionic curvature `k_ion = (n_rep − 1)·k_C / rₑ³`. -/
def ionicForceConstant (nRep kCoulomb rE : ℝ) : ℝ :=
  (nRep - 1) * kCoulomb / rE ^ 3

/-- Native electron-pull asymmetry `δ = |p_i − p_j|/(p_i + p_j)`. -/
def pullAsymmetry (pI pJ : ℝ) : ℝ := |pI - pJ| / (pI + pJ)

/-- Valence-bond ionic character `w = δ²` (a probability, the squared charge partition). -/
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

/-- Therefore a homonuclear bond reports the bare covalent generator — N₂/O₂/F₂/H₂ are
untouched by the resonance. -/
theorem ionicResonance_eq_covalent_of_homonuclear (kCov kIon p : ℝ) :
    ionicResonanceForceConstant kCov kIon (bondIonicCharacter p p) = kCov := by
  rw [bondIonicCharacter_homonuclear, ionicResonanceForceConstant_covalent_at_zero]

/-- The resonance is a genuine convex bracket: a softer ionic well (`k_ion ≤ k_cov`) with
character `w ∈ [0,1]` gives `k_ion ≤ k_eff ≤ k_cov`.  This is exactly the softening the
readout applies to polar/ionic bonds while never crossing past the covalent stiffness. -/
theorem ionicResonanceForceConstant_brackets
    (kCov kIon w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hle : kIon ≤ kCov) :
    kIon ≤ ionicResonanceForceConstant kCov kIon w ∧
      ionicResonanceForceConstant kCov kIon w ≤ kCov := by
  unfold ionicResonanceForceConstant
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hle)]
  · nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hle)]

end

end Hqiv.QuantumChemistry.MolecularSpectroscopy
