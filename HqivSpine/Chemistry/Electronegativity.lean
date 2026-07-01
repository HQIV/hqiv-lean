import HqivSpine.Chemistry.Binding
import HqivSpine.Chemistry.Spectroscopy
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Electronegativity` — Mulliken χ from the hydrogenic ladder

`Chemistry.Spectroscopy` left the **electron pull** `p` in `bondIonicCharacter`/`pullAsymmetry`
abstract precisely so a derived electronegativity could be substituted. This module supplies it: the
**Mulliken electronegativity** `χ = (IE + EA)/2`, with both the ionization energy `IE` and the
electron affinity `EA` read off the spine's hydrogenic binding `Binding.hydrogenicBindingHartree
μ z n = μ z²/(2n²)`. No empirical electronegativity table is injected — `χ` is a function of the
reduced mass, the (Slater) effective charge, and the valence shell only.

What is proved:

* `mullikenChi_eq` — the closed form `χ = μ(z_ion² + z_aff²)/(4n²)`, and `atomElectronegativity_eq_ionization`
  (the uniform-charge Mulliken value is just the hydrogenic IE).
* `electronegativity_strictMono_in_zEff` — **the periodic trend**: at fixed valence shell, χ strictly
  increases with the effective nuclear charge `z_eff` (left→right across a period, where Slater
  `z_eff` rises), and `electronegativity_antitone_in_shell` (down a group, larger `n` lowers χ).
* `bondIonicCharacterChi` feeding `Spectroscopy.bondIonicCharacter`: `pure_covalent_iff_equal_chi`
  (zero ionic character ⇔ equal electronegativity) and `polar_bond_of_distinct_zEff`.
* `atomElectronegativityAufbau` tied to the derived `Binding.slaterEffectiveChargeAufbau`, with the
  unit-charge floor `atomElectronegativityAufbau_ge_hydrogenFloor`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Electronegativity

open HqivSpine.Chemistry

noncomputable section

/-- Ionization energy of the valence electron: its hydrogenic binding magnitude `μ z²/(2n²)`. -/
def ionizationEnergy (μ z n : ℝ) : ℝ := Binding.hydrogenicBindingHartree μ z n

/-- Electron affinity: the hydrogenic binding magnitude released when the extra electron is bound at
its (screened) effective charge. -/
def electronAffinity (μ z n : ℝ) : ℝ := Binding.hydrogenicBindingHartree μ z n

/-- **Mulliken electronegativity** `χ = (IE + EA)/2`, with `z_ion`/`z_aff` the effective charges
seen on removal/addition. -/
def mullikenChi (μ zIon zAff n : ℝ) : ℝ :=
  (ionizationEnergy μ zIon n + electronAffinity μ zAff n) / 2

/-- Closed form `χ = μ (z_ion² + z_aff²)/(4 n²)`. -/
theorem mullikenChi_eq (μ zIon zAff n : ℝ) :
    mullikenChi μ zIon zAff n = μ * (zIon ^ 2 + zAff ^ 2) / (4 * n ^ 2) := by
  unfold mullikenChi ionizationEnergy electronAffinity Binding.hydrogenicBindingHartree; ring

/-- An atom's electronegativity at a single effective charge `z` (removal and addition see the same
charge): `χ(z) = μ z²/(2n²)`. -/
def atomElectronegativity (μ z n : ℝ) : ℝ := mullikenChi μ z z n

/-- The uniform-charge Mulliken value is exactly the hydrogenic ionization energy. -/
theorem atomElectronegativity_eq_ionization (μ z n : ℝ) :
    atomElectronegativity μ z n = ionizationEnergy μ z n := by
  unfold atomElectronegativity mullikenChi ionizationEnergy electronAffinity; ring

theorem atomElectronegativity_eq (μ z n : ℝ) :
    atomElectronegativity μ z n = μ * z ^ 2 / (2 * n ^ 2) := by
  unfold atomElectronegativity; rw [mullikenChi_eq]; ring

theorem atomElectronegativity_nonneg (μ z n : ℝ) (hμ : 0 ≤ μ) :
    0 ≤ atomElectronegativity μ z n := by
  rw [atomElectronegativity_eq]; positivity

/-- **The periodic trend.** At a fixed valence shell `n`, electronegativity is strictly increasing in
the effective nuclear charge `z_eff` — so across a period (where Slater `z_eff` rises, e.g.
`C < N < O < F`) χ rises left→right. -/
theorem electronegativity_strictMono_in_zEff (μ n zA zB : ℝ)
    (hμ : 0 < μ) (hn : n ≠ 0) (hzA : 0 ≤ zA) (hlt : zA < zB) :
    atomElectronegativity μ zA n < atomElectronegativity μ zB n := by
  rw [atomElectronegativity_eq, atomElectronegativity_eq]
  have hn2 : 0 < n ^ 2 := by rcases lt_or_gt_of_ne hn with h | h <;> nlinarith
  have hden : 0 < 2 * n ^ 2 := by linarith
  have hzsq : zA ^ 2 < zB ^ 2 := by nlinarith
  have hpos : 0 < (μ * zB ^ 2 - μ * zA ^ 2) / (2 * n ^ 2) :=
    div_pos (by nlinarith [mul_pos hμ (sub_pos.mpr hzsq)]) hden
  rw [← div_sub_div_same] at hpos
  linarith

/-- **The group trend.** At fixed effective charge, a larger valence shell `n` lowers χ — so down a
group (larger `n`) the atom is less electronegative. -/
theorem electronegativity_antitone_in_shell (μ z nA nB : ℝ)
    (hμ : 0 < μ) (hz : z ≠ 0) (hnA : 0 < nA) (hlt : nA < nB) :
    atomElectronegativity μ z nB < atomElectronegativity μ z nA := by
  rw [atomElectronegativity_eq, atomElectronegativity_eq]
  have hz2 : 0 < z ^ 2 := by rcases lt_or_gt_of_ne hz with h | h <;> nlinarith
  have hnA2 : 0 < 2 * nA ^ 2 := by nlinarith
  exact div_lt_div_of_pos_left (mul_pos hμ hz2) hnA2 (by nlinarith)

/-! ## Bond ionic character from the derived electronegativities -/

/-- Valence-bond ionic character of a bond between atoms at effective charges `zA`, `zB` (same shell
`n`), using the spine `Spectroscopy.bondIonicCharacter` on the derived electronegativities. -/
def bondIonicCharacterChi (μ zA zB n : ℝ) : ℝ :=
  Spectroscopy.bondIonicCharacter (atomElectronegativity μ zA n) (atomElectronegativity μ zB n)

/-- Ionic character is nonnegative. -/
theorem bondIonicCharacterChi_nonneg (μ zA zB n : ℝ) : 0 ≤ bondIonicCharacterChi μ zA zB n :=
  Spectroscopy.bondIonicCharacter_nonneg _ _

/-- A homonuclear bond (equal charges ⇒ equal χ) is purely covalent: zero ionic character. -/
theorem bondIonicCharacterChi_homonuclear (μ z n : ℝ) : bondIonicCharacterChi μ z z n = 0 :=
  Spectroscopy.bondIonicCharacter_homonuclear _

/-- `pullAsymmetry` vanishes exactly when the two pulls are equal (for a positive total). -/
theorem pullAsymmetry_eq_zero_iff (pI pJ : ℝ) (hpos : 0 < pI + pJ) :
    Spectroscopy.pullAsymmetry pI pJ = 0 ↔ pI = pJ := by
  unfold Spectroscopy.pullAsymmetry
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have := abs_eq_zero.mp h; linarith
    · exact absurd h (ne_of_gt hpos)
  · intro h; left; rw [h]; simp

/-- **Pure covalent ⇔ equal electronegativity.** A bond carries zero ionic character exactly when
the two atoms have the same χ. -/
theorem pure_covalent_iff_equal_chi (μ zA zB n : ℝ)
    (hpos : 0 < atomElectronegativity μ zA n + atomElectronegativity μ zB n) :
    bondIonicCharacterChi μ zA zB n = 0 ↔
      atomElectronegativity μ zA n = atomElectronegativity μ zB n := by
  unfold bondIonicCharacterChi Spectroscopy.bondIonicCharacter
  rw [pow_eq_zero_iff (by norm_num)]
  exact pullAsymmetry_eq_zero_iff _ _ hpos

/-- **Distinct effective charges ⇒ polar bond.** Atoms with different `z_eff` (hence different χ) at
the same shell form a bond with strictly positive ionic character. -/
theorem polar_bond_of_distinct_zEff (μ zA zB n : ℝ)
    (hμ : 0 < μ) (hn : n ≠ 0) (hzA : 0 ≤ zA) (hlt : zA < zB) :
    0 < bondIonicCharacterChi μ zA zB n := by
  have hchi : atomElectronegativity μ zA n < atomElectronegativity μ zB n :=
    electronegativity_strictMono_in_zEff μ n zA zB hμ hn hzA hlt
  have hposA : 0 ≤ atomElectronegativity μ zA n := atomElectronegativity_nonneg μ zA n hμ.le
  have hsum : 0 < atomElectronegativity μ zA n + atomElectronegativity μ zB n := by linarith
  rcases (bondIonicCharacterChi_nonneg μ zA zB n).lt_or_eq with h | h
  · exact h
  · exfalso
    have := (pure_covalent_iff_equal_chi μ zA zB n hsum).mp h.symm
    linarith

/-! ## Tie to the derived Slater occupancy -/

/-- Electronegativity at the **derived** Slater/Aufbau effective charge of electron `target` in a
`Z`-electron atom (valence shell `n`). -/
def atomElectronegativityAufbau (Z : ℕ) (target : Fin Z) (μ n : ℝ) : ℝ :=
  atomElectronegativity μ (Binding.slaterEffectiveChargeAufbau Z target) n

/-- **Every bound electron is at least as electronegative as the hydrogen floor.** Since the Slater
effective charge never drops below `1`, χ is bounded below by the unit-charge value. -/
theorem atomElectronegativityAufbau_ge_hydrogenFloor (Z : ℕ) (target : Fin Z) (μ n : ℝ)
    (hμ : 0 < μ) (hn : n ≠ 0) :
    atomElectronegativity μ 1 n ≤ atomElectronegativityAufbau Z target μ n := by
  unfold atomElectronegativityAufbau
  rcases eq_or_lt_of_le (Binding.slaterEffectiveChargeAufbau_ge_one Z target) with h | h
  · rw [h]
  · exact (electronegativity_strictMono_in_zEff μ n 1 _ hμ hn (by norm_num) h).le

end

end HqivSpine.Chemistry.Electronegativity
