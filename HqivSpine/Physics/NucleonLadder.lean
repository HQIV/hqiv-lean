import HqivSpine.Physics.Proton
import HqivSpine.Physics.Frontiers

/-!
# `HqivSpine.Physics.NucleonLadder` — one anchor, real nucleon masses

`Binding` carried the 8×8 composite-trace network symbolically and `Proton` showed the proton mass is a
now-slice readout with **no extra free numbers**. This module finally *instantiates* the abstract inputs
the honest way — one concrete nucleon trace and **one** scale (the proton readout) — and reads off actual
excited-baryon masses as **exact rational multiples** of that single anchor.

* **Concrete nucleon trace.** Three active carrier slots on one generator family give a network whose
  weights sum to `3` (`nucleonWeight_sum`); the binding closes to `E_bind = 3·latticeSimplexCount(m)·α_eff(m)`
  (`E_bind_nucleon`), positive (`E_bind_nucleon_pos`) and bounded `≤ count(m)/14` (`E_bind_nucleon_le`),
  so the QCD-trace shift on the ground state is sub-`2.2` MeV — the proton ground *is* the anchor.
* **One anchor.** `protonConstituent = readout + E_bind(4)`; the ground composite mass reproduces the
  anchor exactly (`ground_reproduces_anchor`) — no new number, just the inversion `Proton` already proved.
* **Operational radial ladder.** The excited baryons sit at `M(n) = m_p · S(4+n)/S(4)` with
  `S(m) = latticeSimplexCount(m) = (m+1)(m+2)`; this is the **exact rational** `m_p·(n+5)(n+6)/30`
  (`radialMass_ratio`), giving rungs `m_p, (7/5)m_p, (28/15)m_p, (12/5)m_p, …` (`radialMass_one/two/three`),
  strictly increasing (`radialMass_strictMono`). Zero free parameters beyond the single anchor.

**Honest scope.** The *spectrum* (every rung as a rational multiple of the anchor) is fully derived; only
the **one** dimensionful scale `m_p` is an input — exactly the `referenceM = 4` proton anchor the
programme allows, and the `MeV` comparison uses `protonMass_MeV_comparison` (comparison, not injection).
The rungs are the *leading* operational readout (`≈5–10%` of the measured `Δ`/Roper region); the
sub-leading detuning/binding fine structure stays the open frontier. Heavy-quark scales remain quarantined
(`heavyQuarkScaleFrontier`). Mathlib + spine only; no `sorry`, no new `axiom`, no PDG table.
-/

namespace HqivSpine.Physics.NucleonLadder

open HqivSpine.Physics
open HqivSpine.Foundation
open scoped BigOperators

/-! ## A concrete nucleon composite trace -/

/-- **Nucleon composite-trace diagonal:** unit weight on the first generator family, the three active
carrier slots `i < 3` (the three valence carriers). -/
def nucleonTraceDiagonal : So8TraceDiagonal := fun k i => if k = 0 ∧ (i : ℕ) < 3 then 1 else 0

/-- **Nucleon trace state:** the all-ones octonion carrier. -/
def nucleonTraceState : OctonionState := fun _ => 1

/-- **Nucleon network weight** from the concrete composite trace. -/
noncomputable def nucleonWeight : NetworkWeight :=
  networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState

theorem nucleonWeight_zero : nucleonWeight 0 = 3 := by
  unfold nucleonWeight networkWeightFromCompositeTrace compositeTraceAtGenerator
    nucleonTraceDiagonal nucleonTraceState
  rw [Fin.sum_univ_eight]
  norm_num

theorem nucleonWeight_of_ne {k : So8Index} (hk : k ≠ 0) : nucleonWeight k = 0 := by
  unfold nucleonWeight networkWeightFromCompositeTrace compositeTraceAtGenerator
    nucleonTraceDiagonal nucleonTraceState
  apply Finset.sum_eq_zero
  intro i _
  have : ¬ (k = 0 ∧ (i : ℕ) < 3) := fun h => hk h.1
  simp [this]

/-- **The nucleon weights sum to `3`** — three active carrier slots. -/
theorem nucleonWeight_sum : ∑ k : So8Index, nucleonWeight k = 3 := by
  rw [Finset.sum_eq_single (0 : So8Index) (fun b _ hb => nucleonWeight_of_ne hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  exact nucleonWeight_zero

/-! ## Binding closed form, positivity, and bound -/

/-- **Nucleon binding closes to `3·latticeSimplexCount(m)·α_eff(m)`.** -/
theorem E_bind_nucleon (m : ℕ) (c : ℝ) :
    E_bind_from_network m nucleonWeight c
      = 3 * (latticeSimplexCount m : ℝ) * alphaEffAtShell m c := by
  unfold E_bind_from_network bindingCouplingAtShell
  rw [← Finset.sum_mul, nucleonWeight_sum]
  ring

theorem log_phi_nonneg (m : ℕ) : 0 ≤ Real.log ((phi m : ℝ) + 1) := by
  apply Real.log_nonneg
  have : (2 : ℝ) ≤ (phi m : ℝ) := by
    have : (2 : ℕ) ≤ phi m := by unfold phi; omega
    exact_mod_cast this
  linarith

/-- The bare-loop inverse coupling is `≥ 42` (the running only *increases* `1/α`). -/
theorem oneOverAlphaEffAtShell_ge (m : ℕ) : 42 ≤ oneOverAlphaEffAtShell m 1 := by
  unfold oneOverAlphaEffAtShell oneOverAlphaBare
  rw [alphaEM_eq]
  nlinarith [log_phi_nonneg m]

theorem oneOverAlphaEffAtShell_pos (m : ℕ) : 0 < oneOverAlphaEffAtShell m 1 := by
  have := oneOverAlphaEffAtShell_ge m; linarith

theorem alphaEffAtShell_pos (m : ℕ) : 0 < alphaEffAtShell m 1 := by
  unfold alphaEffAtShell; exact inv_pos.mpr (oneOverAlphaEffAtShell_pos m)

theorem alphaEffAtShell_le (m : ℕ) : alphaEffAtShell m 1 ≤ 1 / 42 := by
  unfold alphaEffAtShell
  rw [one_div]
  gcongr
  exact oneOverAlphaEffAtShell_ge m

/-- **Nucleon binding is real (positive).** -/
theorem E_bind_nucleon_pos (m : ℕ) : 0 < E_bind_from_network m nucleonWeight 1 := by
  rw [E_bind_nucleon]
  have hcount : (0 : ℝ) < (latticeSimplexCount m : ℝ) := by exact_mod_cast latticeSimplexCount_pos m
  have := alphaEffAtShell_pos m
  positivity

/-- **Nucleon binding bound:** `E_bind(m) ≤ latticeSimplexCount(m)/14`. At `m = 4` this is `≤ 30/14 < 2.2`
MeV, so the composite-trace shift on the proton ground is sub-MeV-scale — the ground *is* the anchor. -/
theorem E_bind_nucleon_le (m : ℕ) :
    E_bind_from_network m nucleonWeight 1 ≤ (latticeSimplexCount m : ℝ) / 14 := by
  rw [E_bind_nucleon]
  have hcount : (0 : ℝ) ≤ (latticeSimplexCount m : ℝ) := by positivity
  have hα := alphaEffAtShell_le m
  nlinarith [hα, hcount, alphaEffAtShell_pos m]

/-! ## One anchor: the constituent and the reproduced ground -/

/-- **Proton constituent** = the single now-slice readout plus the (now concrete) nucleon binding at the
lock-in shell. The only dimensionful input is the readout. -/
noncomputable def protonConstituent (s : NowSlice) (protonFactor : ℝ) : ℝ :=
  protonReadout s protonFactor + E_bind_from_network protonLockinShell nucleonWeight 1

/-- **The ground composite mass reproduces the anchor exactly** — no new number. -/
theorem ground_reproduces_anchor (s : NowSlice) (protonFactor : ℝ) :
    M_composite_from_network protonLockinShell (protonConstituent s protonFactor) nucleonWeight 1
      = protonReadout s protonFactor := by
  unfold M_composite_from_network protonConstituent; ring

/-! ## Operational radial excitation ladder (exact rational multiples) -/

/-- **Operational radial excited-baryon mass:** `M(n) = m_p · S(4+n)/S(4)`, the surface ratio of the
lock-in drum, with `S = latticeSimplexCount`. -/
noncomputable def radialMass (mp : ℝ) (n : ℕ) : ℝ :=
  mp * (latticeSimplexCount (referenceM + n) : ℝ) / (latticeSimplexCount referenceM : ℝ)

theorem latticeSimplexCount_referenceM : latticeSimplexCount referenceM = 30 := by
  norm_num [latticeSimplexCount, shellNumer, referenceM]

theorem latticeSimplexCount_referenceM_add (n : ℕ) :
    latticeSimplexCount (referenceM + n) = (n + 5) * (n + 6) := by
  simp only [latticeSimplexCount, shellNumer, referenceM]; ring

/-- **Every rung is an exact rational multiple of the single anchor:** `M(n) = m_p·(n+5)(n+6)/30`. -/
theorem radialMass_ratio (mp : ℝ) (n : ℕ) :
    radialMass mp n = mp * (((n : ℝ) + 5) * ((n : ℝ) + 6) / 30) := by
  unfold radialMass
  rw [latticeSimplexCount_referenceM, latticeSimplexCount_referenceM_add]
  push_cast; ring

/-- Ground rung = the anchor. -/
theorem radialMass_zero (mp : ℝ) : radialMass mp 0 = mp := by
  rw [radialMass_ratio]; norm_num

/-- First radial excitation: `(7/5)·m_p`. -/
theorem radialMass_one (mp : ℝ) : radialMass mp 1 = mp * (7 / 5) := by
  rw [radialMass_ratio]; norm_num

/-- Second radial excitation: `(28/15)·m_p`. -/
theorem radialMass_two (mp : ℝ) : radialMass mp 2 = mp * (28 / 15) := by
  rw [radialMass_ratio]; norm_num

/-- Third radial excitation: `(12/5)·m_p`. -/
theorem radialMass_three (mp : ℝ) : radialMass mp 3 = mp * (12 / 5) := by
  rw [radialMass_ratio]; norm_num

/-- **The radial ladder is strictly increasing** for a positive anchor. -/
theorem radialMass_strictMono {mp : ℝ} (hmp : 0 < mp) : StrictMono (radialMass mp) := by
  have key : ∀ n : ℕ, radialMass mp n = mp / 30 * (((n : ℝ) + 5) * ((n : ℝ) + 6)) := by
    intro n; rw [radialMass_ratio]; ring
  intro a b hab
  rw [key, key]
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hc : 0 < mp / 30 := by positivity
  apply mul_lt_mul_of_pos_left _ hc
  have hpos : (0 : ℝ) < (b : ℝ) + (a : ℝ) + 11 := by linarith
  nlinarith [mul_pos (sub_pos.mpr hab') hpos]

/-! ## Operational orbital ladder (foundational Rindler detuning `γ/2 = 1/5`) -/

/-- **Rindler detuning** `1 + (γ/2)·m`, with `γ = gammaHQIV = 2/5` the foundational monogamy
complement — so the detuning slope `γ/2 = 1/5` is not a new number. -/
noncomputable def rindlerDetuning (m : ℕ) : ℝ := 1 + gammaHQIV / 2 * (m : ℝ)

theorem rindlerDetuning_eq (m : ℕ) : rindlerDetuning m = (5 + (m : ℝ)) / 5 := by
  unfold rindlerDetuning; rw [gammaHQIV_eq]; ring

theorem rindlerDetuning_pos (m : ℕ) : 0 < rindlerDetuning m := by
  rw [rindlerDetuning_eq]; positivity

/-- **Detuned surface** `S̃(m) = latticeSimplexCount(m) / (1 + (γ/2)m)`. -/
noncomputable def detunedSurface (m : ℕ) : ℝ := (latticeSimplexCount m : ℝ) / rindlerDetuning m

/-- **Operational orbital step:** detuned-surface ratio `S̃(4+ℓ)/S̃(4)`. -/
noncomputable def orbitalStep (ℓ : ℕ) : ℝ := detunedSurface (referenceM + ℓ) / detunedSurface referenceM

/-- **Orbital step closed form:** `step(ℓ) = 3(ℓ+5)(ℓ+6) / (10(ℓ+9))` — an exact rational. -/
theorem orbitalStep_eq (ℓ : ℕ) :
    orbitalStep ℓ = 3 * ((ℓ : ℝ) + 5) * ((ℓ : ℝ) + 6) / (10 * ((ℓ : ℝ) + 9)) := by
  unfold orbitalStep detunedSurface
  rw [latticeSimplexCount_referenceM, latticeSimplexCount_referenceM_add, rindlerDetuning_eq,
    rindlerDetuning_eq]
  simp only [referenceM]
  push_cast
  have ha : (5 : ℝ) + (4 + (ℓ : ℝ)) ≠ 0 := by positivity
  have hb : ((ℓ : ℝ) + 9) ≠ 0 := by positivity
  field_simp
  ring

theorem orbitalStep_zero : orbitalStep 0 = 1 := by rw [orbitalStep_eq]; norm_num

/-- The orbital step never lowers the mass: `step(ℓ) ≥ 1`. -/
theorem orbitalStep_ge_one (ℓ : ℕ) : 1 ≤ orbitalStep ℓ := by
  rw [orbitalStep_eq, le_div_iff₀ (by positivity : (0 : ℝ) < 10 * ((ℓ : ℝ) + 9))]
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  nlinarith [hℓ, mul_nonneg hℓ hℓ]

/-- First orbital excitation: `step = 63/50`. -/
theorem orbitalStep_one : orbitalStep 1 = 63 / 50 := by rw [orbitalStep_eq]; norm_num

/-- Second orbital excitation: `step = 84/55`. -/
theorem orbitalStep_two : orbitalStep 2 = 84 / 55 := by rw [orbitalStep_eq]; norm_num

/-- **The orbital ladder is strictly increasing.** -/
theorem orbitalStep_strictMono : StrictMono orbitalStep := by
  intro a b hab
  rw [orbitalStep_eq, orbitalStep_eq]
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hab', ha, hb, mul_pos (sub_pos.mpr hab')
    (by positivity : (0 : ℝ) < (a : ℝ) * (b : ℝ) + 9 * (a : ℝ) + 9 * (b : ℝ) + 69)]

/-! ## The full operational `(n, ℓ)` excitation grid -/

/-- **Operational excited-baryon mass** on the `(n, ℓ)` grid: radial surface ratio plus orbital step
excess, all times the single anchor. -/
noncomputable def excitedMass (mp : ℝ) (n ℓ : ℕ) : ℝ :=
  mp * ((latticeSimplexCount (referenceM + n) : ℝ) / (latticeSimplexCount referenceM : ℝ)
    + (orbitalStep ℓ - 1))

/-- Pure radial axis recovers `radialMass`. -/
theorem excitedMass_radial (mp : ℝ) (n : ℕ) : excitedMass mp n 0 = radialMass mp n := by
  unfold excitedMass radialMass; rw [orbitalStep_zero]; ring

/-- Pure orbital axis is `m_p · step(ℓ)`. -/
theorem excitedMass_orbital (mp : ℝ) (ℓ : ℕ) : excitedMass mp 0 ℓ = mp * orbitalStep ℓ := by
  unfold excitedMass
  rw [Nat.add_zero, div_self (by exact_mod_cast (latticeSimplexCount_pos referenceM).ne')]
  ring

/-- **Every grid cell is an exact rational multiple of the single anchor.** -/
theorem excitedMass_ratio (mp : ℝ) (n ℓ : ℕ) :
    excitedMass mp n ℓ = mp * (((n : ℝ) + 5) * ((n : ℝ) + 6) / 30
      + (3 * ((ℓ : ℝ) + 5) * ((ℓ : ℝ) + 6) / (10 * ((ℓ : ℝ) + 9)) - 1)) := by
  unfold excitedMass
  rw [latticeSimplexCount_referenceM, latticeSimplexCount_referenceM_add, orbitalStep_eq]
  push_cast; ring

/-- Sample grid cell `(n=1, ℓ=1)`: `M = m_p · 83/50`. -/
theorem excitedMass_one_one (mp : ℝ) : excitedMass mp 1 1 = mp * (83 / 50) := by
  rw [excitedMass_ratio]; norm_num

/-! ## Naive composite-trace readout: the binding grows with shell

The bare network binding `E_bind(m) = 3·count(m)·α_eff(m)` *increases* with shell (the quadratic mode
count outruns the slow `log` weakening of `α_eff`), so the naive composite-trace excited "mass"
`constituent − E_bind` falls *below* the ground. This is why the physical (rising) tower is read off the
operational surface law above, not the bare binding — and we now certify both. The one `Real.log`
obligation is discharged with honest `exp`/`log` interval bounds (no decimals injected). -/

/-- **Binding grows by one shell, for every shell.** The honest analytic core: `log(1+x) ≤ x` (via
`Real.log_le_sub_one_of_pos`) bounds the per-shell `log` increment, so the quadratic mode count always
wins and `E_bind(m) < E_bind(m+1)`. -/
theorem E_bind_lt_succ (m : ℕ) :
    E_bind_from_network m nucleonWeight 1 < E_bind_from_network (m + 1) nucleonWeight 1 := by
  rw [E_bind_nucleon, E_bind_nucleon]
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have ep : ((phi m : ℝ) + 1) = 2 * (m : ℝ) + 3 := by simp only [phi]; push_cast; ring
  have ep1 : ((phi (m + 1) : ℝ) + 1) = 2 * (m : ℝ) + 5 := by simp only [phi]; push_cast; ring
  have hcm : (latticeSimplexCount m : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    simp only [latticeSimplexCount, shellNumer]; push_cast; ring
  have hcm1 : (latticeSimplexCount (m + 1) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 3) := by
    simp only [latticeSimplexCount, shellNumer]; push_cast; ring
  have hLm : (0 : ℝ) ≤ Real.log (2 * (m : ℝ) + 3) := Real.log_nonneg (by linarith)
  have hδ : (0 : ℝ) ≤ Real.log (2 * (m : ℝ) + 5) - Real.log (2 * (m : ℝ) + 3) :=
    sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
  -- per-shell `log` increment bound: `(2m+3)·(log(2m+5) − log(2m+3)) ≤ 2`.
  have hratio : Real.log (2 * (m : ℝ) + 5) - Real.log (2 * (m : ℝ) + 3) ≤ 2 / (2 * (m : ℝ) + 3) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have hy : (0 : ℝ) < (2 * (m : ℝ) + 5) / (2 * (m : ℝ) + 3) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hy
    have heq : (2 * (m : ℝ) + 5) / (2 * (m : ℝ) + 3) - 1 = 2 / (2 * (m : ℝ) + 3) := by
      field_simp; ring
    rw [heq] at h1; exact h1
  have hratio' : (2 * (m : ℝ) + 3) * (Real.log (2 * (m : ℝ) + 5) - Real.log (2 * (m : ℝ) + 3)) ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 3)
    have e : (2 * (m : ℝ) + 3) * (2 / (2 * (m : ℝ) + 3)) = 2 := by field_simp
    linarith [h, e.le, e.ge]
  have hOm : oneOverAlphaEffAtShell m 1 = 42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 3)) := by
    simp only [oneOverAlphaEffAtShell, oneOverAlphaBare]; rw [alphaEM_eq, ep]; ring
  have hOm1 : oneOverAlphaEffAtShell (m + 1) 1 = 42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 5)) := by
    simp only [oneOverAlphaEffAtShell, oneOverAlphaBare]; rw [alphaEM_eq, ep1]; ring
  -- reduced cross-multiplied inequality `(m+1)·Q < (m+3)·P`.
  have hkey : ((m : ℝ) + 1) * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 5))
      < ((m : ℝ) + 3) * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 3)) := by
    nlinarith [hratio', hδ, hLm, hm]
  unfold alphaEffAtShell
  rw [hcm, hcm1, hOm, hOm1]
  have hP : (0 : ℝ) < 42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 3)) := by nlinarith [hLm]
  have hQ : (0 : ℝ) < 42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 5)) := by nlinarith [hLm, hδ]
  rw [show (3 : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 3)))⁻¹
        = (3 * (((m : ℝ) + 1) * ((m : ℝ) + 2))) / (42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 3))) by ring,
    show (3 : ℝ) * (((m : ℝ) + 2) * ((m : ℝ) + 3)) * (42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 5)))⁻¹
        = (3 * (((m : ℝ) + 2) * ((m : ℝ) + 3))) / (42 * (1 + 3 / 5 * Real.log (2 * (m : ℝ) + 5))) by ring,
    div_lt_div_iff₀ hP hQ]
  have hfin := mul_lt_mul_of_pos_left hkey (by positivity : (0 : ℝ) < 126 * ((m : ℝ) + 2))
  nlinarith [hfin]

/-- **The bare binding is strictly increasing in shell.** -/
theorem E_bind_strictMono :
    StrictMono (fun m => E_bind_from_network m nucleonWeight 1) :=
  strictMono_nat_of_lt_succ E_bind_lt_succ

theorem E_bind_four_lt_five :
    E_bind_from_network 4 nucleonWeight 1 < E_bind_from_network 5 nucleonWeight 1 :=
  E_bind_strictMono (by norm_num)

/-- **Naive composite-trace excited mass** at the lock-in shell `+ n + ℓ` (the bare binding readout). -/
noncomputable def naiveExcitedMass (s : NowSlice) (protonFactor : ℝ) (n ℓ : ℕ) : ℝ :=
  M_composite_from_network (protonLockinShell + n + ℓ) (protonConstituent s protonFactor) nucleonWeight 1

/-- **The naive tower falls below ground for every excitation** `n + ℓ ≥ 1`: the binding grows with
shell (`E_bind_strictMono`), so the bare composite-trace readout drops — which is exactly why the rising
physical tower must be the operational surface law, not the bare binding. -/
theorem naive_excited_lt_ground (s : NowSlice) (protonFactor : ℝ) {n ℓ : ℕ} (h : 1 ≤ n + ℓ) :
    naiveExcitedMass s protonFactor n ℓ < protonReadout s protonFactor := by
  unfold naiveExcitedMass M_composite_from_network protonConstituent
  have hlt : E_bind_from_network protonLockinShell nucleonWeight 1
      < E_bind_from_network (protonLockinShell + n + ℓ) nucleonWeight 1 := by
    apply E_bind_strictMono
    simp only [protonLockinShell, referenceM]; omega
  linarith [hlt]

/-- `ΔM(1,0) < 0` — the original specific case. -/
theorem naive_excited_below_ground (s : NowSlice) (protonFactor : ℝ) :
    naiveExcitedMass s protonFactor 1 0 < protonReadout s protonFactor :=
  naive_excited_lt_ground s protonFactor (by norm_num)

/-! ## Meson sector: a second carrier composite, still one anchor

A meson is a **two-carrier** composite (quark–antiquark) against the baryon's three. Both the constituent
mass and the binding scale with carrier count (the network has `∑ w = carrier count`), so *everything*
scales together and the meson ground is the **exact** `2/3` of the proton — the per-carrier mass and the
binding cancel in the ratio. No second anchor: the meson rides the same `referenceM = 4` proton scale.
(`(2/3)·938.272 ≈ 625.5` MeV, the spin-averaged light `(π,ρ)` center-of-gravity region.) -/

/-- Two active carrier slots (quark–antiquark). -/
def mesonTraceDiagonal : So8TraceDiagonal := fun k i => if k = 0 ∧ (i : ℕ) < 2 then 1 else 0

noncomputable def mesonWeight : NetworkWeight :=
  networkWeightFromCompositeTrace mesonTraceDiagonal nucleonTraceState

theorem mesonWeight_zero : mesonWeight 0 = 2 := by
  unfold mesonWeight networkWeightFromCompositeTrace compositeTraceAtGenerator
    mesonTraceDiagonal nucleonTraceState
  rw [Fin.sum_univ_eight]; norm_num

theorem mesonWeight_of_ne {k : So8Index} (hk : k ≠ 0) : mesonWeight k = 0 := by
  unfold mesonWeight networkWeightFromCompositeTrace compositeTraceAtGenerator
    mesonTraceDiagonal nucleonTraceState
  apply Finset.sum_eq_zero
  intro i _
  have : ¬ (k = 0 ∧ (i : ℕ) < 2) := fun h => hk h.1
  simp [this]

/-- **The meson weights sum to `2`** — two carriers. -/
theorem mesonWeight_sum : ∑ k : So8Index, mesonWeight k = 2 := by
  rw [Finset.sum_eq_single (0 : So8Index) (fun b _ hb => mesonWeight_of_ne hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  exact mesonWeight_zero

theorem E_bind_meson (m : ℕ) (c : ℝ) :
    E_bind_from_network m mesonWeight c
      = 2 * (latticeSimplexCount m : ℝ) * alphaEffAtShell m c := by
  unfold E_bind_from_network bindingCouplingAtShell
  rw [← Finset.sum_mul, mesonWeight_sum]; ring

/-- **Per-carrier mass** = the proton constituent split over its three carriers. -/
noncomputable def carrierMass (s : NowSlice) (protonFactor : ℝ) : ℝ :=
  protonConstituent s protonFactor / 3

/-- **Meson ground** = two carriers minus the two-carrier binding. -/
noncomputable def mesonGround (s : NowSlice) (protonFactor : ℝ) : ℝ :=
  2 * carrierMass s protonFactor - E_bind_from_network protonLockinShell mesonWeight 1

/-- **Meson ground is exactly `2/3` of the proton.** Carrier mass and binding both scale with count, so
they cancel in the ratio and the meson rides the *same* single anchor. -/
theorem mesonGround_eq (s : NowSlice) (protonFactor : ℝ) :
    mesonGround s protonFactor = 2 / 3 * protonReadout s protonFactor := by
  unfold mesonGround carrierMass protonConstituent
  rw [E_bind_meson, E_bind_nucleon]; ring

theorem mesonGround_lt_proton (s : NowSlice) (protonFactor : ℝ)
    (h : 0 < protonReadout s protonFactor) :
    mesonGround s protonFactor < protonReadout s protonFactor := by
  rw [mesonGround_eq]; linarith

/-- **Meson excitations** ride the same operational rational ladder, anchored at the `2/3` meson ground:
`M_meson(n) = (2/3)·m_p·(n+5)(n+6)/30`. -/
theorem mesonRadialMass_eq (s : NowSlice) (protonFactor : ℝ) (n : ℕ) :
    radialMass (mesonGround s protonFactor) n
      = 2 / 3 * protonReadout s protonFactor * (((n : ℝ) + 5) * ((n : ℝ) + 6) / 30) := by
  rw [radialMass_ratio, mesonGround_eq]

/-! ## MeV comparison (comparison only — the single allowed anchor) -/

/-- The radial rungs against the `referenceM = 4` proton comparison anchor (`938.272` MeV, comparison
only per `Frontiers`). Exact rational outputs: `938.272, 1313.58, 1751.44, 2251.85 …` MeV. -/
theorem radialMass_one_comparison :
    radialMass protonMass_MeV_comparison 1 = 938.272 * (7 / 5) := by
  rw [radialMass_one]; norm_num [protonMass_MeV_comparison]

theorem radialMass_two_comparison :
    radialMass protonMass_MeV_comparison 2 = 938.272 * (28 / 15) := by
  rw [radialMass_two]; norm_num [protonMass_MeV_comparison]

/-! ## Closure -/

/-- **Nucleon-ladder discharge bundle.** One concrete trace, one anchor, an exact rational spectrum. -/
structure NucleonLadderDischarged : Prop where
  weight_sum : ∑ k : So8Index, nucleonWeight k = 3
  binding_closed : ∀ m : ℕ, E_bind_from_network m nucleonWeight 1
    = 3 * (latticeSimplexCount m : ℝ) * alphaEffAtShell m 1
  binding_pos : ∀ m : ℕ, 0 < E_bind_from_network m nucleonWeight 1
  ground_anchor : ∀ (s : NowSlice) (pf : ℝ),
    M_composite_from_network protonLockinShell (protonConstituent s pf) nucleonWeight 1
      = protonReadout s pf
  rung_rational : ∀ (mp : ℝ) (n : ℕ),
    radialMass mp n = mp * (((n : ℝ) + 5) * ((n : ℝ) + 6) / 30)
  rungs_increase : ∀ mp : ℝ, 0 < mp → StrictMono (radialMass mp)
  orbital_rational : ∀ ℓ : ℕ,
    orbitalStep ℓ = 3 * ((ℓ : ℝ) + 5) * ((ℓ : ℝ) + 6) / (10 * ((ℓ : ℝ) + 9))
  orbital_increase : StrictMono orbitalStep
  grid_rational : ∀ (mp : ℝ) (n ℓ : ℕ),
    excitedMass mp n ℓ = mp * (((n : ℝ) + 5) * ((n : ℝ) + 6) / 30
      + (3 * ((ℓ : ℝ) + 5) * ((ℓ : ℝ) + 6) / (10 * ((ℓ : ℝ) + 9)) - 1))
  binding_strictMono : StrictMono (fun m => E_bind_from_network m nucleonWeight 1)
  naive_binding_falls : ∀ (s : NowSlice) (pf : ℝ) (n ℓ : ℕ), 1 ≤ n + ℓ →
    naiveExcitedMass s pf n ℓ < protonReadout s pf
  meson_weight_sum : ∑ k : So8Index, mesonWeight k = 2
  meson_two_thirds : ∀ (s : NowSlice) (pf : ℝ),
    mesonGround s pf = 2 / 3 * protonReadout s pf

theorem nucleonLadderDischarged_holds : NucleonLadderDischarged where
  weight_sum := nucleonWeight_sum
  binding_closed := fun m => E_bind_nucleon m 1
  binding_pos := E_bind_nucleon_pos
  ground_anchor := ground_reproduces_anchor
  rung_rational := radialMass_ratio
  rungs_increase := fun _ hmp => radialMass_strictMono hmp
  orbital_rational := orbitalStep_eq
  orbital_increase := orbitalStep_strictMono
  grid_rational := excitedMass_ratio
  binding_strictMono := E_bind_strictMono
  naive_binding_falls := fun s pf _ _ h => naive_excited_lt_ground s pf h
  meson_weight_sum := mesonWeight_sum
  meson_two_thirds := mesonGround_eq

end HqivSpine.Physics.NucleonLadder
