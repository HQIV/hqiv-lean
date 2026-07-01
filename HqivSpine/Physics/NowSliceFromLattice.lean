import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.Curvature
import HqivSpine.Physics.Shell
import HqivSpine.Physics.Age
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Topology.NullLatticeComplex
import HqivSpine.Topology.ShellBudget
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# `HqivSpine.Physics.NowSliceFromLattice` — `(φ, Φ, Ω_k)` from lattice geometry

Mined from legacy `OctonionicLightCone` / `Now` / `HQVMetric`, disentangled onto the spine
null-lattice stack. The now-slice curvatures are **read off combinatorial geometry**:

* **Temperature ladder** `T(m) = 1/(m+1)` ⇒ auxiliary field `φ(m) = 2/T(m) = 2(m+1)` (the spine
  `Shell.phi`);
* **Expansion rate at "now"** `φ = H₀ = 1` in natural units (homogeneous Hubble reference — the
  Friedmann `Gravity.hubble` anchor, not the shell-indexed auxiliary field);
* **Weak-field potential** `Φ` = normalised shell-budget mismatch `−Δ/ latticeSimplexCount(m)` on
  the null-lattice 3-complex (zero on the reference template);
* **Spatial curvature** `Ω_k(m) = (∑_{k<m} shellShape k) / (∑_{k<referenceM} shellShape k)` — the
  discrete horizon ratio (`omega_k_partial` in legacy), normalised to `1` at lock-in.

Honest scope: the **discrete** null-lattice derivation. The continuous chart
(`ContinuousHorizon.omegaKContinuous`) is a parallel readout on `ξ`; identifying the discrete sum
with the analytic primitive on all shells is *not* claimed here. Bulk hyperboloid / dynamical
`H(t)` closure remains in `Frontiers.nowSliceCurvatureFrontier`.
-/

namespace HqivSpine.Physics.NowSliceFromLattice

open HqivSpine.Topology
open HqivSpine.Physics
open HqivSpine.Physics.ContinuousHorizon
open scoped BigOperators

/-! ## Temperature ladder and auxiliary field -/

/-- **Shell temperature** on the null ladder: `T(m) = 1/(m+1)` with `T_Pl = 1`. -/
noncomputable def shellTemperature (m : ℕ) : ℝ := 1 / ((m + 1 : ℝ))

theorem shellTemperature_pos (m : ℕ) : 0 < shellTemperature m := by
  unfold shellTemperature; positivity

/-- **Structural inverse** of the temperature ladder (no observed `T_CMB` input). -/
noncomputable def shellIndexFromTemperature (T : ℝ) : ℝ := 1 / T - 1

theorem shellIndexFromTemperature_of_shell (m : ℕ) :
    shellIndexFromTemperature (shellTemperature m) = m := by
  unfold shellIndexFromTemperature shellTemperature
  field_simp [ne_of_gt (shellTemperature_pos m)]
  ring

/-- **Lattice division rule:** `φ(m) = 2/T(m) = 2(m+1)` agrees with `Shell.phi`. -/
theorem auxiliaryFieldFromTemperature (m : ℕ) :
    2 / shellTemperature m = (phi m : ℝ) := by
  unfold shellTemperature phi; push_cast; field_simp

/-- **Natural Hubble at "now":** `H₀ = 1` (natural units; legacy `Now.nowPhi`). -/
def hubbleReference : ℝ := 1

theorem hubbleReference_eq_one : hubbleReference = 1 := rfl

/-! ## Discrete curvature integral and `Ω_k` -/

/-- **Discrete curvature integral** over shells `0 … n−1` (legacy `curvature_integral`). -/
noncomputable def curvatureIntegral (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, shellShape m

theorem curvatureIntegral_zero : curvatureIntegral 0 = 0 := rfl

theorem curvatureIntegral_succ (n : ℕ) :
    curvatureIntegral (n + 1) = curvatureIntegral n + shellShape n := by
  simp only [curvatureIntegral, Finset.sum_range_succ]

theorem curvatureIntegral_pos {n : ℕ} (hn : 0 < n) : 0 < curvatureIntegral n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst hm
  rw [curvatureIntegral_succ]
  by_cases hm0 : m = 0
  · subst hm0; simp [curvatureIntegral_zero, shellShape_pos]
  · exact add_pos (curvatureIntegral_pos (Nat.pos_of_ne_zero hm0)) (shellShape_pos m)

theorem curvatureIntegral_referenceM_pos : 0 < curvatureIntegral referenceM := by
  unfold referenceM; exact curvatureIntegral_pos (by decide : 0 < 4)

/-- **Horizon ratio** `Ω_k(n | N) = I(n)/I(N)` on the discrete imprint sum. -/
noncomputable def omegaKAtHorizon (n N : ℕ) : ℝ :=
  curvatureIntegral n / curvatureIntegral N

theorem curvatureIntegral_nonneg (n : ℕ) : 0 ≤ curvatureIntegral n := by
  unfold curvatureIntegral
  exact Finset.sum_nonneg fun _ _ => (shellShape_pos _).le

theorem curvatureIntegral_mono {n N : ℕ} (h : n ≤ N) :
    curvatureIntegral n ≤ curvatureIntegral N := by
  induction h with
  | refl => rfl
  | step _ ih =>
    rw [curvatureIntegral_succ]
    exact le_add_of_le_of_nonneg ih (shellShape_pos _).le

theorem omegaKAtHorizon_self_of_pos (N : ℕ) (hN : 0 < N) :
    omegaKAtHorizon N N = 1 := by
  unfold omegaKAtHorizon; field_simp [curvatureIntegral_pos hN |>.ne']

theorem omegaKAtHorizon_self (N : ℕ) (hN : 0 < N) : omegaKAtHorizon N N = 1 :=
  omegaKAtHorizon_self_of_pos N hN

theorem omegaKAtHorizon_le_one (n N : ℕ) (hN : 0 < N) (hn : n ≤ N) :
    omegaKAtHorizon n N ≤ 1 := by
  unfold omegaKAtHorizon
  rw [div_le_one (curvatureIntegral_pos hN)]
  exact curvatureIntegral_mono hn

/-- **Partial spatial curvature** normalised to lock-in (`referenceM = 4`). -/
noncomputable def omegaKPartial (n : ℕ) : ℝ := omegaKAtHorizon n referenceM

theorem omegaKPartial_at_referenceM : omegaKPartial referenceM = 1 := by
  unfold omegaKPartial referenceM
  exact omegaKAtHorizon_self_of_pos 4 (by decide : 0 < 4)

theorem omegaKPartial_nonneg (n : ℕ) : 0 ≤ omegaKPartial n := by
  unfold omegaKPartial omegaKAtHorizon
  exact div_nonneg (curvatureIntegral_nonneg n) (curvatureIntegral_nonneg referenceM)

theorem omegaKPartial_pos {n : ℕ} (hn : 0 < n) : 0 < omegaKPartial n := by
  unfold omegaKPartial omegaKAtHorizon
  exact div_pos (curvatureIntegral_pos hn) curvatureIntegral_referenceM_pos

theorem omegaKPartial_le_one (n : ℕ) (hn : n ≤ referenceM) :
    omegaKPartial n ≤ 1 := by
  unfold omegaKPartial referenceM
  exact omegaKAtHorizon_le_one n 4 (by decide : 0 < 4) hn

/-- **Shape dominates the harmonic weight:** `1/(m+1) ≤ shellShape m`. -/
theorem shellShape_ge_imprintWeight (m : ℕ) : imprintWeight m ≤ shellShape m := by
  unfold shellShape
  have hlog : 0 ≤ Real.log ((m : ℝ) + 1) := by
    have hx : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
    exact Real.log_nonneg hx
  have hα : 0 ≤ alphaEM := by rw [alphaEM_eq]; norm_num
  have hfac : (1 : ℝ) ≤ 1 + alphaEM * Real.log ((m : ℝ) + 1) := by
    nlinarith [mul_nonneg hα hlog]
  simpa using mul_le_mul_of_nonneg_left hfac (imprintWeight_pos m).le

/-- **Harmonic partial sum** `∑_{k<n} 1/(k+1)` (legacy lower bound on the discrete integral). -/
noncomputable def harmonicSum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, (1 : ℝ) / (m + 1)

theorem harmonicSum_le_curvatureIntegral (n : ℕ) :
    harmonicSum n ≤ curvatureIntegral n := by
  unfold harmonicSum curvatureIntegral
  exact Finset.sum_le_sum fun m _ => shellShape_ge_imprintWeight m

theorem curvatureIntegral_strictMono {n1 n2 : ℕ} (h : n1 < n2) :
    curvatureIntegral n1 < curvatureIntegral n2 := by
  refine Nat.le_induction ?base ?step n2 (Nat.succ_le_of_lt h)
  · show curvatureIntegral n1 < curvatureIntegral (n1 + 1)
    rw [curvatureIntegral_succ]
    linarith [shellShape_pos n1]
  · intro m _ ih
    exact lt_trans ih (by rw [curvatureIntegral_succ]; linarith [shellShape_pos m])

theorem omegaKPartial_strictMono {n1 n2 : ℕ} (h : n1 < n2) (_href : n2 ≤ referenceM) :
    omegaKPartial n1 < omegaKPartial n2 := by
  unfold omegaKPartial omegaKAtHorizon
  refine div_lt_div_of_pos_right (curvatureIntegral_strictMono h) ?_
  exact curvatureIntegral_referenceM_pos

/-! ## Weak-field `Φ` from the signed shell ledger -/

/-- **Weak-field potential** from budget mismatch: `Φ = −Δ/(m+2)(m+1)`. -/
noncomputable def weakFieldPotential (M : Discrete3Complex NullShellVertex) (m : ℕ) : ℝ :=
  -(shellBudgetMismatch M m : ℝ) / (latticeSimplexCount m : ℝ)

theorem weakFieldPotential_equilibrium (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : shellBudgetOpen M m) :
    weakFieldPotential M m = 0 := by
  unfold weakFieldPotential shellBudgetOpen at *
  simp [h]

theorem weakFieldPotential_S3NullReference (n m : ℕ) (hm : m ≤ n) :
    weakFieldPotential (S3NullReference n) m = 0 := by
  unfold weakFieldPotential
  rw [S3NullReference_shell_budget_zero n m hm]
  simp

/-! ## Lattice-backed `NowSlice` -/

/-- Observer on null-shell layer `m` with combinatorial complex `M`. -/
structure LatticeObserver where
  shell : ℕ
  complex : Discrete3Complex NullShellVertex

/-- Observer on a **balanced** null horizon: quadratic growth ⇒ zero shell-ledger mismatch. -/
structure BalancedLatticeObserver extends LatticeObserver where
  horizon : ℕ
  shell_le_horizon : shell ≤ horizon
  quadratic : QuadraticNullShellGrowthOnHorizon complex horizon

/-- **Lock-in observer** on the reference null-lattice template at horizon `n`. -/
noncomputable def lockinObserver (n : ℕ := referenceM) : LatticeObserver :=
  { shell := n, complex := S3NullReference n }

/-- Read `(φ, Φ, Ω_k, t)` from lattice data.

* `φ = H₀ = 1` (natural now);
* `Φ` = weak-field ledger potential at the observer shell;
* `Ω_k` = discrete partial curvature at the observer shell;
* `t` = shell index (coordinate age on the ladder). -/
noncomputable def nowSliceOf (obs : LatticeObserver) : NowSlice :=
  { phi := hubbleReference
    bigPhi := weakFieldPotential obs.complex obs.shell
    omegaK := omegaKPartial obs.shell
    apparentAge := obs.shell }

theorem nowSliceOf_phi (obs : LatticeObserver) : (nowSliceOf obs).phi = 1 := rfl

theorem nowSliceOf_apparentAge (obs : LatticeObserver) :
    (nowSliceOf obs).apparentAge = (obs.shell : ℝ) := rfl

theorem balancedNowSlice_bigPhi_zero (obs : BalancedLatticeObserver) :
    (nowSliceOf ({ shell := obs.shell, complex := obs.complex } : LatticeObserver)).bigPhi = 0 := by
  unfold nowSliceOf weakFieldPotential
  have h := quadraticNullShellGrowthOnHorizon_shell_budget_zero obs.complex obs.horizon
    obs.quadratic obs.shell_le_horizon
  rw [h]
  simp

theorem referenceM_eq_four : referenceM = 4 := rfl

theorem referenceM_add_one_eq_five : (referenceM + 1 : ℝ) = 5 := by
  rw [referenceM_eq_four]; norm_num

theorem nowSliceOf_lockin_phi :
    (nowSliceOf (lockinObserver referenceM)).phi = 1 := rfl

theorem nowSliceOf_lockin_bigPhi :
    (nowSliceOf (lockinObserver referenceM)).bigPhi = 0 := by
  unfold nowSliceOf lockinObserver weakFieldPotential referenceM
  rw [S3NullReference_shell_budget_zero 4 4 (Nat.le_refl 4)]
  simp

theorem nowSliceOf_lockin_omegaK :
    (nowSliceOf (lockinObserver referenceM)).omegaK = 1 := by
  unfold nowSliceOf lockinObserver omegaKPartial referenceM
  exact omegaKAtHorizon_self_of_pos 4 (by decide : 0 < 4)

theorem nowSliceOf_lockin_apparentAge :
    (nowSliceOf (lockinObserver referenceM)).apparentAge = 4 := by
  unfold nowSliceOf lockinObserver referenceM
  norm_num

/-- Convenience alias: the lock-in now slice from lattice geometry. -/
noncomputable def lockinNowSlice : NowSlice := nowSliceOf (lockinObserver referenceM)

theorem lockinNowSlice_fields :
    lockinNowSlice.phi = 1 ∧
    lockinNowSlice.bigPhi = 0 ∧
    lockinNowSlice.omegaK = 1 ∧
    lockinNowSlice.apparentAge = 4 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold lockinNowSlice nowSliceOf lockinObserver weakFieldPotential referenceM
    rw [S3NullReference_shell_budget_zero 4 4 (Nat.le_refl 4)]
    simp
  · unfold lockinNowSlice nowSliceOf lockinObserver omegaKPartial referenceM
    exact omegaKAtHorizon_self_of_pos 4 (by decide : 0 < 4)
  · unfold lockinNowSlice nowSliceOf lockinObserver referenceM
    norm_num

theorem lockinNowSlice_massUnit :
    lockinNowSlice.massUnit = 5 := by
  rw [NowSlice.massUnit_eq]
  unfold lockinNowSlice nowSliceOf lockinObserver referenceM hubbleReference
  simp [weakFieldPotential, S3NullReference_shell_budget_zero 4 4 (Nat.le_refl 4)]
  norm_num

theorem lockinNowSlice_wallClockAge :
    lockinNowSlice.wallClockAge = 12 := by
  unfold NowSlice.wallClockAge
  rcases lockinNowSlice_fields with ⟨hphi, _, _, ht⟩
  rw [hphi, ht]
  norm_num

theorem lockinNowSlice_ageRatio :
    lockinNowSlice.wallClockAge / lockinNowSlice.apparentAgeValue = 3 := by
  have ht : lockinNowSlice.apparentAge ≠ 0 := by
    rcases lockinNowSlice_fields with ⟨_, _, _, ht⟩
    rw [ht]; norm_num
  rw [NowSlice.ageRatio_eq lockinNowSlice ht]
  rcases lockinNowSlice_fields with ⟨hphi, _, _, ht⟩
  rw [hphi, ht]; norm_num

/-! ## Link to the continuous-ξ chart (export coordinate only) -/

/-- **Export chart at lock-in:** `omegaKContinuous ξ_lock ξ_lock = 1` agrees with discrete
`omegaKPartial referenceM = 1` — not a second curvature field. -/
theorem omegaKContinuous_agrees_at_lockin :
    omegaKContinuous xiLockin xiLockin = 1 :=
  omegaKContinuous_lockin

theorem xiOfShell_strictMono {m1 m2 : ℕ} (h : m1 < m2) :
    xiOfShell m1 < xiOfShell m2 := by
  unfold xiOfShell
  exact_mod_cast Nat.add_lt_add_right h 1

theorem xiOfShell_gt_one {m : ℕ} (hm : 0 < m) : 1 < xiOfShell m := by
  unfold xiOfShell
  exact_mod_cast Nat.add_lt_add_right hm 1

private theorem continuousCurvaturePrimitive_xiLockin_pos :
    0 < continuousCurvaturePrimitive xiLockin := by
  rw [xiLockin_eq_five]
  exact continuousCurvaturePrimitive_pos_for_gt_one (5 : ℝ) (by norm_num : (1 : ℝ) < 5)

theorem omegaKContinuous_at_shell (m : ℕ) :
    omegaKContinuous (xiOfShell m) xiLockin =
      continuousCurvaturePrimitive (xiOfShell m) / continuousCurvaturePrimitive xiLockin := by
  unfold omegaKContinuous
  simp [continuousCurvaturePrimitive_xiLockin_pos.ne']

theorem omegaKContinuous_shell_strictMono {m1 m2 : ℕ}
    (h : m1 < m2) (_hm2 : m2 ≤ referenceM) (hm1 : 0 < m1) :
    omegaKContinuous (xiOfShell m1) xiLockin < omegaKContinuous (xiOfShell m2) xiLockin := by
  have hξ1 : 1 < xiOfShell m1 := xiOfShell_gt_one hm1
  have hξ2 : xiOfShell m1 < xiOfShell m2 := xiOfShell_strictMono h
  rw [omegaKContinuous_at_shell, omegaKContinuous_at_shell]
  refine div_lt_div_of_pos_right
    (continuousCurvaturePrimitive_strictMono_gt_one (xiOfShell m1) (xiOfShell m2) hξ1 hξ2) ?_
  exact continuousCurvaturePrimitive_xiLockin_pos

/-- **Chart ordering consistency (weak):** below lock-in, discrete `omegaKPartial` and the
continuous `ξ` export `omegaKContinuous` are both strictly increasing on shell index.
This is **not** a pointwise identification theorem and must not be read as parallel
curvature ontologies. -/
theorem omegaK_readouts_strictMono_parallel {m1 m2 : ℕ}
    (h : m1 < m2) (hm2 : m2 ≤ referenceM) (hm1 : 0 < m1) :
    omegaKPartial m1 < omegaKPartial m2 ∧
    omegaKContinuous (xiOfShell m1) xiLockin < omegaKContinuous (xiOfShell m2) xiLockin :=
  ⟨omegaKPartial_strictMono h hm2, omegaKContinuous_shell_strictMono h hm2 hm1⟩

structure nowSliceFromLatticeDischarged : Prop where
  temperature_auxiliary : ∀ m, 2 / shellTemperature m = (phi m : ℝ)
  temperature_inverse : ∀ m, shellIndexFromTemperature (shellTemperature m) = m
  hubble_now : hubbleReference = 1
  harmonic_lower_bound : ∀ n, harmonicSum n ≤ curvatureIntegral n
  omegaK_strict_mono :
    ∀ {n1 n2 : ℕ}, n1 < n2 → n2 ≤ referenceM → omegaKPartial n1 < omegaKPartial n2
  balanced_phi_zero : ∀ obs : BalancedLatticeObserver,
    (nowSliceOf ({ shell := obs.shell, complex := obs.complex } : LatticeObserver)).bigPhi = 0
  lockin_slice :
    lockinNowSlice.phi = 1 ∧
    lockinNowSlice.bigPhi = 0 ∧
    lockinNowSlice.omegaK = 1 ∧
    lockinNowSlice.apparentAge = referenceM
  lockin_lapse : lockinNowSlice.massUnit = (referenceM + 1 : ℝ)
  lockin_ages :
    lockinNowSlice.wallClockAge = 12 ∧
    lockinNowSlice.wallClockAge / lockinNowSlice.apparentAgeValue = 3
  continuous_lockin_norm : omegaKContinuous xiLockin xiLockin = 1

theorem nowSliceFromLatticeDischarged_holds : nowSliceFromLatticeDischarged where
  temperature_auxiliary := auxiliaryFieldFromTemperature
  temperature_inverse := shellIndexFromTemperature_of_shell
  hubble_now := hubbleReference_eq_one
  harmonic_lower_bound := harmonicSum_le_curvatureIntegral
  omegaK_strict_mono := fun h href => omegaKPartial_strictMono h href
  balanced_phi_zero := balancedNowSlice_bigPhi_zero
  lockin_slice := lockinNowSlice_fields
  lockin_lapse := by rw [lockinNowSlice_massUnit, referenceM_add_one_eq_five]
  lockin_ages := ⟨lockinNowSlice_wallClockAge, lockinNowSlice_ageRatio⟩
  continuous_lockin_norm := omegaKContinuous_agrees_at_lockin

end HqivSpine.Physics.NowSliceFromLattice
