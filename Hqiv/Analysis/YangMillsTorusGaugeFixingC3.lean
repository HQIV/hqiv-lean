import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Bounds.Basic

/-!
# Problem C3 — gauge fixing along Yang–Mills gradient flow on `T²`

**Theorem (Problem C3).** Fix a compact Lie group `G` with Ad-invariant norm on `𝔤`.
For `κ ∈ (0, 1/2)` there exist `c, C > 0` such that every smooth connection `B₀` on the
trivial `G`-bundle over `T²` admits a smooth gauge `g` with
`‖g • B₀‖_{C^{-κ}} + sup_{s∈(0,1]} s^κ ‖div(g • B(s))‖_{L^∞}`
controlled polynomially by `‖B₀‖_{cov,-κ}`.

## Proof pipeline (see `papers/yang_mills_torus_gauge_fixing/problem_c3_proof.tex`)

1. **Parabolic scaling** — `‖F(s)‖_{L^∞} ≲ s^{-κ} M` from the invariant norm.
2. **Short time** — choose `s₀ = c₀ M^{-a}` with **`a ≥ 1/κ`**, so `‖F(s₀)‖_{L^2}` is **O(1)**
   in `M = 1 + ‖B₀‖_{cov,-κ}` and global Uhlenbeck applies after smoothing.
3. **Coulomb gauge at `s₀`** — Uhlenbeck + `W^{1,2} ↪ C^{-κ}` for `κ < 1/2`.
4. **Divergence along flow** — elliptic propagation with time-independent `g`.
5. **Initial pullback** — parabolic comparison from `s₀` to `0`.

Each step is a named field in `YangMillsTorusGaugeFixingHypothesis`. The implication to
Theorem C3 is proved without `sorry`.
-/

namespace Hqiv.Analysis

namespace ProblemC3

def kappaAdmissible (κ : ℝ) : Prop :=
  0 < κ ∧ κ < 1 / 2

/-- Short-time exponent: `a ≥ 1/κ` makes `M^{1-aκ} ≤ 1` (curvature at `s₀` uniformly bounded). -/
def shortTimeExponentValid (κ a : ℝ) : Prop :=
  kappaAdmissible κ ∧ 1 / κ ≤ a

structure SmoothTorusConnection (G : Type*) where
  deriving Inhabited

structure SmoothGaugeTransform (G : Type*) where
  deriving Inhabited

opaque gaugeAct {G : Type*} (g : SmoothGaugeTransform G) (B₀ : SmoothTorusConnection G) :
    SmoothTorusConnection G

opaque ymFlow {G : Type*} (B₀ : SmoothTorusConnection G) (s : ℝ) (hs : 0 < s ∧ s ≤ 1) :
    SmoothTorusConnection G

opaque normCminusKappa {G : Type*} (κ : ℝ) (B : SmoothTorusConnection G) : ℝ

/-- Problem norm `‖B₀‖_{cov,-κ}`. -/
opaque covInvNorm {G : Type*} (κ : ℝ) (B₀ : SmoothTorusConnection G) : ℝ

opaque divLinftyNorm {G : Type*} (B : SmoothTorusConnection G) : ℝ

noncomputable def invMass {G : Type*} (κ : ℝ) (B₀ : SmoothTorusConnection G) : ℝ :=
  1 + covInvNorm κ B₀

noncomputable def gaugeFixingLeftHand {G : Type*} (κ : ℝ) (g : SmoothGaugeTransform G)
    (B₀ : SmoothTorusConnection G) : ℝ :=
  normCminusKappa κ (gaugeAct g B₀) +
    sSup
      (Set.image (fun s : { x // 0 < x ∧ x ≤ 1 } =>
        s.1 ^ κ * divLinftyNorm (gaugeAct g (ymFlow B₀ s.1 s.2))) Set.univ)

noncomputable def gaugeFixingRightHand {G : Type*} (κ c C : ℝ) (B₀ : SmoothTorusConnection G) :
    ℝ :=
  max 0 C * invMass κ B₀ ^ max 0 c

def gaugeFixingTheorem (G : Type*) (κ c C : ℝ) : Prop :=
  kappaAdmissible κ → 0 < c → 0 < C →
    ∀ B₀ : SmoothTorusConnection G,
      ∃ g : SmoothGaugeTransform G,
        gaugeFixingLeftHand κ g B₀ ≤ gaugeFixingRightHand κ c C B₀

namespace GaugeFixingPoly

lemma one_le_invMass {G : Type*} (κ : ℝ) (B₀ : SmoothTorusConnection G)
    (hnonneg : 0 ≤ covInvNorm κ B₀) : 1 ≤ invMass κ B₀ := by
  dsimp [invMass]; linarith

lemma one_add_mul_pow_le {a M p q : ℝ} (ha : 0 ≤ a) (hM : 1 ≤ M) (hp : 0 < p) (hq : 0 < q) :
    (1 + a * M ^ p) ^ q ≤ (1 + a) ^ q * M ^ (p * q) := by
  have hMp : 1 ≤ M ^ p := Real.one_le_rpow hM (le_of_lt hp)
  have hsum : 1 + a * M ^ p ≤ (1 + a) * M ^ p := by nlinarith
  calc
    (1 + a * M ^ p) ^ q ≤ ((1 + a) * M ^ p) ^ q :=
      Real.rpow_le_rpow (by positivity) hsum (le_of_lt hq)
    _ = (1 + a) ^ q * (M ^ p) ^ q := by
      exact Real.mul_rpow (by positivity) (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hM)) p)
    _ = (1 + a) ^ q * M ^ (p * q) := by
      rw [Real.rpow_mul (le_of_lt (lt_of_lt_of_le zero_lt_one hM))]

lemma rpow_le_of_one_le {M c d : ℝ} (hM : 1 ≤ M) (hcd : c ≤ d) :
    M ^ c ≤ M ^ d :=
  Real.rpow_le_rpow_of_exponent_le hM hcd

/-- Key parameter: if `aκ ≥ 1` and `M ≥ 1`, then `M^{1-aκ} ≤ 1`. -/
lemma curvature_mass_bound {M a κ : ℝ} (hM : 1 ≤ M) (haκ : 1 ≤ a * κ) :
    M ^ (1 - a * κ) ≤ 1 := by
  have hexp : 1 - a * κ ≤ 0 := by linarith
  calc
    M ^ (1 - a * κ) ≤ M ^ 0 := Real.rpow_le_rpow_of_exponent_le hM hexp
    _ = 1 := by simp

end GaugeFixingPoly

/-!
### Five-step analytic pipeline
-/

structure YangMillsTorusGaugeFixingHypothesis (G : Type*) where
  /-- Step 1: nonnegativity of the invariant input norm. -/
  cov_nonneg :
    ∀ (κ : ℝ) (B₀ : SmoothTorusConnection G), 0 ≤ covInvNorm κ B₀
  normC_nonneg :
    ∀ (κ : ℝ) (B : SmoothTorusConnection G), 0 ≤ normCminusKappa κ B
  flow_exists :
    ∀ B₀ : SmoothTorusConnection G, ∀ s : ℝ, (hs : 0 < s ∧ s ≤ 1) →
      ∃! Bs : SmoothTorusConnection G, Bs = ymFlow B₀ s hs
  /-- Step 2: short-time smoothing at some `s₀ ∈ (0,1]` (intended: `s₀ = c₀ M^{-a}`, `a ≥ 1/κ`). -/
  short_time_smoothing :
    ∃ (s₀ : ℝ) (hs₀ : 0 < s₀ ∧ s₀ ≤ 1) (c₁ C₁ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧
      ∀ (_κ : ℝ) (_hκ : kappaAdmissible _κ) (B₀ : SmoothTorusConnection G),
        normCminusKappa _κ (ymFlow B₀ s₀ hs₀) ≤ C₁ * invMass _κ B₀ ^ c₁
  /-- Step 3: Coulomb gauge at the smoothed connection (Uhlenbeck; `‖F(s₀)‖_{L²}` bounded when `aκ ≥ 1`). -/
  coulomb_at_smooth_time :
    ∀ (κ : ℝ) (_hκ : kappaAdmissible κ), ∃ c₂ C₃ : ℝ, 0 < c₂ ∧ 0 < C₃ ∧
      ∀ (B₀ : SmoothTorusConnection G) (s₀ : ℝ) (hs₀ : 0 < s₀ ∧ s₀ ≤ 1),
        ∃ g : SmoothGaugeTransform G,
          divLinftyNorm (gaugeAct g (ymFlow B₀ s₀ hs₀)) = 0 ∧
          normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) ≤
            C₃ * (1 + normCminusKappa κ (ymFlow B₀ s₀ hs₀)) ^ c₂
  /-- Step 4: divergence bound along the gauged flow (elliptic propagation). -/
  gauged_flow_divergence :
    ∀ (κ : ℝ) (_hκ : kappaAdmissible κ), ∃ c_div C_div : ℝ, 0 < c_div ∧ 0 < C_div ∧
      ∀ (B₀ : SmoothTorusConnection G) (s₀ : ℝ) (hs₀ : 0 < s₀ ∧ s₀ ≤ 1)
        (g : SmoothGaugeTransform G),
        divLinftyNorm (gaugeAct g (ymFlow B₀ s₀ hs₀)) = 0 →
        ∀ (s : ℝ) (hs : 0 < s ∧ s ≤ 1),
          divLinftyNorm (gaugeAct g (ymFlow B₀ s hs)) ≤
            C_div * s ^ (-κ) * invMass κ B₀ ^ c_div
  /-- Step 5: pull back `𝒞^{-κ}` from `s₀` to initial data. -/
  initial_gauge_pullback :
    ∀ (κ : ℝ) (_hκ : kappaAdmissible κ), ∃ c₄ C₄ : ℝ, 0 < c₄ ∧ 0 < C₄ ∧
      ∀ (B₀ : SmoothTorusConnection G) (s₀ : ℝ) (hs₀ : 0 < s₀ ∧ s₀ ≤ 1)
        (g : SmoothGaugeTransform G),
        normCminusKappa κ (gaugeAct g B₀) ≤
          C₄ * invMass κ B₀ ^ c₄ *
            (normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) + 1)

namespace YangMillsTorusGaugeFixingHypothesis

variable {G : Type*}

private lemma divSup_bound {κ c₂ C₃ : ℝ} (_hκ : kappaAdmissible κ) (_hc₂ : 0 < c₂) (_hC₃ : 0 < C₃)
    (B₀ : SmoothTorusConnection G) (g : SmoothGaugeTransform G)
    (hdiv :
      ∀ (s : ℝ) (hs : 0 < s ∧ s ≤ 1),
        divLinftyNorm (gaugeAct g (ymFlow B₀ s hs)) ≤
          C₃ * s ^ (-κ) * invMass κ B₀ ^ c₂)
    (hnonneg : 0 ≤ covInvNorm κ B₀) :
    sSup
        (Set.image (fun s : { x // 0 < x ∧ x ≤ 1 } =>
          s.1 ^ κ * divLinftyNorm (gaugeAct g (ymFlow B₀ s.1 s.2))) Set.univ) ≤
      C₃ * invMass κ B₀ ^ c₂ := by
  set M := invMass κ B₀
  have hM : 1 ≤ M := GaugeFixingPoly.one_le_invMass κ B₀ hnonneg
  have hs1 : (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 := by constructor <;> norm_num
  have hne :
      (Set.image (fun s : { x // 0 < x ∧ x ≤ 1 } =>
          s.1 ^ κ * divLinftyNorm (gaugeAct g (ymFlow B₀ s.1 s.2))) Set.univ).Nonempty := by
    refine ⟨1 ^ κ * divLinftyNorm (gaugeAct g (ymFlow B₀ 1 hs1)), ?_⟩
    exact ⟨⟨1, hs1⟩, Set.mem_univ _, rfl⟩
  refine csSup_le hne ?_
  intro y hy
  obtain ⟨s, _, rfl⟩ := hy
  have hs := s.2
  have hs_pos : 0 < s.1 := hs.1
  have hdiv' := hdiv s.1 hs
  calc
    s.1 ^ κ * divLinftyNorm (gaugeAct g (ymFlow B₀ s.1 hs)) ≤
        s.1 ^ κ * (C₃ * s.1 ^ (-κ) * M ^ c₂) := by gcongr
    _ = C₃ * (s.1 ^ κ * s.1 ^ (-κ)) * M ^ c₂ := by ring
    _ = C₃ * M ^ c₂ := by
      have hpow : s.1 ^ κ * s.1 ^ (-κ) = 1 := by
        rw [← Real.rpow_add hs_pos, show κ + (-κ) = 0 by ring, Real.rpow_zero]
      rw [hpow]; ring

private lemma gaugedSmooth_norm_bound {κ c₁ c₂ c₄ C₁ C₃ C₄ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (_hc₄ : 0 < c₄) (hC₁ : 0 < C₁) (hC₃ : 0 < C₃) (hC₄ : 0 < C₄)
    (_hκ : kappaAdmissible κ) (B₀ : SmoothTorusConnection G) (s₀ : ℝ) (hs₀ : 0 < s₀ ∧ s₀ ≤ 1)
    (g : SmoothGaugeTransform G)
    (hsmooth : normCminusKappa κ (ymFlow B₀ s₀ hs₀) ≤ C₁ * invMass κ B₀ ^ c₁)
    (hnorm :
      normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) ≤
        C₃ * (1 + normCminusKappa κ (ymFlow B₀ s₀ hs₀)) ^ c₂)
    (hinitial :
      normCminusKappa κ (gaugeAct g B₀) ≤
        C₄ * invMass κ B₀ ^ c₄ * (normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) + 1))
    (hnonneg : 0 ≤ covInvNorm κ B₀)
    (hnormC : 0 ≤ normCminusKappa κ (ymFlow B₀ s₀ hs₀)) :
    normCminusKappa κ (gaugeAct g B₀) ≤
      C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) * invMass κ B₀ ^ (c₄ + c₁ * c₂) := by
  set M := invMass κ B₀
  have hM : 1 ≤ M := GaugeFixingPoly.one_le_invMass κ B₀ hnonneg
  have hsmooth' : normCminusKappa κ (ymFlow B₀ s₀ hs₀) ≤ C₁ * M ^ c₁ := by simpa [M] using hsmooth
  have hinner :
      (1 + normCminusKappa κ (ymFlow B₀ s₀ hs₀)) ^ c₂ ≤ (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) := by
    calc
      (1 + normCminusKappa κ (ymFlow B₀ s₀ hs₀)) ^ c₂ ≤ (1 + C₁ * M ^ c₁) ^ c₂ := by gcongr
      _ ≤ (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) :=
        GaugeFixingPoly.one_add_mul_pow_le (a := C₁) (M := M) (p := c₁) (q := c₂)
          (le_of_lt hC₁) hM hc₁ hc₂
  have hmid :
      normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) ≤
        C₃ * (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) := by
    calc
      normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) ≤
          C₃ * (1 + normCminusKappa κ (ymFlow B₀ s₀ hs₀)) ^ c₂ := hnorm
      _ ≤ C₃ * ((1 + C₁) ^ c₂ * M ^ (c₁ * c₂)) := by gcongr
      _ = C₃ * (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) := by ring
  have hMpow : 1 ≤ M ^ (c₁ * c₂) := Real.one_le_rpow hM (mul_nonneg (le_of_lt hc₁) (le_of_lt hc₂))
  have hX : 1 ≤ (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) := by
    nlinarith [Real.one_le_rpow (show 1 ≤ 1 + C₁ from by linarith) (le_of_lt hc₂), hMpow]
  have hcoef : C₃ * (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) + 1 ≤
      (C₃ + 1) * (1 + C₁) ^ c₂ * M ^ (c₁ * c₂) := by nlinarith [hX]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  calc
    normCminusKappa κ (gaugeAct g B₀) ≤
        C₄ * M ^ c₄ * (normCminusKappa κ (gaugeAct g (ymFlow B₀ s₀ hs₀)) + 1) := by
      simpa [M, mul_assoc, mul_left_comm, mul_comm] using hinitial
    _ ≤ C₄ * M ^ c₄ * ((C₃ + 1) * (1 + C₁) ^ c₂ * M ^ (c₁ * c₂)) := by gcongr; linarith [hmid, hcoef]
    _ = C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) * M ^ (c₄ + c₁ * c₂) := by
      rw [Real.rpow_add hMpos]; ring
    _ = C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) * invMass κ B₀ ^ (c₄ + c₁ * c₂) := by simp [M]

theorem exists_gaugeFixing_constants (κ : ℝ) (hκ : kappaAdmissible κ)
    (H : YangMillsTorusGaugeFixingHypothesis G) :
    ∃ c C, 0 < c ∧ 0 < C ∧ gaugeFixingTheorem G κ c C := by
  rcases H.short_time_smoothing with ⟨s₀, hs₀, c₁, C₁, hc₁, hC₁, hsmooth⟩
  rcases H.coulomb_at_smooth_time κ hκ with ⟨c₂, C₃, hc₂, hC₃, hgauge⟩
  rcases H.initial_gauge_pullback κ hκ with ⟨c₄, C₄, hc₄, hC₄, hpullback⟩
  rcases H.gauged_flow_divergence κ hκ with ⟨c_div, C_div, hc_div, hC_div, hdiv_prop⟩
  set c := max c_div (max c₂ (c₄ + c₁ * c₂))
  set C := C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) + C_div
  have hc : 0 < c := by
    dsimp [c]
    rcases max_choice c_div (max c₂ (c₄ + c₁ * c₂)) with h | h <;> rw [h]
    · exact hc_div
    · rcases max_choice c₂ (c₄ + c₁ * c₂) with h' | h' <;> rw [h']
      · exact hc₂
      · nlinarith [hc₄, mul_pos hc₁ hc₂]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro _ _ _ B₀
  rcases hgauge B₀ s₀ hs₀ with ⟨g, hdiv₀, hnorm⟩
  have hnonneg := H.cov_nonneg κ B₀
  have hnormC := H.normC_nonneg κ (ymFlow B₀ s₀ hs₀)
  have hdiv : ∀ (s : ℝ) (hs : 0 < s ∧ s ≤ 1),
      divLinftyNorm (gaugeAct g (ymFlow B₀ s hs)) ≤
        C_div * s ^ (-κ) * invMass κ B₀ ^ c_div :=
    fun s hs => hdiv_prop B₀ s₀ hs₀ g hdiv₀ s hs
  have hnorm₀ :=
    gaugedSmooth_norm_bound hc₁ hc₂ hc₄ hC₁ hC₃ hC₄ hκ B₀ s₀ hs₀ g (hsmooth κ hκ B₀) hnorm
      (hpullback B₀ s₀ hs₀ g) hnonneg hnormC
  have hsup := divSup_bound hκ hc_div hC_div B₀ g hdiv hnonneg
  refine ⟨g, ?_⟩
  dsimp [gaugeFixingLeftHand]
  set M := invMass κ B₀
  have hM : 1 ≤ M := GaugeFixingPoly.one_le_invMass κ B₀ hnonneg
  have hMpos : 0 ≤ M := le_of_lt (lt_of_lt_of_le zero_lt_one hM)
  have hc₂_le : c₂ ≤ c := by
    dsimp [c]
    exact le_trans (le_max_left c₂ _) (le_max_right c_div _)
  have hc_div_le : c_div ≤ c := by
    dsimp [c]
    exact le_max_left c_div _
  have hc_combined : c₄ + c₁ * c₂ ≤ c := by
    dsimp [c]
    exact le_trans (le_max_right c₂ _) (le_max_right c_div _)
  have hM_c : M ^ c₂ ≤ M ^ c := GaugeFixingPoly.rpow_le_of_one_le hM hc₂_le
  have hM_c' : M ^ (c₄ + c₁ * c₂) ≤ M ^ c :=
    GaugeFixingPoly.rpow_le_of_one_le hM hc_combined
  have hM_cdiv : M ^ c_div ≤ M ^ c := GaugeFixingPoly.rpow_le_of_one_le hM hc_div_le
  have hrhs : gaugeFixingRightHand κ c C B₀ = C * M ^ c := by
    dsimp [gaugeFixingRightHand, invMass, c, M]
    rw [max_eq_right hc.le, max_eq_right hC.le]
  have hterm₁ : C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) * M ^ (c₄ + c₁ * c₂) ≤
      C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) * M ^ c := by gcongr
  have hterm₂ : C_div * M ^ c_div ≤ C_div * M ^ c := by gcongr
  calc
    gaugeFixingLeftHand κ g B₀ ≤
        C₄ * (1 + C₁) ^ c₂ * (C₃ + 1) * M ^ (c₄ + c₁ * c₂) + C_div * M ^ c_div := by
      exact add_le_add hnorm₀ hsup
    _ ≤ C * M ^ c := by
      dsimp [C]
      nlinarith [hterm₁, hterm₂, hMpos, Real.rpow_nonneg hMpos c]
    _ = gaugeFixingRightHand κ c C B₀ := hrhs.symm

theorem gaugeFixingTheorem_of_hypothesis (κ : ℝ) (hκ : kappaAdmissible κ)
    (H : YangMillsTorusGaugeFixingHypothesis G) :
    ∃ c C, 0 < c ∧ 0 < C ∧ gaugeFixingTheorem G κ c C :=
  exists_gaugeFixing_constants κ hκ H

end YangMillsTorusGaugeFixingHypothesis

end ProblemC3

end Hqiv.Analysis
