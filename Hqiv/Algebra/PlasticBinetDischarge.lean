import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Algebra.PlasticZeta3Closed
import Hqiv.Algebra.PlasticDominantRoot

namespace Hqiv.Algebra

/-!
# Plastic Binet discharge helpers

This module reduces certificate construction to concrete algebraic checks:
- root equations for the three spectral values,
- initial-value matching at `n = 0,1,2`,
- one ratio identity assumption.
-/

/-- Generic order-3 recurrence sequence in Binet form. -/
def binetSeq (a r b s c t : ℝ) (n : ℕ) : ℝ :=
  a * r ^ (n : ℕ) + b * s ^ (n : ℕ) + c * t ^ (n : ℕ)

/-- The canonical plastic root satisfies `ρ^3 = ρ + 1`. -/
lemma plasticRoot_pow_three_eq :
    plasticRoot ^ (3 : ℕ) = plasticRoot + 1 := by
  have h0 : plasticCubic plasticRoot = 0 := plasticRoot_eq_zero
  unfold plasticCubic at h0
  linarith

@[simp] lemma plasticPReal_zero : plasticPReal 0 = 1 := by
  unfold plasticPReal
  norm_num

@[simp] lemma plasticPReal_one : plasticPReal 1 = 1 := by
  unfold plasticPReal
  norm_num

@[simp] lemma plasticPReal_two : plasticPReal 2 = 2 := by
  unfold plasticPReal
  norm_num

@[simp] lemma plasticQReal_zero : plasticQReal 0 = 1 := by
  unfold plasticQReal
  norm_num

@[simp] lemma plasticQReal_one : plasticQReal 1 = 2 := by
  unfold plasticQReal
  norm_num

@[simp] lemma plasticQReal_two : plasticQReal 2 = 3 := by
  unfold plasticQReal
  norm_num

@[simp] lemma binetSeq_zero (a r b s c t : ℝ) :
    binetSeq a r b s c t 0 = a + b + c := by
  unfold binetSeq
  ring

@[simp] lemma binetSeq_one (a r b s c t : ℝ) :
    binetSeq a r b s c t 1 = a * r + b * s + c * t := by
  unfold binetSeq
  ring

@[simp] lemma binetSeq_two (a r b s c t : ℝ) :
    binetSeq a r b s c t 2 = a * r ^ (2 : ℕ) + b * s ^ (2 : ℕ) + c * t ^ (2 : ℕ) := by
  unfold binetSeq
  ring

/-- No real number with `|x| < 1` can satisfy `x^3 = x + 1`. -/
lemma not_real_root_cubic_of_abs_lt_one
    {x : ℝ}
    (hxabs : |x| < (1 : ℝ)) :
    x ^ (3 : ℕ) ≠ x + 1 := by
  intro hx
  have hxlt1 : x < 1 := (abs_lt.mp hxabs).2
  have hxgtm1 : -1 < x := (abs_lt.mp hxabs).1
  have hx2lt : x ^ (2 : ℕ) < 1 := by nlinarith
  have hfactor : x ^ (3 : ℕ) - x = x * (x ^ (2 : ℕ) - 1) := by ring
  have habs_lt_one : |x ^ (3 : ℕ) - x| < 1 := by
    rw [hfactor, abs_mul]
    have habs_sq_sub : |x ^ (2 : ℕ) - 1| = 1 - x ^ (2 : ℕ) := by
      have hnonneg : 0 ≤ 1 - x ^ (2 : ℕ) := by linarith
      have hrewrite : x ^ (2 : ℕ) - 1 = -(1 - x ^ (2 : ℕ)) := by ring
      rw [hrewrite, abs_neg, abs_of_nonneg hnonneg]
    rw [habs_sq_sub]
    have habs_nonneg : 0 ≤ |x| := abs_nonneg x
    have hfac_nonneg : 0 ≤ 1 - x ^ (2 : ℕ) := by linarith
    have habs_lt : |x| < 1 := hxabs
    have hfac_le : 1 - x ^ (2 : ℕ) ≤ 1 := by nlinarith [hx2lt]
    have hmul_lt : |x| * (1 - x ^ (2 : ℕ)) < 1 * 1 := by nlinarith
    simpa using hmul_lt
  have hlt : x ^ (3 : ℕ) - x < 1 := lt_of_le_of_lt (le_abs_self (x ^ (3 : ℕ) - x)) habs_lt_one
  have hx_eq : x ^ (3 : ℕ) - x = 1 := by linarith [hx]
  linarith

/-- Immediate contradiction form used when assumptions include both
`|x| < 1` and `x^3 = x + 1`.
-/
lemma false_of_abs_lt_one_and_cubic_eq
    {x : ℝ}
    (hxabs : |x| < (1 : ℝ))
    (hx : x ^ (3 : ℕ) = x + 1) :
    False := by
  exact (not_real_root_cubic_of_abs_lt_one hxabs) hx

lemma binetSeq_rec
    (a r b s c t : ℝ)
    (hr : r ^ (3 : ℕ) = r + 1)
    (hs : s ^ (3 : ℕ) = s + 1)
    (ht : t ^ (3 : ℕ) = t + 1)
    (n : ℕ) :
    binetSeq a r b s c t (n + 3) = binetSeq a r b s c t (n + 1) + binetSeq a r b s c t n := by
  unfold binetSeq
  -- Expand each power with `x^(n+3) = x^n * x^3`.
  repeat rw [pow_add]
  repeat rw [pow_one]
  rw [hr, hs, ht]
  ring

lemma eq_of_third_order_recurrence
    (u v : ℕ → ℝ)
    (hu : ∀ n : ℕ, u (n + 3) = u (n + 1) + u n)
    (hv : ∀ n : ℕ, v (n + 3) = v (n + 1) + v n)
    (h0 : u 0 = v 0)
    (h1 : u 1 = v 1)
    (h2 : u 2 = v 2) :
    ∀ n : ℕ, u n = v n
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | n + 3 => by
      rw [hu n, hv n, eq_of_third_order_recurrence u v hu hv h0 h1 h2 (n + 1),
        eq_of_third_order_recurrence u v hu hv h0 h1 h2 n]

/-- Build `hP` from spectral root equations and initial-value matching. -/
lemma plasticPReal_eq_binet_of_data
    (ap bp cp rho sRoot tRoot : ℝ)
    (hrho : rho ^ (3 : ℕ) = rho + 1)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap rho bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap rho bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap rho bp sRoot cp tRoot 2) :
    ∀ n : ℕ, plasticPReal n = binetSeq ap rho bp sRoot cp tRoot n := by
  apply eq_of_third_order_recurrence plasticPReal (binetSeq ap rho bp sRoot cp tRoot)
  · intro n
    simp [plasticPReal_rec]
  · intro n
    simpa using binetSeq_rec ap rho bp sRoot cp tRoot hrho hs ht n
  · simpa using hp0
  · simpa using hp1
  · simpa using hp2

/-- Build `hQ` from spectral root equations and initial-value matching. -/
lemma plasticQReal_eq_binet_of_data
    (aq bq cq rho sRoot tRoot : ℝ)
    (hrho : rho ^ (3 : ℕ) = rho + 1)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hq0 : plasticQReal 0 = binetSeq aq rho bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq rho bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq rho bq sRoot cq tRoot 2) :
    ∀ n : ℕ, plasticQReal n = binetSeq aq rho bq sRoot cq tRoot n := by
  apply eq_of_third_order_recurrence plasticQReal (binetSeq aq rho bq sRoot cq tRoot)
  · intro n
    simp [plasticQReal_rec]
  · intro n
    simpa using binetSeq_rec aq rho bq sRoot cq tRoot hrho hs ht n
  · simpa using hq0
  · simpa using hq1
  · simpa using hq2

/-- Certificate constructor with `hP/hQ` discharged from root + init data. -/
theorem exists_plasticBinetCertificate_of_root_and_init_data
    (ap aq bp cp bq cq rho sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hrho : rho ^ (3 : ℕ) = rho + 1)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap rho bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap rho bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap rho bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq rho bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq rho bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq rho bq sRoot cq tRoot 2)
    (hratio :
      ∀ n : ℕ,
        (ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)) /
        (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) = ap / aq)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate := by
  refine exists_plasticBinetCertificate_of_data
    ap aq bp cp bq cq rho sRoot tRoot
    hsRoot htRoot hAq
    ?_ ?_ hratio hclosed
  · intro n
    simpa [binetSeq] using
      plasticPReal_eq_binet_of_data ap bp cp rho sRoot tRoot hrho hs ht hp0 hp1 hp2 n
  · intro n
    simpa [binetSeq] using
      plasticQReal_eq_binet_of_data aq bq cq rho sRoot tRoot hrho hs ht hq0 hq1 hq2 n

/-- Ratio identity from coefficient proportionality for two Binet tracks. -/
lemma binet_ratio_identity_of_proportional_coeffs
    (ap aq bp cp bq cq rho sRoot tRoot : ℝ)
    (k : ℝ)
    (hAq : aq ≠ 0)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0) :
    ∀ n : ℕ,
      (ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)) /
      (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) = ap / aq := by
  intro n
  have hnum :
      ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)
        = k * (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) := by
    rw [hap, hbp, hcp]
    ring
  rw [hnum]
  have hden' := hden n
  have hfrac :
      (k * (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ))) /
        (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) = k := by
    rw [mul_div_assoc, div_self hden', mul_one]
  rw [hfrac]
  rw [hap]
  field_simp [hAq]

/-- If `ap = k * aq` and `aq ≠ 0`, then the dominant ratio is `k`. -/
lemma ratio_eq_of_proportional
    (ap aq k : ℝ)
    (hAq : aq ≠ 0)
    (hap : ap = k * aq) :
    ap / aq = k := by
  rw [hap]
  field_simp [hAq]

/-- Convenience: discharge `hclosed` directly from proportionality and a
target value for `k`.
-/
lemma closed_eq_of_proportional
    (ap aq k : ℝ)
    (hAq : aq ≠ 0)
    (hap : ap = k * aq)
    (hk : k = plasticZeta3Candidate) :
    ap / aq = plasticZeta3Candidate := by
  rw [ratio_eq_of_proportional ap aq k hAq hap, hk]

/-- Strong certificate constructor: discharges `hP`, `hQ`, and `hratio`
from root equations, initial matching, and coefficient proportionality.
-/
theorem exists_plasticBinetCertificate_of_root_init_and_proportionality
    (ap aq bp cp bq cq rho sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hrho : rho ^ (3 : ℕ) = rho + 1)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap rho bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap rho bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap rho bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq rho bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq rho bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq rho bq sRoot cq tRoot 2)
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate := by
  apply exists_plasticBinetCertificate_of_root_and_init_data
    ap aq bp cp bq cq rho sRoot tRoot
    hsRoot htRoot hAq
    hrho hs ht
    hp0 hp1 hp2
    hq0 hq1 hq2
  · exact binet_ratio_identity_of_proportional_coeffs
      ap aq bp cp bq cq rho sRoot tRoot k hAq hap hbp hcp hden
  · exact hclosed

/-- Dominant-term criterion implying denominator nonvanishing for all `n`. -/
lemma denominator_ne_zero_of_dominant_bound
    (aq bq cq rho sRoot tRoot : ℝ)
    (hdom :
      ∀ n : ℕ,
        |aq * rho ^ (n : ℕ)| >
          |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)|) :
    ∀ n : ℕ,
      aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0 := by
  intro n hzero
  have h1 :
      |aq * rho ^ (n : ℕ)| = |bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)| := by
    have :
        aq * rho ^ (n : ℕ) = -(bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) := by
      linarith [hzero]
    rw [this, abs_neg]
  have h2 :
      |bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)| ≤
        |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| := by
    exact abs_add_le _ _
  have hle :
      |aq * rho ^ (n : ℕ)| ≤ |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| := by
    calc
      |aq * rho ^ (n : ℕ)| = |bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)| := h1
      _ ≤ |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| := h2
  exact (not_le_of_gt (hdom n)) hle

/-- Convenience wrapper: if you can prove a strict dominant absolute-value bound,
you get the denominator nonvanishing hypothesis required by the ratio identity.
-/
lemma denominator_ne_zero_for_constructor
    (aq bq cq rho sRoot tRoot : ℝ)
    (hdom :
      ∀ n : ℕ,
        |aq * rho ^ (n : ℕ)| >
          |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)|) :
    ∀ n : ℕ,
      aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0 :=
  denominator_ne_zero_of_dominant_bound aq bq cq rho sRoot tRoot hdom

/-- Split-bound variant: prove strict dominance by combining a lower bound for
the dominant term with an upper bound for the perturbation envelope.
-/
lemma denominator_ne_zero_of_split_bounds
    (aq bq cq rho sRoot tRoot : ℝ)
    (D : ℕ → ℝ)
    (hmain : ∀ n : ℕ, |aq * rho ^ (n : ℕ)| > D n)
    (hpert :
      ∀ n : ℕ, |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| ≤ D n) :
    ∀ n : ℕ,
      aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0 := by
  apply denominator_ne_zero_of_dominant_bound aq bq cq rho sRoot tRoot
  intro n
  exact lt_of_le_of_lt (hpert n) (hmain n)

/-- Convenience corollary mirroring constructor inputs. -/
lemma denominator_ne_zero_for_constructor_of_split_bounds
    (aq bq cq rho sRoot tRoot : ℝ)
    (D : ℕ → ℝ)
    (hmain : ∀ n : ℕ, |aq * rho ^ (n : ℕ)| > D n)
    (hpert :
      ∀ n : ℕ, |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| ≤ D n) :
    ∀ n : ℕ,
      aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0 :=
  denominator_ne_zero_of_split_bounds aq bq cq rho sRoot tRoot D hmain hpert

/-- Basic geometric bound: if `|x| ≤ r` with `r ≥ 0`, then
`|a * x^n| ≤ |a| * r^n`.
-/
lemma abs_mul_pow_le_of_abs_le_radius
    (a x r : ℝ)
    (hx : |x| ≤ r)
    (n : ℕ) :
    |a * x ^ (n : ℕ)| ≤ |a| * r ^ (n : ℕ) := by
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg x) hx n)
    (abs_nonneg a)

/-- Perturbation envelope from a common radius bound on subdominant roots. -/
lemma perturbation_bound_of_common_radius
    (bq cq sRoot tRoot r : ℝ)
    (hsr : |sRoot| ≤ r)
    (htr : |tRoot| ≤ r)
    (n : ℕ) :
    |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| ≤
      (|bq| + |cq|) * r ^ (n : ℕ) := by
  have hb : |bq * sRoot ^ (n : ℕ)| ≤ |bq| * r ^ (n : ℕ) :=
    abs_mul_pow_le_of_abs_le_radius bq sRoot r hsr n
  have hc : |cq * tRoot ^ (n : ℕ)| ≤ |cq| * r ^ (n : ℕ) :=
    abs_mul_pow_le_of_abs_le_radius cq tRoot r htr n
  have hadd : |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)|
      ≤ |bq| * r ^ (n : ℕ) + |cq| * r ^ (n : ℕ) := add_le_add hb hc
  have hfactor : |bq| * r ^ (n : ℕ) + |cq| * r ^ (n : ℕ) =
      (|bq| + |cq|) * r ^ (n : ℕ) := by ring
  exact hadd.trans (by simp [hfactor])

/-- Variant with the canonical dominant root `plasticRoot`, so `hrho` is
discharged internally. -/
theorem exists_plasticBinetCertificate_of_plasticRoot_init_and_proportionality
    (ap aq bp cp bq cq sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap plasticRoot bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap plasticRoot bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap plasticRoot bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq plasticRoot bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq plasticRoot bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq plasticRoot bq sRoot cq tRoot 2)
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate := by
  exact exists_plasticBinetCertificate_of_root_init_and_proportionality
    ap aq bp cp bq cq plasticRoot sRoot tRoot
    hsRoot htRoot hAq
    plasticRoot_pow_three_eq hs ht
    hp0 hp1 hp2
    hq0 hq1 hq2
    k hap hbp hcp hden hclosed

/-- Same constructor, but `hclosed` is discharged from `ap = k*aq` and `k`
being the target closed value.
-/
theorem exists_plasticBinetCertificate_of_plasticRoot_init_and_proportionality'
    (ap aq bp cp bq cq sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap plasticRoot bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap plasticRoot bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap plasticRoot bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq plasticRoot bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq plasticRoot bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq plasticRoot bq sRoot cq tRoot 2)
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0)
    (hk : k = plasticZeta3Candidate) :
    ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate := by
  exact exists_plasticBinetCertificate_of_plasticRoot_init_and_proportionality
    ap aq bp cp bq cq sRoot tRoot
    hsRoot htRoot hAq hs ht
    hp0 hp1 hp2
    hq0 hq1 hq2
    k hap hbp hcp hden
    (closed_eq_of_proportional ap aq k hAq hap hk)

/-- Concrete certificate object extracted from the strong plastic-root constructor. -/
noncomputable def plasticBinetCertificate_of_plasticRoot_init_and_proportionality
    (ap aq bp cp bq cq sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap plasticRoot bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap plasticRoot bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap plasticRoot bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq plasticRoot bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq plasticRoot bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq plasticRoot bq sRoot cq tRoot 2)
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    PlasticBinetCertificate :=
  Classical.choose <|
    exists_plasticBinetCertificate_of_plasticRoot_init_and_proportionality
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq hs ht
      hp0 hp1 hp2 hq0 hq1 hq2
      k hap hbp hcp hden hclosed

/-- The extracted certificate has the required closed-form dominant ratio. -/
theorem plasticBinetCertificate_of_plasticRoot_init_and_proportionality_spec
    (ap aq bp cp bq cq sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap plasticRoot bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap plasticRoot bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap plasticRoot bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq plasticRoot bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq plasticRoot bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq plasticRoot bq sRoot cq tRoot 2)
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    (plasticBinetCertificate_of_plasticRoot_init_and_proportionality
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq hs ht
      hp0 hp1 hp2 hq0 hq1 hq2
      k hap hbp hcp hden hclosed).ap /
      (plasticBinetCertificate_of_plasticRoot_init_and_proportionality
        ap aq bp cp bq cq sRoot tRoot
        hsRoot htRoot hAq hs ht
        hp0 hp1 hp2 hq0 hq1 hq2
        k hap hbp hcp hden hclosed).aq = plasticZeta3Candidate := by
  exact (Classical.choose_spec
    (exists_plasticBinetCertificate_of_plasticRoot_init_and_proportionality
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq hs ht
      hp0 hp1 hp2 hq0 hq1 hq2
      k hap hbp hcp hden hclosed))

/-- Split-bounds variant that discharges `hden` before extracting a concrete
certificate object.
-/
noncomputable def plasticBinetCertificate_of_plasticRoot_init_prop_splitBounds
    (ap aq bp cp bq cq sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hs : sRoot ^ (3 : ℕ) = sRoot + 1)
    (ht : tRoot ^ (3 : ℕ) = tRoot + 1)
    (hp0 : plasticPReal 0 = binetSeq ap plasticRoot bp sRoot cp tRoot 0)
    (hp1 : plasticPReal 1 = binetSeq ap plasticRoot bp sRoot cp tRoot 1)
    (hp2 : plasticPReal 2 = binetSeq ap plasticRoot bp sRoot cp tRoot 2)
    (hq0 : plasticQReal 0 = binetSeq aq plasticRoot bq sRoot cq tRoot 0)
    (hq1 : plasticQReal 1 = binetSeq aq plasticRoot bq sRoot cq tRoot 1)
    (hq2 : plasticQReal 2 = binetSeq aq plasticRoot bq sRoot cq tRoot 2)
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (D : ℕ → ℝ)
    (hmain : ∀ n : ℕ, |aq * plasticRoot ^ (n : ℕ)| > D n)
    (hpert : ∀ n : ℕ, |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| ≤ D n)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    PlasticBinetCertificate :=
  plasticBinetCertificate_of_plasticRoot_init_and_proportionality
    ap aq bp cp bq cq sRoot tRoot
    hsRoot htRoot hAq hs ht
    hp0 hp1 hp2 hq0 hq1 hq2
    k hap hbp hcp
    (denominator_ne_zero_for_constructor_of_split_bounds
      aq bq cq plasticRoot sRoot tRoot D hmain hpert)
    hclosed

/-- Realistic constructor: keep `plasticRoot` as the real dominant root and
assume the full Binet identities directly (no real cubic-root constraints on
`sRoot,tRoot`).
-/
theorem exists_plasticBinetCertificate_of_plasticRoot_binet_and_proportionality
    (ap aq bp cp bq cq sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hP : ∀ n : ℕ, plasticPReal n = ap * plasticRoot ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ))
    (hQ : ∀ n : ℕ, plasticQReal n = aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ))
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hden :
      ∀ n : ℕ,
        aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ) ≠ 0)
    (hk : k = plasticZeta3Candidate) :
    ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate := by
  refine exists_plasticBinetCertificate_of_data
    ap aq bp cp bq cq plasticRoot sRoot tRoot
    hsRoot htRoot hAq
    hP hQ
    ?_ ?_
  · exact binet_ratio_identity_of_proportional_coeffs
      ap aq bp cp bq cq plasticRoot sRoot tRoot k hAq hap hbp hcp hden
  · exact closed_eq_of_proportional ap aq k hAq hap hk

end Hqiv.Algebra

