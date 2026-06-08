import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Hqiv.Algebra.PlasticBinetDischarge
import Hqiv.Algebra.PlasticZeta3Closed

namespace Hqiv.Algebra

open Filter
open scoped Topology

/-!
# Plastic zeta-3 milestone theorem

This module states the focused "second-half" formal theorem:
from concrete spectral/Binet assumptions (including the external zeta-limit
bridge), conclude the closed plastic expression.
-/

/-- Bundles the remaining concrete obligations for the plastic-ζ(3) endpoint in
the corrected-assumptions setting (real dominant root + direct Binet identities
for subdominant channels).
-/
structure PlasticZeta3MilestoneAssumptions where
  zeta3Value : ℝ
  ap : ℝ
  aq : ℝ
  bp : ℝ
  cp : ℝ
  bq : ℝ
  cq : ℝ
  sRoot : ℝ
  tRoot : ℝ
  hsRoot : |sRoot| < (1 : ℝ)
  htRoot : |tRoot| < (1 : ℝ)
  hAq : aq ≠ 0
  hP : ∀ n : ℕ, plasticPReal n = ap * plasticRoot ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)
  hQ : ∀ n : ℕ, plasticQReal n = aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)
  k : ℝ
  hap : ap = k * aq
  hbp : bp = k * bq
  hcp : cp = k * cq
  D : ℕ → ℝ
  hmain : ∀ n : ℕ, |aq * plasticRoot ^ (n : ℕ)| > D n
  hpert : ∀ n : ℕ, |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| ≤ D n
  hk : k = plasticZeta3Candidate
  hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)

/-- Milestone theorem: once the spectral/Binet side and the zeta-limit bridge
are provided, the closed form follows.
-/
theorem zeta_three_plastic_closed_milestone
    (zeta3Value : ℝ)
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
    (hclosed : ap / aq = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate := by
  let c : PlasticBinetCertificate :=
    plasticBinetCertificate_of_plasticRoot_init_prop_splitBounds
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq hs ht
      hp0 hp1 hp2 hq0 hq1 hq2
      k hap hbp hcp
      D hmain hpert
      hclosed
  have hcert : ∃ c' : PlasticBinetCertificate, c'.ap / c'.aq = plasticZeta3Candidate := by
    refine ⟨c, ?_⟩
    -- Unfolding the local abbreviation `c` yields the concrete constructor spec.
    dsimp [c]
    exact plasticBinetCertificate_of_plasticRoot_init_and_proportionality_spec
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq hs ht
      hp0 hp1 hp2 hq0 hq1 hq2
      k hap hbp hcp
      (denominator_ne_zero_for_constructor_of_split_bounds
        aq bq cq plasticRoot sRoot tRoot D hmain hpert)
      hclosed
  exact zeta_three_plastic_closed zeta3Value hcert hzeta

/-- Stronger milestone variant: the closed-ratio condition is discharged from
`ap = k*aq` and `k = plasticZeta3Candidate`, so no separate `hclosed` input is
needed.
-/
theorem zeta_three_plastic_closed_milestone'
    (zeta3Value : ℝ)
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
    (hk : k = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate := by
  have hcert : ∃ c' : PlasticBinetCertificate, c'.ap / c'.aq = plasticZeta3Candidate := by
    have hclosed : ap / aq = plasticZeta3Candidate := by
      rw [hap]
      field_simp [hAq]
      simp [hk]
    exact exists_plasticBinetCertificate_of_plasticRoot_init_and_proportionality
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq hs ht
      hp0 hp1 hp2 hq0 hq1 hq2
      k hap hbp hcp
      (denominator_ne_zero_for_constructor_of_split_bounds
        aq bq cq plasticRoot sRoot tRoot D hmain hpert)
      hclosed
  exact zeta_three_plastic_closed zeta3Value hcert hzeta

/-- Corrected-assumptions milestone: uses direct Binet identities `hP/hQ`
for the subdominant channels, avoiding inconsistent real cubic-root constraints
on `sRoot,tRoot`.
-/
theorem zeta_three_plastic_closed_milestone_binet
    (zeta3Value : ℝ)
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
    (D : ℕ → ℝ)
    (hmain : ∀ n : ℕ, |aq * plasticRoot ^ (n : ℕ)| > D n)
    (hpert : ∀ n : ℕ, |bq * sRoot ^ (n : ℕ)| + |cq * tRoot ^ (n : ℕ)| ≤ D n)
    (hk : k = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate := by
  have hcert : ∃ c' : PlasticBinetCertificate, c'.ap / c'.aq = plasticZeta3Candidate := by
    exact exists_plasticBinetCertificate_of_plasticRoot_binet_and_proportionality
      ap aq bp cp bq cq sRoot tRoot
      hsRoot htRoot hAq
      hP hQ
      k hap hbp hcp
      (denominator_ne_zero_for_constructor_of_split_bounds
        aq bq cq plasticRoot sRoot tRoot D hmain hpert)
      hk
  exact zeta_three_plastic_closed zeta3Value hcert hzeta

/-- Milestone variant with geometric perturbation envelope auto-discharged from
`|sRoot|,|tRoot| ≤ r`.
-/
theorem zeta_three_plastic_closed_milestone_binet_geometric
    (zeta3Value : ℝ)
    (ap aq bp cp bq cq sRoot tRoot r : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hP : ∀ n : ℕ, plasticPReal n = ap * plasticRoot ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ))
    (hQ : ∀ n : ℕ, plasticQReal n = aq * plasticRoot ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ))
    (k : ℝ)
    (hap : ap = k * aq)
    (hbp : bp = k * bq)
    (hcp : cp = k * cq)
    (hsr : |sRoot| ≤ r)
    (htr : |tRoot| ≤ r)
    (hmain : ∀ n : ℕ, |aq * plasticRoot ^ (n : ℕ)| > (|bq| + |cq|) * r ^ (n : ℕ))
    (hk : k = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate := by
  apply zeta_three_plastic_closed_milestone_binet
    zeta3Value
    ap aq bp cp bq cq sRoot tRoot
    hsRoot htRoot hAq
    hP hQ
    k hap hbp hcp
    (fun n => (|bq| + |cq|) * r ^ (n : ℕ))
    hmain
    ?_ hk hzeta
  intro n
  simpa using perturbation_bound_of_common_radius bq cq sRoot tRoot r hsr htr n

/-- Single-entry final theorem in bundled form: discharge one structure and get
the closed plastic expression.
-/
theorem zeta_three_plastic_closed_milestone_bundled
    (h : PlasticZeta3MilestoneAssumptions) :
    h.zeta3Value = plasticZeta3Candidate := by
  exact zeta_three_plastic_closed_milestone_binet
    h.zeta3Value
    h.ap h.aq h.bp h.cp h.bq h.cq h.sRoot h.tRoot
    h.hsRoot h.htRoot h.hAq
    h.hP h.hQ
    h.k h.hap h.hbp h.hcp
    h.D h.hmain h.hpert
    h.hk h.hzeta

end Hqiv.Algebra

