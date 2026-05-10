import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Hqiv.Algebra.PlasticBinetClosed
import Hqiv.Algebra.PlasticRatioLimit

namespace Hqiv.Algebra

open Filter
open scoped Topology

theorem plasticRatioReal_tendsto_plasticZeta3Candidate
    (hcert : ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate) :
    Tendsto plasticRatioReal atTop (𝓝 plasticZeta3Candidate) :=
  plasticRatioReal_tendsto_plasticZeta3Candidate_of_exists_certificate hcert

theorem zeta_three_plastic_closed_of_tendsto
    (zeta3Value : ℝ)
    (hcert : ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate := by
  have hclosed : Tendsto plasticRatioReal atTop (𝓝 plasticZeta3Candidate) :=
    plasticRatioReal_tendsto_plasticZeta3Candidate hcert
  exact tendsto_nhds_unique hzeta hclosed

theorem exists_plasticBinetCertificate_of_data
    (ap aq bp cp bq cq rho sRoot tRoot : ℝ)
    (hsRoot : |sRoot| < (1 : ℝ))
    (htRoot : |tRoot| < (1 : ℝ))
    (hAq : aq ≠ 0)
    (hP : ∀ n : ℕ, plasticPReal n = ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ))
    (hQ : ∀ n : ℕ, plasticQReal n = aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ))
    (hratio :
      ∀ n : ℕ,
        (ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)) /
        (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) = ap / aq)
    (hclosed : ap / aq = plasticZeta3Candidate) :
    ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate := by
  refine ⟨{
    ap := ap
    aq := aq
    bp := bp
    cp := cp
    bq := bq
    cq := cq
    rho := rho
    sRoot := sRoot
    tRoot := tRoot
    hsRoot := hsRoot
    htRoot := htRoot
    hAq := hAq
    hP := hP
    hQ := hQ
    hratio := hratio
  }, hclosed⟩

theorem zeta_three_plastic_closed
    (zeta3Value : ℝ)
    (hcert : ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate :=
  zeta_three_plastic_closed_of_tendsto zeta3Value hcert hzeta

end Hqiv.Algebra

