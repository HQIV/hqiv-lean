import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Hqiv.Algebra.PlasticZeta3Closed

namespace Hqiv.Algebra

open Filter
open scoped Topology

theorem zeta_three_plastic_closed_from_spectral_data
    (zeta3Value : ℝ)
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
    (hclosed : ap / aq = plasticZeta3Candidate)
    (hzeta : Tendsto plasticRatioReal atTop (𝓝 zeta3Value)) :
    zeta3Value = plasticZeta3Candidate := by
  have hcert : ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate :=
    exists_plasticBinetCertificate_of_data
      ap aq bp cp bq cq rho sRoot tRoot
      hsRoot htRoot hAq hP hQ hratio hclosed
  exact zeta_three_plastic_closed zeta3Value hcert hzeta

end Hqiv.Algebra

