import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic
import Hqiv.Algebra.PlasticBinet
import Hqiv.Algebra.PlasticRatioLimit

namespace Hqiv.Algebra

open Filter
open scoped Topology

/-!
# Plastic Binet closed-certificate layer

Archived location (source moved from `Hqiv/Algebra/PlasticBinetClosed.lean`).
-/

structure PlasticBinetCertificate where
  ap : ℝ
  aq : ℝ
  bp : ℝ
  cp : ℝ
  bq : ℝ
  cq : ℝ
  rho : ℝ
  sRoot : ℝ
  tRoot : ℝ
  hsRoot : |sRoot| < (1 : ℝ)
  htRoot : |tRoot| < (1 : ℝ)
  hAq : aq ≠ 0
  hP : ∀ n : ℕ, plasticPReal n = ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)
  hQ : ∀ n : ℕ, plasticQReal n = aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)
  hratio :
    ∀ n : ℕ,
      (ap * rho ^ (n : ℕ) + bp * sRoot ^ (n : ℕ) + cp * tRoot ^ (n : ℕ)) /
      (aq * rho ^ (n : ℕ) + bq * sRoot ^ (n : ℕ) + cq * tRoot ^ (n : ℕ)) = ap / aq

theorem plasticRatioReal_tendsto_of_certificate
    (c : PlasticBinetCertificate) :
    Tendsto plasticRatioReal atTop (𝓝 (c.ap / c.aq)) :=
  plasticRatioReal_tendsto_of_binet
    c.ap c.aq c.bp c.cp c.bq c.cq c.rho c.sRoot c.tRoot
    c.hsRoot c.htRoot c.hAq c.hP c.hQ c.hratio

theorem plasticRatioReal_tendsto_plasticZeta3Candidate_of_certificate
    (c : PlasticBinetCertificate)
    (hclosed : c.ap / c.aq = plasticZeta3Candidate) :
    Tendsto plasticRatioReal atTop (𝓝 plasticZeta3Candidate) := by
  simpa [hclosed] using plasticRatioReal_tendsto_of_certificate c

theorem plasticRatioReal_tendsto_plasticZeta3Candidate_of_exists_certificate
    (hcert : ∃ c : PlasticBinetCertificate, c.ap / c.aq = plasticZeta3Candidate) :
    Tendsto plasticRatioReal atTop (𝓝 plasticZeta3Candidate) := by
  rcases hcert with ⟨c, hclosed⟩
  exact plasticRatioReal_tendsto_plasticZeta3Candidate_of_certificate c hclosed

end Hqiv.Algebra

