import Hqiv.Algebra.PlasticRecurrence
import Hqiv.Algebra.PlasticZeta3
import Hqiv.Algebra.PlasticDominantRoot
import Hqiv.Algebra.PlasticAsymptotics
import Hqiv.Algebra.PlasticRatioLimit
import Hqiv.Algebra.PlasticBinet
import Hqiv.Algebra.PlasticBinetClosed
import Hqiv.Algebra.PlasticBinetDischarge
import Hqiv.Algebra.PlasticZeta3Closed
import Hqiv.Algebra.PlasticZeta3Feed
import Hqiv.Algebra.PlasticZeta3Milestone

/-!
# Plastic zeta(3) proof-work archive

This file archives the full plastic-number zeta(3) formalization track developed
in this repository.

Archived modules:

1. `Hqiv.Algebra.PlasticRecurrence`
2. `Hqiv.Algebra.PlasticZeta3`
3. `Hqiv.Algebra.PlasticDominantRoot`
4. `Hqiv.Algebra.PlasticAsymptotics`
5. `Hqiv.Algebra.PlasticRatioLimit`
6. `Hqiv.Algebra.PlasticBinet`
7. `Hqiv.Algebra.PlasticBinetClosed`
8. `Hqiv.Algebra.PlasticBinetDischarge`
9. `Hqiv.Algebra.PlasticZeta3Closed`
10. `Hqiv.Algebra.PlasticZeta3Feed`
11. `Hqiv.Algebra.PlasticZeta3Milestone`

The goal of this archive is traceability and reproducibility: the endpoint
theorems below provide stable entry points into the formal chain at its current
state.
-/

namespace Hqiv.Archive.Algebra

open Hqiv.Algebra

/-- Archived endpoint theorem: bundled milestone closure statement. -/
theorem plastic_zeta3_archived_endpoint
    (h : PlasticZeta3MilestoneAssumptions) :
    h.zeta3Value = plasticZeta3Candidate :=
  zeta_three_plastic_closed_milestone_bundled h

/-- Archived endpoint theorem: geometric-envelope milestone closure statement. -/
theorem plastic_zeta3_archived_endpoint_geometric
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
    (hzeta : Filter.Tendsto plasticRatioReal Filter.atTop (Filter.nhds zeta3Value)) :
    zeta3Value = plasticZeta3Candidate :=
  zeta_three_plastic_closed_milestone_binet_geometric
    zeta3Value ap aq bp cp bq cq sRoot tRoot r
    hsRoot htRoot hAq hP hQ k hap hbp hcp
    hsr htr hmain hk hzeta

end Hqiv.Archive.Algebra

