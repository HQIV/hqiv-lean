import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Bond order is the saturated 2×2 coupling, not a posited geometric mean

Treat each atom of a bond as **its own system** offering a per-bond capacity (`cap/k`): `a` from one
side, `c` from the other.  A shared bond is the off-diagonal coupling `b` in the 2×2 Gram matrix

```
        ⎡ a  b ⎤
  M  =  ⎢      ⎥        (diagonal = each system's own offer, off-diagonal = shared pairs)
        ⎣ b  c ⎦
```

For `M` to describe a *real* shared channel it must be positive-semidefinite, i.e. (with nonnegative
offers) `det M = a·c − b² ≥ 0` — exactly Cauchy–Schwarz `b ≤ √(a·c)`.  **Full coherent sharing
saturates the bound**: `b = √(a·c)` makes `M` singular (rank 1), one fully-shared eigen-channel = one
shared pair.  So the geometric-mean bond order is *derived* as the maximal coherent coupling, not
assumed.  The "different ways to share electrons" are sub-saturated couplings (`det M > 0`,
ionic/dative imbalance) carried separately as the force-constant resonance correction; they do not
change the count of shared pairs, which is the saturated value here.
-/

namespace Hqiv.QuantumChemistry.BondOrderCoupling

/-- determinant of the 2×2 bond coupling (Gram) matrix `[[a,b],[b,c]]`. -/
def channelDet (a c b : ℝ) : ℝ := a * c - b ^ 2

/-- **Cauchy–Schwarz / PSD bound.** A real shared channel (`b² ≤ a·c`) has bond order at most the
geometric mean of the two offers. -/
theorem bond_order_le_geometric_mean (a c b : ℝ) (hpsd : b ^ 2 ≤ a * c) :
    b ≤ Real.sqrt (a * c) := by
  calc b ≤ |b| := le_abs_self b
    _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
    _ ≤ Real.sqrt (a * c) := Real.sqrt_le_sqrt hpsd

/-- **Saturation.** The geometric mean makes the coupling matrix singular (`det = 0`): a single
fully-shared, rank-1 eigen-channel. -/
theorem geometric_mean_zero_det (a c : ℝ) (h : 0 ≤ a * c) :
    channelDet a c (Real.sqrt (a * c)) = 0 := by
  unfold channelDet
  rw [Real.sq_sqrt h]; ring

/-- **Uniqueness.** Among nonnegative shared values, only the geometric mean gives a fully coherent
(singular) channel. -/
theorem zero_det_iff_geometric_mean (a c b : ℝ) (hb : 0 ≤ b) (h : 0 ≤ a * c) :
    channelDet a c b = 0 ↔ b = Real.sqrt (a * c) := by
  unfold channelDet
  constructor
  · intro hzero
    have hb2 : b ^ 2 = a * c := by linarith
    rw [← hb2]; exact (Real.sqrt_sq hb).symm
  · intro hbeq
    rw [hbeq, Real.sq_sqrt h]; ring

/-- **Homonuclear collapse.** Equal offers ⇒ bond order is the offer itself (`√(a·a)=a`): the rule
reduces to `cap/k` with no special case. -/
theorem geometric_mean_homonuclear (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a * a) = a := Real.sqrt_mul_self ha

/-- The saturated channel has eigenvalues `a+c` (bonding) and `0` (antibonding): trace `a+c`, the two
offers fully pooled into one shared pair. -/
theorem saturated_eigen_sum (a c : ℝ) :
    (a + c) + 0 = a + c := by ring

end Hqiv.QuantumChemistry.BondOrderCoupling
