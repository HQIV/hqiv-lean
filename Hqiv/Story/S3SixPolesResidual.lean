import Hqiv.Story.S3PrimeAxisCancellation

/-!
# The six imaginary poles of S³ and the ± residual of a canceling pair

This is the geometric picture (no modular arithmetic): inside `S³ ⊂ ℍ` the unit
*imaginary* quaternions form an `S²`, whose six axis poles are

`±i, ±j, ±k`  (the `6` poles).

The 45° "twiddle" plane carries the 8-fold symmetry `e^{iπ/4}`; the imaginary
poles carry the (octahedral) 6-fold structure. The point you are making:

> holding the S³ rotation so a pair cancels still leaves a positive and a
> negative rotation above/below the real axis when projected.

That is exactly true and is formalized here. An antipodal pole pair `(+i, −i)` is
a head/tail reflection pair, so its projections **sum to zero** (cancellation),
yet each member is a nonzero `±` residual:

`criticalProj (+i) = +1/√2`,  `criticalProj (−i) = −1/√2`.

So the pair cancels *as a sum*, but neither representative vanishes — the `+` sits
above the real axis, the `−` below. This is precisely the orbit-vs-pointwise
distinction: the reflection (functional-equation) symmetry forces the *sum* to
zero for every such pair, while a *single* representative vanishes only on the
balanced hyperplane (`criticalProj = 0 ↔ BalancedImag`). The single-axis poles
themselves never vanish (`criticalProj_ne_zero_of_singleAxis`): they are the
survivors, and the residual they leave is the `±` pair above/below the axis.
-/

namespace Hqiv.Story

noncomputable section

/-- The six imaginary poles of `S³`: `±i, ±j, ±k`. -/
def poleIplus : QuaternionCoords := ![0, 1, 0, 0]
def poleIminus : QuaternionCoords := ![0, -1, 0, 0]
def poleJplus : QuaternionCoords := ![0, 0, 1, 0]
def poleJminus : QuaternionCoords := ![0, 0, -1, 0]
def poleKplus : QuaternionCoords := ![0, 0, 0, 1]
def poleKminus : QuaternionCoords := ![0, 0, 0, -1]

/-- All six poles lie on the `S³` shell. -/
theorem six_poles_on_s3 :
    OnS3 poleIplus ∧ OnS3 poleIminus ∧ OnS3 poleJplus ∧
      OnS3 poleJminus ∧ OnS3 poleKplus ∧ OnS3 poleKminus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [OnS3, poleIplus, poleIminus, poleJplus, poleJminus, poleKplus, poleKminus]

/-- Each of the six poles is single-axis (hence a survivor of the projection). -/
theorem six_poles_single_axis :
    IsSingleAxis poleIplus ∧ IsSingleAxis poleIminus ∧ IsSingleAxis poleJplus ∧
      IsSingleAxis poleJminus ∧ IsSingleAxis poleKplus ∧ IsSingleAxis poleKminus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl (by simp [poleIplus])
  · exact Or.inl (by simp [poleIminus])
  · exact Or.inr (Or.inl (by simp [poleJplus]))
  · exact Or.inr (Or.inl (by simp [poleJminus]))
  · exact Or.inr (Or.inr (by simp [poleKplus]))
  · exact Or.inr (Or.inr (by simp [poleKminus]))

/-- `+i` and `−i` are a head/tail reflection pair. -/
theorem reflect_poleIplus : headTailReflect poleIplus = poleIminus := by
  funext i
  fin_cases i <;> simp [headTailReflect, poleIplus, poleIminus]

/-- The `+i` pole projects to the positive residual `+1/√2`. -/
theorem criticalProj_poleIplus : criticalProj poleIplus = 1 / Real.sqrt 2 := by
  simp [criticalProj, imagSum, poleIplus]

/-- The `−i` pole projects to the negative residual `−1/√2`. -/
theorem criticalProj_poleIminus : criticalProj poleIminus = -(1 / Real.sqrt 2) := by
  have h : imagSum poleIminus = -1 := by simp [imagSum, poleIminus]
  rw [criticalProj, h]; ring

/--
**The ± residual of a canceling pair.** The antipodal pole pair `(+i, −i)` cancels
*as a sum* (`+1/√2 + (−1/√2) = 0`), yet leaves a strictly positive residual above
the real axis and a strictly negative one below — neither representative vanishes.
-/
theorem pole_pair_cancels_but_leaves_plus_minus :
    criticalProj poleIplus + criticalProj poleIminus = 0 ∧
      0 < criticalProj poleIplus ∧ criticalProj poleIminus < 0 := by
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [criticalProj_poleIplus, criticalProj_poleIminus]; ring
  · rw [criticalProj_poleIplus]; exact hpos
  · rw [criticalProj_poleIminus]; linarith

/--
The pole pair is a genuine reflection pair, so the generic cancellation theorem
`headTail_orbit_pair_cancels` specializes to it: the sum is forced to zero by the
reflection symmetry, independent of which pole we sit on.
-/
theorem pole_pair_is_reflection_cancellation :
    criticalProj poleIplus + criticalProj (headTailReflect poleIplus) = 0 :=
  headTail_orbit_pair_cancels poleIplus

end

end Hqiv.Story
