import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hqiv.Geometry

noncomputable section

/-- Multiplicative approximation ratio (oracle cost over optimal cost). -/
def approximationRatio (oracleCost optimalCost : ℝ) : ℝ :=
  oracleCost / optimalCost

/--
Exact-degenerate case: if oracle and optimal costs are equal, the ratio is exactly `1`.
-/
theorem exact_degenerate_ratio_eq_one
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost = 1 := by
  simp [approximationRatio, hEq, hOptPos.ne']

/--
Envelope floor used in the HQIV near-degenerate conjecture:
`1 ≤ 1 + n^(1/n)` (interpreting `n` in `ℝ`).
-/
theorem one_le_one_plus_nat_root_envelope (n : ℕ) :
    (1 : ℝ) ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (1 / (n : ℝ)) := by
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  linarith

/--
Exact-degenerate regime is inside the envelope `1 + n^(1/n)`.
-/
theorem exact_degenerate_ratio_le_nat_root_envelope
    (n : ℕ)
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  have hRatio : approximationRatio oracleCost optimalCost = 1 :=
    exact_degenerate_ratio_eq_one oracleCost optimalCost hEq hOptPos
  rw [hRatio]
  exact one_le_one_plus_nat_root_envelope n

/--
Exact-degenerate regime strictly beats the envelope whenever the root term is
strictly positive (in particular for every positive `n`).
-/
theorem exact_degenerate_ratio_lt_nat_root_envelope
    (n : ℕ)
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost)
    (hn : 0 < n) :
    approximationRatio oracleCost optimalCost < 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  have hRatio : approximationRatio oracleCost optimalCost = 1 :=
    exact_degenerate_ratio_eq_one oracleCost optimalCost hEq hOptPos
  have hRootPos : 0 < (n : ℝ) ^ (1 / (n : ℝ)) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  rw [hRatio]
  linarith

/--
Additive-gap-to-ratio transfer:
`oracleCost ≤ optimalCost + ε` implies ratio bound `≤ 1 + ε/optimalCost`.
-/
theorem additive_gap_implies_ratio_bound
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + ε) :
    approximationRatio oracleCost optimalCost ≤ 1 + ε / optimalCost := by
  have hinv_nonneg : 0 ≤ optimalCost⁻¹ := by positivity
  have hmul :
      oracleCost * optimalCost⁻¹ ≤ (optimalCost + ε) * optimalCost⁻¹ :=
    mul_le_mul_of_nonneg_right hGap hinv_nonneg
  calc
    approximationRatio oracleCost optimalCost = oracleCost * optimalCost⁻¹ := by
      simp [approximationRatio, div_eq_mul_inv]
    _ ≤ (optimalCost + ε) * optimalCost⁻¹ := hmul
    _ = 1 + ε / optimalCost := by
      field_simp [hOptPos.ne']

/--
Near-degenerate envelope:
if additive gap `ε` is bounded by `optimalCost * n^(1/n)`, then ratio is bounded
by `1 + n^(1/n)`.
-/
theorem near_degenerate_ratio_le_nat_root_envelope
    (n : ℕ)
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + ε)
    (hEpsBound : ε ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  let r : ℝ := (n : ℝ) ^ (1 / (n : ℝ))
  have hBase : approximationRatio oracleCost optimalCost ≤ 1 + ε / optimalCost :=
    additive_gap_implies_ratio_bound oracleCost optimalCost ε hOptPos hGap
  have hDiv : ε / optimalCost ≤ r := by
    have hMul : ε ≤ r * optimalCost := by
      simpa [r, mul_comm] using hEpsBound
    have hinv_nonneg : 0 ≤ optimalCost⁻¹ := by positivity
    have hMulInv : ε * optimalCost⁻¹ ≤ (r * optimalCost) * optimalCost⁻¹ :=
      mul_le_mul_of_nonneg_right hMul hinv_nonneg
    calc
      ε / optimalCost = ε * optimalCost⁻¹ := by simp [div_eq_mul_inv]
      _ ≤ (r * optimalCost) * optimalCost⁻¹ := hMulInv
      _ = r := by
        field_simp [hOptPos.ne']
  have hLift : 1 + ε / optimalCost ≤ 1 + r := by
    linarith
  simpa [r] using le_trans hBase hLift

/--
Strict near-degenerate envelope:
if additive gap `ε` is strictly below `optimalCost * n^(1/n)`, then the oracle
strictly beats the generic worst-case degeneracy envelope.
-/
theorem near_degenerate_ratio_lt_nat_root_envelope
    (n : ℕ)
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + ε)
    (hEpsBound : ε < optimalCost * ((n : ℝ) ^ (1 / (n : ℝ)))) :
    approximationRatio oracleCost optimalCost < 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  let r : ℝ := (n : ℝ) ^ (1 / (n : ℝ))
  have hBase : approximationRatio oracleCost optimalCost ≤ 1 + ε / optimalCost :=
    additive_gap_implies_ratio_bound oracleCost optimalCost ε hOptPos hGap
  have hDiv : ε / optimalCost < r := by
    have hMul : ε < r * optimalCost := by
      simpa [r, mul_comm] using hEpsBound
    have hinv_pos : 0 < optimalCost⁻¹ := by positivity
    have hMulInv : ε * optimalCost⁻¹ < (r * optimalCost) * optimalCost⁻¹ :=
      mul_lt_mul_of_pos_right hMul hinv_pos
    calc
      ε / optimalCost = ε * optimalCost⁻¹ := by simp [div_eq_mul_inv]
      _ < (r * optimalCost) * optimalCost⁻¹ := hMulInv
      _ = r := by
        field_simp [hOptPos.ne']
  have hLift : 1 + ε / optimalCost < 1 + r := by
    linarith
  exact lt_of_le_of_lt hBase (by simpa [r] using hLift)

/--
Strict worst-case certified behavior contract:
exact degeneracy or a strict sub-envelope additive gap both force the oracle
strictly below the generic worst-case degeneracy envelope.
-/
theorem strictly_beats_worst_case_degeneracy_nat_root_envelope
    (n : ℕ)
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hn : 0 < n)
    (hCase :
      oracleCost = optimalCost ∨
      (oracleCost ≤ optimalCost + ε ∧
       ε < optimalCost * ((n : ℝ) ^ (1 / (n : ℝ))))) :
    approximationRatio oracleCost optimalCost < 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  rcases hCase with hExact | hNear
  · exact exact_degenerate_ratio_lt_nat_root_envelope
      n oracleCost optimalCost hExact hOptPos hn
  · exact near_degenerate_ratio_lt_nat_root_envelope
      n oracleCost optimalCost ε hOptPos hNear.1 hNear.2

/--
Worst-case certified behavior contract (assumption-explicit):
either exact degeneracy (`oracleCost = optimalCost`) or near-degeneracy with an
additive gap bounded by `optimalCost * n^(1/n)` yields the same envelope.
-/
theorem worst_case_certified_behavior_nat_root_envelope
    (n : ℕ)
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hCase :
      oracleCost = optimalCost ∨
      (oracleCost ≤ optimalCost + ε ∧
       ε ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ))))) :
    approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  rcases hCase with hExact | hNear
  · exact exact_degenerate_ratio_le_nat_root_envelope n oracleCost optimalCost hExact hOptPos
  · exact near_degenerate_ratio_le_nat_root_envelope
      n oracleCost optimalCost ε hOptPos hNear.1 hNear.2

/--
Abstract hook for random/poly-search certification:
once an external certificate supplies the ratio bound, this theorem exposes it in
the same envelope contract.
-/
theorem random_poly_search_hits_nat_root_envelope_of_certificate
    (n : ℕ)
    (oracleCost optimalCost : ℝ)
    (hCert : approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ))) :
    approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) :=
  hCert

/-- Data-certificate for finite-sample envelope checks. -/
structure EnvelopeCertificate where
  n : ℕ
  oracleCost : ℝ
  optimalCost : ℝ

/-- Canonical HQIV envelope for a certificate row. -/
def envelopeBound (c : EnvelopeCertificate) : ℝ :=
  1 + (c.n : ℝ) ^ (1 / (c.n : ℝ))

/-- Row-level certificate validity predicate. -/
def validEnvelopeCertificate (c : EnvelopeCertificate) : Prop :=
  0 < c.optimalCost ∧ approximationRatio c.oracleCost c.optimalCost ≤ envelopeBound c

/--
Row-level transfer: any valid certificate row implies the corresponding envelope
ratio bound.
-/
theorem validEnvelopeCertificate_implies_bound
    (c : EnvelopeCertificate)
    (hValid : validEnvelopeCertificate c) :
    approximationRatio c.oracleCost c.optimalCost ≤ envelopeBound c :=
  hValid.2

/-- Batch-level finite-sample certificate predicate. -/
def validEnvelopeBatch (cs : List EnvelopeCertificate) : Prop :=
  ∀ c ∈ cs, validEnvelopeCertificate c

/--
Batch transfer theorem:
if a finite sample batch is valid, every member row satisfies the envelope bound.
-/
theorem validEnvelopeBatch_member_implies_bound
    (cs : List EnvelopeCertificate)
    (hBatch : validEnvelopeBatch cs)
    (c : EnvelopeCertificate)
    (hMem : c ∈ cs) :
    approximationRatio c.oracleCost c.optimalCost ≤ envelopeBound c := by
  exact (hBatch c hMem).2

/-! ## Oracle-bridge proof contract (Phase roadmap) -/

/--
Stage-2 local completion monotonicity transfer:
if local completion does not increase cost from a seed witness, any additive-gap
bound carried by the seed is preserved after completion.
-/
theorem local_completion_preserves_additive_gap
    (seedCost refinedCost optimalCost ε : ℝ)
    (hSeedGap : seedCost ≤ optimalCost + ε)
    (hLocalMono : refinedCost ≤ seedCost) :
    refinedCost ≤ optimalCost + ε :=
  le_trans hLocalMono hSeedGap

/--
Projection/truncation residual transfer:
if seed cost is bounded by optimal plus three certified channels
(`tensorResidualErr`, `rapidityErr`, `axisErr`) and their sum is bounded by `ε`,
then seed cost satisfies the additive-gap form `≤ optimal + ε`.
-/
theorem projection_residual_implies_seed_gap
    (seedCost optimalCost ε tensorResidualErr rapidityErr axisErr : ℝ)
    (hProj :
      seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr)
    (hBudget : tensorResidualErr + rapidityErr + axisErr ≤ ε) :
    seedCost ≤ optimalCost + ε := by
  have hLift :
      optimalCost + tensorResidualErr + rapidityErr + axisErr ≤ optimalCost + ε := by
    linarith
  exact le_trans hProj hLift

/--
Worst-case degeneracy budget:
geometric witness slack plus the explicit tensor / rapidity / axis residual
channels.
-/
def worstCaseDegeneracyBudget
    (geometricGap tensorResidualErr rapidityErr axisErr : ℝ) : ℝ :=
  geometricGap + tensorResidualErr + rapidityErr + axisErr

/--
Geometric plus certified residual channel transfer:
if the seed is within the geometric witness slack plus the explicit tensor,
rapidity, and axis residuals, then it lies within the summed worst-case
degeneracy budget.
-/
theorem geometric_residual_budget_implies_seed_gap
    (seedCost optimalCost ε geometricGap tensorResidualErr rapidityErr axisErr : ℝ)
    (hProj :
      seedCost ≤ optimalCost + geometricGap + tensorResidualErr + rapidityErr + axisErr)
    (hBudget :
      worstCaseDegeneracyBudget geometricGap tensorResidualErr rapidityErr axisErr ≤ ε) :
    seedCost ≤ optimalCost + ε := by
  have hLift :
      optimalCost + geometricGap + tensorResidualErr + rapidityErr + axisErr ≤
        optimalCost + ε := by
    simpa [worstCaseDegeneracyBudget, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hBudget optimalCost
  exact le_trans hProj hLift

/--
Geometric bridge assumptions linking the uniform-cost witness route to the
real-valued ATSP envelope lemmas.

The geometric slack may be obtained from
`degenerate_uniform_cost_yields_real_geometric_gap`, while the remaining three
channels record tensor, rapidity, and axis residuals.
-/
structure GeometricOracleBridgeAssumptions where
  n : ℕ
  oracleCost : ℝ
  seedCost : ℝ
  optimalCost : ℝ
  ε : ℝ
  geometricGap : ℝ
  tensorResidualErr : ℝ
  rapidityErr : ℝ
  axisErr : ℝ
  hOptPos : 0 < optimalCost
  hProjResidual :
    seedCost ≤ optimalCost + geometricGap + tensorResidualErr + rapidityErr + axisErr
  hWorstCaseBudget :
    worstCaseDegeneracyBudget geometricGap tensorResidualErr rapidityErr axisErr ≤ ε
  hLocalCompletion : oracleCost ≤ seedCost
  hEpsEnvelope : ε ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ)))

/--
Geometric bridge theorem:
once the geometric witness slack and the three certified residual channels are
summed into a worst-case degeneracy budget, the same `1 + n^(1/n)` envelope
follows.
-/
theorem geometric_oracle_bridge_implies_nat_root_envelope
    (A : GeometricOracleBridgeAssumptions) :
    approximationRatio A.oracleCost A.optimalCost ≤
      1 + (A.n : ℝ) ^ (1 / (A.n : ℝ)) := by
  have hSeedGap : A.seedCost ≤ A.optimalCost + A.ε :=
    geometric_residual_budget_implies_seed_gap
      A.seedCost A.optimalCost A.ε
      A.geometricGap A.tensorResidualErr A.rapidityErr A.axisErr
      A.hProjResidual A.hWorstCaseBudget
  have hGlobalGap : A.oracleCost ≤ A.optimalCost + A.ε :=
    local_completion_preserves_additive_gap
      A.seedCost A.oracleCost A.optimalCost A.ε
      hSeedGap A.hLocalCompletion
  exact near_degenerate_ratio_le_nat_root_envelope
    A.n A.oracleCost A.optimalCost A.ε
    A.hOptPos hGlobalGap A.hEpsEnvelope

/--
Strict geometric bridge theorem:
if the realized degeneracy budget is strictly smaller than the generic
`optimalCost * n^(1/n)` scale, then the oracle strictly beats the worst-case
degeneracy envelope.
-/
theorem geometric_oracle_bridge_strictly_beats_nat_root_envelope
    (A : GeometricOracleBridgeAssumptions)
    (hStrict : A.ε < A.optimalCost * ((A.n : ℝ) ^ (1 / (A.n : ℝ)))) :
    approximationRatio A.oracleCost A.optimalCost <
      1 + (A.n : ℝ) ^ (1 / (A.n : ℝ)) := by
  have hSeedGap : A.seedCost ≤ A.optimalCost + A.ε :=
    geometric_residual_budget_implies_seed_gap
      A.seedCost A.optimalCost A.ε
      A.geometricGap A.tensorResidualErr A.rapidityErr A.axisErr
      A.hProjResidual A.hWorstCaseBudget
  have hGlobalGap : A.oracleCost ≤ A.optimalCost + A.ε :=
    local_completion_preserves_additive_gap
      A.seedCost A.oracleCost A.optimalCost A.ε
      hSeedGap A.hLocalCompletion
  exact near_degenerate_ratio_lt_nat_root_envelope
    A.n A.oracleCost A.optimalCost A.ε
    A.hOptPos hGlobalGap hStrict

/--
Abstract bridge assumptions linking the implemented oracle to certified bounds.
This is the proof roadmap contract to discharge incrementally:

- `hProjResidual`: projection/truncation channel yields an additive cost gap.
- `hLocalCompletion`: seeded local completion never worsens cost.
- `hGlobalGap`: resulting oracle cost is bounded by `optimal + ε`.
- `hEpsEnvelope`: `ε` is controlled by the `optimal * n^(1/n)` envelope scale.
-/
structure OracleBridgeAssumptions where
  n : ℕ
  oracleCost : ℝ
  seedCost : ℝ
  optimalCost : ℝ
  ε : ℝ
  tensorResidualErr : ℝ
  rapidityErr : ℝ
  axisErr : ℝ
  hOptPos : 0 < optimalCost
  hProjResidual :
    seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr
  hResidualBudget : tensorResidualErr + rapidityErr + axisErr ≤ ε
  hLocalCompletion : oracleCost ≤ seedCost
  hEpsEnvelope : ε ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ)))

/--
Bridge theorem:
once the oracle-bridge assumptions are discharged, the target worst-case envelope
follows directly.
-/
theorem oracle_bridge_implies_nat_root_envelope
    (A : OracleBridgeAssumptions) :
    approximationRatio A.oracleCost A.optimalCost ≤
      1 + (A.n : ℝ) ^ (1 / (A.n : ℝ)) := by
  have hSeedGap : A.seedCost ≤ A.optimalCost + A.ε :=
    projection_residual_implies_seed_gap
      A.seedCost A.optimalCost A.ε A.tensorResidualErr A.rapidityErr A.axisErr
      A.hProjResidual A.hResidualBudget
  have hGlobalGap : A.oracleCost ≤ A.optimalCost + A.ε :=
    local_completion_preserves_additive_gap
      A.seedCost A.oracleCost A.optimalCost A.ε
      hSeedGap A.hLocalCompletion
  exact near_degenerate_ratio_le_nat_root_envelope
    A.n A.oracleCost A.optimalCost A.ε
    A.hOptPos hGlobalGap A.hEpsEnvelope

/--
Exact-degenerate bridge specialization:
if the bridge records exact cost equality, the envelope follows with ratio `1`.
-/
theorem oracle_bridge_exact_degenerate_implies_envelope
    (A : OracleBridgeAssumptions)
    (hExact : A.oracleCost = A.optimalCost) :
    approximationRatio A.oracleCost A.optimalCost ≤
      1 + (A.n : ℝ) ^ (1 / (A.n : ℝ)) := by
  exact exact_degenerate_ratio_le_nat_root_envelope
    A.n A.oracleCost A.optimalCost hExact A.hOptPos

/--
Single-entry composed contract for downstream use:
hybrid residual channels + local completion monotonicity + envelope scaling imply
the target `1 + n^(1/n)` bound in one theorem.
-/
theorem hybrid_channels_and_local_monotone_imply_envelope
    (n : ℕ)
    (oracleCost seedCost optimalCost ε tensorResidualErr rapidityErr axisErr : ℝ)
    (hOptPos : 0 < optimalCost)
    (hProjResidual :
      seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr)
    (hResidualBudget : tensorResidualErr + rapidityErr + axisErr ≤ ε)
    (hLocalCompletion : oracleCost ≤ seedCost)
    (hEpsEnvelope : ε ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  let A : OracleBridgeAssumptions :=
    { n := n
      oracleCost := oracleCost
      seedCost := seedCost
      optimalCost := optimalCost
      ε := ε
      tensorResidualErr := tensorResidualErr
      rapidityErr := rapidityErr
      axisErr := axisErr
      hOptPos := hOptPos
      hProjResidual := hProjResidual
      hResidualBudget := hResidualBudget
      hLocalCompletion := hLocalCompletion
      hEpsEnvelope := hEpsEnvelope }
  exact oracle_bridge_implies_nat_root_envelope A

/--
Fractional channel-budget bridge:
if each certified channel is bounded by `optimalCost * ρᵢ` and the fractional
sum `ρₜ + ρᵣ + ρₐ` is within the envelope root scale `n^(1/n)`, then the same
`1 + n^(1/n)` approximation envelope follows.
-/
theorem hybrid_channels_fractional_budget_imply_envelope
    (n : ℕ)
    (oracleCost seedCost optimalCost tensorResidualErr rapidityErr axisErr : ℝ)
    (ρt ρr ρa : ℝ)
    (hOptPos : 0 < optimalCost)
    (hProjResidual :
      seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr)
    (hLocalCompletion : oracleCost ≤ seedCost)
    (hTensorBound : tensorResidualErr ≤ optimalCost * ρt)
    (hRapidityBound : rapidityErr ≤ optimalCost * ρr)
    (hAxisBound : axisErr ≤ optimalCost * ρa)
    (hFracBudget : ρt + ρr + ρa ≤ (n : ℝ) ^ (1 / (n : ℝ))) :
    approximationRatio oracleCost optimalCost ≤ 1 + (n : ℝ) ^ (1 / (n : ℝ)) := by
  let ε : ℝ := tensorResidualErr + rapidityErr + axisErr
  have hSeedGap : seedCost ≤ optimalCost + ε := by
    simpa [ε, add_assoc, add_left_comm, add_comm] using hProjResidual
  have hGlobalGap : oracleCost ≤ optimalCost + ε :=
    local_completion_preserves_additive_gap
      seedCost oracleCost optimalCost ε hSeedGap hLocalCompletion
  have hEpsLeScaled :
      ε ≤ optimalCost * ρt + optimalCost * ρr + optimalCost * ρa := by
    linarith [hTensorBound, hRapidityBound, hAxisBound]
  have hScaledEq : optimalCost * ρt + optimalCost * ρr + optimalCost * ρa
      = optimalCost * (ρt + ρr + ρa) := by ring
  have hScaleToEnvelope :
      optimalCost * (ρt + ρr + ρa) ≤
        optimalCost * ((n : ℝ) ^ (1 / (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hFracBudget (le_of_lt hOptPos)
  have hEpsEnvelope : ε ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ))) := by
    calc
      ε ≤ optimalCost * ρt + optimalCost * ρr + optimalCost * ρa := hEpsLeScaled
      _ = optimalCost * (ρt + ρr + ρa) := hScaledEq
      _ ≤ optimalCost * ((n : ℝ) ^ (1 / (n : ℝ))) := hScaleToEnvelope
  exact near_degenerate_ratio_le_nat_root_envelope
    n oracleCost optimalCost ε hOptPos hGlobalGap hEpsEnvelope

/--
Batch-ready certificate for the fractional channel-budget bridge: records the
three residual channels, their fractional coefficients `ρᵢ`, and the usual
monotone completion field `oracleCost ≤ seedCost`.
-/
structure FractionalChannelCertificate where
  n : ℕ
  oracleCost : ℝ
  seedCost : ℝ
  optimalCost : ℝ
  tensorResidualErr : ℝ
  rapidityErr : ℝ
  axisErr : ℝ
  ρt : ℝ
  ρr : ℝ
  ρa : ℝ

namespace FractionalChannelCertificate

/-- Predicate mirroring the hypotheses of `hybrid_channels_fractional_budget_imply_envelope`. -/
def IsValid (c : FractionalChannelCertificate) : Prop :=
  0 < c.optimalCost ∧
  c.seedCost ≤ c.optimalCost + c.tensorResidualErr + c.rapidityErr + c.axisErr ∧
  c.oracleCost ≤ c.seedCost ∧
  c.tensorResidualErr ≤ c.optimalCost * c.ρt ∧
  c.rapidityErr ≤ c.optimalCost * c.ρr ∧
  c.axisErr ≤ c.optimalCost * c.ρa ∧
  c.ρt + c.ρr + c.ρa ≤ (c.n : ℝ) ^ (1 / (c.n : ℝ))

theorem isValid_implies_envelope
    (c : FractionalChannelCertificate)
    (h : c.IsValid) :
    approximationRatio c.oracleCost c.optimalCost ≤ 1 + (c.n : ℝ) ^ (1 / (c.n : ℝ)) := by
  rcases h with ⟨hOpt, hProj, hLocal, hT, hR, hA, hFrac⟩
  exact hybrid_channels_fractional_budget_imply_envelope
    c.n c.oracleCost c.seedCost c.optimalCost
    c.tensorResidualErr c.rapidityErr c.axisErr
    c.ρt c.ρr c.ρa
    hOpt hProj hLocal hT hR hA hFrac

end FractionalChannelCertificate

/-! ## Geometric route (n = 3 first) -/

/-- `n = 3` envelope constant used by the geometric-first route. -/
def envelope3 : ℝ := 1 + (3 : ℝ) ^ (1 / (3 : ℝ))

/--
Degenerate `n = 3` baseline:
if the oracle output has the same cost as optimum, the ratio is exactly `1`.
-/
theorem n3_exact_degenerate_ratio_eq_one
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost = 1 :=
  exact_degenerate_ratio_eq_one oracleCost optimalCost hEq hOptPos

/--
Degenerate `n = 3` baseline lies inside the envelope `1 + 3^(1/3)`.
-/
theorem n3_exact_degenerate_ratio_le_envelope
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost ≤ envelope3 := by
  simpa [envelope3] using
    exact_degenerate_ratio_le_nat_root_envelope 3 oracleCost optimalCost hEq hOptPos

/--
Degenerate `n = 3` baseline strictly beats the generic worst-case envelope.
-/
theorem n3_exact_degenerate_ratio_lt_envelope
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost < envelope3 := by
  simpa [envelope3] using
    exact_degenerate_ratio_lt_nat_root_envelope 3 oracleCost optimalCost hEq hOptPos (by norm_num)

/--
Additive perturbation transfer for `n = 3`:
if perturbations raise oracle cost by at most `Δ`, ratio increases by at most
`Δ / optimalCost`.
-/
theorem n3_additive_perturbation_ratio_bound
    (oracleCost optimalCost Δ : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + Δ) :
    approximationRatio oracleCost optimalCost ≤ 1 + Δ / optimalCost :=
  additive_gap_implies_ratio_bound oracleCost optimalCost Δ hOptPos hGap

/--
`n = 3` envelope under bounded additive perturbation:
if `Δ ≤ optimalCost * 3^(1/3)`, then ratio is within `envelope3`.
-/
theorem n3_additive_perturbation_within_envelope
    (oracleCost optimalCost Δ : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + Δ)
    (hΔ : Δ ≤ optimalCost * ((3 : ℝ) ^ (1 / (3 : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ envelope3 := by
  simpa [envelope3] using
    near_degenerate_ratio_le_nat_root_envelope 3 oracleCost optimalCost Δ hOptPos hGap hΔ

/--
`n = 3` strict sub-envelope perturbation:
if `Δ < optimalCost * 3^(1/3)`, the ratio is strictly below `envelope3`.
-/
theorem n3_additive_perturbation_strictly_beats_envelope
    (oracleCost optimalCost Δ : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + Δ)
    (hΔ : Δ < optimalCost * ((3 : ℝ) ^ (1 / (3 : ℝ)))) :
    approximationRatio oracleCost optimalCost < envelope3 := by
  simpa [envelope3] using
    near_degenerate_ratio_lt_nat_root_envelope 3 oracleCost optimalCost Δ hOptPos hGap hΔ

/-! ## 3+1 route (`n = 4`) -/

/-- `n = 4` envelope constant (`3 + 1` case). -/
def envelope4 : ℝ := 1 + (4 : ℝ) ^ (1 / (4 : ℝ))

/--
Degenerate `n = 4` baseline:
if oracle and optimal costs are equal, ratio is exactly `1`.
-/
theorem n4_exact_degenerate_ratio_eq_one
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost = 1 :=
  exact_degenerate_ratio_eq_one oracleCost optimalCost hEq hOptPos

/--
Degenerate `n = 4` baseline lies inside the envelope `1 + 4^(1/4)`.
-/
theorem n4_exact_degenerate_ratio_le_envelope
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost ≤ envelope4 := by
  simpa [envelope4] using
    exact_degenerate_ratio_le_nat_root_envelope 4 oracleCost optimalCost hEq hOptPos

/--
Degenerate `n = 4` baseline strictly beats the generic worst-case envelope.
-/
theorem n4_exact_degenerate_ratio_lt_envelope
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost < envelope4 := by
  simpa [envelope4] using
    exact_degenerate_ratio_lt_nat_root_envelope 4 oracleCost optimalCost hEq hOptPos (by norm_num)

/--
`n = 4` additive perturbation transfer into the envelope.
-/
theorem n4_additive_perturbation_within_envelope
    (oracleCost optimalCost Δ : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + Δ)
    (hΔ : Δ ≤ optimalCost * ((4 : ℝ) ^ (1 / (4 : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ envelope4 := by
  simpa [envelope4] using
    near_degenerate_ratio_le_nat_root_envelope 4 oracleCost optimalCost Δ hOptPos hGap hΔ

/--
`n = 4` strict sub-envelope perturbation.
-/
theorem n4_additive_perturbation_strictly_beats_envelope
    (oracleCost optimalCost Δ : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + Δ)
    (hΔ : Δ < optimalCost * ((4 : ℝ) ^ (1 / (4 : ℝ)))) :
    approximationRatio oracleCost optimalCost < envelope4 := by
  simpa [envelope4] using
    near_degenerate_ratio_lt_nat_root_envelope 4 oracleCost optimalCost Δ hOptPos hGap hΔ

/-! ## General successor route (`n + 1`) -/

/-- Successor envelope constant. -/
def envelopeSucc (n : ℕ) : ℝ :=
  1 + ((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ))

/--
Exact-degenerate successor case:
for `n+1`, ratio `= 1` and therefore lies inside the successor envelope.
-/
theorem succ_exact_degenerate_ratio_le_envelope
    (n : ℕ)
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost ≤ envelopeSucc n := by
  simpa [envelopeSucc] using
    exact_degenerate_ratio_le_nat_root_envelope (Nat.succ n) oracleCost optimalCost hEq hOptPos

/--
Exact-degenerate successor case strictly beats the successor envelope.
-/
theorem succ_exact_degenerate_ratio_lt_envelope
    (n : ℕ)
    (oracleCost optimalCost : ℝ)
    (hEq : oracleCost = optimalCost)
    (hOptPos : 0 < optimalCost) :
    approximationRatio oracleCost optimalCost < envelopeSucc n := by
  simpa [envelopeSucc] using
    exact_degenerate_ratio_lt_nat_root_envelope
      (Nat.succ n) oracleCost optimalCost hEq hOptPos (Nat.succ_pos _)

/--
Near-degenerate successor case:
if additive gap is bounded by `optimal * (n+1)^(1/(n+1))`, the ratio lies inside
the successor envelope.
-/
theorem succ_near_degenerate_ratio_le_envelope
    (n : ℕ)
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + ε)
    (hEpsBound : ε ≤ optimalCost * (((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ envelopeSucc n := by
  simpa [envelopeSucc] using
    near_degenerate_ratio_le_nat_root_envelope
      (Nat.succ n) oracleCost optimalCost ε hOptPos hGap hEpsBound

/--
Successor-form strict near-degenerate case:
if the additive gap is strictly smaller than the successor root scale, the ratio
strictly beats the successor envelope.
-/
theorem succ_near_degenerate_ratio_lt_envelope
    (n : ℕ)
    (oracleCost optimalCost ε : ℝ)
    (hOptPos : 0 < optimalCost)
    (hGap : oracleCost ≤ optimalCost + ε)
    (hEpsBound : ε < optimalCost * (((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ)))) :
    approximationRatio oracleCost optimalCost < envelopeSucc n := by
  simpa [envelopeSucc] using
    near_degenerate_ratio_lt_nat_root_envelope
      (Nat.succ n) oracleCost optimalCost ε hOptPos hGap hEpsBound

/--
Successor-form bridge contract:
hybrid residual channels + local completion monotonicity imply the successor
envelope bound (`n+1` case).
-/
theorem succ_hybrid_channels_and_local_monotone_imply_envelope
    (n : ℕ)
    (oracleCost seedCost optimalCost ε tensorResidualErr rapidityErr axisErr : ℝ)
    (hOptPos : 0 < optimalCost)
    (hProjResidual :
      seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr)
    (hResidualBudget : tensorResidualErr + rapidityErr + axisErr ≤ ε)
    (hLocalCompletion : oracleCost ≤ seedCost)
    (hEpsEnvelope :
      ε ≤ optimalCost * (((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ envelopeSucc n := by
  have hMain :
      approximationRatio oracleCost optimalCost ≤
        1 + ((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ)) := by
    exact hybrid_channels_and_local_monotone_imply_envelope
      (Nat.succ n)
      oracleCost seedCost optimalCost ε tensorResidualErr rapidityErr axisErr
      hOptPos hProjResidual hResidualBudget hLocalCompletion hEpsEnvelope
  simpa [envelopeSucc] using hMain

/--
Successor-form fractional channel-budget bridge:
if each certified channel is bounded by `optimalCost * ρᵢ` and
`ρₜ + ρᵣ + ρₐ ≤ (n+1)^(1/(n+1))`, the successor envelope holds.
-/
theorem succ_hybrid_channels_fractional_budget_imply_envelope
    (n : ℕ)
    (oracleCost seedCost optimalCost tensorResidualErr rapidityErr axisErr : ℝ)
    (ρt ρr ρa : ℝ)
    (hOptPos : 0 < optimalCost)
    (hProjResidual :
      seedCost ≤ optimalCost + tensorResidualErr + rapidityErr + axisErr)
    (hLocalCompletion : oracleCost ≤ seedCost)
    (hTensorBound : tensorResidualErr ≤ optimalCost * ρt)
    (hRapidityBound : rapidityErr ≤ optimalCost * ρr)
    (hAxisBound : axisErr ≤ optimalCost * ρa)
    (hFracBudget :
      ρt + ρr + ρa ≤ (((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ)))) :
    approximationRatio oracleCost optimalCost ≤ envelopeSucc n := by
  have hMain :
      approximationRatio oracleCost optimalCost ≤
        1 + ((Nat.succ n : ℕ) : ℝ) ^ (1 / ((Nat.succ n : ℕ) : ℝ)) := by
    exact hybrid_channels_fractional_budget_imply_envelope
      (Nat.succ n)
      oracleCost seedCost optimalCost tensorResidualErr rapidityErr axisErr
      ρt ρr ρa
      hOptPos hProjResidual hLocalCompletion
      hTensorBound hRapidityBound hAxisBound hFracBudget
  simpa [envelopeSucc] using hMain

end

