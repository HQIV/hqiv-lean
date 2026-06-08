import Hqiv.QuantumComputing.FrequencyCertificate

/-!
# Abstract sparse schedule cost model

Conditional polynomial classical cost for domain-aware frequency sparse simulation:
if an exported certificate is `acceptedPolynomial` at size `n`, total schedule cost is
bounded by a polynomial in `n` under this explicit bookkeeping model.

This is certificate-first; gate-level fast-path semantics are in `FrequencyGateSemantics`.
-/

namespace Hqiv.QuantumComputing

/-- Per-step sparse frequency cost: linear in support, scaled by frequency χ. -/
def frequencySparseStepCost (maxSupport maxChiFrequencyBand : Nat) : Nat :=
  maxSupport * maxChiFrequencyBand + maxSupport

theorem frequencySparseStepCost_mono_support {s s' c : Nat} (h : s ≤ s') :
    frequencySparseStepCost s c ≤ frequencySparseStepCost s' c := by
  unfold frequencySparseStepCost
  exact Nat.add_le_add (Nat.mul_le_mul_right c h) h

theorem frequencySparseStepCost_mono_chi {s c c' : Nat} (h : c ≤ c') :
    frequencySparseStepCost s c ≤ frequencySparseStepCost s c' := by
  unfold frequencySparseStepCost
  exact Nat.add_le_add (Nat.mul_le_mul_left s h) (Nat.le_refl s)

theorem frequencySparseStepCost_mono {s s' c c' : Nat} (hs : s ≤ s') (hc : c ≤ c') :
    frequencySparseStepCost s c ≤ frequencySparseStepCost s' c' :=
  le_trans (frequencySparseStepCost_mono_support hs) (frequencySparseStepCost_mono_chi hc)

/-- Total schedule cost for a depth-`d` circuit with uniform step bounds. -/
def scheduleCost (depth maxSupport maxChiFrequencyBand : Nat) : Nat :=
  depth * frequencySparseStepCost maxSupport maxChiFrequencyBand

theorem frequencySparseStepCost_le_work_bound (c : FrequencyObligations) :
    frequencySparseStepCost c.maxSupport c.maxChiFrequencyBand ≤ certificateWorkBound c := by
  dsimp [frequencySparseStepCost, certificateWorkBound]
  omega

theorem scheduleCost_le_depth_mul_work (c : FrequencyObligations) :
    scheduleCost c.depth c.maxSupport c.maxChiFrequencyBand ≤
      c.depth * certificateWorkBound c := by
  dsimp [scheduleCost]
  exact Nat.mul_le_mul_left _ (frequencySparseStepCost_le_work_bound c)

/-- Combined polynomial degree for schedule cost from witness degrees. -/
def schedulePolyDegree (w : PolynomialWitness) : Nat :=
  w.polyDegreeSupport + w.polyDegreeFrequencyChi + w.polyDegreeRouteCount + 3

theorem polyEnvelope_mul_le {n a b : Nat} :
    polyEnvelope n a * polyEnvelope n b ≤ polyEnvelope n (a + b + 1) := by
  simp [polyEnvelope, Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem polyEnvelope_triple_product_le {n a b c : Nat} :
    polyEnvelope n a * polyEnvelope n b * polyEnvelope n c ≤
      polyEnvelope n (a + b + c + 2) := by
  calc
    polyEnvelope n a * polyEnvelope n b * polyEnvelope n c
        ≤ polyEnvelope n (a + b + 1) * polyEnvelope n c := by
          exact Nat.mul_le_mul_right _ (polyEnvelope_mul_le (n := n) (a := a) (b := b))
    _ ≤ polyEnvelope n (a + b + c + 2) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        polyEnvelope_mul_le (n := n) (a := a + b + 1) (b := c)

/-- Crude envelope for `A * (B * C + B)` when `A,B,C` are already envelope-bounded. -/
private theorem polyEnvelope_depth_step_le {n a b c : Nat} (_hn : 1 ≤ n) :
    polyEnvelope n a * (polyEnvelope n b * polyEnvelope n c + polyEnvelope n b) ≤
      polyEnvelope n (a + b + c + 3) := by
  have h1 := polyEnvelope_triple_product_le (n := n) (a := a) (b := b) (c := c)
  have h2 := polyEnvelope_mul_le (n := n) (a := a) (b := b)
  have hn : 2 ≤ n + 1 := Nat.succ_le_succ _hn
  calc
    polyEnvelope n a * (polyEnvelope n b * polyEnvelope n c + polyEnvelope n b)
        = polyEnvelope n a * polyEnvelope n b * polyEnvelope n c +
            polyEnvelope n a * polyEnvelope n b := by
      rw [Nat.mul_add, Nat.mul_assoc]
    _ ≤ polyEnvelope n (a + b + c + 2) + polyEnvelope n (a + b + 1) := Nat.add_le_add h1 h2
    _ ≤ polyEnvelope n (a + b + c + 3) := by
          unfold polyEnvelope
          have hmono :
              (n + 1) ^ (a + b + 1 + 1) ≤ (n + 1) ^ (a + b + c + 3) := by
            apply Nat.pow_le_pow_right (Nat.succ_pos n)
            omega
          have hsum :
              (n + 1) ^ (a + b + c + 3) + (n + 1) ^ (a + b + 1 + 1) ≤
                2 * (n + 1) ^ (a + b + c + 3) := by omega
          have hdouble :
              2 * (n + 1) ^ (a + b + c + 3) ≤ (n + 1) ^ (a + b + c + 4) := by
            calc
              2 * (n + 1) ^ (a + b + c + 3)
                  ≤ (n + 1) * (n + 1) ^ (a + b + c + 3) := Nat.mul_le_mul_right _ hn
              _ = (n + 1) ^ (a + b + c + 4) := by
                rw [← Nat.mul_comm ((n + 1) ^ (a + b + c + 3)) (n + 1)]
                exact (Nat.pow_succ (n + 1) (a + b + c + 3)).symm
          exact le_trans hsum hdouble

/-- **Main conditional cost theorem (certificate layer). -/
theorem scheduleCost_polynomial_of_acceptedPolynomial
    (cert : FrequencyPolynomialCertificate) (n : Nat)
    (_hn : 1 ≤ n)
    (h : cert.acceptedPolynomial n) :
    ∃ d,
      scheduleCost cert.obligations.depth cert.obligations.maxSupport
          cert.obligations.maxChiFrequencyBand ≤ polyEnvelope n d := by
  let w := cert.witness
  let c := cert.obligations
  have hpoly := FrequencyPolynomialCertificate.polyBoundedAt_of_acceptedPolynomial h
  have hs := hpoly.1
  have hchi := hpoly.2.1
  have hdepth := hpoly.2.2
  refine ⟨schedulePolyDegree w, ?_⟩
  dsimp [scheduleCost, frequencySparseStepCost, schedulePolyDegree]
  have hstep :
      c.maxSupport * c.maxChiFrequencyBand + c.maxSupport ≤
        polyEnvelope n w.polyDegreeSupport * polyEnvelope n w.polyDegreeFrequencyChi +
          polyEnvelope n w.polyDegreeSupport := by
    exact certificateWorkBound_le_envelope hpoly
  have hmul :
      c.depth * (c.maxSupport * c.maxChiFrequencyBand + c.maxSupport) ≤
        polyEnvelope n w.polyDegreeRouteCount *
          (polyEnvelope n w.polyDegreeSupport * polyEnvelope n w.polyDegreeFrequencyChi +
            polyEnvelope n w.polyDegreeSupport) := by
    exact Nat.mul_le_mul hdepth hstep
  have hdepth_step := polyEnvelope_depth_step_le (n := n)
    (a := w.polyDegreeRouteCount) (b := w.polyDegreeSupport) (c := w.polyDegreeFrequencyChi) _hn
  have hdeg :
      w.polyDegreeRouteCount + w.polyDegreeSupport + w.polyDegreeFrequencyChi + 3 =
        schedulePolyDegree w := by
    unfold schedulePolyDegree
    ac_rfl
  exact le_trans hmul (by simpa [hdeg] using hdepth_step)

/--
Reusable symbolic version of the schedule-cost theorem: fixed polynomial degree witnesses for
route count, support, and frequency χ give a fixed polynomial bound on total schedule cost.
-/
theorem scheduleCost_le_polyEnvelope_of_bounds
    (w : PolynomialWitness) (n depth maxSupport maxChiFrequencyBand : Nat)
    (_hn : 1 ≤ n)
    (hdepth : depth ≤ polyEnvelope n w.polyDegreeRouteCount)
    (hsupport : maxSupport ≤ polyEnvelope n w.polyDegreeSupport)
    (hchi : maxChiFrequencyBand ≤ polyEnvelope n w.polyDegreeFrequencyChi) :
    scheduleCost depth maxSupport maxChiFrequencyBand ≤ polyEnvelope n (schedulePolyDegree w) := by
  dsimp [scheduleCost, frequencySparseStepCost, schedulePolyDegree]
  have hstep :
      maxSupport * maxChiFrequencyBand + maxSupport ≤
        polyEnvelope n w.polyDegreeSupport * polyEnvelope n w.polyDegreeFrequencyChi +
          polyEnvelope n w.polyDegreeSupport := by
    exact Nat.add_le_add (Nat.mul_le_mul hsupport hchi) hsupport
  have hmul :
      depth * (maxSupport * maxChiFrequencyBand + maxSupport) ≤
        polyEnvelope n w.polyDegreeRouteCount *
          (polyEnvelope n w.polyDegreeSupport * polyEnvelope n w.polyDegreeFrequencyChi +
            polyEnvelope n w.polyDegreeSupport) := by
    exact Nat.mul_le_mul hdepth hstep
  have hdepth_step := polyEnvelope_depth_step_le (n := n)
    (a := w.polyDegreeRouteCount) (b := w.polyDegreeSupport) (c := w.polyDegreeFrequencyChi) _hn
  have hdeg :
      w.polyDegreeRouteCount + w.polyDegreeSupport + w.polyDegreeFrequencyChi + 3 =
        schedulePolyDegree w := by
    unfold schedulePolyDegree
    ac_rfl
  exact le_trans hmul (by simpa [hdeg] using hdepth_step)

/-- Accepted polynomial certificate ⇒ no dense fallback (routing stays sparse). -/
theorem acceptedPolynomial_no_dense_fallback
    {cert : FrequencyPolynomialCertificate} {n : Nat}
    (h : cert.acceptedPolynomial n) :
    cert.obligations.denseFallbackCount = 0 :=
  FrequencyObligations.accepted_no_dense_fallback
    (FrequencyPolynomialCertificate.accepted_of_acceptedPolynomial h)

/-- Accepted polynomial certificate ⇒ frequency χ within global χ export. -/
theorem acceptedPolynomial_frequency_chi_le_global
    {cert : FrequencyPolynomialCertificate} {n : Nat}
    (h : cert.acceptedPolynomial n) :
    cert.obligations.maxChiFrequencyBand ≤ cert.obligations.maxChiBound :=
  FrequencyObligations.accepted_frequency_chi_le_global
    (FrequencyPolynomialCertificate.accepted_of_acceptedPolynomial h)

end Hqiv.QuantumComputing
