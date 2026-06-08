import Mathlib.Data.Real.Basic

import Hqiv.Geometry.SATRapidityPackingBridge

/-!
# SAT rapidity tangent-packing bridge

This file formalizes the second candidate final bridge:
Riemannian tangent-space packing.

Again, the treatment is assumption-explicit. The goal is to encode the exact
interface by which a tangent-space kissing / packing theorem would plug into the
SAT residual-budget machinery.
-/

namespace Hqiv.Geometry

noncomputable section

/--
Abstract tangent-space packing certificate.

The intended interpretation is that residuals are represented by tangent vectors
whose pairwise angular separation and norm control induce a frontier bound.
-/
structure SATRapidityTangentPackingCertificate (M : Type*) where
  control : SuccessorStepResidualControl M
  tangentBound : ℕ → ℝ
  tangentDim : ℕ
  hTangentLen : (control.arityResiduals.length : ℝ) ≤ tangentBound tangentDim
  hTangentDimBound : tangentBound tangentDim ≤ tangentBound (control.shared.varDim + control.shared.clauseDim)

/-- Tangent-packing certificate yields a packing certificate directly. -/
def SATRapidityTangentPackingCertificate.toPackingCertificate
    {M : Type*}
    (C : SATRapidityTangentPackingCertificate M) :
    SATRapidityPackingCertificate M where
  control := C.control
  frontierBound := C.tangentBound
  effectiveDim := C.tangentDim
  hFrontierLen := C.hTangentLen
  hFrontierBoundPoly := C.hTangentDimBound

/--
Tangent-packing route into the polynomial residual-budget pipeline.
-/
theorem tangentPackingCertificate_hasPolynomialResidualBudget
    {M : Type*}
    (C : SATRapidityTangentPackingCertificate M)
    (polyBound : ℕ → ℝ)
    (hPoly : C.control.rapidThreshold ≤ polyBound (C.control.shared.varDim + C.control.shared.clauseDim))
    (hPolyNonneg : 0 ≤ polyBound (C.control.shared.varDim + C.control.shared.clauseDim))
    (hTangentNonneg : 0 ≤ C.tangentBound (C.control.shared.varDim + C.control.shared.clauseDim))
    (hResidualNonneg : ∀ ε ∈ C.control.arityResiduals, 0 ≤ ε) :
    HasPolynomialResidualBudget
      (fun n => C.tangentBound n * polyBound n)
      (C.control.shared.varDim + C.control.shared.clauseDim)
      C.control.arityResiduals := by
  simpa using packingCertificate_hasPolynomialResidualBudget
    (P := C.toPackingCertificate)
    (polyBound := polyBound)
    hPoly hPolyNonneg hTangentNonneg hResidualNonneg

end

end Hqiv.Geometry
