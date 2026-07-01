import Hqiv.Algebra.CliffordCl06SixSpinorMonomialMatrixData

/-!
# Compatibility import for `HQIVSpinorMonomialCert`

The nonsingularity theorem `spinorMonomialGramColumns_det_ne_zero` now lives in
`CliffordCl06SixSpinorMonomialMatrixData`, where it is *proved* (no longer an external-script
axiom) from the closed form `spinorMonomialGramColumns_eq_one` (`W = I₆₄`) via the Kronecker
mixed-product reduction of the Frobenius pairing.  The former `ZMod 101` determinant axiom has
been removed.

The optional lake target `HQIVSpinorMonomialCert` still points at this file for historical
`lake build HQIVSpinorMonomialCert` workflows.
-/
