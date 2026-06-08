import Hqiv.Algebra.CliffordCl06SixSpinorMonomialMatrixData

/-!
# Compatibility import for `HQIVSpinorMonomialCert`

The mod-`101` axiom `spinorMonomialGramColumnsZMod101_det` and the theorem
`spinorMonomialGramColumns_det_ne_zero` now live in `CliffordCl06SixSpinorMonomialMatrixData` so
that default `HQIVLEAN` builds can consume the nonsingularity fact.

The optional lake target `HQIVSpinorMonomialCert` still points at this file for historical
`lake build HQIVSpinorMonomialCert` workflows.
-/
