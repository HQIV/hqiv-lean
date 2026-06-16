# TODO: Audit the frozen octonion left-multiplication tables

**Status:** OPEN (bookmarked 2026-06-10 during the S³/ζ associator-channel work)

## Finding

While computing concrete associator witnesses for
`Hqiv/Story/S3OctonionicAssociatorChannel.lean`, the frozen tables in
`Hqiv/OctonionLeftMultiplication.lean` (source: `HQVM/matrices.py`,
`_build_left_multiplications`, regenerated via
`scripts/print_lean_octonion_L.py`) were found to violate two properties
that the standard Cayley octonions must satisfy:

1. **Non-alternating associator.** On the frozen tables
   `[e1,e2,e4] = (e1·e2)·e4 − e1·(e2·e4) = −e3 − e4`, but
   `[e2,e1,e4] = e3 − e4 ≠ −[e1,e2,e4] = e3 + e4`.
   The octonion associator is totally antisymmetric (the algebra is
   alternative); the frozen tables are not.

2. **Fano incidence violation.** Reading products off columns:
   `e1·e3 = −e6` (line {1,3,6}) and `e2·e3 = e6` (line {2,3,6}).
   Two distinct Fano lines share two points {3,6}, which is impossible in
   a projective plane. Similarly `e1·e2 = e7` ({1,2,7}) and
   `e5·e2 = e7` ({2,5,7}) share {2,7}.

So the frozen matrices do **not** encode the standard octonion
multiplication in any basis relabeling — most likely a sign/convention
or transposition bug in `_build_left_multiplications` (e.g. row/column
convention flipped for some units, or an index permutation applied
inconsistently).

## Impact assessment (current corpus)

- `Hqiv/Story/S3OctonionicAssociatorChannel.lean` and
  `Hqiv/Story/S3OctonionS7TorsionCancellation.lean` only use facts
  *proved directly from the tables* (specific products, trilinearity,
  the concrete witness `[e1,e2,e4] = −e3 − e4` with norm² 2), so the
  theorems are true as stated for the frozen carrier — but the witness
  values (direction, norm) will change if the tables are corrected.
- Anything that *narratively* assumes alternativity, Moufang identities,
  G₂ = derivation algebra, or Fano-plane incidence on top of these
  matrices needs re-checking (see warning already present in
  `Hqiv/Algebra/WeakFromLeftMulOctonion.lean`: the su(2) closure check
  also failed on the frozen tables — plausibly the same root cause).

## Action items

- [ ] Audit `HQVM/matrices.py::_build_left_multiplications` against a
      reference octonion table (e.g. e_i·e_j with the standard
      {(1,2,3),(1,4,5),(1,7,6),(2,4,6),(2,5,7),(3,4,7),(3,6,5)} cycles);
      check row/column convention of `L(e_i)[k][j] = coefficient of e_k
      in e_i·e_j`.
- [ ] Regenerate `Hqiv/OctonionLeftMultiplication.lean` via
      `scripts/print_lean_octonion_L.py` and rebuild; expect breakage in
      column-signature theorems (`octonionLeftMul_*_k_*`) — update signs.
- [ ] Re-prove alternativity spot-checks in Lean after the fix:
      `[e2,e1,e4] = −[e1,e2,e4]` should hold.
- [ ] Recompute the associator-channel witness constants
      (`octonionAssociator_e1_e2_e4`, norm² value) and propagate to
      `papers/s3_zeta_so4_projection` (§ associator channel, § S⁷ torsion
      cancellation) and the claim-status table.
- [ ] Re-run the `WeakFromLeftMulOctonion` su(2)-closure check after the
      fix to see whether the documented failure disappears.
