import Hqiv.Physics.StrongColorSu3fStructureSimp

/-!
# Strong color: SU(3) Lie certificate (optional)

Build with `lake build HQIVStrongColorSu3Certificate`.

This module re-exports the auto-generated `@[simp]` table `StrongColorSu3fStructureSimp` (54 nonzero
`f^{abc}` triples). Regenerate the table with:

`python3 scripts/gen_strong_color_su3_f_simp.py`

The full matrix identity `∀ a b, [T^a,T^b] = \mathrm{i}\sum_c f^{abc}T^c` can be layered on top of this
table (e.g. `Finset.sum_eq_single` / `fin_cases` on chart indices) without bloating the default `HQIVLEAN`
cone.
-/
