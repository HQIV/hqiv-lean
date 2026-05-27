import Hqiv.Physics.StrongColorSu3fStructureSimp

/-!
# Strong color: SU(3) Lie certificate (optional)

Build with `lake build HQIVStrongColorSu3Certificate`.

This module re-exports the auto-generated `@[simp]` table `StrongColorSu3fStructureSimp` (54 nonzero
`f^{abc}` triples). Regenerate the table with:

`python3 scripts/gen_strong_color_su3_f_simp.py`

The full matrix identity `∀ a b, [T^a,T^b] = \mathrm{i}\sum_c f^{abc}T^c` on the abstract `3×3` chart is proved in
`StrongColorSu3LieChartLaw` (`colorHalfGellMannFull_lieBracket_eq_I_smul_f_sum`; regenerate
`python3 scripts/gen_strong_color_su3_lie_chart_law.py`). The root module `HQIVStrongColorSu3Certificate` imports
both this re-export and `StrongColorSu3LieChartLaw` so `lake build HQIVStrongColorSu3Certificate` checks the
entire optional cone without bloating the default `HQIVLEAN` glob.
-/
