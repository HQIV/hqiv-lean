import HqivSpine.Algebra.StrongColorSu3fSimp

/-!
# `HqivSpine.Algebra.StrongColorSu3LieCertificate` — SU(3) Lie certificate re-export

Builds with `HQIVCleanSpine`. Re-exports the auto-generated `@[simp]` table for the 54 nonzero
`f^{abc}` triples. Regenerate with:

`python3 scripts/gen_strong_color_su3_f_simp.py --spine`

The full matrix identity `∀ a b, [T^a,T^b] = Complex.I • ∑_c f^{abc} T^c` is in
`StrongColorSu3LieLaw` (regenerate `python3 scripts/gen_strong_color_su3_lie_chart_law.py --spine`).
-/
