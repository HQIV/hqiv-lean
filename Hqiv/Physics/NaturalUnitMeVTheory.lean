/-!
# Natural-unit MeV readout layer (conceptual)

This file records the high-level MeV chart philosophy and the trapped-radiative
/ shell-sampled curvature imprint direction.  The shell labels are readout
samples of the moving carrier; they are not intended to do the mass generation
alone.

All executable low-level definitions and wiring live in the main
bridge file (`HopfShellBeltramiMassBridge.lean`) to keep this file
lightweight and the builds green.

See the AGENTS document for the current detailed status of the
per-shell α_n attack and the trapped-Casimir reading.
-/

namespace Hqiv.Physics

/-! ## Suggested step 2 focus: Lepton-specific chart example

The proton export chart (`referenceM`) is a **hadronic calibration convention**, not a derived
shell. The current mass readout is driven by the carrier geometry, trapped Planck / Casimir budget,
and phase motion on the TUFT heavy chart (`tuftHeavyChartShell`), not by treating `m = 4` as
physics output.

An optional lepton-specific chart can be constructed using the T3 gap candidate
(or T12-modulated trapping on the n=3 heavy shell) as the heavy lepton anchor.
This can bring the heavy lepton natural-unit readout into ballpark range while
preserving the proton chart as the default for hadrons.

The T12 witness + trappingSelectionFromThreeHopfShellsWithAlphas (with α_n from
the three integrable Hopf shells) supply the per-shell imprint data needed for
such a chart. See the dedicated section in the bridge for the explicit three-step
focus (heavy observable decision, this lepton chart, and the gluonic vs leptonic
scoping).

The ontological tension (gluonic vs color-neutral lepton masses on the same
carrier) is documented honestly in the bridge and the md.
-/

/-! ## Accurate T → mass in MeV (T1-T13 complete, bidirectional, physical units)

The bridge now exposes the full dynamic pipeline wired to MeV:

* `heavy_lepton_gap_at_physical_T_MeV T_phys_MeV`   -- T (e.g. CMB 2.725 K in MeV) → heavy lepton mass in MeV
* `leptonMassSpectrum_at_physical_T_MeV T_phys_MeV` -- full (heavy, μ, e) in MeV
* `heavy_lepton_gap_CMB_today_MeV`, `..._BBN_window_MeV`
* `xi_for_target_heavy_mass` / `physical_T_for_target_heavy_mass` (inverse chart helpers)
* `heavy_lepton_scale_multiplier_at_physical_T` (the pure geometry factor ~183× at CMB vs lock-in)

All numbers are produced by the complete pulled T8 (zeta leading on heavy shell) +
T11 (torsionMatrixCoefficient = 4/5 on T12 n=3 witness) + T10 (144/91 admissible row) +
T12 (three-shell per-imprint trapping + cannot_factor) + dynamic T13 outer suppression on
the neutral singlet extension (recovering 1/140 at lock-in) + the inner/outer Casimir dynamic scale running with
`omegaK_xi(ξ)` from the continuous curvature primitive on the temperature ladder.

At ξ=5 (vev/lock-in read from the ladder) the legacy good ratios are recovered exactly.
At any other T the absolute scale and the generation splittings evolve according to the
same Casimir symmetry-breaking mechanism acting on the inside contact surfaces vs. the
outer neutral surface of the carrier.

See `HopfShellBeltramiMassBridge.lean` (the MeV-anchored readouts section and the long
"Temperature to mass spectrum" docstring) for the executable defs and the #checks.
The synthesis narrative is in `AGENTS/TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md`.
-/

end Hqiv.Physics
