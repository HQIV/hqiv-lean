import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.ContinuousXiPath

namespace Hqiv.Physics

open ContinuousXiPath

/-!
# TUFT shell chart vs HQIV lock-in shell (ontology)

Two shell languages appear in-repo. **Do not conflate them in prose or readouts.**

| Name | Role | Value (current pins) |
|------|------|---------------------|
| `referenceM` | HQIV substrate lock-in (`qcdShell + latticeStepCount`); cosmology / export pin | 4 |
| `tuft*HopfWinding` | Integrable Hopf shell index on the TUFT Beltrami ladder | 1, 2, 3 |
| `tuft*ChartShell` | Chart sample `m = winding + 1` on that ladder | 2, 3, 4 |
| `tuftHadronModeShell n ℓ` | Baryon excitation channel on the **heavy TUFT chart** | `4 + n + ℓ` |

**Hadron spectroscopy** names `tuftHeavyChartShell` and `tuftHadronModeShell`.
**Cosmology, CMB, and the single-scale witness** name `referenceM`.

Numeric equality `referenceM = tuftHeavyChartShell` is certified separately; it is **not**
definitional. Future pin decoupling must not silently alias the two in TUFT papers.
-/

/-- TUFT weak-sector Hopf winding (first nontrivial shell → `S³` chart). -/
def tuftWeakHopfWinding : ℕ := 1

/-- TUFT strong-sector Hopf winding (`S⁵` chart). -/
def tuftStrongHopfWinding : ℕ := 2

/-- TUFT heavy-sector Hopf winding (T12 trefoil / charged-lepton vev row). -/
def tuftHeavyHopfWinding : ℕ := 3

/-- Legacy alias: weak Hopf index. -/
def tuftWeakHopfShellIndex : ℕ := tuftWeakHopfWinding

/-- Legacy alias: strong Hopf index. -/
def tuftStrongHopfShellIndex : ℕ := tuftStrongHopfWinding

/-- Beltrami chart row `m = Hopf winding + 1` (weak sector). -/
def tuftWeakChartShell : ℕ := tuftWeakHopfWinding + 1

/-- Beltrami chart row (strong sector). -/
def tuftStrongChartShell : ℕ := tuftStrongHopfWinding + 1

/-- Beltrami chart row (heavy sector — baryon / τ vev anchor). -/
def tuftHeavyChartShell : ℕ := tuftHeavyHopfWinding + 1

theorem tuftWeakChartShell_eq_two : tuftWeakChartShell = 2 := by decide

theorem tuftStrongChartShell_eq_three : tuftStrongChartShell = 3 := by decide

theorem tuftHeavyChartShell_eq_four : tuftHeavyChartShell = 4 := by decide

theorem tuftHeavyChartShell_eq_winding_plus_one :
    tuftHeavyChartShell = tuftHeavyHopfWinding + 1 := rfl

theorem tuftStrongChartShell_lt_tuftHeavyChartShell :
    tuftStrongChartShell < tuftHeavyChartShell := by
  rw [tuftStrongChartShell_eq_three, tuftHeavyChartShell_eq_four]
  decide

theorem tuftHeavyChartShell_ne_tuftWeakWinding :
    tuftHeavyChartShell ≠ tuftWeakHopfWinding := by decide

theorem hqivLockinShell_ne_tuftWeakWinding : referenceM ≠ tuftWeakHopfWinding := by
  rw [referenceM_eq_four]
  decide

/-- Numeric coincidence under current substrate pins — not definitional equality. -/
theorem referenceM_eq_tuftHeavyChartShell_numeric :
    referenceM = tuftHeavyChartShell := by
  rw [tuftHeavyChartShell_eq_four, referenceM_eq_four]

/-! ## Hadron mode shells (heavy TUFT chart only) -/

/-- Radial Beltrami step `n` on the heavy TUFT chart. -/
def tuftHadronRadialShell (n : ℕ) : ℕ := tuftHeavyChartShell + n

/-- Orbital Beltrami step `ℓ` on the heavy TUFT chart. -/
def tuftHadronOrbitalShell (ℓ : ℕ) : ℕ := tuftHeavyChartShell + ℓ

/-- Combined excitation channel tag: heavy chart + internal quanta `(n, ℓ)`. -/
def tuftHadronModeShell (n ℓ : ℕ) : ℕ := tuftHeavyChartShell + n + ℓ

theorem tuftHadronModeShell_zero_zero :
    tuftHadronModeShell 0 0 = tuftHeavyChartShell := by
  unfold tuftHadronModeShell
  simp

theorem tuftHadronRadialShell_zero :
    tuftHadronRadialShell 0 = tuftHeavyChartShell := by
  unfold tuftHadronRadialShell
  simp

theorem tuftHadronOrbitalShell_zero :
    tuftHadronOrbitalShell 0 = tuftHeavyChartShell := by
  unfold tuftHadronOrbitalShell
  simp

/-! ## Meson mode shells (strong TUFT chart) -/

/-- Radial Beltrami step `n` on the strong TUFT chart. -/
def tuftMesonRadialShell (n : ℕ) : ℕ := tuftStrongChartShell + n

/-- Orbital Beltrami step `ℓ` on the strong TUFT chart. -/
def tuftMesonOrbitalShell (ℓ : ℕ) : ℕ := tuftStrongChartShell + ℓ

/-- Combined vector-meson channel tag: strong chart + internal quanta `(n, ℓ)`. -/
def tuftMesonModeShell (n ℓ : ℕ) : ℕ := tuftStrongChartShell + n + ℓ

theorem tuftMesonModeShell_zero_zero :
    tuftMesonModeShell 0 0 = tuftStrongChartShell := by
  unfold tuftMesonModeShell
  simp

theorem tuftMesonRadialShell_zero :
    tuftMesonRadialShell 0 = tuftStrongChartShell := by
  unfold tuftMesonRadialShell
  simp

theorem tuftMesonOrbitalShell_zero :
    tuftMesonOrbitalShell 0 = tuftStrongChartShell := by
  unfold tuftMesonOrbitalShell
  simp

end Hqiv.Physics
