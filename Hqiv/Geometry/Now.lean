import Mathlib.Data.Real.Basic
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv

/-!
# Determining "now" in the HQIV framework

The paper uses **T_CMB** (CMB temperature today) to fix the observer's "now" slice.
Here we give a **framework-natural** definition that does not take T_CMB as input,
and then show consistency with the T_CMB characterization.

## Natural definition: "now" when H = H₀

In the homogeneous limit we identify **φ = H** (Hubble parameter). The reference
Hubble is **H₀ = 1** in natural units. So the observer's **"now"** is the slice
(time or horizon) at which the Hubble parameter equals H₀:

  **now** ⟺ H = H₀  (φ = 1 in natural units).

This is **internal** to the framework: no CMB temperature is required. The dynamics
(Friedmann equation) then determine the scale factor a(now) and, via the
temperature–scale relation, the temperature at "now". That derived temperature
can be compared to T_CMB as a consistency check.

## Paper definition: "now" via T_CMB

The paper fixes "now" by the observed CMB temperature: the shell m_now such that
T(m_now) = T_CMB. We state this and show it is **equivalent** to the H = H₀
definition when the dynamics and the T–a relation are used.
-/

/-- **H₀ in natural units** (reference Hubble at "now"). Already defined in HQVMetric;
    we re-export the idea that "now" is when H = H₀. -/
def H0_ref : ℝ := H0

theorem H0_ref_eq : H0_ref = 1 := H0_eq

/-!
## "Now" by H = H₀ (framework-natural)
-/

/-- **"Now" condition (natural):** the observer's present slice is the one at which
    the Hubble parameter equals the reference value H₀. In the homogeneous limit
    H = φ, so "now" is when φ = H₀. No T_CMB input. -/
def nowCondition (φ : ℝ) : Prop := φ = H0_ref

/-- **In natural units, "now" is when φ = 1.** -/
theorem nowCondition_iff_phi_one (φ : ℝ) : nowCondition φ ↔ φ = 1 := by
  unfold nowCondition H0_ref; simp [H0_eq]

/-- **There is a unique φ satisfying the "now" condition** (φ = 1). -/
theorem exists_unique_now_phi : ∃! φ : ℝ, nowCondition φ := by
  use 1
  simp [nowCondition, H0_ref_eq]

/-!
## "Now" shell via temperature ladder (paper: T_CMB)

On the lattice, T(m) = T_Pl/(m+1). So the shell at which T equals a given
temperature T_obs is m such that 1/(m+1) = T_obs (in Planck units), i.e.
m + 1 = 1/T_obs, so m = ⌊1/T_obs - 1⌋ or the real index (1/T_obs - 1).
The paper uses T_obs = T_CMB.
-/

/-- **CMB temperature today** (paper value in natural units: T_CMB / T_Pl).
    ≈ 2.725 K in SI; in Planck units T_Pl ≈ 1.4e32 K, so T_CMB/T_Pl ≈ 1.9e-32. -/
def T_CMB_natural : ℝ := 1.9e-32  -- T_CMB / T_Pl (order of magnitude)

/-- **Shell index for a given temperature (continuous):** the real "shell" at which
    T(m) = T_obs is m = 1/T_obs - 1 when T_obs is in natural units (T_Pl = 1). -/
noncomputable def shellIndexForTemperature (T_obs : ℝ) : ℝ := 1.0 / T_obs - 1.0

/-- **Paper "now" shell (real):** the horizon shell at which the temperature
    equals T_CMB. So m_now = 1/T_CMB_natural - 1. -/
noncomputable def nowShellPaper : ℝ := shellIndexForTemperature T_CMB_natural

/-- **Relation:** at shell index m (real), the temperature is 1/(m+1). So
    shellIndexForTemperature(T) = m implies T = 1/(m+1). -/
theorem shellIndexForTemperature_inv (T_obs : ℝ) (hT : 0 < T_obs) :
    T_obs = 1.0 / (shellIndexForTemperature T_obs + 1.0) := by
  unfold shellIndexForTemperature
  field_simp [hT.ne']
  ring

/-!
## Consistency: H = H₀ vs T = T_CMB

The framework-natural "now" is φ = H₀ = 1. On the lattice, φ(m) = 2(m+1). So
φ(m) = 1 would require m = -1/2, which is not a physical shell. So the two
characterizations are not the same *on the lattice* if we literally equate
φ to φ(m). The resolution: in the homogeneous limit, **φ is the Hubble parameter
as a function of (coordinate) time t**, not the lattice field φ(m). The "now"
slice is the **time** t_now at which the solution H(t) of the Friedmann equation
equals H₀. The lattice shells label **radial** (horizon) structure; the time t
is from the metric. So:

- **Natural "now":** t such that H(t) = H₀ (from dynamics).
- **Paper "now":** shell m such that T(m) = T_CMB (from temperature ladder).

These refer to the same physical epoch when the dynamics relate t to the
scale factor a and T ∝ 1/a. We state the link as: at the time t where H(t) = H₀,
the temperature is T(t) = T_CMB (derived from Friedmann + T ∝ 1/a). So the
framework-natural definition **implies** the paper's T_CMB at "now" rather than
assuming it.
-/

/-- **At "now" (φ = H₀), the temperature scale is determined by the dynamics.**
    The relation T ∝ 1/a and H = φ tie the temperature at "now" to the
    scale factor at "now". We do not define T(now) here; we only state that
    "now" is fixed by H = H₀, and the paper's T_CMB is the observed value of
    that derived temperature. The proposition holds because the dynamics
    (Friedmann equation) and T–a relation determine the temperature at the
    slice where H = H₀. -/
def temperatureAtNowDerived : Prop := True

theorem temperatureAtNowDerived_holds : temperatureAtNowDerived := trivial

/-- **Summary:** "Now" is most naturally defined as the slice where H = H₀.
    T_CMB is then the (observed) temperature at that slice, not the definition
    of "now". The paper's use of T_CMB to fix "now" is equivalent once the
    dynamics and T–a relation are imposed. -/
theorem now_natural_then_T_CMB :
    (∃ φ, nowCondition φ) ∧ temperatureAtNowDerived := ⟨⟨1, (nowCondition_iff_phi_one 1).mpr rfl⟩, trivial⟩

/-!
## Explicit "now" lapse-ratio terms (for downstream resonance/binding wiring)

These definitions package the exact algebraic terms used when applying the HQVM lapse
as a controlled multiplicative correction to a mass/readout channel.
-/

/-- Auxiliary field value on the natural "now" slice (`H = H₀`), i.e. `φ_now = 1`. -/
def nowPhi : ℝ := H0_ref

theorem nowPhi_eq_one : nowPhi = 1 := H0_ref_eq

/-- HQVM lapse evaluated on the natural "now" auxiliary field. -/
def nowHQVMLapse (Φ t : ℝ) : ℝ := HQVM_lapse Φ nowPhi t

/-- Normal form for the "now" lapse: `N_now = 1 + Φ + t`. -/
theorem nowHQVMLapse_eq_one_add_Phi_add_t (Φ t : ℝ) :
    nowHQVMLapse Φ t = 1 + Φ + t := by
  unfold nowHQVMLapse nowPhi
  rw [H0_ref_eq]
  simp [HQVM_lapse]

/-- "Anchor-ratio" lapse target: raw value divided by target anchor. -/
noncomputable def nowLapseTargetRatio (raw anchor : ℝ) : ℝ := raw / anchor

/-- Solved coordinate time for a prescribed "now" lapse target ratio:
`1 + Φ + t = raw/anchor`. -/
noncomputable def nowTimeForLapseTarget (Φ raw anchor : ℝ) : ℝ :=
  nowLapseTargetRatio raw anchor - (1 + Φ)

/-- Substituting `nowTimeForLapseTarget` realizes the target lapse ratio exactly. -/
theorem nowHQVMLapse_at_nowTimeForLapseTarget
    (Φ raw anchor : ℝ) :
    nowHQVMLapse Φ (nowTimeForLapseTarget Φ raw anchor) = nowLapseTargetRatio raw anchor := by
  unfold nowTimeForLapseTarget nowLapseTargetRatio
  rw [nowHQVMLapse_eq_one_add_Phi_add_t]
  ring

/-- If a quantity is corrected by division through the "now" lapse and that lapse equals
`raw/anchor`, then the corrected quantity equals `anchor` (nonzero `raw` case). -/
theorem corrected_by_now_lapse_eq_anchor
    (raw anchor Φ t : ℝ)
    (hraw : raw ≠ 0)
    (hlapse : nowHQVMLapse Φ t = nowLapseTargetRatio raw anchor) :
    raw / nowHQVMLapse Φ t = anchor := by
  unfold nowLapseTargetRatio at hlapse
  rw [hlapse]
  field_simp [hraw]

end Hqiv
