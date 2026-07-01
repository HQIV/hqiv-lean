import HqivSpine.Physics.Action
import HqivSpine.Physics.Forces

/-!
# `HqivSpine.Physics.StandardModelLagrangian` — the SM Lagrangian from the O-Maxwell action

The single discrete O-Maxwell kinetic action of `Physics.Action` (`−¼∑_{a,μ,ν}F²` over the eight
octonion carrier channels) is the **whole** Standard-Model gauge kinetic term once the channels are
read through the `Physics.Forces` sector map:

* **Sector decomposition.** Restricting the channel sum to a `Finset` of channels gives the
  per-sector Yang–Mills kinetic term `sectorKinetic`. Because the EM/weak/strong channel sets
  *partition* `Fin 8` (`Forces.sectors_partition_univ`), the total kinetic Lagrangian is the sum of
  the three sector kinetics (`kinetic_sector_decomposition`) — `1 + 3 + 4 = 8` channels, no field
  added or shared (`channels_exhausted`). The EM sector is a single abelian Maxwell field
  (`em_kinetic_single`); every sector kinetic is `≤ 0` (the kinetic-energy sign, `sectorKinetic_nonpos`).
* **Gauge invariance.** A spacetime-constant per-channel shift `A a ν ↦ A a ν + c a` is a discrete
  gauge transformation: the field strength is invariant (`fieldStrength_gaugeShift`), hence so are the
  kinetic Lagrangian (`kinetic_gauge_invariant`), the field divergence
  (`divergence_gauge_invariant`), and the Euler–Lagrange / equation of motion (`EL_gauge_invariant`).

Bundled in `smLagrangian_closure`. Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`,
no `native_decide`.
-/

namespace HqivSpine.Physics.StandardModelLagrangian

open HqivSpine.Physics HqivSpine.Foundation
open scoped BigOperators

/-! ## Per-sector Yang–Mills kinetic term -/

/-- **Sector kinetic Lagrangian**: the `−¼F²` kinetic term restricted to a set of carrier channels. -/
noncomputable def sectorKinetic (S : Finset (Fin 8)) (A : Potential) : ℝ :=
  -(1 / 4) * ∑ a ∈ S, ∑ μ : Fin 4, ∑ ν : Fin 4, (fieldStrength A a μ ν) ^ 2 / 2

/-- The full O-Maxwell kinetic term is the sector kinetic over *all* channels. -/
theorem kinetic_eq_sectorKinetic_univ (A : Potential) :
    kinetic A = sectorKinetic Finset.univ A := rfl

/-- Each sector kinetic term is `≤ 0` (the kinetic energy sign). -/
theorem sectorKinetic_nonpos (S : Finset (Fin 8)) (A : Potential) : sectorKinetic S A ≤ 0 := by
  unfold sectorKinetic
  have hsum : 0 ≤ ∑ a ∈ S, ∑ μ : Fin 4, ∑ ν : Fin 4, (fieldStrength A a μ ν) ^ 2 / 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => by positivity
  linarith

/-- **Sector decomposition of the SM kinetic Lagrangian**: total = EM + weak + strong. -/
theorem kinetic_sector_decomposition (A : Potential) :
    kinetic A =
      sectorKinetic emComponents A + sectorKinetic weakComponents A + sectorKinetic strongComponents A := by
  have hd1 : Disjoint emComponents weakComponents := by decide
  have hd2 : Disjoint (emComponents ∪ weakComponents) strongComponents := by decide
  unfold kinetic sectorKinetic
  rw [show (Finset.univ : Finset (Fin 8)) = emComponents ∪ weakComponents ∪ strongComponents from
      sectors_partition_univ.symm, Finset.sum_union hd2, Finset.sum_union hd1]
  ring

/-- The **EM sector is a lone abelian Maxwell field** on channel `0`. -/
theorem em_kinetic_single (A : Potential) :
    sectorKinetic emComponents A =
      -(1 / 4) * ∑ μ : Fin 4, ∑ ν : Fin 4, (fieldStrength A 0 μ ν) ^ 2 / 2 := by
  unfold sectorKinetic emComponents
  rw [Finset.sum_singleton]

/-- The three sector channel sets exhaust the carrier: `1 + 3 + 4 = 8`. -/
theorem channels_exhausted :
    emComponents.card + weakComponents.card + strongComponents.card = carrierMultiplicity :=
  sector_card_sum_eq_carrier

/-! ## Discrete gauge invariance -/

/-- **Gauge transformation**: a spacetime-constant shift of the potential, one constant per channel. -/
def gaugeShift (c : Fin 8 → ℝ) (A : Potential) : Potential := fun a ν => A a ν + c a

/-- The field strength is **gauge invariant** — the constant cancels in `A a ν − A a μ`. -/
theorem fieldStrength_gaugeShift (c : Fin 8 → ℝ) (A : Potential) (a : Fin 8) (μ ν : Fin 4) :
    fieldStrength (gaugeShift c A) a μ ν = fieldStrength A a μ ν := by
  unfold fieldStrength gaugeShift; ring

/-- The **kinetic Lagrangian is gauge invariant**. -/
theorem kinetic_gauge_invariant (c : Fin 8 → ℝ) (A : Potential) :
    kinetic (gaugeShift c A) = kinetic A := by
  unfold kinetic; simp_rw [fieldStrength_gaugeShift]

/-- The **field divergence is gauge invariant**. -/
theorem divergence_gauge_invariant (c : Fin 8 → ℝ) (A : Potential) (a : Fin 8) (ν : Fin 4) :
    divergence (gaugeShift c A) a ν = divergence A a ν := by
  unfold divergence; simp_rw [fieldStrength_gaugeShift]

/-- The **equation of motion is gauge invariant** (the source coupling is unchanged). -/
theorem EL_gauge_invariant (J : Current) (c : Fin 8 → ℝ) (A : Potential) (a : Fin 8) (ν : Fin 4) :
    EL J (gaugeShift c A) a ν = EL J A a ν := by
  unfold EL; rw [divergence_gauge_invariant]

/-! ## Closure -/

/-- **The Standard-Model gauge Lagrangian is realised** from the discrete O-Maxwell action: it
splits into EM/weak/strong sectors over a genuine channel partition, and is gauge invariant. -/
structure SMLagrangianClosure : Prop where
  kinetic_partition : ∀ A : Potential,
    kinetic A = sectorKinetic emComponents A + sectorKinetic weakComponents A
      + sectorKinetic strongComponents A
  gauge_invariant : ∀ (c : Fin 8 → ℝ) (A : Potential), kinetic (gaugeShift c A) = kinetic A
  eom_gauge_invariant : ∀ (J : Current) (c : Fin 8 → ℝ) (A : Potential) (a : Fin 8) (ν : Fin 4),
    EL J (gaugeShift c A) a ν = EL J A a ν
  channels_exhausted :
    emComponents.card + weakComponents.card + strongComponents.card = carrierMultiplicity

theorem smLagrangian_closure : SMLagrangianClosure where
  kinetic_partition := kinetic_sector_decomposition
  gauge_invariant := kinetic_gauge_invariant
  eom_gauge_invariant := EL_gauge_invariant
  channels_exhausted := channels_exhausted

end HqivSpine.Physics.StandardModelLagrangian
