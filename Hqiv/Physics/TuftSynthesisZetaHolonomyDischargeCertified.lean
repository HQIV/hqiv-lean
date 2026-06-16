import Hqiv.Physics.TuftSynthesisZetaHolonomyDischarge
import Hqiv.SO8Closure

/-!
# TUFT synthesis discharge — certified SO(8) closure variant

`TuftSynthesisZetaHolonomyDischarge` uses the lightweight `SO8ClosureSymbolic` interface so
`HQIVPhysics` / `HQIVMeaningfulPhysics` never pull the `LieBracketCell` matrix certificate.

This module is listed only under `HQIVSO8Closure`. It re-proves the holonomy discharge witness
using the **certified** `so8_closure_theorem` from `Hqiv.SO8Closure` (full `GeneratorsLieClosure`
+ `LieBracketCell` build).
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Topology

theorem lightconeSO8HolonomyDischarged_certified_holds :
    LightconeSO8HolonomyDischarged where
  so8_closure := so8_closure_theorem
  delta_antisymmetric_in_so8 := delta_antisymmetric
  delta_u1_plane := preferred_delta_u1_plane
  triality_three_eight_dim_slots := so8_triality_three_slots_default
  shell_torsion_skew := fun s h => HopfShell.torsionMatrix_skew s h
  hopf_shell_so8_admissible := fun s h =>
    HopfShell.t11_torsion_supplies_delta_in_so8_admissible_holonomy s h

theorem patchHolonomyUpgradeDischarged_certified_holds :
    PatchHolonomyUpgradeDischarged where
  lightcone_so8 := lightconeSO8HolonomyDischarged_certified_holds
  admissible_generation_cycle := the_three_generation_fano_vertices_form_admissible_cycle
  abelian_cyclic_plaquette_flat := discreteSquareHolonomy_F_cyclic_eq_one
  readout_seed_cycle_flat := fun ω θ a =>
    seedPotentialMinimalCycle_discrete_holonomy_one ω θ a
  nonabelian_su2_chart := weakHiggsNonAbelianLieCertified_holds
  su2_matrix_transport_nonabelian := weakPauliPlus_mul_ne_comm_weakPauliMinus
  t10_heavy_to_middle := assembleT10MixingPhaseMatrix_heavyToMiddle_eq
  t10_middle_to_light := assembleT10MixingPhaseMatrix_middleToLight_eq

theorem tuftSynthesisZetaHolonomyDischarged_certified_holds :
    TuftSynthesisZetaHolonomyDischarged where
  subleading_zeta := patchSubleadingZetaDischarged_holds
  holonomy_upgrade := patchHolonomyUpgradeDischarged_certified_holds

end Hqiv.Physics
