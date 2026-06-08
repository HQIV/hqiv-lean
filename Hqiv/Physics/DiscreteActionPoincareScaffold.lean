import Hqiv.Physics.Action
import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.NonAbelianHolonomyMeasureScaffold
import Hqiv.Physics.DiscreteActionStrongPoincareBridge
import Hqiv.Geometry.RapidityLorentzClosure
import Hqiv.Geometry.SpatialRotationLorentzClosure
import Hqiv.Topology.ParallelPoincareReferenceModel
import RhFourierLift.Setup

/-!
# Discrete O–Maxwell action ↔ Poincaré invariance (honest scope)

See `DiscreteActionStrongPoincareBridge` for the latest partial discharge layer.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry
open Hqiv.Topology
open RhFourierLift

noncomputable section

structure DiscreteActionLorentzChartDischarged : Prop where
  rapidity : Nonempty RapidityLorentzClosure
  spatial : Nonempty SpatialRotationLorentzClosure
  full : Nonempty FullLorentzClosure

theorem discreteActionLorentzChartDischarged_holds : DiscreteActionLorentzChartDischarged where
  rapidity := rapidity_lorentz_closure_discharged
  spatial := spatial_rotation_lorentz_closure_discharged
  full := full_lorentz_closure_discharged

structure DiscreteActionAbelianHolonomyDischarged : Prop where
  cyclic_flat :
    ∀ (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8),
      discreteSquareHolonomy (fun i => linearEnd (F_from_A A a i (i + 1))) = 1

theorem discreteActionAbelianHolonomyDischarged_holds : DiscreteActionAbelianHolonomyDischarged where
  cyclic_flat := discreteSquareHolonomy_F_cyclic_eq_one

structure DiscreteParallelPoincareTemplateDischarged : Prop where
  reference_witness :
    ∀ (n : ℕ) (_href : 0 < K n (1 : ℝ)),
      ∃ H : DiscreteParallelPoincareHypothesis,
        (∃ k M', H.evo.iterate k H.data.M = some M' ∧ IsS3NullVertexTemplate M' H.data.maxShell)

theorem discreteParallelPoincareTemplateDischarged_holds :
    DiscreteParallelPoincareTemplateDischarged where
  reference_witness := fun n _href => by
    let H := referenceParallelPoincareHypothesis n _href
    exact ⟨H, discrete_parallel_poincare H⟩

structure DiscreteActionStrongPoincarePartialDischarged : Prop where
  holonomy : NonAbelianHolonomyMeasureProgram
  abelian_holonomy : DiscreteActionAbelianHolonomyDischarged
  flat_hqvm : DiscreteActionFlatHQVMPoincareDischarged

theorem discreteActionStrongPoincarePartialDischarged_holds :
    DiscreteActionStrongPoincarePartialDischarged where
  holonomy := nonAbelianHolonomyMeasureProgram_default
  abelian_holonomy := discreteActionAbelianHolonomyDischarged_holds
  flat_hqvm := discreteActionFlatHQVMPoincare_discharged

structure DiscreteActionStrongPoincarePending : Prop where
  partial_discharge : DiscreteActionStrongPoincarePartialDischarged
  flat01_kinetic_boost : ¬ Flat01HQVMKineticBoostDischarged
  general_kinetic_boost : ¬ GeneralFlatHQVMKineticBoostDischarged
  measure_matches_holonomy : ¬ MeasureHolonomyAlignmentDischarged

def discreteActionStrongPoincarePending_default : DiscreteActionStrongPoincarePending where
  partial_discharge := discreteActionStrongPoincarePartialDischarged_holds
  flat01_kinetic_boost := flat01HQVMKineticBoost_not_discharged
  general_kinetic_boost := generalFlatHQVMKineticBoost_not_discharged
  measure_matches_holonomy := measureHolonomyAlignment_not_discharged

structure DiscreteActionPoincareProgram where
  lorentz_chart : DiscreteActionLorentzChartDischarged
  abelian_holonomy : DiscreteActionAbelianHolonomyDischarged
  parallel_template : DiscreteParallelPoincareTemplateDischarged
  strong_partial : DiscreteActionStrongPoincarePartialDischarged
  strong_discharged : FullActionStrongPoincareDischarged
  strong_pending : DiscreteActionStrongPoincarePending
  measure_partial : MeasureHolonomyPartialAlignmentDischarged

theorem discreteActionPoincareProgram_default : DiscreteActionPoincareProgram where
  lorentz_chart := discreteActionLorentzChartDischarged_holds
  abelian_holonomy := discreteActionAbelianHolonomyDischarged_holds
  parallel_template := discreteParallelPoincareTemplateDischarged_holds
  strong_partial := discreteActionStrongPoincarePartialDischarged_holds
  strong_discharged := fullActionStrongPoincare_discharged
  strong_pending := discreteActionStrongPoincarePending_default
  measure_partial := measureHolonomyPartialAlignment_discharged

end

end Hqiv.Physics
