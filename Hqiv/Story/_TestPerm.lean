import Mathlib.Analysis.Normed.Lp.PiLp
import Hqiv.Story.MillenniumBridgePatchVacuum
open Hqiv.Story
open EuclideanSpace
variable (σ : Equiv.Perm (Fin 4))
#check (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ : PatchHilbert →ₗᵢ[ℂ] PatchHilbert)
#check (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toLinearEquiv
#check LinearEquiv.restrictScalars ℝ (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ : PatchHilbert ≃ₗ[ℂ] PatchHilbert).toLinearEquiv
