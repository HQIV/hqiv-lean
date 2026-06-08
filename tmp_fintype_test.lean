import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Fin

#check (inferInstance : Fintype ((ℓ : Fin 3) × Fin (2 * ℓ.val + 1)))
