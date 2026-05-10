import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

def HarmonicIndex (L : ℕ) : Type :=
  Σ ℓ : Fin (L + 1), Fin (2 * ℓ.val + 1)

#check (inferInstance : Fintype (HarmonicIndex 3))
