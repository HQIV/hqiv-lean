import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

open Classical

def HarmonicIndex (L : ℕ) : Type :=
  (ℓ : Fin (L + 1)) × Fin (2 * ℓ.val + 1)

#check (inferInstance : Fintype (HarmonicIndex 3))
