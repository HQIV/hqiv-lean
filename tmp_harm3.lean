import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Fin

def HarmonicIndex (L : ℕ) := Σ ℓ : Fin (L + 1), Fin (2 * ℓ.val + 1)

instance (L : ℕ) : Fintype (HarmonicIndex L) :=
  Sigma.instFintype

#check (inferInstance : Fintype (HarmonicIndex 3))
