import Hqiv.Geometry.BondedHorizonCasimir

/-!
# Molecule benchmark wrappers for bonded-horizon surplus

This file provides lightweight Lean aliases tying common small-molecule
electron-count splits to `bondHorizonSurplus_*` from
`Hqiv.Geometry.BondedHorizonCasimir`.

The formulas are definitional; numerical comparison to experiment is handled
in the Python benchmark script.
-/

namespace Hqiv.Geometry

/-- H2 dissociation toy split: joint `(2)` vs fragments `(1,1)`. -/
noncomputable def h2DissociationSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplus_eV 2 1 1 cfg

/-- LiH dissociation toy split: joint `(4)` vs fragments `(3,1)`. -/
noncomputable def lihDissociationSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplus_eV 4 3 1 cfg

/-- HF dissociation toy split: joint `(10)` vs fragments `(9,1)`. -/
noncomputable def hfDissociationSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplus_eV 10 9 1 cfg

/-- H2O atomization toy split: joint `(10)` vs fragments `(8,2)`. -/
noncomputable def h2oAtomizationSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplus_eV 10 8 2 cfg

/-- CH4 atomization toy split: joint `(10)` vs fragments `(6,4)`. -/
noncomputable def ch4AtomizationSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplus_eV 10 6 4 cfg

@[simp] theorem h2DissociationSurplus_eV_eq (cfg : NuclearTorusConfig) :
    h2DissociationSurplus_eV cfg = bondHorizonSurplus_eV 2 1 1 cfg := rfl

@[simp] theorem lihDissociationSurplus_eV_eq (cfg : NuclearTorusConfig) :
    lihDissociationSurplus_eV cfg = bondHorizonSurplus_eV 4 3 1 cfg := rfl

@[simp] theorem hfDissociationSurplus_eV_eq (cfg : NuclearTorusConfig) :
    hfDissociationSurplus_eV cfg = bondHorizonSurplus_eV 10 9 1 cfg := rfl

@[simp] theorem h2oAtomizationSurplus_eV_eq (cfg : NuclearTorusConfig) :
    h2oAtomizationSurplus_eV cfg = bondHorizonSurplus_eV 10 8 2 cfg := rfl

@[simp] theorem ch4AtomizationSurplus_eV_eq (cfg : NuclearTorusConfig) :
    ch4AtomizationSurplus_eV cfg = bondHorizonSurplus_eV 10 6 4 cfg := rfl

end Hqiv.Geometry
