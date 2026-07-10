import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import HqivSpine.Physics.Binding
import HqivSpine.Physics.CurvatureKernel
import HqivSpine.Physics.NestedHopfBinding
import HqivSpine.Physics.NucleonLadder
import HqivSpine.Physics.PlaquetteCurvature
import HqivSpine.Physics.TuftBeltramiAnchor
import HqivSpine.Algebra.Closure
import HqivSpine.Algebra.So8

/-!
# `HqivSpine.Physics.SystemMatrixFunctors` — chemistry as functors on the carrier matrix

The chemistry-extent program wants dynamics as **functors on a matrix that already
carries ⟨bra|ket⟩ information**, not as free scalar second-order multipliers.

This module packages that architecture on the clean spine:

* **System carrier** — `OctonionState` / `NetworkWeight` (the 8×8 composite-trace network);
* **Functors** — endomaps: shell projection, Beltrami-contact dress, continuous SO(8)
  plane rotation, bond-closure update;
* **Stable coupling shells** — nested Hopf chart rows where contact sits strictly below
  the ladder (`NestedHopfBinding`);
* **Beltrami contact points** — contact-kernel evaluation at Beltrami chart data
  (`TuftBeltramiAnchor` + `CurvatureKernel`);
* **Off-lattice continuous symmetry** — a continuous plane rotation in `SO(8)` and a
  continuous contact coordinate (real winding), so the readout is not forced to sit
  only on integer shell indices.

No fitted coefficients, no PDG masses, no new axioms.  Foundation anchors remain
`α = 3/5`, carrier multiplicity `8`, and `referenceM = 4`.
-/

namespace HqivSpine.Physics.SystemMatrixFunctors

open Matrix
open HqivSpine.Physics
open HqivSpine.Physics.NestedHopfBinding
open HqivSpine.Physics.NucleonLadder
open HqivSpine.Physics.PlaquetteCurvature
open HqivSpine.Physics.TuftBeltramiAnchor
open HqivSpine.Algebra

/-! ## System matrix (⟨bra|ket⟩ carrier) -/

/-- The system matrix for chemistry: an 8-component carrier state together with its
so(8) network weight (composite-trace channels). -/
structure SystemMatrix where
  /-- Octonion / spinor amplitudes (ket data). -/
  state : OctonionState
  /-- Per-generator network weights (bra–ket diagonal channels). -/
  weight : NetworkWeight

/-- Build a system matrix from an explicit composite-trace diagonal and a state. -/
noncomputable def systemMatrixFromTrace
    (diag : So8TraceDiagonal) (ψ : OctonionState) : SystemMatrix where
  state := ψ
  weight := networkWeightFromCompositeTrace diag ψ

/-- Uniform carrier ket (equal amplitude on all eight channels). -/
noncomputable def uniformState : OctonionState := fun _ => 1

/-- Nucleon-trace system matrix (default chemistry / hadron network). -/
noncomputable def nucleonSystemMatrix : SystemMatrix where
  state := uniformState
  weight := NucleonLadder.nucleonWeight

/-! ## Functors as endomaps on `SystemMatrix` -/

/-- A chemistry functor is an endomap of the system matrix. -/
abbrev SystemFunctor := SystemMatrix → SystemMatrix

/-- Identity functor: no dress, no shell move. -/
def idFunctor : SystemFunctor := id

theorem idFunctor_eq (S : SystemMatrix) : idFunctor S = S := rfl

/-- Shell-projection functor: re-read the network weight through the binding coupling
at chart shell `m` (structural; weight unchanged, projection is the readout). -/
noncomputable def shellProjectReadout (m : ℕ) (S : SystemMatrix) (c : ℝ := 1) : ℝ :=
  E_bind_from_network m S.weight c

/-- Bond-closure functor: add an edge/hyperclosure weight channelwise. -/
noncomputable def bondClosureFunctor (edge : NetworkWeight) : SystemFunctor :=
  fun S => { S with weight := fun k => S.weight k + edge k }

theorem bondClosureFunctor_zero (S : SystemMatrix) :
    bondClosureFunctor (fun _ => 0) S = S := by
  cases S
  simp [bondClosureFunctor]

/-! ## Continuous SO(8) plane rotation (off the lattice) -/

/-- Continuous rotation in the `(i,j)`-plane by angle `θ`.
Algebraic SO(2)⊂SO(8) embedding:
`I + (cosθ−1)(Eᵢᵢ+Eⱼⱼ) + sinθ (Eⱼᵢ−Eᵢⱼ)`.
At `θ = 0` this is exactly `I`, so the continuous symmetry recovers the lattice
readout with no fitted coefficient. -/
noncomputable def planeRotation (i j : Fin 8) (θ : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 : Matrix (Fin 8) (Fin 8) ℝ) +
    (Real.cos θ - 1) • (Matrix.single i i (1 : ℝ) + Matrix.single j j 1) +
    Real.sin θ • (Matrix.single j i (1 : ℝ) - Matrix.single i j 1)

/-- At `θ = 0` the plane rotation is the identity matrix. -/
theorem planeRotation_zero (i j : Fin 8) :
    planeRotation i j 0 = 1 := by
  unfold planeRotation
  simp [Real.cos_zero, Real.sin_zero]

/-- Continuous SO(8) dress functor: rotate the carrier ket by a plane rotation.
The network weight is rebuilt from a supplied composite-trace diagonal so the
bra–ket channels follow the rotated state. -/
noncomputable def so8DressFunctor
    (diag : So8TraceDiagonal) (i j : Fin 8) (θ : ℝ) : SystemFunctor :=
  fun S =>
    let ψ' := planeRotation i j θ *ᵥ S.state
    systemMatrixFromTrace diag ψ'

/-- Zero-angle dress recovers the original ket. -/
theorem so8DressFunctor_zero
    (diag : So8TraceDiagonal) (i j : Fin 8) (S : SystemMatrix) :
    (so8DressFunctor diag i j 0 S).state = S.state := by
  unfold so8DressFunctor systemMatrixFromTrace
  simp [planeRotation_zero]

/-! ## Continuous contact coordinate (off integer shells) -/

/-- Continuous shell shape `φ(ξ) = 2(ξ+1)` — the lattice `phi m = 2(m+1)` extended
off integer shells. -/
noncomputable def phiCont (ξ : ℝ) : ℝ := 2 * (ξ + 1)

/-- Continuous contact chart coordinate at real winding `ξ`. -/
noncomputable def contactArgCont (ξ : ℝ) : ℝ :=
  1 + (phiCont ξ / 6) * alphaEM

/-- Continuous ladder chart coordinate at real shell `ξ`. -/
noncomputable def ladderArgCont (ξ : ℝ) : ℝ := phiCont ξ + 1

theorem contactArgCont_of_nat (w : ℕ) :
    contactArgCont (w : ℝ) = contactArg w := by
  unfold contactArgCont contactArg phiCont phi
  push_cast
  ring

theorem ladderArgCont_of_nat (m : ℕ) :
    ladderArgCont (m : ℝ) = ladderArg m := by
  unfold ladderArgCont ladderArg phiCont phi
  push_cast
  ring

/-- Continuous curvature log kernel at a real contact coordinate. -/
noncomputable def contactKernelCont (ξ c : ℝ) : ℝ :=
  curvatureLogKernel (contactArgCont ξ) c

/-- Continuous Hopf fiber–base shape `ξ/(ξ+2)` (off integer windings). -/
noncomputable def hopfFibrationShapeCont (ξ : ℝ) : ℝ :=
  ξ / (ξ + 2)

theorem hopfFibrationShapeCont_of_nat (n : ℕ) :
    hopfFibrationShapeCont (n : ℝ) = hopfFibrationShape n := by
  unfold hopfFibrationShapeCont hopfFibrationShape
  rfl

/-! ## Stable coupling shells -/

/-- A stable coupling shell is an integrable nested Hopf row (weak / strong / heavy). -/
abbrev StableCouplingShell := IntegrableHopfShell

/-- The three stable coupling shells on the nested Hopf ladder. -/
def stableCouplingShells : List StableCouplingShell :=
  [weakShell, strongShell, heavyShell]

/-- Lock-in (heavy) shell is the proton-anchor stable coupling shell. -/
def lockinCouplingShell : StableCouplingShell := heavyShell

theorem lockinCouplingShell_chart :
    chartShell lockinCouplingShell = referenceM :=
  chartShell_heavy

/-- On every stable coupling shell, contact amplification sits strictly below the
ladder (proved nested-Hopf ordering). -/
theorem stableCouplingShell_contact_lt_ladder
    (s : StableCouplingShell) (c : ℝ) (hc : 0 < c) :
    contactKernel s c < ladderKernel s c :=
  integrableContactKernel_lt_ladder s c hc

/-! ## Beltrami contact points -/

/-- A Beltrami contact point: Beltrami spectral label together with the contact
kernel at the corresponding Hopf winding. -/
structure BeltramiContactPoint where
  /-- Hopf winding (integrable `1/2/3` or continuous extension). -/
  winding : ℕ
  /-- Minimal Beltrami eigenvalue `λ_min = winding + 1`. -/
  beltramiEigenvalue : ℝ
  /-- Contact kernel at that winding. -/
  contactAmp : ℝ

/-- Build the Beltrami contact point on an integrable Hopf shell. -/
noncomputable def beltramiContactAtShell (s : IntegrableHopfShell) (c : ℝ := 1) :
    BeltramiContactPoint where
  winding := s.winding
  beltramiEigenvalue := tuftMinimalBeltramiEigenvalue s.winding
  contactAmp := contactKernel s c

theorem beltramiContactAtShell_eigenvalue (s : IntegrableHopfShell) (c : ℝ) :
    (beltramiContactAtShell s c).beltramiEigenvalue =
      (s.winding + 1 : ℝ) := by
  unfold beltramiContactAtShell tuftMinimalBeltramiEigenvalue tuftFiberMultiplicity
  push_cast
  rfl

/-- Continuous Beltrami contact: real winding `ξ`, Beltrami label `ξ+1`, continuous
contact kernel.  This is the off-lattice contact point. -/
noncomputable def beltramiContactCont (ξ c : ℝ) : BeltramiContactPoint where
  winding := 0  -- sentinel: continuous point is carried by ξ in the kernel
  beltramiEigenvalue := ξ + 1
  contactAmp := contactKernelCont ξ c

/-! ## Off-lattice dress (continuous symmetry readout) -/

/-- Off-lattice continuous-symmetry dress:
`hopfShape(ξ) · K_contact(ξ) / K_ladder(m_chart)`.

At integer lock-in with `ξ = 3` and chart `m = 4` this recovers a pure Hopf-localized
contact/ladder ratio — no fitted coefficient.  For non-integer `ξ` the same formula
moves continuously off the discrete shell lattice inside the carrier geometry. -/
noncomputable def offLatticeDress (ξ : ℝ) (mChart : ℕ) (c : ℝ := 1) : ℝ :=
  hopfFibrationShapeCont ξ *
    contactKernelCont ξ c / curvatureLogKernel (ladderArg mChart) c

/-- At zero running coefficient both kernels are `1`, so the dress collapses to the
continuous Hopf shape alone. -/
theorem offLatticeDress_zero_running (ξ : ℝ) (mChart : ℕ) :
    offLatticeDress ξ mChart 0 = hopfFibrationShapeCont ξ := by
  unfold offLatticeDress contactKernelCont
  simp [curvatureLogKernel_zero]

/-- Identity composition: applying no SO(8) dress and reading the shell projection
is exactly `E_bind_from_network`. -/
theorem shellProject_eq_bind (m : ℕ) (S : SystemMatrix) (c : ℝ) :
    shellProjectReadout m S c = E_bind_from_network m S.weight c := rfl

/-- Second-order as functor composition: bond closure then shell projection.
The zero-edge case recovers the bare network readout. -/
theorem composedFunctor_trivial_edge (m : ℕ) (S : SystemMatrix) (c : ℝ) :
    shellProjectReadout m (bondClosureFunctor (fun _ => 0) S) c =
      shellProjectReadout m S c := by
  rw [bondClosureFunctor_zero]

/-- Combined continuous-symmetry readout on a system matrix:
shell projection at the chart, multiplied by the off-lattice dress at continuous
winding `ξ`.  When `ξ` is the integer Hopf winding of a stable shell and `c = 0`,
this is Hopf-shape × bare binding. -/
noncomputable def continuousSymmetryReadout
    (S : SystemMatrix) (ξ : ℝ) (mChart : ℕ) (c : ℝ := 1) : ℝ :=
  offLatticeDress ξ mChart c * shellProjectReadout mChart S c

theorem continuousSymmetryReadout_zero_running
    (S : SystemMatrix) (ξ : ℝ) (mChart : ℕ) :
    continuousSymmetryReadout S ξ mChart 0 =
      hopfFibrationShapeCont ξ * E_bind_from_network mChart S.weight 0 := by
  unfold continuousSymmetryReadout
  rw [offLatticeDress_zero_running, shellProject_eq_bind]

/-- When the shell coupling is generator-independent (the current
`bindingCouplingAtShell`), any redistribution of network weight that preserves
the total `∑ w` leaves the binding energy unchanged.  Continuous SO(8) rotations
of the carrier that only reshuffle `w_k` among generators are therefore a no-op
on `E_bind_from_network` until the coupling cell itself becomes
generator-dependent (colour-filtered / plane-local emission). -/
theorem shellProject_eq_of_weight_sum
    (m : ℕ) (S S' : SystemMatrix) (c : ℝ)
    (h : ∑ k : So8Index, S.weight k = ∑ k : So8Index, S'.weight k) :
    shellProjectReadout m S c = shellProjectReadout m S' c := by
  unfold shellProjectReadout E_bind_from_network bindingCouplingAtShell
  have hcoup :
      (∑ k : So8Index, S.weight k * ((latticeSimplexCount m : ℝ) * alphaEffAtShell m c)) =
        (∑ k : So8Index, S.weight k) * ((latticeSimplexCount m : ℝ) * alphaEffAtShell m c) := by
    rw [← Finset.sum_mul]
  have hcoup' :
      (∑ k : So8Index, S'.weight k * ((latticeSimplexCount m : ℝ) * alphaEffAtShell m c)) =
        (∑ k : So8Index, S'.weight k) * ((latticeSimplexCount m : ℝ) * alphaEffAtShell m c) := by
    rw [← Finset.sum_mul]
  rw [hcoup, hcoup', h]

/-- Lock-in-relative off-lattice dress: absolute dress divided by the dress at the
integer Hopf lock-in winding `n = 3` and chart `m = referenceM`.  Equals `1` exactly
at lock-in, so continuous motion off the lattice is measured relative to the proved
integer shell rather than as an absolute Hopf-shape suppression. -/
noncomputable def offLatticeDressRelative (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  offLatticeDress ξ referenceM c / offLatticeDress 3 referenceM c

theorem offLatticeDressRelative_lockin (c : ℝ)
    (h : offLatticeDress 3 referenceM c ≠ 0) :
    offLatticeDressRelative 3 c = 1 :=
  div_self h

/-- Combined continuous-symmetry readout using the lock-in-relative dress. -/
noncomputable def continuousSymmetryReadoutRelative
    (S : SystemMatrix) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  offLatticeDressRelative ξ c * shellProjectReadout referenceM S c

theorem continuousSymmetryReadoutRelative_lockin
    (S : SystemMatrix) (c : ℝ) (h : offLatticeDress 3 referenceM c ≠ 0) :
    continuousSymmetryReadoutRelative S 3 c =
      shellProjectReadout referenceM S c := by
  unfold continuousSymmetryReadoutRelative
  rw [offLatticeDressRelative_lockin c h, one_mul]

end HqivSpine.Physics.SystemMatrixFunctors
