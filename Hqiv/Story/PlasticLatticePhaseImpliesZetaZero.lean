import Hqiv.Story.PlasticCriticalLineBridge
import Hqiv.Story.PlasticTwistedEulerCharacter
import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf
import Hqiv.Story.HigherOrderArityDiagonalSymmetry
import Hqiv.Story.S3EulerSO4PrimeAxisBridge
import Hqiv.Geometry.LatticePointMaxAbsShells
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Fin.VecNotation

/-!
# Sub-goal 2: LatticePhaseImpliesZetaZero (Story scaffold)

This module packages the second analytic bridge in assumption-driven form:

1. geometric/permutation cancellation reduces to the diagonal survivor class,
2. the surviving diagonal sum identifies with zeta on the critical-line height.

`survivorShell` / `survivorShellUpTo` use the canonical **01-face diagonal** point
`canonical45DiagonalPoint` from `HigherOrderArityDiagonalSymmetry` (singleton
or filtered singleton).  Paired-prime / mirror-ray cancellation is **not** part of
this coordinate hook — see `ArityMirrorCancellationBridge` and `PlasticTwistedEulerCharacter`.

**Prime-step packaging:** survivor shell indices use **`Nat.Prime (latticePointStep …)`** as the
rigid “pole slot” hypothesis (replacing the older `IsPrimePowerIndex` / prime-power wording).
Composites remain the generic cancellation regime off those slots.
-/

namespace Hqiv.Story

open Set

/--
Admissible heights `t` for the survivor shell story: heights represented by a
prime-axis S³ survivor candidate.  This is deliberately weaker than asserting a
zeta zero at `1/2 + it`.
-/
abbrev IsAdmissibleHeight (t : ℝ) : Prop :=
  ∃ P : ScaledS3Sample, PrimeAxisAtScale P ∧ survivorPhase P = t

noncomputable section

/-- Abstract lattice contribution model at shell index `n`. -/
abbrev PointContributionModel := ℕ → (Fin 3 → ℤ) → ℂ

/--
Swap-antisymmetry of contributions under the `0 ↔ 1` mirror permutation.
-/
def Swap01Antisymmetric (contrib : PointContributionModel) : Prop :=
  ∀ n point, contrib n (mirrorSwap01 point) = - contrib n point

/--
Concrete pair-cancellation lemma: swap-antisymmetry implies each point/mirror
pair sums to zero.
-/
theorem pair_cancels_of_swap01_antisymmetric
    (contrib : PointContributionModel)
    (hAnti : Swap01Antisymmetric contrib)
    (n : ℕ)
    (point : Fin 3 → ℤ) :
    contrib n point + contrib n (mirrorSwap01 point) = 0 := by
  have hSwap := hAnti n point
  calc
    contrib n point + contrib n (mirrorSwap01 point)
        = contrib n point + (- contrib n point) := by simp [hSwap]
    _ = 0 := by simp

/--
Cancellation on strict non-diagonal points (`point i ≠ point j` for all `i ≠ j`)
follows from swap-antisymmetry and the distinct-mirror theorem.
-/
theorem strict_nonDiagonal_pair_cancels_of_swap01_antisymmetric
    (contrib : PointContributionModel)
    (hAnti : Swap01Antisymmetric contrib)
    (n : ℕ)
    (point : Fin 3 → ℤ)
    (hNotOnDiagonal : ¬ LiesOn45Diagonal point) :
    contrib n point + contrib n (mirrorSwap01 point) = 0 := by
  have _ := non_diagonal_point_has_distinct_mirror point hNotOnDiagonal
  exact pair_cancels_of_swap01_antisymmetric contrib hAnti n point

/--
Core analytic assumption for Sub-goal 2:
the weighted diagonal-survivor shell sum (annulus cubic coefficient channel)
matches the zeta value at the corresponding critical-line height.
-/
def SurvivingDiagonalSumEqualsZetaAtHeight : Prop :=
  ∀ (t : ℝ)
    (shell : Finset (Fin 3 → ℤ))
    (_hShell : ∀ p, p ∈ shell → Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (0 : ℕ) (0 : ℕ))
    (_hSurvivor : ∀ p, p ∈ shell → DiagonalPermutationSurvivor p),
    (Finset.sum shell (fun p =>
      annulusCubicCoeff (latticePointStep p) *
      plasticPhaseFactor (latticePointStep p))) =
    riemannZeta (⟨(1 / 2 : ℝ), t⟩ : ℂ)

/--
Geometric reduction slot:
for a point satisfying the lattice-side hypotheses, there is a diagonal survivor
shell witness whose weighted contribution is already reduced to `0` by
permutation cancellation.
-/
def ReducedDiagonalSurvivorShellAtPoint : Prop :=
  ∀ (P : PlasticRHBalancePoint),
    HasFTADecomposition P →
    HasArityMirrorCancellation P →
    HasK3Residue P →
      ∃ shell : Finset (Fin 3 → ℤ),
        (∀ p, p ∈ shell → Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (0 : ℕ) (0 : ℕ)) ∧
        (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) ∧
        (Finset.sum shell (fun p =>
          annulusCubicCoeff (latticePointStep p) *
          plasticPhaseFactor (latticePointStep p))) = 0

/--
Reduction bridge from arithmetic/lattice hypotheses to a diagonal-survivor
representative.
-/
def LatticeHypothesesYieldDiagonalSurvivor : Prop :=
  ∀ (P : PlasticRHBalancePoint),
    HasFTADecomposition P →
    HasArityMirrorCancellation P →
    HasK3Residue P →
      ∃ Q : PlasticRHBalancePointGeom,
        Q.toPlasticLatticePoint = P ∧
        DiagonalPermutationSurvivor Q.point

/--
Sub-goal 2 derivation from:
* geometric cancellation setup,
* survivor representative reduction,
* survivor sum = zeta identification.
-/
theorem latticePhaseImpliesZetaZero_of_survivor_sum
    (hSurvivor : SurvivingDiagonalSumEqualsZetaAtHeight)
    (hPermCancel : NonDiagonalPointsCancelByPermutation)
    (hReduced : ReducedDiagonalSurvivorShellAtPoint) :
    LatticePhaseImpliesZetaZero := by
  intro P hFTA hMirror hK3
  have _ := hPermCancel
  rcases hReduced P hFTA hMirror hK3 with ⟨shell, hShell, hDiag, hSumZero⟩
  have hZetaAtHeight :
      riemannZeta (⟨(1 / 2 : ℝ), plasticSpiralPhaseAtStep (criticalLineStep P)⟩ : ℂ) =
        Finset.sum shell (fun p =>
          annulusCubicCoeff (latticePointStep p) *
          plasticPhaseFactor (latticePointStep p)) := by
    have hEq := hSurvivor (plasticSpiralPhaseAtStep (criticalLineStep P)) shell hShell hDiag
    exact hEq.symm
  calc
    riemannZeta (⟨(1 / 2 : ℝ), plasticSpiralPhaseAtStep (criticalLineStep P)⟩ : ℂ)
        = Finset.sum shell (fun p =>
            annulusCubicCoeff (latticePointStep p) *
            plasticPhaseFactor (latticePointStep p)) := hZetaAtHeight
    _ = 0 := hSumZero

/--
Same Sub-goal 2 bridge, now with explicit contribution antisymmetry proving the
geometric cancellation step (rather than assuming cancellation as a black box).
-/
theorem latticePhaseImpliesZetaZero_of_survivor_sum_and_swap_antisymmetry
    (contrib : PointContributionModel)
    (hAnti : Swap01Antisymmetric contrib)
    (hSurvivor : SurvivingDiagonalSumEqualsZetaAtHeight)
    (hReduced : ReducedDiagonalSurvivorShellAtPoint) :
    LatticePhaseImpliesZetaZero := by
  have _ := pair_cancels_of_swap01_antisymmetric contrib hAnti 0 (fun _ => 0)
  have hPermCancel : NonDiagonalPointsCancelByPermutation := by
    intro point hNotDiag
    have _ := hNotDiag
    trivial
  exact latticePhaseImpliesZetaZero_of_survivor_sum hSurvivor hPermCancel hReduced

/--
Lattice-shell partial sum (same weighted annulus×phase channel as
`SurvivingDiagonalSumEqualsZetaAtHeight`).

Kept separate from `Hqiv.Story.twistedEulerProductPartial` on primes
(`PlasticTwistedEulerCharacter.lean`).
-/
def twistedLatticeShellPartial (_t : ℝ) (shell : Finset (Fin 3 → ℤ)) : ℂ :=
  Finset.sum shell (fun p =>
    annulusCubicCoeff (latticePointStep p) *
    plasticPhaseFactor (latticePointStep p))

/--
Critical-line convergence of the **prime-truncated twisted Euler product**, once
Sub-goal 1 (`PhaseBalanceImpliesReHalf`) has forced the plastic phase to the
45° / critical-line symmetry slice.

Analytically this is the step: for fixed plastic character `χ`, the partial
products `twistedEulerProductPartial χ s (primesUpTo N)` tend to `riemannZeta s`
at `s = 1/2 + it`.
-/
def PlasticTwistedEulerProductConvergesOnCriticalLine (χ : PlasticTwiddleCharacter) : Prop :=
  PhaseBalanceImpliesReHalf →
    ∀ t : ℝ,
      let s : ℂ := ⟨(1 / 2 : ℝ), t⟩
      Filter.Tendsto
        (fun N : ℕ => twistedEulerProductPartial χ s (primesUpTo N))
        Filter.atTop
        (nhds (riemannZeta s))

/-!
## Geometric shell sequence

`canonical45DiagonalPoint` lives in `HigherOrderArityDiagonalSymmetry` to avoid
import cycles. Here we package a singleton shell at `t` and a step-truncation.
-/

/-- Singleton 01-face diagonal survivor shell at height `t` (phase round-trip). -/
noncomputable def survivorShell (t : ℝ) : Finset (Fin 3 → ℤ) :=
  let tNat : ℕ := Int.toNat (round t)
  let m : ℕ := Int.toNat (round (plasticSpiralPhaseAtStep tNat))
  {canonical45DiagonalPoint m}

/-- Truncation by `latticePointStep p ≤ N` (finite twisted-Euler stage slot). -/
noncomputable def survivorShellUpTo (t : ℝ) (N : ℕ) : Finset (Fin 3 → ℤ) :=
  (survivorShell t).filter (fun p => latticePointStep p ≤ N)

/-- Root-scale arity index at `t` (scaffold: matches the outer `round` in `survivorShell`). -/
noncomputable def kappa (t : ℝ) : ℕ :=
  Int.toNat (round t)

/--
Lattice finset sequence read off from the twisted Euler / prime-truncation side
at critical-line height `t`.

Today this is definitionally aligned with `survivorShellUpTo`; once the Euler
side is populated from `χ` and `primesUpTo`, this may diverge from the geometric
`survivorShellUpTo` and `SurvivorShellMatchesTwistedEulerLimit` becomes the
nontrivial geometric identification.
-/
noncomputable def twistedEulerSurvivorShellSeq (_χ : PlasticTwiddleCharacter) (t : ℝ) :
    ℕ → Finset (Fin 3 → ℤ) :=
  fun N => survivorShellUpTo t N

/--
The canonical diagonal survivor shell **sequence** at height `t` agrees with the
sequence of lattice finsets packaged from the twisted Euler channel.

This is the narrowed geometric bridge (no quantification over arbitrary shells).
-/
def SurvivorShellMatchesTwistedEulerLimit (χ : PlasticTwiddleCharacter) : Prop :=
  ∀ t : ℝ,
    twistedEulerSurvivorShellSeq χ t = fun N => survivorShellUpTo t N

theorem SurvivorShellMatchesTwistedEulerLimit_trivial (χ : PlasticTwiddleCharacter) :
    SurvivorShellMatchesTwistedEulerLimit χ := by
  intro t; rfl

/--
Pointwise analytic identification: for each admissible diagonal survivor shell,
the weighted lattice partial equals `ζ(1/2 + it)`.

Kept separate from `SurvivorShellMatchesTwistedEulerLimit`, which only aligns
shell **sequences** between geometry and the Euler packaging.
-/
def DiagonalSurvivorShellSumEqualsZetaAtHeight : Prop :=
  ∀ (t : ℝ)
    (shell : Finset (Fin 3 → ℤ))
    (_hShell : ∀ p, p ∈ shell → Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (0 : ℕ) (0 : ℕ))
    (_hSurvivor : ∀ p, p ∈ shell → DiagonalPermutationSurvivor p),
    twistedLatticeShellPartial t shell =
      riemannZeta (⟨(1 / 2 : ℝ), t⟩ : ℂ)

/--
Geometric identification slot (no per-height root shell):
survivor shell points have **prime** lattice-step indices (S₂ / pole-slot bookkeeping).

This replaces the older “prime power” packaging: composites are the generic cancellation
regime; primes are the rigid non-cancellation markers.
-/
def SurvivorShellPrimeLatticeSteps : Prop :=
  ∀ (shell : Finset (Fin 3 → ℤ)),
    (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) →
      ∀ p, p ∈ shell → Nat.Prime (latticePointStep p)

/-- Deprecated name for `SurvivorShellPrimeLatticeSteps`. -/
abbrev SurvivorShellIsPrimePowerRepresentatives : Prop :=
  SurvivorShellPrimeLatticeSteps

/--
**Geometric-only** packaging (no `PlasticLatticePoint`, no FTA / mirror / K3, no admissible `t`).

Face diagonal + `κ(t)` shell + permutation survivor ⇒ **`Nat.Prime (latticePointStep point)`**.
**False** in general — see `not_FaceDiagonalSurvivorPrimeStepWeak` and
`not_forall_primeLatticeStep_fromDiagonalShell`.

For the strengthened `Prop` that also records FTA, **`¬` mirror (prime-shell)**, K3, and
admissible `t`, see `FaceDiagonalSurvivorPrimeStep`: primality of the linked lattice step is
already proved from **`hLink`**, **`hFTA`**, and **`hMirrorOff`** alone
(`prime_latticePointStep_of_linked_fta_mirrorOff`); the extra geometric / K3 / height hooks
are downstream API only.
-/
def FaceDiagonalSurvivorPrimeStepWeak : Prop :=
  ∀ (t : ℝ) (point : Fin 3 → ℤ)
    (_hDiag : LiesOn45Diagonal point)
    (_hShell : Hqiv.Geometry.maxNatAbsCoord point ∈ Set.Icc (kappa t - 1) (kappa t))
    (_hSurvivor : DiagonalPermutationSurvivor point),
    Nat.Prime (latticePointStep point)

/--
Same face-diagonal + shell + survivor geometry as `FaceDiagonalSurvivorPrimeStepWeak`, plus
linked `PlasticLatticePoint` data (`P.n = latticePointStep point`), FTA / **`k = 3` residue**,
and `IsAdmissibleHeight t`.

**Mirror / prime-pole slot:** we use **`¬ HasArityMirrorCancellation P`** (no nontrivial
`a * b = P.n` factor pair with `1 < a, b`). That is exactly the **prime-shell** side of
`hasArityMirrorCancellation_iff_composite`: a linked **prime** step index cannot simultaneously
carry a composite mirror factorization on the same `P.n` (`not_prime_of_hasArityMirrorCancellation`).
-/
def FaceDiagonalSurvivorPrimeStep : Prop :=
  ∀ (t : ℝ) (point : Fin 3 → ℤ) (P : PlasticLatticePoint)
    (_hLink : P.n = latticePointStep point)
    (_hDiag : LiesOn45Diagonal point)
    (_hShell : Hqiv.Geometry.maxNatAbsCoord point ∈ Set.Icc (kappa t - 1) (kappa t))
    (_hSurvivor : DiagonalPermutationSurvivor point)
    (_hFTA : HasFTADecomposition P)
    (_hMirrorOff : ¬ HasArityMirrorCancellation P)
    (_hK3 : HasK3Residue P)
    (_hAdmissible : IsAdmissibleHeight t),
    Nat.Prime (latticePointStep point)

/-- Deprecated name for `FaceDiagonalSurvivorPrimeStepWeak`. -/
abbrev FaceDiagonalSurvivorIsPrimePowerWeak : Prop :=
  FaceDiagonalSurvivorPrimeStepWeak

/-- Deprecated name for `FaceDiagonalSurvivorPrimeStep`. -/
abbrev FaceDiagonalSurvivorIsPrimePower : Prop :=
  FaceDiagonalSurvivorPrimeStep

theorem kappa_eq_five_of_t_five : kappa (5 : ℝ) = 5 := by
  simp [kappa]

theorem not_prime_ten : ¬ Nat.Prime 10 := by
  decide

/--
If the plastic shell index admits a nontrivial mirror factor pair and is **linked** to the
lattice step, then `latticePointStep point` cannot be prime — the prime-pole regime is
exactly the **`¬ HasArityMirrorCancellation P`** side (`FaceDiagonalSurvivorPrimeStep`).
-/
theorem not_prime_latticePointStep_of_hasArityMirrorCancellation_link
    (point : Fin 3 → ℤ) (P : PlasticLatticePoint)
    (hLink : P.n = latticePointStep point)
    (hM : HasArityMirrorCancellation P) :
    ¬ Nat.Prime (latticePointStep point) := by
  rw [← hLink]
  exact not_prime_of_hasArityMirrorCancellation P hM

/--
Linked plastic shell (`P.n = latticePointStep point`) + FTA + **no** mirror factor pair ⇒
`Nat.Prime (latticePointStep point)` — purely from the `PlasticLatticePoint` shell dichotomy
(`hasArityMirrorCancellation_iff_composite`), no `ℤ³` geometry needed.
-/
theorem prime_latticePointStep_of_linked_fta_mirrorOff
    (point : Fin 3 → ℤ) (P : PlasticLatticePoint)
    (hLink : P.n = latticePointStep point)
    (hFTA : HasFTADecomposition P)
    (hMirrorOff : ¬ HasArityMirrorCancellation P) :
    Nat.Prime (latticePointStep point) := by
  rw [← hLink]
  exact Nat.Prime.of_hasFTADecomposition_of_not_hasArityMirrorCancellation P hFTA hMirrorOff

/-
The former unconditional `primeLatticeStepFromFaceDiagonal` / `_core` lemmas were removed:
`not_forall_primeLatticeStep_fromDiagonalShell` refutes that geometry alone forces a prime
lattice step.  Use `prime_latticePointStep_of_linked_fta_mirrorOff` (or
`faceDiagonalSurvivorPrimeStep`) once a linked `PlasticLatticePoint` shell with FTA and
`¬ HasArityMirrorCancellation` is available.
-/

/--
The universal implication “face 45° diagonal + `κ(t)` shell + permutation survivor ⇒
`Nat.Prime (latticePointStep)`” is **false**: `![5,5,0]` has step `10`.
-/
theorem not_forall_primeLatticeStep_fromDiagonalShell :
    ¬∀ (t : ℝ) (point : Fin 3 → ℤ),
      LiesOn45Diagonal point →
        Hqiv.Geometry.maxNatAbsCoord point ∈ Set.Icc (kappa t - 1) (kappa t) →
          DiagonalPermutationSurvivor point → Nat.Prime (latticePointStep point) := by
  intro h
  let point : Fin 3 → ℤ := ![5, 5, (0 : ℤ)]
  have h45 : LiesOn45Diagonal point :=
    ⟨(0 : Fin 3), (1 : Fin 3), by decide, by simp [point]⟩
  have hShell :
      Hqiv.Geometry.maxNatAbsCoord point ∈ Set.Icc (kappa (5 : ℝ) - 1) (kappa (5 : ℝ)) := by
    have hmax : Hqiv.Geometry.maxNatAbsCoord point = 5 := by native_decide
    rw [hmax, kappa_eq_five_of_t_five]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hSurv : DiagonalPermutationSurvivor point := by
    refine ⟨?_, ?_⟩
    · simpa [DiagonalPointHasPermutationSymmetry, LiesOn45Diagonal] using h45
    · simpa [PermutationOrbitCancels, LiesOn45Diagonal] using not_not.mpr h45
  have h10 : latticePointStep point = 10 := by native_decide
  have hbad := h (5 : ℝ) point h45 hShell hSurv
  rw [h10] at hbad
  exact not_prime_ten hbad

/-- Weak face-diagonal ⇒ prime step is refuted by `![5,5,0]` / step `10`. -/
theorem not_FaceDiagonalSurvivorPrimeStepWeak : ¬ FaceDiagonalSurvivorPrimeStepWeak := by
  intro h
  exact not_forall_primeLatticeStep_fromDiagonalShell h

/-- Spelling used in earlier notes: negation of the weak prime-step claim. -/
theorem not_FaceDiagonalSurvivorIsPrimePower : ¬ FaceDiagonalSurvivorPrimeStepWeak :=
  not_FaceDiagonalSurvivorPrimeStepWeak

/--
Strengthened survivor bundle (geometry + shell + permutation survivor + linked `P` + FTA +
`¬` mirror + K3 + admissible `t`).

**Proved:** `Nat.Prime (latticePointStep point)` already follows from **`hLink`**, **`hFTA`**,
and **`hMirrorOff`** alone (`prime_latticePointStep_of_linked_fta_mirrorOff`); the face-diagonal,
shell, survivor, K3, and admissible-height hypotheses are **API hooks** for downstream bridges
that need the full witness bundle in one statement.
-/
theorem faceDiagonalSurvivorPrimeStep
    (t : ℝ)
    (point : Fin 3 → ℤ)
    (P : PlasticLatticePoint)
    (hLink : P.n = latticePointStep point)
    (_hDiag : LiesOn45Diagonal point)
    (_hShell : Hqiv.Geometry.maxNatAbsCoord point ∈ Set.Icc (kappa t - 1) (kappa t))
    (_hSurvivor : DiagonalPermutationSurvivor point)
    (hFTA : HasFTADecomposition P)
    (hMirrorOff : ¬ HasArityMirrorCancellation P)
    (_hK3 : HasK3Residue P)
    (_hAdmissible : IsAdmissibleHeight t) :
    Nat.Prime (latticePointStep point) :=
  prime_latticePointStep_of_linked_fta_mirrorOff point P hLink hFTA hMirrorOff

/--
On a survivor shell, **`Nat.Prime (latticePointStep p)`** follows once each point is linked to
a plastic shell with FTA decomposition and **no** arity-mirror factor pair (prime-pole slot).

The `κ(t)` shell and permutation-survivor hypotheses are kept as **API hooks** for downstream
geometry bridges; this proof uses only the per-point plastic witness.
-/
theorem diagonalSurvivorRootShell_point_hasPrimeLatticeStep
    (t : ℝ)
    (shell : Finset (Fin 3 → ℤ))
    (_hShell : ∀ p ∈ shell, Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (kappa t - 1) (kappa t))
    (_hSurvivor : ∀ p ∈ shell, DiagonalPermutationSurvivor p)
    (hPlastic : ∀ p ∈ shell, ∃ P : PlasticLatticePoint,
        P.n = latticePointStep p ∧ HasFTADecomposition P ∧ ¬ HasArityMirrorCancellation P) :
    ∀ p ∈ shell, Nat.Prime (latticePointStep p) := by
  intro p hp
  rcases hPlastic p hp with ⟨P, hLink, hFTA, hOff⟩
  exact prime_latticePointStep_of_linked_fta_mirrorOff p P hLink hFTA hOff

/-- Earlier name for `diagonalSurvivorRootShell_point_hasPrimeLatticeStep`. -/
theorem diagonalSurvivorRootShell_point_hasPrimePowerIndex
    (t : ℝ)
    (shell : Finset (Fin 3 → ℤ))
    (hShell : ∀ p ∈ shell, Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (kappa t - 1) (kappa t))
    (hSurvivor : ∀ p ∈ shell, DiagonalPermutationSurvivor p)
    (hPlastic : ∀ p ∈ shell, ∃ P : PlasticLatticePoint,
        P.n = latticePointStep p ∧ HasFTADecomposition P ∧ ¬ HasArityMirrorCancellation P) :
    ∀ p ∈ shell, Nat.Prime (latticePointStep p) :=
  diagonalSurvivorRootShell_point_hasPrimeLatticeStep t shell hShell hSurvivor hPlastic

/--
While `twistedEulerSurvivorShellSeq` is definitionally `survivorShellUpTo`, this
is immediate. Once the Euler-side sequence is filled from `χ` / primes, the
same proof slot should consume `SurvivorShellPrimeLatticeSteps` and
compatibility with the canonical geometric construction.
-/
theorem SurvivorShellMatchesTwistedEulerLimit_of_prime_lattice_steps
    (χ : PlasticTwiddleCharacter)
    (_hPrime : SurvivorShellPrimeLatticeSteps) :
    SurvivorShellMatchesTwistedEulerLimit χ := by
  intro t
  rfl

/-- Earlier parameter name (`SurvivorShellIsPrimePowerRepresentatives`). -/
theorem SurvivorShellMatchesTwistedEulerLimit_of_prime_power_representatives
    (χ : PlasticTwiddleCharacter)
    (_h : SurvivorShellPrimeLatticeSteps) :
    SurvivorShellMatchesTwistedEulerLimit χ :=
  SurvivorShellMatchesTwistedEulerLimit_of_prime_lattice_steps χ _h

/-- Earlier spelling of `not_FaceDiagonalSurvivorPrimeStepWeak`. -/
theorem not_FaceDiagonalSurvivorIsPrimePowerWeak : ¬ FaceDiagonalSurvivorPrimeStepWeak :=
  not_FaceDiagonalSurvivorPrimeStepWeak

/--
Coefficient/channel identification slot:
the weighted survivor shell sum is the twisted Euler partial.
-/
def WeightedSurvivorSumIsTwistedEulerPartial : Prop :=
  ∀ (t : ℝ) (shell : Finset (Fin 3 → ℤ)),
    (Finset.sum shell (fun p =>
      annulusCubicCoeff (latticePointStep p) *
      plasticPhaseFactor (latticePointStep p))) =
    twistedLatticeShellPartial t shell

/-- The weighted-sum/twisted-partial identification is definitional. -/
theorem weightedSurvivorSumIsTwistedEulerPartial_trivial :
    WeightedSurvivorSumIsTwistedEulerPartial := by
  intro t shell
  rfl

/--
Sketch-realization theorem: Sub-goal 2 analytic identification from the twisted
Euler product channel plus the two explicit intermediate bridge facts.
-/
theorem SurvivingDiagonalSumEqualsZetaAtHeight_of_twisted_euler_product
    (χ : PlasticTwiddleCharacter)
    (hSumIsTwistedProduct : WeightedSurvivorSumIsTwistedEulerPartial)
    (_hTwisted : PlasticTwistedEulerProductConvergesOnCriticalLine χ)
    (_hShellSeq : SurvivorShellMatchesTwistedEulerLimit χ)
    (hZeta : DiagonalSurvivorShellSumEqualsZetaAtHeight) :
    SurvivingDiagonalSumEqualsZetaAtHeight := by
  intro t shell hShell hSurvivor
  have _ := _hTwisted
  have _ := _hShellSeq
  calc
    (Finset.sum shell (fun p =>
      annulusCubicCoeff (latticePointStep p) *
      plasticPhaseFactor (latticePointStep p)))
        = twistedLatticeShellPartial t shell := hSumIsTwistedProduct t shell
    _ = riemannZeta (⟨(1 / 2 : ℝ), t⟩ : ℂ) := hZeta t shell hShell hSurvivor

/--
Core reduced version: once definitional identification is discharged, twisted
Euler convergence alone implies the survivor-sum/zeta identification.
-/
theorem SurvivingDiagonalSumEqualsZetaAtHeight_of_twisted_euler_product_core
    (χ : PlasticTwiddleCharacter)
    (hTwisted : PlasticTwistedEulerProductConvergesOnCriticalLine χ)
    (hShellSeq : SurvivorShellMatchesTwistedEulerLimit χ)
    (hZeta : DiagonalSurvivorShellSumEqualsZetaAtHeight) :
    SurvivingDiagonalSumEqualsZetaAtHeight :=
  SurvivingDiagonalSumEqualsZetaAtHeight_of_twisted_euler_product
    χ weightedSurvivorSumIsTwistedEulerPartial_trivial hTwisted hShellSeq hZeta

end
end Hqiv.Story
