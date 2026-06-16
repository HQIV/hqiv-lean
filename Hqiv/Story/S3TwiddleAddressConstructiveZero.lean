import Hqiv.Story.S3DiagonalZeroAddressCapstone
import Hqiv.Story.S3HarmonicShellZeroCounting
import Hqiv.Story.S3HopfJKUnitCircleZeroReadout
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3ZeroProducingOrbits
import Hqiv.Story.PlasticLatticePhaseImpliesZetaZero
import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf
import Hqiv.Story.PlasticCriticalLineBridge
import Hqiv.Story.ArityFTADecomposition
import Hqiv.Story.PlasticTwistedEulerCharacter

/-!
# Twiddle / voxel addresses constructively force line zeros

The theta-doubling law `2t = cumulativeArcSlotCount n` would identify **every**
critical-line height with a global circle partition index — full **coverage** of
the line by arc-slot counting.  That is stronger than the program here.

We only need a **line**: at height `t` the rolled sample is the single point
`stripRollingMap t` on the `j`–`k` circle.  A twiddle-factor / voxel **address**
labels which harmonic slot on that line is in play; **balance** at that slot is
the constructive zero mechanism.

## Constructive chain (proved here)

1. **Off-diagonal voxels cancel** — swap-antisymmetric contributions pair to zero
   (`voxel_pair_cancellation_off_diagonal`).
2. **Twiddle addresses survive on the 45° diagonal** — `(m,m,0)` from the
   product tuple `(m,m,c)` is a `DiagonalPermutationSurvivor`
   (`twiddle_voxel_lattice_point_survives`).
3. **Balance at the partition slot** ⟹ `criticalProj = 0` ⟹ `ZeroProducingOrbit`
   on the rolled line (`partition_balance_constructive_zero_producing`).
4. Under `RollingZetaIdentificationAtCriticalLine`, balance ⟹ `ζ = 0` on the
   critical line at that slot height (`partition_balance_constructive_zeta_zero`).
5. **Lattice identification** — if the diagonal survivor shell sum vanishes and
   equals `ζ(½+it)`, then `ζ = 0` (`constructive_zeta_zero_from_vanishing_diagonal_shell`).

## Honesty

* `(2,2,2) ↦ shell 8 ↦ slot k = 1` is an **address**, not an automatic zero:
  `cos(π/4) + sin(π/4) ≠ 0`.  Zeros require the balance event at the slot.
* The doubling law and `DiagonalPartitionAssignment` are **not** used here.
* Proving *which* heights balance (or that every actual zero does) remains open.
* **FTA / mirror at `(m,m,1)`:** composite product shell `m²` with mirror pair
  `(m,m)`; `ReducedDiagonalSurvivorShell` at balance once lattice sum identifies
  with rolled amplitude (see below).
-/

namespace Hqiv.Story

noncomputable section

/-! ## Line-only readout vs full circle coverage -/

/--
Critical-line **height** carried by a harmonic shell slot — one real parameter
per `(n,k)`, not a scan of all `t ∈ ℝ`.
-/
noncomputable def criticalLineHeightAtSlot {n : ℕ} (hn : 0 < n) (k : Fin n) : ℝ :=
  shellSweepAngle hn k

noncomputable def criticalLineHeightOfPartition (addr : DiagonalS3PartitionAddress)
    (hn : 0 < addr.slot.1) : ℝ :=
  criticalLineHeightAtSlot hn addr.slot.2

/--
The rolled line evaluates **one** circle point at the slot height — the slot
indexes a line parameter, not a filled circle partition of all heights.
-/
theorem strip_rolling_at_slot_is_line_readout {n : ℕ} (hn : 0 < n) (k : Fin n) :
    stripRollingAtSlot hn k = stripRollingMap (criticalLineHeightAtSlot hn k) := by
  dsimp [stripRollingAtSlot, criticalLineHeightAtSlot]

/--
**Too strong for the line program:** every real height is the slot height of
some partition cell.  Equivalent in spirit to global theta-doubling / full cover.
-/
def TwiddlePartitionFullLineCoverage : Prop :=
  ∀ t : ℝ, ∃ addr : DiagonalS3PartitionAddress,
    ∃ hn : 0 < addr.slot.1, criticalLineHeightOfPartition addr hn = t

theorem not_claimed_twiddle_partition_full_line_coverage :
    TwiddlePartitionFullLineCoverage → True :=
  fun _ => trivial

/-! ## Voxel / twiddle lattice point -/

/--
Lattice witness for a twiddle-factor address: use the twiddle leg magnitude `m`
as the equal coordinate on the **01-face diagonal** `(m,m,0)`.

This is the product-address chart, **not** the ℤ³ voxel `(2,2,2)` on shell `12`.
-/
noncomputable def latticePointOfTwiddleAddress (addr : TwiddleFactorAddress) : Fin 3 → ℤ :=
  canonical45DiagonalPoint (max 1 addr.1)

theorem twiddle_voxel_lattice_point_on_diagonal (addr : TwiddleFactorAddress) :
    LiesOn45Diagonal (latticePointOfTwiddleAddress addr) := by
  dsimp [latticePointOfTwiddleAddress, canonical45DiagonalPoint]
  refine ⟨(0 : Fin 3), (1 : Fin 3), ?_, ?_⟩
  · decide
  · simp

theorem twiddle_voxel_lattice_point_survives (addr : TwiddleFactorAddress) :
    DiagonalPermutationSurvivor (latticePointOfTwiddleAddress addr) := by
  refine ⟨twiddle_voxel_lattice_point_on_diagonal addr, ?_⟩
  simpa [PermutationOrbitCancels, twiddle_voxel_lattice_point_on_diagonal]

theorem twiddle_address_222_lattice_point :
    latticePointOfTwiddleAddress twiddleAddress222 = canonical45DiagonalPoint 2 := by
  simp [latticePointOfTwiddleAddress, twiddleAddress222, canonical45DiagonalPoint]

theorem partition_address_lattice_point_survives (addr : DiagonalS3PartitionAddress) :
    DiagonalPermutationSurvivor (latticePointOfTwiddleAddress addr.twiddle) :=
  twiddle_voxel_lattice_point_survives addr.twiddle

/-! ## Off-diagonal voxel cancellation (constructive) -/

theorem voxel_pair_cancellation_off_diagonal
    (contrib : PointContributionModel)
    (hAnti : Swap01Antisymmetric contrib)
    (n : ℕ) (point : Fin 3 → ℤ) (hNotDiag : ¬ LiesOn45Diagonal point) :
    contrib n point + contrib n (mirrorSwap01 point) = 0 :=
  pair_cancels_of_swap01_antisymmetric contrib hAnti n point

theorem off_diagonal_voxels_cancel_in_shell
    (contrib : PointContributionModel)
    (hAnti : Swap01Antisymmetric contrib)
    (shell : Finset (Fin 3 → ℤ))
    (point : Fin 3 → ℤ) (hmem : point ∈ shell) (hNotDiag : ¬ LiesOn45Diagonal point) :
    contrib (latticePointStep point) point +
        contrib (latticePointStep point) (mirrorSwap01 point) = 0 :=
  voxel_pair_cancellation_off_diagonal contrib hAnti _ point hNotDiag

/-! ## Balance at slot ⇒ zero-producing orbit (unconditional) -/

theorem partition_balance_constructive_zero_producing
    {n : ℕ} (hn : 0 < n) (k : Fin n)
    (hbal : HarmonicShellBalanceEvent hn k) :
    ZeroProducingOrbit (stripRollingAtSlot hn k) := by
  dsimp [HarmonicShellBalanceEvent, stripRollingAtSlot] at hbal ⊢
  exact (zero_producing_orbit_iff_critical_proj_zero _).mpr hbal

theorem partition_balance_constructive_hopf_twiddle_vanishes
    {n : ℕ} (hn : 0 < n) (k : Fin n)
    (hbal : HarmonicShellBalanceEvent hn k) :
    hopfJKTwiddleReadout (criticalLineHeightAtSlot hn k) = 0 :=
  (harmonic_shell_balance_iff_jk_product_phase hn k).mp hbal

theorem diagonal_partition_balance_constructive_zero_producing
    (addr : DiagonalS3PartitionAddress)
    (hn : 0 < addr.slot.1)
    (hbal : HarmonicShellBalanceEvent hn addr.slot.2) :
    ZeroProducingOrbit (stripRollingAtSlot hn addr.slot.2) :=
  partition_balance_constructive_zero_producing hn addr.slot.2 hbal

/-! ## Balance ⇒ ζ-zero on the line (conditional identification) -/

theorem partition_balance_constructive_zeta_zero
    (hId : RollingZetaIdentificationAtCriticalLine)
    {n : ℕ} (hn : 0 < n) (k : Fin n)
    (hbal : HarmonicShellBalanceEvent hn k) :
    riemannZeta (criticalLinePointAtHeight (criticalLineHeightAtSlot hn k)) = 0 :=
  (zeta_zero_iff_shell_slot_balance hId hn k).mpr hbal

theorem diagonal_partition_balance_constructive_zeta_zero
    (hId : RollingZetaIdentificationAtCriticalLine)
    (addr : DiagonalS3PartitionAddress)
    (hn : 0 < addr.slot.1)
    (hbal : HarmonicShellBalanceEvent hn addr.slot.2) :
    riemannZeta (criticalLinePointAtHeight (criticalLineHeightOfPartition addr hn)) = 0 :=
  partition_balance_constructive_zeta_zero hId hn addr.slot.2 hbal

theorem diagonal_partition_balance_constructive_matched_rolling
    (hId : RollingZetaIdentificationAtCriticalLine)
    (addr : DiagonalS3PartitionAddress)
    (hn : 0 < addr.slot.1)
    (_hbal : HarmonicShellBalanceEvent hn addr.slot.2) :
    MatchedRollingZeroAt
      (criticalLinePointAtHeight (criticalLineHeightOfPartition addr hn))
      (rolledSampleAtHeight (criticalLineHeightOfPartition addr hn)) := by
  refine ⟨?_, ?_⟩
  · simp [RollingMatchesCriticalHeight, criticalLinePointAtHeight,
      rolledSampleAtHeight, criticalLineHeightOfPartition]
  · exact hId (criticalLineHeightOfPartition addr hn)

/-! ## Lattice shell vanishing ⇒ ζ-zero (constructive identification) -/

theorem constructive_zeta_zero_from_vanishing_diagonal_shell
    (hIdent : DiagonalSurvivorShellSumEqualsZetaAtHeight)
    (t : ℝ) (shell : Finset (Fin 3 → ℤ))
    (hShell : ∀ p, p ∈ shell → Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (0 : ℕ) (0 : ℕ))
    (hSurv : ∀ p, p ∈ shell → DiagonalPermutationSurvivor p)
    (hSumZero : twistedLatticeShellPartial t shell = 0) :
    riemannZeta (⟨(1 / 2 : ℝ), t⟩ : ℂ) = 0 := by
  have hEq := hIdent t shell hShell hSurv
  rw [← hEq, hSumZero]

theorem constructive_zeta_zero_from_twiddle_voxel_shell
    (hIdent : DiagonalSurvivorShellSumEqualsZetaAtHeight)
    (addr : DiagonalS3PartitionAddress) (t : ℝ)
    (shell : Finset (Fin 3 → ℤ))
    (hMem : latticePointOfTwiddleAddress addr.twiddle ∈ shell)
    (hShell : ∀ p, p ∈ shell → Hqiv.Geometry.maxNatAbsCoord p ∈ Set.Icc (0 : ℕ) (0 : ℕ))
    (hSurvShell : ∀ p, p ∈ shell → DiagonalPermutationSurvivor p)
    (hSumZero : twistedLatticeShellPartial t shell = 0) :
    riemannZeta (⟨(1 / 2 : ℝ), t⟩ : ℂ) = 0 :=
  constructive_zeta_zero_from_vanishing_diagonal_shell hIdent t shell hShell hSurvShell hSumZero

/-! ## Canonical `(2,2,2)` address: mechanism, not automatic zero -/

theorem twiddle_address_222_height_is_pi_quarter :
    criticalLineHeightOfPartition diagonalPartitionAddress222 (Nat.succ_pos 7) =
      Real.pi / 4 := by
  dsimp [criticalLineHeightOfPartition, diagonalPartitionAddress222,
    diagonal_partition_address_222_slot, twiddlePiQuarterSlot, criticalLineHeightAtSlot,
    shellSweepAngle]
  field_simp
  ring

/-! ## `(m,m,1)` twiddle: FTA / mirror / K3 / reduced survivor shell -/

/-- Canonical `(m,m,1)` twiddle-factor address (product shell `m²`). -/
def twiddleAddressMMM1 (m : ℕ) : TwiddleFactorAddress :=
  (m, m, 1)

theorem twiddle_address_mmm1_shell_depth (m : ℕ) :
    twiddleAddressShellDepth (twiddleAddressMMM1 m) = m * m := by
  dsimp [twiddleAddressShellDepth, twiddleAddressMMM1]
  ring

theorem latticePointStep_canonical45 (m : ℕ) :
    latticePointStep (canonical45DiagonalPoint m) = 2 * m := by
  dsimp [latticePointStep, canonical45DiagonalPoint]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_zero]
  norm_cast
  simp [Int.natAbs_eq, two_mul]

theorem twiddle_mmm1_max_leg (m : ℕ) (hm : 2 ≤ m) : max 1 m = m :=
  Nat.max_eq_right (Nat.le_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hm))

theorem twiddle_mmm1_lattice_step (m : ℕ) (hm : 2 ≤ m) :
    latticePointStep (latticePointOfTwiddleAddress (twiddleAddressMMM1 m)) = 2 * m := by
  dsimp [latticePointOfTwiddleAddress, twiddleAddressMMM1]
  rw [twiddle_mmm1_max_leg m hm]
  exact latticePointStep_canonical45 m

theorem twiddle_mmm1_lattice_step_eq_mirror_annulus_radius (m : ℕ) (hm : 2 ≤ m) :
    (latticePointStep (latticePointOfTwiddleAddress (twiddleAddressMMM1 m)) : ℝ) =
      annulusMirrorRadius m := by
  rw [twiddle_mmm1_lattice_step m hm, annulusMirrorRadius_eq_two_mul]
  norm_cast

theorem twiddle_mmm1_lattice_coeff_eq_k3_diag (m : ℕ) (hm : 2 ≤ m) :
    annulusCubicCoeff (latticePointStep (latticePointOfTwiddleAddress (twiddleAddressMMM1 m))) =
      k3OctantDiagCoeff (2 * m) := by
  rw [twiddle_mmm1_lattice_step m hm]
  exact annulusCubicCoeff_eq_k3OctantDiagCoeff (2 * m) (by nlinarith : 2 * m ≠ 0)

/-- Plastic shell index for the `(m,m,1)` product address: `n = m²`. -/
noncomputable def plasticPointOfTwiddleMMM1 (m : ℕ) : PlasticLatticePoint :=
  { n := m * m, R := 0, X := 0 }

theorem twiddle_mmm1_product_shell_fta (m : ℕ) (hm : 2 ≤ m) :
    HasFTADecomposition (plasticPointOfTwiddleMMM1 m) := by
  dsimp [HasFTADecomposition, plasticPointOfTwiddleMMM1]
  nlinarith

theorem twiddle_mmm1_product_shell_mirror (m : ℕ) (hm : 2 ≤ m) :
    HasArityMirrorCancellation (plasticPointOfTwiddleMMM1 m) := by
  refine ⟨m, m, by omega, by omega, rfl⟩

theorem twiddle_mmm1_product_shell_fta_and_mirror (m : ℕ) (hm : 2 ≤ m) :
    HasFTADecomposition (plasticPointOfTwiddleMMM1 m) ∧
      HasArityMirrorCancellation (plasticPointOfTwiddleMMM1 m) :=
  ⟨twiddle_mmm1_product_shell_fta m hm, twiddle_mmm1_product_shell_mirror m hm⟩

theorem twiddle_mmm1_composite_channel (m : ℕ) (hm : 2 ≤ m) :
    CompositeChannel (plasticPointOfTwiddleMMM1 m).n := by
  dsimp [plasticPointOfTwiddleMMM1]
  exact (hasArityMirrorCancellation_iff_composite _).1 (twiddle_mmm1_product_shell_mirror m hm)

theorem hasK3Residue_unconditional (P : PlasticLatticePoint) : HasK3Residue P :=
  ⟨1, one_ne_zero, annulusCubicCoeff_eq_k3OctantDiagCoeff 1 one_ne_zero⟩

theorem nat_lt_min_one_pred_local {n : ℕ} (hn : 0 < n) : min 1 (n - 1) < n := by
  rcases n with (_ | _ | n)
  · cases hn
  · decide
  · dsimp [min]
    omega

/-- Partition cell for the `(m,m,1)` twiddle address at product-shell depth `m²`. -/
noncomputable def partitionAddressOfTwiddleMMM1 (m : ℕ) (hm : 2 ≤ m) : DiagonalS3PartitionAddress where
  twiddle := twiddleAddressMMM1 m
  diagonal := Or.inl rfl
  slot :=
    let n := m * m
    ⟨n, ⟨min 1 (n - 1), nat_lt_min_one_pred_local (by dsimp [n]; nlinarith)⟩⟩
  shell_product := by
    dsimp [twiddleAddressShellDepth, twiddleAddressMMM1]
    ring

theorem twiddle_mmm1_slot_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < (partitionAddressOfTwiddleMMM1 m hm).slot.1 := by
  dsimp [partitionAddressOfTwiddleMMM1, twiddleAddressMMM1, twiddleAddressShellDepth]
  nlinarith

noncomputable def twiddleMMM1SurvivorShell (m : ℕ) : Finset (Fin 3 → ℤ) :=
  {latticePointOfTwiddleAddress (twiddleAddressMMM1 m)}

theorem mem_twiddle_mmm1_survivor_shell (m : ℕ) :
    latticePointOfTwiddleAddress (twiddleAddressMMM1 m) ∈ twiddleMMM1SurvivorShell m :=
  Finset.mem_singleton.mpr rfl

noncomputable def twiddleMMM1GeomWitness (m : ℕ) : PlasticRHBalancePointGeom :=
  { n := m * m, R := 0, X := 0
    point := latticePointOfTwiddleAddress (twiddleAddressMMM1 m) }

theorem twiddle_mmm1_geom_witness_point (m : ℕ) :
    (twiddleMMM1GeomWitness m).point =
      latticePointOfTwiddleAddress (twiddleAddressMMM1 m) :=
  rfl

theorem twiddle_mmm1_lattice_hypotheses_yield_diagonal_survivor (m : ℕ) (_hm : 2 ≤ m) :
    ∃ Q : PlasticRHBalancePointGeom,
      Q.toPlasticLatticePoint = plasticPointOfTwiddleMMM1 m ∧
        DiagonalPermutationSurvivor Q.point :=
  ⟨twiddleMMM1GeomWitness m, rfl, twiddle_voxel_lattice_point_survives (twiddleAddressMMM1 m)⟩

/--
Singleton `(m,m,1)` voxel shell weighted sum equals the rolled 45° amplitude at the
partition slot height — the lattice-to-line identification hook.
-/
def TwiddleMMM1LatticeSumEqRollingAmplitude (m : ℕ) (hm : 2 ≤ m) : Prop :=
  let addr := partitionAddressOfTwiddleMMM1 m hm
  let hn := twiddle_mmm1_slot_pos hm
  let t := criticalLineHeightOfPartition addr hn
  twistedLatticeShellPartial t (twiddleMMM1SurvivorShell m) =
    (hopfJKCriticalAmplitude t : ℂ)

/--
**Constructive reduction:** FTA + mirror composite channel + K3 + balance at the
linked partition slot + lattice/rolling identification ⇒ diagonal survivor shell
sum vanishes.
-/
theorem reduced_diagonal_survivor_shell_at_twiddle_mmm1_of_balance
    (m : ℕ) (hm : 2 ≤ m)
    (hbal : HarmonicShellBalanceEvent (twiddle_mmm1_slot_pos hm)
      (partitionAddressOfTwiddleMMM1 m hm).slot.2)
    (hIdent : TwiddleMMM1LatticeSumEqRollingAmplitude m hm) :
    ∃ shell : Finset (Fin 3 → ℤ),
      (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) ∧
        Finset.sum shell (fun p =>
          annulusCubicCoeff (latticePointStep p) * plasticPhaseFactor (latticePointStep p)) = 0 := by
  refine ⟨twiddleMMM1SurvivorShell m, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact twiddle_voxel_lattice_point_survives (twiddleAddressMMM1 m)
  · simp only [twiddleMMM1SurvivorShell, Finset.sum_singleton]
    have hamp :=
      (harmonic_shell_balance_iff_hopf_jk_amplitude (twiddle_mmm1_slot_pos hm)
        (partitionAddressOfTwiddleMMM1 m hm).slot.2).mp hbal
    have hsum :
        annulusCubicCoeff (latticePointStep (latticePointOfTwiddleAddress (twiddleAddressMMM1 m))) *
            plasticPhaseFactor (latticePointStep (latticePointOfTwiddleAddress (twiddleAddressMMM1 m))) =
          (hopfJKCriticalAmplitude
            (criticalLineHeightOfPartition (partitionAddressOfTwiddleMMM1 m hm)
              (twiddle_mmm1_slot_pos hm)) : ℂ) := by
      simpa [twistedLatticeShellPartial, twiddleMMM1SurvivorShell, Finset.sum_singleton,
        TwiddleMMM1LatticeSumEqRollingAmplitude, partitionAddressOfTwiddleMMM1,
        criticalLineHeightOfPartition, criticalLineHeightAtSlot] using hIdent
    rw [hsum]
    simpa using Complex.ofReal_eq_zero.mpr hamp

/--
Specialization of `ReducedDiagonalSurvivorShellAtPoint` at `(m,m,1)` composite shells,
discharged from balance + lattice/rolling amplitude identification (not from global
line coverage).
-/
def ReducedDiagonalSurvivorShellAtTwiddleMMM1 : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m),
    HarmonicShellBalanceEvent (twiddle_mmm1_slot_pos hm)
      (partitionAddressOfTwiddleMMM1 m hm).slot.2 →
      TwiddleMMM1LatticeSumEqRollingAmplitude m hm →
        ∃ shell : Finset (Fin 3 → ℤ),
          (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) ∧
            Finset.sum shell (fun p =>
              annulusCubicCoeff (latticePointStep p) *
                plasticPhaseFactor (latticePointStep p)) = 0

theorem reduced_diagonal_survivor_shell_at_twiddle_mmm1 :
    ReducedDiagonalSurvivorShellAtTwiddleMMM1 :=
  fun m hm hbal hIdent =>
    reduced_diagonal_survivor_shell_at_twiddle_mmm1_of_balance m hm hbal hIdent

theorem twiddle_mmm1_fta_mirror_k3 (m : ℕ) (hm : 2 ≤ m) :
    HasFTADecomposition (plasticPointOfTwiddleMMM1 m) ∧
      HasArityMirrorCancellation (plasticPointOfTwiddleMMM1 m) ∧
        HasK3Residue (plasticPointOfTwiddleMMM1 m) :=
  ⟨twiddle_mmm1_product_shell_fta m hm, twiddle_mmm1_product_shell_mirror m hm,
    hasK3Residue_unconditional _⟩

theorem twiddle_mmm1_zeta_zero_of_balance_and_rolling
    (hId : RollingZetaIdentificationAtCriticalLine) (m : ℕ) (hm : 2 ≤ m)
    (hbal : HarmonicShellBalanceEvent (twiddle_mmm1_slot_pos hm)
      (partitionAddressOfTwiddleMMM1 m hm).slot.2) :
    riemannZeta (criticalLinePointAtHeight
      (criticalLineHeightOfPartition (partitionAddressOfTwiddleMMM1 m hm)
        (twiddle_mmm1_slot_pos hm))) = 0 :=
  diagonal_partition_balance_constructive_zeta_zero hId (partitionAddressOfTwiddleMMM1 m hm)
    (twiddle_mmm1_slot_pos hm) hbal

theorem twiddle_address_222_not_automatic_balance :
    ¬ HarmonicShellBalanceEvent (Nat.succ_pos 7) twiddlePiQuarterSlot.2 := by
  intro hbal
  have hangle := twiddle_pi_quarter_slot_angle
  have hcos := (harmonic_shell_balance_iff_cos_sin (Nat.succ_pos 7) twiddlePiQuarterSlot.2).mp hbal
  have hval : Real.cos (Real.pi / 4) + Real.sin (Real.pi / 4) = Real.sqrt 2 := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    ring
  have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  rw [hangle] at hcos
  rw [hval] at hcos
  exact hsqrt hcos

/-! ## Constructive bundle -/

/--
Constructive zero-forcing package: line readout, voxel cancellation, diagonal
survivors, balance ⇒ zero-producing orbit, and conditional ζ identification.
-/
structure TwiddleAddressConstructiveZeroBundle where
  /-- Slot height is a line parameter, not full circle coverage. -/
  slot_is_line_readout :
    ∀ {n : ℕ} (hn : 0 < n) (k : Fin n),
      stripRollingAtSlot hn k = stripRollingMap (criticalLineHeightAtSlot hn k)
  /-- Twiddle addresses yield diagonal lattice survivors. -/
  twiddle_voxel_survives : ∀ addr : TwiddleFactorAddress,
    DiagonalPermutationSurvivor (latticePointOfTwiddleAddress addr)
  /-- Balance at slot forces zero-producing rolling orbit. -/
  balance_forces_zero_producing :
    ∀ {n : ℕ} (hn : 0 < n) (k : Fin n),
      HarmonicShellBalanceEvent hn k →
        ZeroProducingOrbit (stripRollingAtSlot hn k)
  /-- `(2,2,2)` labels π/4 but does not automatically balance. -/
  address_222_not_auto_zero :
    ¬ HarmonicShellBalanceEvent (Nat.succ_pos 7) twiddlePiQuarterSlot.2
  /-- Conditional: balance + rolling identification ⇒ ζ-zero on the line. -/
  balance_forces_zeta_zero :
    RollingZetaIdentificationAtCriticalLine →
      ∀ {n : ℕ} (hn : 0 < n) (k : Fin n),
        HarmonicShellBalanceEvent hn k →
          riemannZeta (criticalLinePointAtHeight (criticalLineHeightAtSlot hn k)) = 0

noncomputable def twiddleAddressConstructiveZeroBundle : TwiddleAddressConstructiveZeroBundle where
  slot_is_line_readout := strip_rolling_at_slot_is_line_readout
  twiddle_voxel_survives := twiddle_voxel_lattice_point_survives
  balance_forces_zero_producing := partition_balance_constructive_zero_producing
  address_222_not_auto_zero := twiddle_address_222_not_automatic_balance
  balance_forces_zeta_zero := fun hId => partition_balance_constructive_zeta_zero hId

/-!
## Status

* **Unconditional constructive:** off-diagonal pair cancellation; twiddle voxel
  diagonal survivors; balance ⟹ `ZeroProducingOrbit` / vanishing `hopfJKTwiddleReadout`.
* **Conditional constructive:** balance ⟹ `ζ = 0` on the line at slot height.
* **Lattice constructive:** `ReducedDiagonalSurvivorShellAtTwiddleMMM1` from balance +
  `TwiddleMMM1LatticeSumEqRollingAmplitude`; FTA + mirror + K3 unconditional on `m²`.
* **Not claimed:** `TwiddlePartitionFullLineCoverage`; theta doubling; automatic
  zero at `(2,2,2)` without balance; full `ReducedDiagonalSurvivorShellAtPoint` globally.
-/

end

end Hqiv.Story
