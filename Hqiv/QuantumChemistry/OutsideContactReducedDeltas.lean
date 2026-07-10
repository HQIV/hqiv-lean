import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.QuantumChemistry.CrystalContactGeometry
import Hqiv.QuantumChemistry.OutsideContactLedger
import Hqiv.QuantumChemistry.SecondOrderEffects
import Hqiv.QuantumChemistry.VoltageGenerationLedger
import HqivSpine.Chemistry.Spectroscopy
import HqivSpine.Chemistry.LineSpectra
import HqivSpine.Physics.GeneratorDependentCoupling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Reduced outside-contact deltas

Not every ledger channel needs heavy quarantine.  In a typical condensed / interface
assay the bookkeeping collapses:

* **Shared ambient** — gravity (`φ`) and bulk medium density (`ρ`) are lab-scale
  and the same for every motif in the assay.  They factor out of motif comparisons.
* **Dry-wall spectrum** — wall / substrate / interface participation is the
  preferred-axis spectral gap of the *wall* contact polarities (or an explicit
  wall coordination excess), not a per-molecule fitted defect.  One wall
  spectrum ⇒ one wall localDefect / tribo factor.
* **Motif-local deltas** — the small residual set that actually distinguishes
  chemistry rows: bond dielectric `em` (or its spectroscopy pin `s*`), network
  coordination excess vs a reference allotrope, and bond-summed contact surplus.

So
\[
  M_{\mathrm{out}}
  = A_{\mathrm{ambient}}\cdot W_{\mathrm{wall}}\cdot \Delta_{\mathrm{motif}}
\]
with \(A\) shared, \(W\) fixed by the dry wall, and \(\Delta\) the only
motif-by-motif variation.  Full multi-channel \(G_{\mathrm{eff}}\) remains hard;
the *comparison* problem is much smaller.

Python: `scripts/hqiv_outside_contact_reduced_deltas.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open HqivSpine.Chemistry
open HqivSpine.Chemistry.LineSpectra
open HqivSpine.Physics.GeneratorDependentCoupling

noncomputable section

/-! ## Shared ambient (lab-scale, motif-independent) -/

/-- Shared ambient dress: gravity × bulk medium density.
Same for every motif in one assay. -/
structure SharedAmbient where
  phiEpsilon : ℝ := 0
  bulkTarget : ℝ := 1
  rhoBulk : ℝ := 0

/-- Ambient product `grav · bulk`. -/
def sharedAmbientDress (A : SharedAmbient) : ℝ :=
  outsideGravityGeffModulator ⟨A.phiEpsilon⟩ *
    outsideBulkChannel A.bulkTarget A.rhoBulk

/-- Dilute / zero-lapse ambient is exactly `1`. -/
def diluteSharedAmbient : SharedAmbient where
  phiEpsilon := 0
  bulkTarget := 1
  rhoBulk := 0

theorem diluteSharedAmbient_dress : sharedAmbientDress diluteSharedAmbient = 1 := by
  unfold sharedAmbientDress diluteSharedAmbient
  have hg : outsideGravityGeffModulator ⟨0⟩ = 1 := by
    unfold outsideGravityGeffModulator; simp
  rw [hg, outsideBulkChannel_dilute]
  ring

/-! ## Dry-wall spectrum (interface, not per-molecule fit) -/

/-- Dry-wall interface from a polarity spectrum and/or an explicit wall excess. -/
structure DryWallSpectrum where
  /-- Wall polarity (or excess) spectrum. -/
  wallPolarities : List ℝ := []
  /-- Explicit wall coordination excess (substrate CN spike, etc.). -/
  wallCoordinationExcess : ℝ := 0

/-- Wall spectral gap (unique dry-wall channel). -/
def dryWallSpectralGap (W : DryWallSpectrum) : ℝ :=
  preferredAxisSpectralGap W.wallPolarities

/-- Wall defect stress: max of explicit excess and spectral gap
(both read as nonnegative participation weights). -/
def dryWallDefectStress (W : DryWallSpectrum) : ℝ :=
  max W.wallCoordinationExcess (dryWallSpectralGap W)

/-- Wall dress: localDefect of the dry-wall stress. -/
def dryWallDress (W : DryWallSpectrum) : ℝ :=
  outsideLocalDefectChannel (dryWallDefectStress W)

/-- Empty / pristine wall: no polarities, zero excess ⇒ dress `1`. -/
def pristineDryWall : DryWallSpectrum where
  wallPolarities := []
  wallCoordinationExcess := 0

theorem pristineDryWall_gap : dryWallSpectralGap pristineDryWall = 0 := by
  unfold dryWallSpectralGap pristineDryWall
  exact preferredAxisSpectralGap_nil

theorem pristineDryWall_dress : dryWallDress pristineDryWall = 1 := by
  unfold dryWallDress dryWallDefectStress
  rw [pristineDryWall_gap]
  unfold pristineDryWall
  simp [outsideLocalDefectChannel_zero]

/-- Dry-wall → tribo: wall spectral gap × wall defect stress feed the
shared tribo / localDefect factor (one wall spectrum ⇒ one channel). -/
def dryWallTriboChannel (W : DryWallSpectrum) : ℝ :=
  triboVoltageChannel (dryWallSpectralGap W) (dryWallDefectStress W)

theorem pristineDryWall_tribo : dryWallTriboChannel pristineDryWall = 1 := by
  unfold dryWallTriboChannel dryWallDefectStress
  rw [pristineDryWall_gap]
  unfold pristineDryWall
  simp [max_self, triboVoltageChannel_zero]

/-- Single-channel dry wall with unit excess: dress = `1 + γ·(4/8)`. -/
def unitExcessDryWall : DryWallSpectrum where
  wallPolarities := []
  wallCoordinationExcess := 1

theorem unitExcessDryWall_dress :
    dryWallDress unitExcessDryWall =
      1 + gamma_HQIV * strongChannelFraction := by
  unfold dryWallDress dryWallDefectStress unitExcessDryWall outsideLocalDefectChannel
    localCurvatureDefectExcess dryWallSpectralGap
  rw [preferredAxisSpectralGap_nil]
  simp

/-! ## Motif-local deltas (the small residual set) -/

/-- Motif-local variation only: dielectric `em`, network coordination excess,
and bond-summed contact surplus.  Gravity / bulk / wall are *not* here. -/
structure MotifLocalDelta where
  nDielectric : ℝ := 1
  coordinationExcess : ℝ := 0
  geffSum : ℝ := 0
  surplus : ℝ := 1

/-- Motif dress `em · localDefect(δ_motif) · contact`. -/
def motifLocalDress (D : MotifLocalDelta) : ℝ :=
  outsideEmChannel D.nDielectric *
    outsideLocalDefectChannel D.coordinationExcess *
    outsideContactChannel D.geffSum D.surplus

/-- Dilute motif: unit dielectric, no excess, no contact sum. -/
def diluteMotifLocalDelta : MotifLocalDelta :=
  { nDielectric := 1
    coordinationExcess := 0
    geffSum := 0
    surplus := 1 }

theorem diluteMotifLocalDress : motifLocalDress diluteMotifLocalDelta = 1 := by
  unfold motifLocalDress diluteMotifLocalDelta outsideContactChannel
  rw [outsideEmChannel_unit, outsideLocalDefectChannel_zero, outsideGeffSurplus_base]
  ring

/-! ## Reduced product -/

/-- Full reduced outside dress: ambient × wall × motif. -/
def reducedOutsideDress (A : SharedAmbient) (W : DryWallSpectrum) (D : MotifLocalDelta) : ℝ :=
  sharedAmbientDress A * dryWallDress W * motifLocalDress D

/-- Dilute ambient + pristine wall + dilute motif recovers identity. -/
theorem reducedOutsideDress_dilute_pristine :
    reducedOutsideDress diluteSharedAmbient pristineDryWall diluteMotifLocalDelta = 1 := by
  unfold reducedOutsideDress
  rw [diluteSharedAmbient_dress, pristineDryWall_dress, diluteMotifLocalDress]
  ring

/-- With shared ambient and fixed wall, motif comparisons reduce to
`motifLocalDress` alone — gravity and bulk cancel in ratios. -/
theorem reducedOutsideDress_motif_ratio
    (A : SharedAmbient) (W : DryWallSpectrum) (D₁ D₂ : MotifLocalDelta)
    (hA : sharedAmbientDress A ≠ 0) (hW : dryWallDress W ≠ 0)
    (hD2 : motifLocalDress D₂ ≠ 0) :
    reducedOutsideDress A W D₁ / reducedOutsideDress A W D₂ =
      motifLocalDress D₁ / motifLocalDress D₂ := by
  unfold reducedOutsideDress
  field_simp [hA, hW, hD2]

/-- Build a classical OutsideContactLedger from the reduced split.
Wall defect and motif defect add into the single localDefect channel;
ambient fills grav/bulk; motif fills em/contact. -/
def outsideContactLedgerFromReduced
    (A : SharedAmbient) (W : DryWallSpectrum) (D : MotifLocalDelta) :
    OutsideContactLedger where
  grav := outsideGravityGeffModulator ⟨A.phiEpsilon⟩
  em := outsideEmChannel D.nDielectric
  bulk := outsideBulkChannel A.bulkTarget A.rhoBulk
  localDefect :=
    outsideLocalDefectChannel (dryWallDefectStress W + D.coordinationExcess)
  contact := outsideContactChannel D.geffSum D.surplus

/-- When wall is pristine, the ledger localDefect is exactly the motif excess. -/
theorem outsideContactLedgerFromReduced_pristine_wall
    (A : SharedAmbient) (D : MotifLocalDelta) :
    (outsideContactLedgerFromReduced A pristineDryWall D).localDefect =
      outsideLocalDefectChannel D.coordinationExcess := by
  unfold outsideContactLedgerFromReduced dryWallDefectStress dryWallSpectralGap
    pristineDryWall
  simp [preferredAxisSpectralGap_nil]

/-- Electro-contact with reduced outside × unstressed voltage. -/
def reducedElectroContactDress
    (A : SharedAmbient) (W : DryWallSpectrum) (D : MotifLocalDelta) : ℝ :=
  outsideContactLedgerDress (outsideContactLedgerFromReduced A W D) *
    voltageGenerationLedgerDress unstressedVoltageGenerationLedger

theorem reducedElectroContactDress_unstressed
    (A : SharedAmbient) (W : DryWallSpectrum) (D : MotifLocalDelta) :
    reducedElectroContactDress A W D =
      outsideContactLedgerDress (outsideContactLedgerFromReduced A W D) := by
  unfold reducedElectroContactDress
  rw [unstressedVoltageGenerationLedger_dress]
  ring

/-! ## Spectroscopy pin into motif em (opens em; does not freeze ambient/wall) -/

/-- Invert an in-bracket spectral pin `A = ω*` into Clausius–Mossotti weight
`s* = log(A/ω_d) / log(ω_c/ω_d)` when the bracket is nontrivial.
Assay pin — not a fitted coefficient. -/
def spectralConcentrationWeight (omegaPin omegaDiffuse omegaConcentrated : ℝ) : ℝ :=
  if omegaDiffuse ≤ 0 ∨ omegaConcentrated ≤ omegaDiffuse then 0
  else
    clampUnitStress (
      Real.log (omegaPin / omegaDiffuse) /
        Real.log (omegaConcentrated / omegaDiffuse))

/-- Electric channel directly from concentration weight `s`
(avoids reconstructing `n` when the pin already supplies `s`). -/
def outsideEmFromConcentrationWeight (s : ℝ) : ℝ :=
  1 + strongChannelFraction * clampUnitStress s

theorem outsideEmFromConcentrationWeight_zero :
    outsideEmFromConcentrationWeight 0 = 1 := by
  unfold outsideEmFromConcentrationWeight
  rw [clampUnitStress_zero]
  ring

/-- Motif delta with em from a spectroscopy pin; other motif slots free. -/
def motifLocalDeltaFromSpectralPin
    (omegaPin omegaDiffuse omegaConcentrated δ geffSum surplus : ℝ) :
    MotifLocalDelta where
  nDielectric :=
    -- recover n from s via n = (1+2s)/(1−s) when s < 1; at s=0 this is n=1
    let s := spectralConcentrationWeight omegaPin omegaDiffuse omegaConcentrated
    let sc := clampUnitStress s
    if sc ≥ 1 then 1 + 2 * sc  -- saturated sentinel; em uses s directly in practice
    else (1 + 2 * sc) / max (1 - sc) 1e-12
  coordinationExcess := δ
  geffSum := geffSum
  surplus := surplus

/-- Motif dress using spectral `s` directly for em (preferred application path). -/
def motifLocalDressFromSpectralWeight
    (s δ geffSum surplus : ℝ) : ℝ :=
  outsideEmFromConcentrationWeight s *
    outsideLocalDefectChannel δ *
    outsideContactChannel geffSum surplus

theorem motifLocalDressFromSpectralWeight_zero_s (δ geffSum surplus : ℝ) :
    motifLocalDressFromSpectralWeight 0 δ geffSum surplus =
      outsideLocalDefectChannel δ * outsideContactChannel geffSum surplus := by
  unfold motifLocalDressFromSpectralWeight
  rw [outsideEmFromConcentrationWeight_zero]
  ring

/-! ## Mass scale anchor with EM (BE) feedback into contact length -/

/-- Contact-length feedback from the electric / BE dress:
`r_eff = r_bare · em^α` with lattice `α = 3/5`.

Mass remains the in-situ scale anchor for converting packing → density; the EM
channel (from binding / dielectric / spectral pin) expands the contact scale
instead of freezing the ledger at dilute identity.  At `em = 1` this is a no-op. -/
def contactLengthFromEmFeedback (rBare em : ℝ) : ℝ :=
  rBare * em ^ alpha

theorem contactLengthFromEmFeedback_unit (rBare : ℝ) :
    contactLengthFromEmFeedback rBare 1 = rBare := by
  unfold contactLengthFromEmFeedback
  simp [Real.one_rpow]

/-- Volumetric density scales as `1/r³`, so EM length feedback multiplies ρ by
`em^(-3α)` when mass is held fixed. -/
def volumetricDensityEmFeedbackFactor (em : ℝ) : ℝ :=
  (em ^ alpha) ^ (-(3 : ℝ))

theorem volumetricDensityEmFeedbackFactor_unit :
    volumetricDensityEmFeedbackFactor 1 = 1 := by
  unfold volumetricDensityEmFeedbackFactor
  simp [Real.one_rpow]

/-- Areal density scales as `1/r²`, so EM length feedback multiplies σ by
`em^(-2α)` when mass is held fixed. -/
def arealDensityEmFeedbackFactor (em : ℝ) : ℝ :=
  (em ^ alpha) ^ (-(2 : ℝ))

theorem arealDensityEmFeedbackFactor_unit :
    arealDensityEmFeedbackFactor 1 = 1 := by
  unfold arealDensityEmFeedbackFactor
  simp [Real.one_rpow]

/-- Dressed volumetric density from bare packing density and EM channel. -/
def volumetricDensityWithEmFeedback (ρBare em : ℝ) : ℝ :=
  ρBare * volumetricDensityEmFeedbackFactor em

/-- Dressed areal density from bare packing density and EM channel. -/
def arealDensityWithEmFeedback (σBare em : ℝ) : ℝ :=
  σBare * arealDensityEmFeedbackFactor em

theorem volumetricDensityWithEmFeedback_unit (ρBare : ℝ) :
    volumetricDensityWithEmFeedback ρBare 1 = ρBare := by
  unfold volumetricDensityWithEmFeedback
  rw [volumetricDensityEmFeedbackFactor_unit]
  ring

theorem arealDensityWithEmFeedback_unit (σBare : ℝ) :
    arealDensityWithEmFeedback σBare 1 = σBare := by
  unfold arealDensityWithEmFeedback
  rw [arealDensityEmFeedbackFactor_unit]
  ring

/-- Length feedback and density feedback are consistent for `em > 0`:
`ρ(r·em^α) = ρ(r) / (em^α)³`. -/
theorem volumetric_density_consistent_with_length_feedback
    (ρBare em : ℝ) (hem : 0 < em) :
    volumetricDensityWithEmFeedback ρBare em =
      ρBare / (em ^ alpha) ^ (3 : ℝ) := by
  unfold volumetricDensityWithEmFeedback volumetricDensityEmFeedbackFactor
  have hpos : 0 < em ^ alpha := Real.rpow_pos_of_pos hem _
  rw [Real.rpow_neg (le_of_lt hpos)]
  ring

/-! ## Crystal spectral gap (DFT optical/electronic slot)

Preferred-axis spectral gap of contact polarities, dressed by Clausius–Mossotti
optical participation and the ionic optical softener — same matrix gap as
molecular preferred-axis selection, read on the crystal contact spectrum.

Python: ``scripts/hqiv_contact_force_readout.py`` / ``crystal_spectral_gap``.
-/

/-- Crystal spectral gap from contact polarity spectrum:
`g · max(CM(n), 0) · ionicOpticalGapSoftener(δ²)`.
Pristine / equal-bond spectra give `g = 0` (metallic continuum or
homopolar network); a unique polar channel gives unit gap before optical dress. -/
noncomputable def crystalSpectralGap
    (contactPolarities : List ℝ) (nDielectric ionicCharacter : ℝ) : ℝ :=
  preferredAxisSpectralGap contactPolarities *
    max (clausiusMossottiOpticalWeight nDielectric) 0 *
    ionicOpticalGapSoftener ionicCharacter

/-- Empty polarity spectrum ⇒ zero crystal gap. -/
theorem crystalSpectralGap_nil (nDielectric ionicCharacter : ℝ) :
    crystalSpectralGap [] nDielectric ionicCharacter = 0 := by
  unfold crystalSpectralGap
  rw [preferredAxisSpectralGap_nil]
  ring

/-- Zero ionic character leaves the softener at identity. -/
theorem crystalSpectralGap_zero_ionic
    (contactPolarities : List ℝ) (nDielectric : ℝ) :
    crystalSpectralGap contactPolarities nDielectric 0 =
      preferredAxisSpectralGap contactPolarities *
        max (clausiusMossottiOpticalWeight nDielectric) 0 := by
  unfold crystalSpectralGap
  rw [ionicOpticalGapSoftener_zero]
  ring

/-! ## Discrete Brillouin-zone electronic bands (tight-binding slot)

Not continuum DFT \(E(\mathbf{k})\): a two-band contact chain on the same
dimensionless ``ka ∈ [0, π]`` path as the phonon dispersion, with hopping and
gap from the crystal spectral-gap / Rydberg contact scale.

\[
  E_c = R_\infty\,\alpha\,(1+\tfrac{4}{8})/(1+r/a_0),\quad
  t = \tfrac{4}{8}\,E_c/\mathrm{CN},\quad
  E_g =
  \begin{cases}
    g\cdot R_\infty/\gamma & g>0 \text{ (polar)}\\
    \alpha\,E_c & \text{homopolar covalent}\\
    0 & \text{metallic}
  \end{cases},\quad
  \varepsilon(k)=\sqrt{(E_g/2)^2+(2t\sin(ka/2))^2}.
\]

Valence / conduction = \(\mp\varepsilon(k)\).  Zone edge ``ka=π``.

Python: ``scripts/hqiv_discrete_bz_band_readout.py``.
-/

/-- Bohr radius [Å] (CODATA). -/
def bohrRadiusAngstrom : ℝ := 0.529177210903

/-- Contact electronic scale [eV]:
``E_c = R_∞ · α · (1 + 4/8) / (1 + r/a₀)``. -/
noncomputable def contactElectronicScaleEv (contactDistAng : ℝ) : ℝ :=
  rydbergEv * alpha * (1 + strongChannelFraction) /
    (1 + max contactDistAng 0 / bohrRadiusAngstrom)

/-- Discrete band hopping [eV]: ``t = (4/8) · E_c / max(CN, 1)``. -/
noncomputable def discreteBandHoppingEv (contactDistAng nCoord : ℝ) : ℝ :=
  strongChannelFraction * contactElectronicScaleEv contactDistAng / max nCoord 1

/-- Discrete band gap [eV] from axis gap / covalent flag.
Polar: ``g · R_∞ / γ``; homopolar covalent: ``α · E_c``; metallic: ``0``. -/
noncomputable def discreteBandGapEv
    (axisGap contactDistAng : ℝ) (covalent : Bool) : ℝ :=
  if 0 < axisGap then axisGap * rydbergEv / gamma_HQIV
  else if covalent then alpha * contactElectronicScaleEv contactDistAng
  else 0

/-- Two-band dispersion magnitude [eV]:
``ε(k) = √((E_g/2)² + (2 t sin(ka/2))²)``. -/
noncomputable def discreteBandDispersionEv (bandGap hopping ka : ℝ) : ℝ :=
  Real.sqrt ((bandGap / 2) ^ 2 + (2 * hopping * Real.sin (ka / 2)) ^ 2)

/-- Conduction branch ``+ε(k)``. -/
noncomputable def discreteConductionBandEv (bandGap hopping ka : ℝ) : ℝ :=
  discreteBandDispersionEv bandGap hopping ka

/-- Valence branch ``−ε(k)``. -/
noncomputable def discreteValenceBandEv (bandGap hopping ka : ℝ) : ℝ :=
  -discreteBandDispersionEv bandGap hopping ka

/-- Γ-point gap = ``E_g`` (full valence–conduction separation). -/
noncomputable def discreteBandGapAtGamma (bandGap : ℝ) : ℝ :=
  abs bandGap

/-! ## Multi-orbital discrete bands (s / pσ / pπ Extended-Hückel slot)

Still discrete: same ``ka ∈ [0, π]`` contact chain, now with three orbital
channels from angular degeneracy ``2ℓ+1`` (s:1, p:3) and HQIV hoppings

\[
  t_{ss}=t,\quad t_{pp}=\gamma t,\quad t_{sp}=\sqrt{t_{ss}t_{pp}},\quad
  t_{\pi}=(4/8)\,t_{pp}.
\]

Insulator (``E_g>0``) keeps the two-band Γ gap:
``H_s=-E_g/2+2t_{ss}(\cos ka-1)``, ``H_p=+E_g/2+2t_{pp}(\cos ka-1)``,
``V=2t_{sp}|\sin(ka/2)|``, hybrid ``ε_±``, and ``H_π`` parallel to ``H_p``
with ``t_π``.  Metal (``E_g=0``) uses pure ``2t\cos ka`` (finite bandwidth,
zero insulating gap).

Python: ``scripts/hqiv_multi_orbital_bz_readout.py``.
-/

/-- ``t_ss`` = base discrete hopping. -/
noncomputable def multiOrbitalHoppingSS (contactDistAng nCoord : ℝ) : ℝ :=
  discreteBandHoppingEv contactDistAng nCoord

/-- ``t_pp = γ · t_ss``. -/
noncomputable def multiOrbitalHoppingPP (contactDistAng nCoord : ℝ) : ℝ :=
  gamma_HQIV * multiOrbitalHoppingSS contactDistAng nCoord

/-- ``t_sp = √(t_ss · t_pp)`` (geometric-mean σ mixing). -/
noncomputable def multiOrbitalHoppingSP (contactDistAng nCoord : ℝ) : ℝ :=
  Real.sqrt (
    multiOrbitalHoppingSS contactDistAng nCoord *
      multiOrbitalHoppingPP contactDistAng nCoord)

/-- ``t_π = (4/8) · t_pp``. -/
noncomputable def multiOrbitalHoppingPi (contactDistAng nCoord : ℝ) : ℝ :=
  strongChannelFraction * multiOrbitalHoppingPP contactDistAng nCoord

/-- On-site s / p levels for insulator: ``∓ E_g/2``. -/
noncomputable def multiOrbitalOnsiteS (bandGap : ℝ) : ℝ := -bandGap / 2
noncomputable def multiOrbitalOnsiteP (bandGap : ℝ) : ℝ := bandGap / 2

/-- Diagonal s (or p) channel: ``ε₀ + 2 t (cos(ka) − 1)`` (insulator Γ pin). -/
noncomputable def multiOrbitalDiagonalInsulator (onsite hopping ka : ℝ) : ℝ :=
  onsite + 2 * hopping * (Real.cos ka - 1)

/-- Diagonal metal channel: ``2 t cos(ka)``. -/
noncomputable def multiOrbitalDiagonalMetal (hopping ka : ℝ) : ℝ :=
  2 * hopping * Real.cos ka

/-- Off-diagonal s–pσ mixing: ``2 t_sp |sin(ka/2)|``. -/
noncomputable def multiOrbitalMixingV (hoppingSP ka : ℝ) : ℝ :=
  2 * hoppingSP * |Real.sin (ka / 2)|

/-- Hybrid σ eigenvalues ``mid ± √((Δ/2)² + V²)``. -/
noncomputable def multiOrbitalHybridLower (Hs Hp V : ℝ) : ℝ :=
  let mid := (Hs + Hp) / 2
  let half := Real.sqrt (((Hs - Hp) / 2) ^ 2 + V ^ 2)
  mid - half

noncomputable def multiOrbitalHybridUpper (Hs Hp V : ℝ) : ℝ :=
  let mid := (Hs + Hp) / 2
  let half := Real.sqrt (((Hs - Hp) / 2) ^ 2 + V ^ 2)
  mid + half

/-- Insulator multi-orbital bundle at wavevector ``ka``. -/
noncomputable def multiOrbitalInsulatorAtKa
    (bandGap tSS tPP tSP tPi ka : ℝ) : ℝ × ℝ × ℝ :=
  let Hs := multiOrbitalDiagonalInsulator (multiOrbitalOnsiteS bandGap) tSS ka
  let Hp := multiOrbitalDiagonalInsulator (multiOrbitalOnsiteP bandGap) tPP ka
  let V := multiOrbitalMixingV tSP ka
  let Hpi := multiOrbitalDiagonalInsulator (multiOrbitalOnsiteP bandGap) tPi ka
  (multiOrbitalHybridLower Hs Hp V, multiOrbitalHybridUpper Hs Hp V, Hpi)

/-- Metal multi-orbital bundle at wavevector ``ka``. -/
noncomputable def multiOrbitalMetalAtKa
    (tSS tPP tSP tPi ka : ℝ) : ℝ × ℝ × ℝ :=
  let Hs := multiOrbitalDiagonalMetal tSS ka
  let Hp := multiOrbitalDiagonalMetal tPP ka
  let V := multiOrbitalMixingV tSP ka
  let Hpi := multiOrbitalDiagonalMetal tPi ka
  (multiOrbitalHybridLower Hs Hp V, multiOrbitalHybridUpper Hs Hp V, Hpi)

/-! ## Discrete SCF fixed point (charge dress on EH bands)

Not continuum Fock/KS SCF: a discrete fixed point on the same EH contact
chain, mirroring piezo↔stiffness / homogeneous-feedback loops.

Charge excess from ionic character × contact/gap softener:
``δ = clamp01(ι · γ · E_c / (E_g + E_c))``.
Dress ``f = 1 + (4/8)·δ`` widens the gap and softens hoppings:
``E_g' = f·E_g``, ``t' = t/f``.
Mixing step ``δ ← (1−α)·δ + α·δ_new`` (HQIV α as under-relaxation).
Covalent / metallic (ι=0) is identity (δ=0, f=1).

Python: ``scripts/hqiv_discrete_scf_readout.py``.
-/

/-- Charge excess from ionic character and contact/gap softener. -/
noncomputable def discreteScfChargeExcess
    (ionicCharacter contactScaleEv bandGapEv : ℝ) : ℝ :=
  let ι := max 0 (min 1 ionicCharacter)
  let soft := contactScaleEv / max (bandGapEv + contactScaleEv) 1e-9
  max 0 (min 1 (ι * gamma_HQIV * soft))

/-- SCF dress ``f = 1 + (4/8)·δ``. -/
noncomputable def discreteScfDress (chargeExcess : ℝ) : ℝ :=
  1 + strongChannelFraction * max 0 (min 1 chargeExcess)

/-- Dressed gap ``E_g' = f · E_g``. -/
noncomputable def discreteScfDressedGap (bandGap dress : ℝ) : ℝ :=
  dress * bandGap

/-- Softened hopping ``t' = t / f``. -/
noncomputable def discreteScfDressedHopping (hopping dress : ℝ) : ℝ :=
  hopping / max dress 1e-9

/-- Under-relaxed charge update ``(1−α)·δ + α·δ_new``. -/
noncomputable def discreteScfMixCharge (deltaOld deltaNew : ℝ) : ℝ :=
  (1 - alpha) * deltaOld + alpha * deltaNew

/-- One SCF map step: (δ, E_g, t) → (δ', E_g', t'). -/
noncomputable def discreteScfStep
    (ionicCharacter contactScaleEv bandGap hopping chargeExcess : ℝ) :
    ℝ × ℝ × ℝ :=
  let dress := discreteScfDress chargeExcess
  let eg' := discreteScfDressedGap bandGap dress
  let t' := discreteScfDressedHopping hopping dress
  let δ_new := discreteScfChargeExcess ionicCharacter contactScaleEv eg'
  let δ' := discreteScfMixCharge chargeExcess δ_new
  (δ', eg', t')

theorem discreteScfDress_zero : discreteScfDress 0 = 1 := by
  unfold discreteScfDress; simp

theorem discreteScfChargeExcess_zero_ionic (contactScaleEv bandGapEv : ℝ) :
    discreteScfChargeExcess 0 contactScaleEv bandGapEv = 0 := by
  unfold discreteScfChargeExcess
  simp

/-! ## Discrete Fock matrix (same fixed point, explicit \(F[P]\))

Not continuum AO Fock/KS: a \(2\times 2\) σ Fock on \(\{s,p_\sigma\}\) plus a
π channel, built from the EH core and the same charge dress \(\delta,f\).

Core at \(\Gamma\): \(H_s=-E_g/2\), \(H_p=+E_g/2\), \(V=0\) (insulator pin).
Occupations \(n_s,n_p\in[0,1]\) (valence projector on the lower hybrid).
Hartree \(J_\mu=(4/8)\,U\,n_\mu\) with \(U=\gamma E_c\delta\);
exchange \(K=\alpha E_c\delta\); then
\[
  F_s=f H_s+J_s-(4/8)K n_s,\quad
  F_p=f H_p+J_p-(4/8)K n_p,\quad
  F_{sp}=-(4/8)K\sqrt{n_s n_p}.
\]
The charge map is identical to ``discreteScfStep``: \(\delta\) updates from
the dressed EH gap \(f\cdot E_g\), not from the Fock eigenvalue gap.  Fock
eigenvalues are a separate EH readout on \(\{s,p_\sigma\}\).  Zero ionic /
zero \(\delta\) recovers the EH core (identity Fock).

Python: ``scripts/hqiv_discrete_fock_readout.py``.
-/

/-- Hartree scale ``U = γ · E_c · δ``. -/
noncomputable def discreteFockHartreeU
    (contactScaleEv chargeExcess : ℝ) : ℝ :=
  gamma_HQIV * contactScaleEv * max 0 (min 1 chargeExcess)

/-- Exchange scale ``K = α · E_c · δ``. -/
noncomputable def discreteFockExchangeK
    (contactScaleEv chargeExcess : ℝ) : ℝ :=
  alpha * contactScaleEv * max 0 (min 1 chargeExcess)

/-- Diagonal Hartree ``J = (4/8) · U · n``. -/
noncomputable def discreteFockHartreeJ (U occupation : ℝ) : ℝ :=
  strongChannelFraction * U * max 0 (min 1 occupation)

/-- Core on-site dressed by SCF factor ``f``. -/
noncomputable def discreteFockCoreS (bandGap dress : ℝ) : ℝ :=
  dress * multiOrbitalOnsiteS bandGap

noncomputable def discreteFockCoreP (bandGap dress : ℝ) : ℝ :=
  dress * multiOrbitalOnsiteP bandGap

/-- Fock diagonal ``F_μ = f H_μ + J_μ − (4/8) K n_μ``. -/
noncomputable def discreteFockDiag
    (coreJ hartreeJ exchangeK occupation : ℝ) : ℝ :=
  coreJ + hartreeJ - strongChannelFraction * exchangeK * max 0 (min 1 occupation)

/-- Fock off-diagonal ``F_sp = −(4/8) K √(n_s n_p)``. -/
noncomputable def discreteFockOffDiag
    (exchangeK nS nP : ℝ) : ℝ :=
  -strongChannelFraction * exchangeK *
    Real.sqrt (max 0 (min 1 nS) * max 0 (min 1 nP))

/-- Build (F_s, F_p, F_sp) from bare gap, contact scale, δ, and occupations. -/
noncomputable def discreteFockMatrix
    (bandGap contactScaleEv chargeExcess nS nP : ℝ) : ℝ × ℝ × ℝ :=
  let dress := discreteScfDress chargeExcess
  let U := discreteFockHartreeU contactScaleEv chargeExcess
  let K := discreteFockExchangeK contactScaleEv chargeExcess
  let Hs := discreteFockCoreS bandGap dress
  let Hp := discreteFockCoreP bandGap dress
  let Js := discreteFockHartreeJ U nS
  let Jp := discreteFockHartreeJ U nP
  (discreteFockDiag Hs Js K nS,
    discreteFockDiag Hp Jp K nP,
    discreteFockOffDiag K nS nP)

/-- Fock eigenvalues (lower, upper) from the 2×2 σ block. -/
noncomputable def discreteFockEigenvalues (Fs Fp Fsp : ℝ) : ℝ × ℝ :=
  (multiOrbitalHybridLower Fs Fp Fsp, multiOrbitalHybridUpper Fs Fp Fsp)

/-- Fock gap = upper − lower. -/
noncomputable def discreteFockGap (Fs Fp Fsp : ℝ) : ℝ :=
  let ev := discreteFockEigenvalues Fs Fp Fsp
  ev.2 - ev.1

/--
One Fock charge step: same δ map as ``discreteScfStep`` (dressed EH gap),
returning the updated δ together with the Fock matrix at the old δ.
-/
noncomputable def discreteFockStep
    (ionicCharacter contactScaleEv bandGap chargeExcess nS nP : ℝ) :
    ℝ × (ℝ × ℝ × ℝ) :=
  let dress := discreteScfDress chargeExcess
  let eg' := discreteScfDressedGap bandGap dress
  let δ_new := discreteScfChargeExcess ionicCharacter contactScaleEv eg'
  let δ' := discreteScfMixCharge chargeExcess δ_new
  let F := discreteFockMatrix bandGap contactScaleEv chargeExcess nS nP
  (δ', F)

theorem discreteFockHartreeU_zero (contactScaleEv : ℝ) :
    discreteFockHartreeU contactScaleEv 0 = 0 := by
  unfold discreteFockHartreeU; simp

theorem discreteFockExchangeK_zero (contactScaleEv : ℝ) :
    discreteFockExchangeK contactScaleEv 0 = 0 := by
  unfold discreteFockExchangeK; simp

/-- At δ=0 the Fock matrix collapses to the dressed EH core (dress=1). -/
theorem discreteFockMatrix_zero_delta (bandGap contactScaleEv nS nP : ℝ) :
    discreteFockMatrix bandGap contactScaleEv 0 nS nP =
      (multiOrbitalOnsiteS bandGap, multiOrbitalOnsiteP bandGap, 0) := by
  unfold discreteFockMatrix discreteFockHartreeU discreteFockExchangeK
    discreteFockHartreeJ discreteFockCoreS discreteFockCoreP
    discreteFockDiag discreteFockOffDiag discreteScfDress
  simp [multiOrbitalOnsiteS, multiOrbitalOnsiteP]

/-! ## Discrete Kohn–Sham matrix (local XC, same δ/f map)

Same Hartree \(J\) and dress \(f\) as Fock; nonlocal exchange is replaced by a
local XC potential on the EH occupations:
\[
  V_{\mathrm{xc}}=-\alpha E_c\delta,\qquad
  V_{\mathrm{xc},\mu}=\tfrac{4}{8}\,V_{\mathrm{xc}}\,n_\mu,\qquad
  K_\mu=f H_\mu+J_\mu+V_{\mathrm{xc},\mu},\qquad
  K_{sp}=0.
\]
Charge updates from the dressed EH gap (identical to ``discreteScfStep``).
\(\delta=0\) recovers the EH core.

Python: ``scripts/hqiv_discrete_ks_readout.py``.
-/

/-- Local XC scale ``V_xc = −α · E_c · δ``. -/
noncomputable def discreteKsXcScale
    (contactScaleEv chargeExcess : ℝ) : ℝ :=
  -alpha * contactScaleEv * max 0 (min 1 chargeExcess)

/-- Local XC on orbital ``μ``: ``(4/8) · V_xc · n_μ``. -/
noncomputable def discreteKsXcOrbital (Vxc occupation : ℝ) : ℝ :=
  strongChannelFraction * Vxc * max 0 (min 1 occupation)

/-- KS diagonal ``K_μ = f H_μ + J_μ + V_xc,μ``. -/
noncomputable def discreteKsDiag
    (coreJ hartreeJ VxcOrb : ℝ) : ℝ :=
  coreJ + hartreeJ + VxcOrb

/-- Build (K_s, K_p, K_sp=0) from bare gap, contact scale, δ, occupations. -/
noncomputable def discreteKsMatrix
    (bandGap contactScaleEv chargeExcess nS nP : ℝ) : ℝ × ℝ × ℝ :=
  let dress := discreteScfDress chargeExcess
  let U := discreteFockHartreeU contactScaleEv chargeExcess
  let Vxc := discreteKsXcScale contactScaleEv chargeExcess
  let Hs := discreteFockCoreS bandGap dress
  let Hp := discreteFockCoreP bandGap dress
  let Js := discreteFockHartreeJ U nS
  let Jp := discreteFockHartreeJ U nP
  (discreteKsDiag Hs Js (discreteKsXcOrbital Vxc nS),
    discreteKsDiag Hp Jp (discreteKsXcOrbital Vxc nP),
    (0 : ℝ))

/-- One KS charge step: same δ map as ``discreteScfStep``. -/
noncomputable def discreteKsStep
    (ionicCharacter contactScaleEv bandGap chargeExcess nS nP : ℝ) :
    ℝ × (ℝ × ℝ × ℝ) :=
  let dress := discreteScfDress chargeExcess
  let eg' := discreteScfDressedGap bandGap dress
  let δ_new := discreteScfChargeExcess ionicCharacter contactScaleEv eg'
  let δ' := discreteScfMixCharge chargeExcess δ_new
  let K := discreteKsMatrix bandGap contactScaleEv chargeExcess nS nP
  (δ', K)

theorem discreteKsXcScale_zero (contactScaleEv : ℝ) :
    discreteKsXcScale contactScaleEv 0 = 0 := by
  unfold discreteKsXcScale; simp

theorem discreteKsMatrix_zero_delta (bandGap contactScaleEv nS nP : ℝ) :
    discreteKsMatrix bandGap contactScaleEv 0 nS nP =
      (multiOrbitalOnsiteS bandGap, multiOrbitalOnsiteP bandGap, 0) := by
  unfold discreteKsMatrix discreteFockHartreeU discreteKsXcScale
    discreteFockHartreeJ discreteKsXcOrbital discreteFockCoreS discreteFockCoreP
    discreteKsDiag discreteScfDress
  simp [multiOrbitalOnsiteS, multiOrbitalOnsiteP]

/-! ## Discrete AO integrals on the EH \(\{s,p_\sigma\}\) basis

Overlap / kinetic / nuclear / two-electron slots from the contact scale
\(E_c\) and softener \(s=1/(1+r/a_0)\).  No fitted GTO exponents.
\[
  S_{ss}=S_{pp}=1,\quad S_{sp}=\alpha\,s,
\]
\[
  T_{ss}=E_c,\quad T_{pp}=\gamma E_c,\quad
  T_{sp}=\tfrac{4}{8}\alpha\,s\,E_c,
\]
\[
  V_{\mu\nu}=-(1+\tfrac{4}{8})E_c\,S_{\mu\nu},
\]
\[
  (ss|ss)=(pp|pp)=\gamma E_c,\quad
  (ss|pp)=\tfrac{4}{8}\gamma E_c,\quad
  (sp|sp)=\alpha E_c.
\]

Python: ``scripts/hqiv_discrete_ao_integrals_readout.py``.
-/

/-- Softener ``s = 1 / (1 + r/a₀)``. -/
noncomputable def discreteAoSoftener (contactDistAng : ℝ) : ℝ :=
  1 / (1 + max contactDistAng 0 / bohrRadiusAngstrom)

/-- Overlap ``S_sp = α · s`` (diagonal overlaps = 1). -/
noncomputable def discreteAoOverlapSP (contactDistAng : ℝ) : ℝ :=
  alpha * discreteAoSoftener contactDistAng

/-- Kinetic diagonal ``T_ss = E_c``. -/
noncomputable def discreteAoKineticSS (contactDistAng : ℝ) : ℝ :=
  contactElectronicScaleEv contactDistAng

/-- Kinetic diagonal ``T_pp = γ · E_c``. -/
noncomputable def discreteAoKineticPP (contactDistAng : ℝ) : ℝ :=
  gamma_HQIV * contactElectronicScaleEv contactDistAng

/-- Kinetic off-diagonal ``T_sp = (4/8)·α·s·E_c``. -/
noncomputable def discreteAoKineticSP (contactDistAng : ℝ) : ℝ :=
  strongChannelFraction * alpha * discreteAoSoftener contactDistAng *
    contactElectronicScaleEv contactDistAng

/-- Nuclear attraction ``V_μν = −(1+4/8)·E_c·S_μν``. -/
noncomputable def discreteAoNuclear
    (contactDistAng overlap : ℝ) : ℝ :=
  -(1 + strongChannelFraction) * contactElectronicScaleEv contactDistAng * overlap

/-- Two-electron Coulomb ``(ss|ss) = γ · E_c``. -/
noncomputable def discreteAoCoulombSS (contactDistAng : ℝ) : ℝ :=
  gamma_HQIV * contactElectronicScaleEv contactDistAng

/-- Two-electron ``(ss|pp) = (4/8)·γ·E_c``. -/
noncomputable def discreteAoCoulombSSPP (contactDistAng : ℝ) : ℝ :=
  strongChannelFraction * discreteAoCoulombSS contactDistAng

/-- Two-electron exchange-like ``(sp|sp) = α · E_c``. -/
noncomputable def discreteAoExchangeSPSP (contactDistAng : ℝ) : ℝ :=
  alpha * contactElectronicScaleEv contactDistAng

/-- Core Hamiltonian diagonal from T+V with unit overlap. -/
noncomputable def discreteAoCoreDiag
    (kinetic contactDistAng : ℝ) : ℝ :=
  kinetic + discreteAoNuclear contactDistAng 1

theorem discreteAoSoftener_zero_dist :
    discreteAoSoftener 0 = 1 := by
  unfold discreteAoSoftener; simp

theorem discreteAoOverlapSP_zero_dist :
    discreteAoOverlapSP 0 = alpha := by
  unfold discreteAoOverlapSP; rw [discreteAoSoftener_zero_dist]; ring

/-! ## Discrete core spectroscopy (XPS chemical shift)

Hydrogenic core binding on principal shell \(n\) with effective charge
\(Z_{\mathrm{eff}}=Z-\gamma\cdot(n_{\mathrm{occ}}-1)\) (same-shell monogamy
softener), dressed by the SCF factor \(f\):
\[
  E_{\mathrm{core}}=\frac{Z_{\mathrm{eff}}^{2}}{2n^{2}}\,\mathrm{Ha}\to\mathrm{eV},\qquad
  E_{\mathrm{XPS}}=f\cdot E_{\mathrm{core}},\qquad
  \Delta_{\mathrm{chem}}=\gamma E_c\delta.
\]
Valence IE is the \(n\) outermost case; core XPS uses \(n=1\).
NIST lines are quarantine only.

Python: ``scripts/hqiv_discrete_core_spectroscopy_readout.py``.
-/

/-- Same-shell core screening softener ``γ`` per co-occupied electron. -/
noncomputable def discreteCoreScreenPerElectron : ℝ := gamma_HQIV

/-- Effective nuclear charge for a core shell with ``nOcc`` electrons. -/
noncomputable def discreteCoreZeff (Z nOcc : ℝ) : ℝ :=
  max 1 (Z - discreteCoreScreenPerElectron * max 0 (nOcc - 1))

/-- Bare core binding [eV]: ``Z_eff² / (2 n²) · Ha→eV``. -/
noncomputable def discreteCoreBindingEv (Zeff nPrincipal : ℝ) : ℝ :=
  let n := max nPrincipal 1
  Zeff * Zeff / (2 * n * n) * Binding.hartreeToEv

/-- Chemical shift scale ``γ · E_c · δ``. -/
noncomputable def discreteCoreChemShiftEv
    (contactScaleEv chargeExcess : ℝ) : ℝ :=
  gamma_HQIV * contactScaleEv * max 0 (min 1 chargeExcess)

/-- XPS binding ``f · E_core`` (SCF dress on the bare core line). -/
noncomputable def discreteCoreXpsEv
    (coreBindEv chargeExcess : ℝ) : ℝ :=
  discreteScfDress chargeExcess * coreBindEv

theorem discreteCoreChemShift_zero (contactScaleEv : ℝ) :
    discreteCoreChemShiftEv contactScaleEv 0 = 0 := by
  unfold discreteCoreChemShiftEv; simp

theorem discreteCoreXps_zero_delta (coreBindEv : ℝ) :
    discreteCoreXpsEv coreBindEv 0 = coreBindEv := by
  unfold discreteCoreXpsEv; rw [discreteScfDress_zero]; ring

theorem discreteCoreZeff_single (Z : ℝ) (h : 1 ≤ Z) :
    discreteCoreZeff Z 1 = Z := by
  unfold discreteCoreZeff
  have h0 : max 0 ((1 : ℝ) - 1) = 0 := by norm_num
  rw [h0]
  simp only [mul_zero, sub_zero]
  exact max_eq_right h

end

end Hqiv.QuantumChemistry
