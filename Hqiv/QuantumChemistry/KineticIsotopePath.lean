import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.QuantumChemistry.BondRearrangementPath
import HqivSpine.Physics.Tunneling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Kinetic isotope effect on bond-rearrangement paths

The discrete path barrier \(B\) is mass-independent (coordination excess +
binding depth).  Isotope dependence enters only through the tunneling reduced
mass \(\mu\) in ``kappaForbidden`` / ``transmissionCoefficient``.

\[
  \mathrm{KIE} = \frac{T(\mu_{\mathrm{H}})}{T(\mu_{\mathrm{D}})} \ge 1
\]

when \(\mu_{\mathrm{H}} \le \mu_{\mathrm{D}}\) at fixed sub-barrier \((E,V,L)\).

Secondary (spectator) KIE softens the primary channel by the lattice factor
``γ``: ``KIE_sec = KIE_pri^γ`` (identity at KIE=1).

Python: ``scripts/hqiv_kinetic_isotope_readout.py`` (W4 / GMTKN H/D subset).
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open HqivSpine.Physics

noncomputable section

/-- Tunneling transmission at fixed barrier for a given reduced mass. -/
noncomputable def pathTunnelTransmission (μ E V L : ℝ) : ℝ :=
  transmissionCoefficient (kappaForbidden μ E V) L

/-- Kinetic isotope effect = light / heavy transmission (primary KIE). -/
noncomputable def pathKineticIsotopeEffect (μLight μHeavy E V L : ℝ) : ℝ :=
  pathTunnelTransmission μLight E V L / pathTunnelTransmission μHeavy E V L

/-- Secondary KIE softener: spectator-mass channel scaled by ``γ``.
``KIE_sec = exp(γ · log KIE_pri) = KIE_pri^γ`` (identity at KIE=1). -/
noncomputable def secondaryKineticIsotopeEffect (kiePrimary : ℝ) : ℝ :=
  if kiePrimary ≤ 0 then 0 else Real.exp (gamma_HQIV * Real.log kiePrimary)

/-- Path barrier as the tunneling height above the attempt energy:
``V = E + B`` with ``B = bondRearrangementPathBarrier``. -/
noncomputable def pathBarrierHeight (path : BondRearrangementPath) (E : ℝ) : ℝ :=
  E + bondRearrangementPathBarrier path

theorem pathKineticIsotopeEffect_ge_one
    (E V L : ℝ) (hL : 0 < L) (hEV : E ≤ V)
    {μH μD : ℝ} (hμ : 0 ≤ μH) (h : μH ≤ μD)
    (hD : 0 < pathTunnelTransmission μD E V L) :
    1 ≤ pathKineticIsotopeEffect μH μD E V L := by
  unfold pathKineticIsotopeEffect pathTunnelTransmission
  have hT := kineticIsotopeEffect_ge_one E V L hL hEV hμ h
  exact (one_le_div hD).mpr hT

/-- Harmonic saddle height candidate ``strong² · D`` (Morse F²/2k). -/
noncomputable def harmonicTunnelHeight (bindingEv : ℝ) : ℝ :=
  harmonicSaddleGateEv bindingEv

end

end Hqiv.QuantumChemistry
