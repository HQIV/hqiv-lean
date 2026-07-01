import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.Binding

/-!
# `HqivSpine.Physics.Proton` — the proton as a now-slice readout

The proton is **not** the anchor. The anchor is the now slice (`NowSlice`), which
carries the curvature bookkeeping. The proton mass at the lock-in shell
`referenceM = 4` is a *readout*: the dimensionless now-scale `massUnit` times a
dimensionless proton factor, with the composite-trace binding network supplying
the `constituent − binding` structure.

This keeps the curvatures (`φ`, `Φ`, `Ω_k`) explicit instead of collapsing them
into one opaque MeV literal.
-/

namespace HqivSpine.Physics

/-- **Proton lock-in shell** = the anchor index. -/
def protonLockinShell : ℕ := referenceM

theorem protonLockinShell_eq_four : protonLockinShell = 4 := rfl

/-- **The proton mass as a now-slice readout:** `massUnit · (dimensionless proton
factor)`. The dimensionful scale comes entirely from the now slice. -/
noncomputable def protonReadout (s : NowSlice) (protonFactor : ℝ) : ℝ :=
  s.readout protonFactor

theorem protonReadout_eq (s : NowSlice) (protonFactor : ℝ) :
    protonReadout s protonFactor = s.massUnit * protonFactor := rfl

/-- The proton readout is positive on a forward-time weak-field slice with a
positive dimensionless factor. -/
theorem protonReadout_pos (s : NowSlice) (protonFactor : ℝ)
    (hPhi : 0 < 1 + s.bigPhi) (hphi : 0 ≤ s.phi) (ht : 0 ≤ s.apparentAge)
    (hfac : 0 < protonFactor) :
    0 < protonReadout s protonFactor := by
  rw [protonReadout_eq]
  exact mul_pos (s.massUnit_pos hPhi hphi ht) hfac

/-- A proton lock-in witness: a now slice plus a composite-trace state whose
`constituent − network binding` at the lock-in shell equals the now-slice readout. -/
structure ProtonLockin where
  slice : NowSlice
  protonFactor : ℝ
  constituent : ℝ
  diag : So8TraceDiagonal
  state : OctonionState
  coupling : ℝ := 1
  matches_readout :
    M_composite_from_network protonLockinShell constituent
      (networkWeightFromCompositeTrace diag state) coupling
      = protonReadout slice protonFactor

/-- **Readout ⇔ binding relation.** Fixing the proton at the now-slice readout at
shell `4` is equivalent to fixing the network binding at
`constituent − readout` — the only scale involved is the now slice, no extra free
numbers. -/
theorem proton_readout_iff_binding
    (s : NowSlice) (protonFactor constituent : ℝ) (w : NetworkWeight) (c : ℝ) :
    M_composite_from_network protonLockinShell constituent w c = protonReadout s protonFactor
      ↔ E_bind_from_network protonLockinShell w c
          = constituent - protonReadout s protonFactor := by
  unfold M_composite_from_network
  constructor <;> intro h <;> linarith

end HqivSpine.Physics
