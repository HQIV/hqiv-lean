import HqivSpine.Physics.Shell
import HqivSpine.Algebra.Closure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `HqivSpine.Physics.Binding` — the 8×8 composite-trace binding network

Binding at every scale is a **sum over the so(8) network**: the 28 generators
acting on the 8-component carrier state. We give the structural form:

* a per-generator composite-trace contribution against an 8-component state;
* a shell coupling `latticeSimplexCount(m) · α_eff(m)` per generator;
* the binding energy as the network sum, and composite mass = constituents − binding.

Everything is parameterized by `Fin 8` / `Fin 28` and the foundation-derived shell
constants. No numbers are injected here; concrete weights come from a state.
-/

namespace HqivSpine.Physics

open BigOperators

/-- **Dimension of so(8)** = `soDim carrierMultiplicity = 28`. -/
def so8Dim : ℕ := HqivSpine.Foundation.soDim HqivSpine.Foundation.carrierMultiplicity

theorem so8Dim_eq : so8Dim = 28 := HqivSpine.Foundation.soDim_carrier

/-- **8-component carrier state** (octonion-spinor). -/
abbrev OctonionState := Fin 8 → ℝ

/-- **Index set for the so(8) generators.** -/
abbrev So8Index := Fin 28

/-- **8×8 diagonal data** for a generator family: one diagonal entry per generator
and carrier index (the diagonal part of an 8×8 composite trace). -/
abbrev So8TraceDiagonal := So8Index → Fin 8 → ℝ

/-- **Composite-trace contribution** of generator `k` against a state `ψ`. -/
noncomputable def compositeTraceAtGenerator
    (diag : So8TraceDiagonal) (ψ : OctonionState) (k : So8Index) : ℝ :=
  ∑ i : Fin 8, diag k i * ψ i * ψ i

/-- **Network weight:** one coefficient per generator. -/
abbrev NetworkWeight := So8Index → ℝ

/-- **Network weight from composite traces.** -/
noncomputable def networkWeightFromCompositeTrace
    (diag : So8TraceDiagonal) (ψ : OctonionState) : NetworkWeight :=
  fun k => compositeTraceAtGenerator diag ψ k

/-- **Shell coupling per generator** = `latticeSimplexCount(m) · α_eff(m)`. -/
noncomputable def bindingCouplingAtShell (m : ℕ) (_k : So8Index) (c : ℝ := 1) : ℝ :=
  (latticeSimplexCount m : ℝ) * alphaEffAtShell m c

/-- **Binding energy as a sum over the so(8) network:** `∑_k w_k · coupling(m,k)`. -/
noncomputable def E_bind_from_network (m : ℕ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  ∑ k : So8Index, w k * bindingCouplingAtShell m k c

/-- **Binding energy from explicit composite traces.** -/
noncomputable def E_bind_from_composite_trace
    (m : ℕ) (diag : So8TraceDiagonal) (ψ : OctonionState) (c : ℝ := 1) : ℝ :=
  E_bind_from_network m (networkWeightFromCompositeTrace diag ψ) c

theorem E_bind_from_composite_trace_eq (m : ℕ) (diag : So8TraceDiagonal)
    (ψ : OctonionState) (c : ℝ) :
    E_bind_from_composite_trace m diag ψ c =
      ∑ k : So8Index, compositeTraceAtGenerator diag ψ k * bindingCouplingAtShell m k c := rfl

/-- **Composite mass = constituent mass − network binding.** -/
noncomputable def M_composite_from_network
    (m : ℕ) (M_constituent : ℝ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  M_constituent - E_bind_from_network m w c

theorem M_composite_from_network_eq (m : ℕ) (M_constituent : ℝ)
    (w : NetworkWeight) (c : ℝ) :
    M_composite_from_network m M_constituent w c =
      M_constituent - E_bind_from_network m w c := rfl

end HqivSpine.Physics
