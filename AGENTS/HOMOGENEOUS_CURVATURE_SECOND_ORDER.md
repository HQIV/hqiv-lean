# Homogeneous curvature second order (program)

**Status:** Scaffold — **not** the default GMTKN55 / melt pipeline yet.  
**Lean:** `Hqiv.Physics.HomogeneousCurvatureSecondOrder`  
**Python:** `scripts/hqiv_homogeneous_curvature_feedback.py`

## Problem with ρ-scaled κ₆ / G_eff alone

Medium density ρ (intermolecular contacts / 4) was a **proxy**. The next layer is:

1. Compute curvature of the **homogeneous** solution at bulk density ρ.
2. Feed **B_eff** directly back into the binding / melt equation (self-consistent).
3. Treat **nucleation sites** as local **δB** above the homogeneous background.

That is why nucleation matters: a defect, surface, or dust grain breaks homogeneity and raises local curvature before bulk phase stability.

## Equations (HQIV rationals)

| Symbol | Definition |
|--------|------------|
| **ρ** | Medium density ∈ [0,1] vs ice tetrahedral reference (4 contacts) |
| **B_hom(ξ, ρ)** | `1 + ρ·(B_curv(ξ) − 1)` — dilute → unity, bulk → full Casimir budget |
| **δB** | `γ·(4/8)·max(ρ_local − ρ_hom, 0)` — nucleation coordination excess |
| **B_eff** | `B_hom + δB` |
| **Feedback** | `(1 + κ(B_eff)·C_rel)·C₂(ξ)/C₂(ξ_lock)` |

**G_eff(θ)** at bonds uses the same ρ via `scale_outside_coupling_for_medium_density` on the contact network; surplus `outside_geff` inherits scaled bond θ sums.

**BBN precedent:** `bbn_binding_curvature_perturbation` already feeds binding-induced δ into shell opportunity — same **homogeneous + perturbation** pattern for cosmology.

## Self-consistent loop (target)

```
ρ_hom from phase / network
  → B_hom(ξ, ρ_hom)
  → κ feedback, G_eff, melt / binding readout
  → δ_binding (BBN-style or cluster release)
  → update δB at nucleation sites
  → repeat until B_eff stable
```

Python demo: `self_consistent_homogeneous_feedback()` (fixed small iteration count).

## Relation to other modules

| Module | Role |
|--------|------|
| `DynamicBindingChart` | First/second-order κ at ξ (chart default) |
| `HopfShellBeltramiMassBridge` | κ₆ = η·γ·C₂ matter fraction |
| `NuclearOutsideTemperatureDynamics` | Outside G_eff(1+ε) at contacts |
| `hqiv_thermodynamic_phase_from_tp` | Bulk melt uses ρ-scaled κ₆ (interim) |
| `hqiv_curvature_contact_network` | ρ from steric count; G_eff on bonds |
| `bulk_v2.closed_curvature_balance` | Homogeneous inside/outside T closure (ξ_lock hunt) |

## Not done yet

- Replace interim `curvature_second_order_scaled_for_medium_density` with full `bindingCurvatureFeedbackSecondOrderHomogeneous` on melt and chart.
- Lean proof: `bindingCurvatureFeedbackSecondOrderHomogeneous` → `dynamicBindingCurvatureFeedbackSecondOrderAtXi` when ρ=1 and δ=0 (modulo B_curv vs κ coupling normalization).
- Ice unit cell: ρ_hom from lattice, ρ_local at step edges / defects.
- Poisson bridge: `HQVMDiscretePoisson` `G_eff(φ)·δρ` with δρ from binding release on homogeneous slice.

## Commands

```bash
lake build Hqiv.Physics.HomogeneousCurvatureSecondOrder
python3 scripts/hqiv_homogeneous_curvature_feedback.py
python3 scripts/hqiv_homogeneous_curvature_feedback.py --json-out data/homogeneous_curvature_feedback.json
```
