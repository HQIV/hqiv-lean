# TUFT global hadron excitation readout

Single formula for baryon and meson excited masses — no per-particle operator menus.

## Formula

```text
m(ξ, channel) = g_chart(ξ) · [ 1 + (R_in(global) − 1) · G_twist(ξ) ]
```

| Ingredient | Source | Notes |
|------------|--------|-------|
| `g_chart` | vev baryon ground × `m_chart / m_heavy` | `TuftShellChart` |
| `G_twist` | 1-jet Fano detuning × `Ω_k`, unity at ξ_lock | per `(n, ℓ)` |
| `w_content` | `HadronMassReadout.tuftContentExcitationWeight` | 8/27 … 1 |
| `w_exc` | `HadronMassReadout.tuftExcitationCouplingWeight` | 8/9 mixed; 1−γ/(2(ℓ+1)) |
| `R_in` discrete | trapped inside at integer `m_mode` | full-closure mesons |
| `R_in` split | interp at `ξ_split − 1` | partial closure / baryon excitations |

## Split inversion (first principles)

Partial meson closure inverts content-weighted Beltrami steps on the trapped curve:

```text
Δξ = w · ΔM_Beltrami / (g · ∂R/∂m|_{m_ref})
∂R/∂m|_{m_ref} = R(m_ref+1, m_ref) − 1
ξ_split = ξ_chart + Δξ_rad + Δξ_orb
```

Lean: `TuftGlobalHadronReadout.tuftBeltramiDeltaToXiOffset`  
Python: `hqiv_continuous_shell_mass.beltrami_delta_to_xi_offset`

## Content weight (not PDG labels)

| Channel | `w` |
|---------|-----|
| Baryon | 1 |
| Light isovector (ρ) | 8/27 |
| Light isoscalar (ω) | (8/27)·(1 + γ/2) |
| Mixed strangeness (K*) | √(8/27) |
| Full s s̄ (φ) | 1 |

Isoscalar lift uses the same 1-jet Fano slope as channel twist (`γ/2`), not a fitted σ.

## Modules

| Layer | File |
|-------|------|
| Content geometry | `Hqiv/Physics/HadronMassReadout.lean` |
| Chart + Beltrami drum | `Hqiv/Physics/TuftShellChart.lean`, `HopfShellBeltramiMassBridge.lean` |
| Global readout | `Hqiv/Physics/TuftGlobalHadronReadout.lean` |
| Python anchor | `scripts/hqiv_tuft_global_hadron_readout.py` |
| PDG eval | `scripts/hqiv_tuft_mass_spectrum_pdg_eval.py` |

## Baryon chart slots @ ξ_lock (global readout)

| PDG tag | (n, ℓ) | J^P | branch | ratio |
|---------|--------|-----|--------|-------|
| Δ(1232) | (0,1) | 3/2+ | phase orbital | ~1.005 |
| N(1440) | (0,2) | 1/2+ | split orbital, w_exc=1 | ~1.006 |
| N(1520) | (1,1) | 3/2− | split mixed, w_exc=8/9 | ~0.996 |
| N(1680) | (0,3) | 5/2− | split orbital, w_exc=1−γ/8 | ~1.007 |
| N(1710) | (0,3) | 1/2+ | split orbital, w_exc=1 | ~1.015 |

Same `(n, ℓ)` with opposite parity (1680 vs 1710) splits via `tuftExcitationCouplingWeight`,
not a per-particle menu.

Meson vectors unchanged (~1%): ρ, ω, φ, K*.

## Verify

```bash
lake build Hqiv.Physics.TuftGlobalHadronReadout
PYTHONPATH=scripts python3 scripts/hqiv_tuft_global_hadron_readout.py
PYTHONPATH=scripts python3 scripts/test_hqiv_tuft_global_hadron_readout.py
```
