# Alpha_EM Model Comparison (Python Harness)

**Status:** implemented 2026-06 — comparison harness + witness JSON + uniqueness audit.

## Artifacts

| Artifact | Path |
|----------|------|
| Comparison module | `scripts/hqiv_alpha_model_comparison.py` |
| Tests | `scripts/test_hqiv_alpha_model_comparison.py` |
| Witness JSON | `data/alpha_model_comparison_witnesses.json` |
| **IR-running bridge** | `scripts/hqiv_alpha_ir_running.py` |
| **IR-running tests** | `scripts/test_hqiv_alpha_ir_running.py` |
| **IR-running witness** | `data/alpha_ir_running_witnesses.json` |
| Global alpha mirror | `scripts/hqiv_alpha_readout.py` |
| Shell-local alpha | `scripts/hqiv_isotope_hydrogenic_scales.py` |
| Atom benchmark panel | `scripts/hqiv_atom_construction.py` |

```bash
PYTHONPATH=scripts python3 scripts/hqiv_alpha_model_comparison.py
PYTHONPATH=scripts python3 scripts/hqiv_alpha_model_comparison.py --write-json
PYTHONPATH=scripts python3 scripts/test_hqiv_alpha_model_comparison.py
PYTHONPATH=scripts python3 scripts/hqiv_alpha_ir_running.py
PYTHONPATH=scripts python3 scripts/test_hqiv_alpha_ir_running.py
```

## Three candidate routings

| Model | Definition | Typical `1/α` | Atom spine today |
|-------|------------|---------------|------------------|
| **global_brace** | `alpha_EM_primary` = O–Maxwell at Gauss `m=3` × shell ratio to EW `m=5` | ≈ 129 | **Not routed** into atom mass |
| **nuclear_tracking** | `alpha_eff_at_shell(m_nuc(A))` | 102–123 on panel | Indirect via nucleus binding network |
| **electronic_tracking** | `alpha_eff_at_shell(m_shell)` on discharge occupancy | 83–107 on panel | Outside-fight ratio `(α_eff/α_lock)²` |

Lattice **`α = 3/5`** is a fourth object (curvature imprint); it is not CODATA fine-structure α.

## Key findings (benchmark panel)

1. **Global brace is ~5.9% low on `1/α` vs CODATA** — unchanged from prior readout; this harness does not fix it.
2. **Nuclear-tracking `1/α` is shell-dependent** (`m_nuc` grows with `A`); electronic outermost tracks discharge chart (`m=1,4,3…`).
3. **Replacing outside-fight alpha ratio with nuclear-tracking** shifts fight by **1–15 MeV** on the panel — large enough that a single global α cannot silently replace shell-local ratios.
4. **Atom mass panel stays good** because closed mass is dominated by nuclear cluster + `Z·m_e`; alpha_EM_primary decoupling is architectural, not accidental.
5. **Bare O–Maxwell ladder** crosses CODATA `1/α ≈ 137` near **`m ≈ 20`** — supports an **IR running** story from EW brace to Thomson scale rather than picking one shell occupancy.

## Why the W "sees" 1/α ≈ 129 but hydrogen "sees" 1/α ≈ 137

This is **one coupling running between two scales**, not two inconsistent constants.

| Probe | Physical scale | `1/α` | HQIV object |
|-------|----------------|-------|-------------|
| **W boson** | electroweak / `M_Z` | ≈ 129 | `alpha_EM_primary` Gauss→EW double-axis brace |
| **Hydrogen spectroscopy** | far-IR / Thomson, `q² → 0` | ≈ 137.036 (CODATA) | `α(0)` — bare ladder crossing near `m ≈ 20` |

- The fine-structure constant **runs**: vacuum polarization screens the bare charge, so at the
  high electroweak scale the effective coupling is **larger** (`1/α` smaller, ≈ 129) and at the
  low Rydberg/eV scale it relaxes to the Thomson value `1/α ≈ 137`.
- HQIV reproduces **both endpoints**: the brace lands the structural EW shell at ≈ 129
  (`alpha(M_Z)` analogue), and the bare O–Maxwell ladder `42·(1 + (3/5)·ln(2(m+1)+1))`
  crosses CODATA `1/α ≈ 137` near `m ≈ 20` (`α(0)` analogue).
- On that ladder the W value (≈ 129) sits near `m ≈ 14` and the Thomson value (≈ 137) near
  `m ≈ 20`; the IR shells in between are the **running segment** — currently a phenomenological
  bridge, **not** a proved RG theorem (see `hqiv_alpha_ir_running.py`, span ≈ **+6.3%** `W→Thomson`).
- The structural EW shell `m=5` evaluated on the *bare* ladder gives only ≈ 107; the brace's
  Gauss→EW shell-shape factor is what lifts it to ≈ 129. This normalization gap (bare vs braced)
  is the honest open piece, distinct from the running itself.

### When is raw α actually needed?

Most HQIV observables **do not need raw fine-structure α at all** — mass and binding are
dominated by nuclear curvature + proton lock-in and the lattice imprint `α = 3/5`. Raw α only
enters spectroscopy-class readouts. The router lives in `hqiv_alpha_ir_running.py`:

| Observable class | α needed? | Which α |
|------------------|-----------|---------|
| atomic mass, nuclear binding, BBN | **no** | curvature / lock-in dominated |
| outside curvature fight | **ratio only** | `(α_eff(m)/α_eff(lock))²` — absolute scale cancels |
| TUFT sector determinant, `g−2` | **yes** | global brace (EW-scale, ≈ 1/129) |
| fine structure / Lamb shift / ionization precision / H 1s binding | **yes** | IR/Thomson `α(0)` ≈ 1/137 |

Takeaway: chasing a single "correct" raw α is only worthwhile for the spectroscopy row. For the
bulk of the framework the relevant couplings are the lattice imprint and shell-local *ratios*.

## Uniqueness honesty

We **cannot** claim uniqueness today because:

- Global brace pins **fixed chart roles** (`m=3 → m=5`) without a proved modal selector.
- Nuclear and electronic routings are **both** valid evaluations of the same `alpha_eff(m)` on different shell indices.
- TUFT APS `exp(n α/6)` needs a **global** α; atom outside-fight needs **shell-local** ratios — one number cannot serve both without a tiered router.
- No Lean theorem yet proves which routing is forced by the O–Maxwell Lagrangian alone.

## Recommended next Lean step

**Do not merge into one α.** Formalize a split router:

```text
alpha_EM_global   := alpha_EM_primary          -- TUFT / sector topology
alpha_EM_local(m) := alphaEffAtShell m         -- bound-state dressing
alpha_EM_atom(Z)  := electronic_tracking on fight slots; nuclear on nucleus slots
```

Priority proofs:

1. **`alpha_EM_local` router** — document global vs shell-local roles in `EffectiveAlphaReadout.lean`;
   mirror the observable router from `hqiv_alpha_ir_running.py` (none / global-brace / IR-Thomson / shell-ratio).
2. **IR running lemma** — monotone `one_over_alpha_EM_derived m` from brace scale to CODATA crossing
   near `m≈20`. The Python bridge (`hqiv_alpha_ir_running.py`) already exhibits the monotone ladder
   and the W (≈14) and Thomson (≈20) crossings; the Lean target is `StrictMono` + the named crossings.
3. **Optional:** if nuclear-tracking fight variant is adopted, prove it as an explicit alternate policy — not as uniqueness.
4. **Bare-vs-braced normalization** — explain (or close) the factor that lifts the bare EW shell `m=5`
   (≈107) to the braced W value (≈129); this is separate from the running itself.

## Related

- [ALPHA_LEPTON_SHELL_DERIVATION.md](./ALPHA_LEPTON_SHELL_DERIVATION.md) — lepton shells vs α_EM interaction
- [ATOM_CONSTRUCTION_FROM_MATH.md](./ATOM_CONSTRUCTION_FROM_MATH.md) — atom spine (mass good, ionization weak)
