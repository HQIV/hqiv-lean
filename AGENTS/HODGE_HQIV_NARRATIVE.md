# Hodge conjecture: HQIV narrative (not proved in Lean)

The **Hodge conjecture** (Millennium Prize) says, roughly: on a smooth **complex projective** variety \(X\), every **Hodge class** in \(H^{2k}(X,\mathbb{Z})\) is a **rational** linear combination of classes of **algebraic** cycles. This repository **does not** prove the Hodge conjecture, nor a special case on 3-folds, nor a theorem identifying HQIV’s discrete shell data with Hodge classes or motives.

This note records a **paper-level analogy** so agents can orient the vocabulary (horizon cycles, Fano lines, lattice zeta, `φ·t`, `δ_E`) without misrepresenting Mathlib’s logical content. For the **four-problem unified narrative** (same standing-wave / horizon thread, with self-clock only as one candidate state-language; `FanoPeriodRapidityCoincidence` / `HodgeClassProbe` as **conditional** probes), see [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md). For manifold / period / L-function **roadmap** steps, see [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md). For Navier–Stokes vs standing-wave narrative, see [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md). For what `DivisionAlgebraZetaScaffold.lean` **actually** proves, read its module doc.

---

## 1. Informal mapping: HQIV language ↔ Hodge-flavored analogy

| HQIV object (mostly discrete / parametric in Lean) | **Analogue** in classical Hodge–algebraic language (narrative only) | How **rapidity** enters in the story (not in types) |
|---------------------------------------------------|----------------------------------------------------------------------|------------------------------------------------------|
| Local \(S^2\) horizon / standing-wave shell | Divisor or codimension‑1 cycle on a 3‑fold | Standing-wave configuration on the shell; \(\theta_{\mathrm{self}}\) is only one possible **period-style** state-language over that cycle |
| Embedded \(S^2\) shells in \(\Sigma^3\) | Family of cycles in an ambient 3‑fold | Shells indexed by \(m\in\mathbb{N}\) in Lean—not embedded submanifolds in a formal 3‑fold |
| Fano lines (7 residues, `Fin 7`) | Basis of \(H^2(X,\mathbb{Z})\) or similar | **Overstatement in Lean:** we only have **mod‑7 partition** of a **single** \(\mathbb{N}\) sum (`zeta_HQIV_eq_sum_Fano_residue_classes`), not a basis of Hodge classes |
| `φ`, `t` reals; `phi_t_cum` / `timeAngle` | “Period” pairing \(\langle \phi,[\gamma]\rangle\) | **Narrative:** \(\phi t=\int_\gamma \phi(x)\,\mathrm{d}s\); **Lean:** real parameters unless/until a path integral is defined ([MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md)) |
| `Hqiv.deltaE m` (combinatorial) | Chern / curvature / filtration data | **Narrative:** integral \(\int R\sqrt{g}\,\mathrm{d}^3x\); **Lean:** fixed combinatorial `deltaE` from `OctonionicLightCone`, not Ricci integral |
| Lattice zeta (`zetaR1_latticeTerm`, `zeta_HQIV`) | L-function of a motive | **Not formalized:** no motive, no Euler product over cycles, no functional equation proved for HQIV sums |

**Caution:** Identifying a **real** 3-manifold with \(X(\mathbb{R})\) for a **complex projective** 3-fold, or claiming Fano residues **generate** Hodge classes, would require precise algebraic geometry and cycle theory—**absent** from the current HQIV_LEAN scope.

---

## 2. Why this “touches” the Hodge conjecture (without a proof)

**Design intent (paper-level):**

- **Cycles:** \(S^2\) horizons are narrated as preferred **closed** objects; simply connected \(\Sigma^3\) is used to motivate **global** constraints on phase/rapidity (same storytelling as in the manifold roadmap).
- **Period map:** `φ·t` is **hoped** to become a genuine pairing between a 1-form / auxiliary field and homology classes; nothing in Lean instantiates `φ` as a differential form on \(X\).
- **Filtration / \((p,q)\) type:** \(\Delta_{\mathrm{assoc}}\) and octonionic non-associativity are **motivated** as extra phase data; only **commutative** ℂ lemmas exist (e.g. `cexp_I_mul_add_three` in `DivisionAlgebraZetaScaffold`).
- **Comparison to “classical algebraic” formulation:** the narrative claims classical algebraic statements can be **incomplete** without dynamical horizon / standing-wave data. Self-clock may be one way to parametrize that data, but it is not the only possible language. This is **parallel** to the NS narrative, **not** a mathematical reduction of Hodge to HQIV.

Agents must **not** say “HQIV proves cycle generation,” “Hodge follows from self-clock,” or even “standing-wave structure alone proves Hodge”: all of that would be false relative to this repository.

---

## 3. Edge cases and nuance (qualitative only)

| Setting | Narrative caveat |
|--------|-------------------|
| Calabi–Yau 3-folds | Ricci-flat metrics: \(\delta_E\) **integral** story might localize; combinatorial `deltaE` in Lean does not “become small” automatically. |
| Rigid 3-folds | Deformation triviality vs minimal “discordance”—**heuristic** only. |
| Non-projective \(\Sigma^3\) | Hodge conjecture is **algebraic projective**; de Rham classes on smooth manifolds are a **different** formal setting. |
| L-functions / modular forms | Same warning as roadmap §4: **not** connected to `zeta_HQIV` in Lean. |

---

## 4. What would be needed to make contact with real mathematics

This repeats [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) in Hodge-flavored language, still **not** a short task:

1. A **complex projective** variety \(X\), Chow groups, and **algebraic** cycles in Mathlib-compatible form (or a dedicated project).
2. **Hodge classes** defined as \(\mathbb{Q}\)-linear combinations satisfying the Hodge symmetry—**not** conflated with `Fin 7` shell residues.
3. A **proved** statement linking HQIV’s **combinatorial** data to **specific** cycles on \(X\) (existence and rationality of coefficients)—currently **missing**.
4. Optional: motives, periods, L-functions—**Milestones F–G** in the roadmap.

Until a real algebraic-geometry layer exists, treat §§1–4 here as **analogy and research direction** relative to classical Hodge. **§5** lists **proved HQIV-internal** scaffold theorems (also in [THEOREMS.md](./THEOREMS.md)); those still do **not** prove the Hodge conjecture.

---

## 5. Lean stack brought to parity with the rapidity–zeta bridge (still **not** Hodge)

The following are **proved in this repo** and are meant to **reinforce each other** inside HQIV’s own definitions — they do **not** imply the Millennium Hodge conjecture.

| Layer | What Lean fixes | Main names |
|-------|-----------------|------------|
| **Seven-way zeta split ↔ cycle tokens** | Every shell `f.val + 7·k` in `zeta_HQIV_eq_sum_Fano_residue_classes` is tagged `f` as a `FanoVertex` / `shellResidueFano` | `shellResidueFano_of_f_val_add_seven_mul` (`CycleHodgeProbeScaffold`), `fano_vertex_of_shell_f_val_add_seven_mul` (`DivisionAlgebraZetaScaffold`) |
| **Zeta phase ↔ polar angle** | `zetaHQIVTerm` phase is `cexp (I * polarAngleFromRapidity φ t m)` | `RapidityZetaPhaseBridge` |
| **Period / Hodge probe ↔ same `(φ,t)`** | Under `FanoPeriodRapidityCoincidence`, `φ·t = HodgeClassProbe` | `phi_t_eq_hodgeClassProbe`, `HodgeClassProbe_eq_mul_of_FanoPeriodRapidityCoincidence` (`SpatialSliceRapidityScaffold` / `HodgeRapidityZetaBridge`) |
| **Bundle:** coincidence + zeta | If `φ = c.φ` and `t = c.t`, each `zetaHQIVTerm` uses `polarAngleFromRapidity c.φ c.t m` | `zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity` (`HodgeRapidityZetaBridge`) |

**How to narrate it honestly:** the “Hodge class probe” is a **real scalar** built from abstract contour data; the zeta sum is a **complex** shell series. Lean shows that, **once** you assume the period coincidence and **identify** parameters, the **rapidity** feeding the zeta phase is the **same** `(φ,t)` that equals the probe — and the **Fano strands** of the sum line up with the **seven cycle indices**. That is **coherence of scaffolding**, not a theorem in algebraic geometry.

**Manifold / L-roadmap:** [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) (table rows cross-link this §). **Rapidity π/2 discipline:** `OMaxwellAlgebraSeed.delta_theta_prime_eq_arctan_mul_pi_div_two`.

### What is still open (explicit)

Nothing below is a criticism of §5 — it is the **gap list** relative to the **classical** Hodge conjecture and to a full manifold cycle story:

- No **smooth complex projective** variety \(X\), no **Hodge classes** in \(H^{2k}(X,\mathbb{Q})\), no **algebraic cycles** or Chow groups in Mathlib form for this thread.
- `FanoPeriodRapidityCoincidence` is a **hypothesis record**: `timeAngle φ t = fanoContourPeriodSum …` is **assumed**, not derived from topology or `π₁(\Sigma)=0`.
- No theorem that `HodgeClassProbe` **equals** a period of a **specified** differential form on a **constructed** metric; contours are abstract `Path`s.
- No identification of HQIV’s **seven Fano residues** with a **basis** of any cohomology group (table in §1 still warns against overstating).
- L-function / motive layer unchanged from [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) §4 — **strategy only**.

When adding Lean, **prefer lemmas that also help** the zeta / rapidity / `eff` story (same `m` ladder); see [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) **Proof priority**.
