# Octonion `S^7` shell, 8-ball volume, and “patch” narrative (Lean status)

This note tracks what is **proved in Lean** vs what remains **heuristic / roadmap** for the octonion-sphere–patch story (Fourier axis at `π/(2k)`, moiré tomography, Jacobi divisor sums, BSD/Ramanujan links).

## Formalized (`Hqiv.Algebra.OctonionSphereConstruction`)

| Item | Lean name | Notes |
|------|-----------|--------|
| Integer lattice in `ℝ⁸ ≃ O` coordinates | `intLatticeToO8`, `o8normSq` | `PiLp 2` model of `EuclideanSpace ℝ (Fin 8))`. |
| Every `m : ℕ` is a squared norm on `Fin 8 → ℤ` | `exists_int_lattice_o8_norm_sq` | Uses **Lagrange four-squares** (`Nat.sum_four_squares`) + zero padding (`embedNatFour`). |
| Closed 8-ball Lebesgue mass | `volume_closedBall_o8_eq` | `InnerProductSpace.volume_closedBall_of_dim_even` for `finrank = 8` (`k = 4`), giving `π⁴/(4!) = π⁴/24`. |
| Continuous proxies `V₈`, `A₇` and `dV₈/dr = A₇` | `continuousBallVolume8`, `continuousSphereArea7`, `deriv_continuousBallVolume8` | Polynomial derivative; matches `A₇ = (π⁴/3) r⁷`. |
| Shell step `m → m+1` (nested balls, monotone proxies) | `closedBall_o8_sqrt_subset_sqrt_succ`, `volume_closedBall_o8_sqrt_le_sqrt_succ`, `continuousBallVolume8_sqrt_le_sqrt_succ`, `continuousSphereArea7_sqrt_lt_sqrt_succ` | Radii `√m` increase; Lebesgue mass of `closedBall(0,·)` and `V₈`, `A₇` at those radii grow with `m`. |
| Discrete shell count `r₈(m)` on `\mathbb{Z}⁸` | `IntegerLatticeShellCount8` (`sumSqInt8`, `r8`, `r8_zero`, `r8_one`) | Finite filter over a `√m`-box; script `scripts/test_integer_lattice_shell_count8.py`. |
| CRT `mod 28` = `(mod 4, mod 7)` | `ShellResidueCRT` (`modEq_twenty_eight_iff`, `shellClass28`) | Pure arithmetic; pairs with Fano `mod 7` and ζ-bridge `mod 4`. |
| Example shell `m = 143` | `example_143_lattice_norm` | Vector `(9,7,3,2,0,0,0,0)` padded from four squares. |

## Retired: OctonionPatchQuantum namespace (**removed**)

The former **orthogonal 2/1 vs 1/2 ray** story in a patch plane (`ℝ²` → `ℝ⁸`) is **no longer in the Lean tree**. **Patch search** is formalized as **one-dimensional** along the ordered index `j`: **moiré cumulative variation**, cusp / threshold crossing, **BST** (`MoireCuspBracket`, `MoireToyThresholdSearch`). Do not resurrect ray projection as an alternative “search geometry” for the demo pipeline.

## Formalized (`Hqiv.Algebra.OctonionSphereFourierPatch` — discrete moiré score)

| Item | Lean name | Notes |
|------|-----------|-------|
| Real score on the patch | `MoirePatchScore n` | Alias `Fin n → ℝ`. |
| Discrete **slope** (first difference) | `moirePatchScoreSlope` | `S` at consecutive vertices on each edge. |
| **Step change in slope** (second difference) | `moirePatchSlopeStep` | Interior index `j : Fin (n-2)`; locates where slope jumps. |
| Sanity (linear score) | `moirePatchScoreSlope_affine`, `moirePatchSlopeStep_affine` | Affine `S` has constant slope, zero slope-step. |

Fourier concentration on complex correlations is unchanged; this block only fixes **discrete calculus** on a real score. A concrete global `S` from e.g. `Re` of a mode is still a modeling choice.

## Formalized (`Hqiv.Algebra.MoireJerkSphereModeBridge`)

| Item | Lean name | Notes |
|------|-----------|--------|
| Jerk = second difference | `moirePatchSlopeStep_eq_second_diff`, `moireSecondDiff` | Same interior discrete curvature. |
| Sinusoid along patch | `real_second_diff_sin`, `moirePatchSlopeStep_sin` | Jerk `−4 sin(·) sin²(β/2)`. |
| Intrinsic axis + `Ω m = k` | `moirePatchSlopeStep_sin_intrinsic_of_Omega` | Amplitude factor `sin²(π/(4k))`. |
| When jerk is zero | `moirePatchSlopeStep_sin_intrinsic_eq_zero_iff` | Midpoint sine or `sin(π/(4k)) = 0`; module doc ties proof-by-contradiction packaging and **BST** scope (`MoireToyThresholdSearch` vs uniqueness of jerk argmax). |
| `A₇ = dV₈/dr` | `continuousSphereArea7_eq_deriv_volume` | Symmetric restatement of `deriv_continuousBallVolume8`. |

## Script checks

`scripts/test_octonion_sphere_construction.py` recomputes `V₈`, `A₇`, finite-difference `dV₈/dr`, the `143` vector, and double-unwrap demo phases.

## Not in Lean (explicitly)

- **3SAT \(\to\) integer \(M\) + “geometric SAT solver” / P vs NP–scale biconditional** — narrative only; see **[OCTONION_SAT_PIPELINE.md](./OCTONION_SAT_PIPELINE.md)** (not a theorem in `Hqiv/`).
- Jacobi’s divisor formula for representation counts `r₈(m)` and its power-of-2 refinements (only cited in prose).
- Fourier peak at `θ = π/(2k)` on a quaternion block from harmonics — requires a chosen projection and representation theory packaging.
- A closed-form **global** moiré score `Score(y)` from the continuum (and surface vectors as full gradients) — still pipeline/numerics; **discrete** slope / slope-step on `Fin n → ℝ` is in Lean (`moirePatchScoreSlope`, `moirePatchSlopeStep`).
- Complexity claims (`O(log n)` for monotone threshold search; Ω(log n) lower bound in the comparison model) — not formalized; proof targets are stated in **Proof obligations: discrete “quantum” → vector; optimality of binary search** below.

## Discrete score / gradient at the lattice layer (design)

At the **integer lattice** there is no smooth gradient: increments are **discrete** (e.g. steps of size **1/2** in the relevant coordinate), and those increments assemble into a **direction vector** along the patch. The object of interest is not a derivative but a **transition** between regimes of those steps—where the discrete “slope” changes. That transition is located by **binary search** over the patch index range (a finite `Fin n` window): each probe compares score on one side vs the other until the bracket straddles the jump. Interpreting the patch as sitting on the shell, locating this transition is how that shell contributes its **increment to the sphere** (the next discrete layer of the narrative). Shells where the transition is **hard** to pin down by this search are often **easy** by symmetry: they sit on **poles** (e.g. Fano / quaternion block axes), where phase alignment or embedding lemmas give the address directly without searching the full patch.

### Sieves, k-roots, then binary search (design)

**Low-prime trial division** and similar **sieves** do not replace the patch search; they **prune** residue classes and shrink where a candidate may live. In the pole picture, that pruning **restricts attention away from** regions that are already ruled out by small-modulus arithmetic—or equivalently **isolates** the neighborhoods that still need geometric resolution. Any practical pipeline should run **k-root / arity-axis checks first** (the discrete analogue of testing the **k**th roots / peak frequency alignment): if the shell locks to a pole or a root condition, you exit with an address without touching the full patch. Only then does **binary search along the patch index** run on what remains; it is cheap (\(O(\log n)\) probes in index), and the bracketing step **naturally outputs a direction vector** (discrete increment pattern across the transition). Order of operations: **k-roots (and pole shortcuts) → sieve / small-prime constraints → binary search on the patch**.

### Proof obligations: discrete “quantum” → vector; optimality of binary search

**1. The quantum furnishes a vector.**  
Fix a minimal step (the **quantum**, e.g. **1/2** in a chosen coordinate) so that score increments along the patch index `j = 0,…,n−1` live in a fixed discrete monoid or lattice (e.g. `(½ℤ)^d` after embedding). The **first-difference sequence** `Δ_j := S(j+1) − S(j)` (or the corresponding jump in the score’s regime label) is then a well-defined object in that space; stacking coordinates yields an **increment vector** in `ℝ^d` (or `ℤ^d`). The **point of interest** is the **transition index** where the pattern of `Δ_j` changes (or where a monotone predicate “score has crossed the moiré threshold” flips). What must be proved in a formal layer is: (i) `S` and `Δ` are well-typed in the chosen codomain; (ii) the **addressing vector** used downstream (surface vector / lattice step) is recovered from this discrete data—e.g. as the direction of the jump, or as a fixed linear map from the increment pattern into `Fin 8 → ℤ`. Without (i)–(ii), “gradient at the lattice layer” is only narrative.

**2. Binary search is the fastest way to the transition (in the standard model).**  
Suppose the predicate `P(j) :=` “transition lies at or before `j`” is **monotone** in `j` along a total order on `Fin n` (equivalently: there is a unique threshold `j*` and `P(j)` is false then true). Each probe evaluates `P(mid)` (or compares score at one index to a fixed threshold). In the **comparison-based** model with oracle access to `P`, any algorithm that finds `j*` (or the bracket `[j, j+1]` containing it) needs **Ω(log n)** such probes in the worst case—there are `n` possible outcomes along a line, and each probe yields one bit of information. **Binary search** achieves **O(log n)** probes and matches the lower bound up to constants, so it is **asymptotically optimal** for this problem. (Linear scan is O(n).) “Fastest” here means **optimal worst-case complexity among comparison-based search**, not “faster than every heuristic” in a model that allows free structure (e.g. closed form for `j*` from poles).

Together: the **quantum** gives a **discrete calculus** of increments (= vector data); **binary search** is the **information-theoretically optimal** way to locate the **unique transition** along one patch dimension once `P` is monotone and only oracle queries are allowed.

**3. Ray / 2D-slice orthogonality (retired).** The old `OctonionPatchQuantum` layer is **removed**. Discrete increment patterns along the patch still assemble into vector data where needed for lattice bookkeeping, but **search** is moiré–cusp on `j`, not “pick a ray in a slice.”

## Proof engineering notes

- Avoid `open Real` when stating `EuclideanSpace.volume_closedBall`: `Real.volume_closedBall` is the **1D** interval law and breaks name resolution. Prefer `InnerProductSpace.volume_closedBall_of_dim_even` for the closed form `π^k/k!` in even dimension.
- `toLp 2` + `PiLp.toLp_apply` identifies integer coefficients with `ℝ` coordinates pointwise.

## See also

- **[FT_PATCH_CLOSED_TARGET.md](./FT_PATCH_CLOSED_TARGET.md)** — named **falsifiable** targets (Fourier concentration, BST/cum, jerk), gap between toy `moire_score_samples` and Lean `fourierPatchPeakCorrelation`, and `scripts/ft_patch_closed_target_probe.py`.
