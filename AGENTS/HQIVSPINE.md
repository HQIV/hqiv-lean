# HqivSpine — the clean spine charter (theorems · ethics · targets)

`HqivSpine/` is a **ground-up, Mathlib-only restatement** of the HQIV derivation path, built with the
benefit of hindsight as a disentangled alternative to the legacy `Hqiv.*` tree. This doc is the
agent contract for that effort: the **ethics** every spine module obeys, a **distilled theorem
index**, and the **live target list**. Build with `lake build HQIVCleanSpine` (currently **130 modules,
~1500+ theorems/lemmas, 0 `sorry`**).

The narrative-with-Lean-names lives in the module docstring of `HqivSpine.lean`; this doc is the
agent-facing distillation. For the legacy corpus see [THEOREMS.md](./THEOREMS.md) and
[ASSUMPTIONS.md](./ASSUMPTIONS.md).

---

## 1. Ethics (the spine contract — do not violate)

These are hard constraints. A contribution that breaks any of them is **not** spine-grade; put it in
the legacy tree instead.

1. **Mathlib-only.** No `import Hqiv.*`. The spine depends solely on Mathlib + earlier spine modules.
   Re-derive, never re-export.
2. **No `sorry`, no new `axiom`, no `native_decide`.** Every result is a closed proof. The only
   tolerated axioms are Lean/Mathlib's `propext`, `Classical.choice`, `Quot.sound` — audit every
   headline theorem with `#print axioms`.
3. **Foundation-anchored constants.** Physical constants are *read off the foundation*, never
   re-posited as decimal literals: `transverseDim = 3`, `carrierMultiplicity = 8`,
   `alphaRat transverseDim = 3/5` (= α), `gammaRat 3 = 2/5` (= γ), `referenceM = 4`. When you port a
   legacy module that hard-codes `3`, `8`, `3/5`, `4`, replace the literal with its foundation source
   and prove the value lemma (e.g. `monogamyAlpha := alphaRat transverseDim`,
   `octetCapacity_eq_carrierMultiplicity`).
4. **No PDG / current-quark-mass injection.** Charges come from Gell-Mann–Nishijima `Q = I₃+(B+S)/2`;
   masses come from the now-slice ladder; the proton stays the calibration anchor at `referenceM = 4`.
   PDG numbers may appear **only** as comparison labels in docstrings, never as inputs.
5. **Honest scope.** Toy or limited results must state what they do **not** claim (e.g.
   `Physics.DiscreteHeat` is a dissipation/CFL sign on `C₃`, *not* a Navier–Stokes or PDE-existence
   claim; `Geometry.ContinuumChart` is flat Riemannian, *not* a Lorentzian metric). No overreach.
6. **Disentangle + golf.** Mining a legacy module means: strip its `Hqiv.*` deps, anchor its
   constants, shorten its proofs, and **drop dead ends / solver scaffolding** (e.g. the
   whip/objective optimization layer of `ForceCarrierWhip` stayed in legacy; only the physical S2
   carrier envelope came over).
7. **Single physical anchor.** The observer's **now slice** (`Physics.NowSlice`) carries the
   curvatures (`φ`, `Φ`, `Ω_k`) explicitly rather than masking them inside a hard proton mass.

---

## 2. Distilled theorem index (by layer)

Fully-qualified under `HqivSpine.`. Use `#check` for exact types.

### Foundation — `transverseDim = 3` is the only combinatorial input
- `Foundation.ThreeGrowth`: `alphaRat`, `alpha_transverseDim : alphaRat 3 = 3/5`, `gamma_three`,
  `alpha_add_gamma`; null-shell quadratic/cubic growth hinge.
- `Foundation.Carrier`: `carrierMultiplicity = signsPerAxis^transverseDim`,
  `carrierMultiplicity_eq_eight`, `soDim_carrier = 28`, `imaginaryDim = 7`.
- `Foundation.Fano`: `PG(2,2)` incidence; the seven imaginary units.
- `Foundation.HopfLadder`: the division-algebra / Hopf ladder `1,2,4,8`.

### Geometry / analysis
- `Geometry.Lorentz`: rapidity boosts on the radial `1+1` chart form a one-parameter group.
- `Geometry.DiscreteLaplacian`: 7-point central stencil, domain rescaling `c²`, Fourier symbol
  `2(cos kh − 1) = −(4/h²)sin²(kh/2)`.
- `Geometry.SphericalHarmonics`: `∑_{ℓ≤L}(2ℓ+1) = (L+1)²`; `cumulativeModes m/(m+1)² → 4`;
  `64 = 8×8` first at `m = 3` (`minimal_shell_ge_sixty_four`).
- `Geometry.MaxwellSpectral`: `S³` Maxwell carrier `λ_ℓ = ℓ(ℓ+2)`, degeneracy `(ℓ+1)²`
  (`harmonicDimS3_eq_succ_sq`); `S⁴` O-Maxwell `λ_ℓ = ℓ(ℓ+3)`.
- `Geometry.ContinuumChart`: flat `ℝ⁴` Fréchet `coordsGradient` / `coordsDivergence`
  (`chart_dim : spacetimeDim = 4`); constants are flat.
- `Geometry.MetricGradient`: contravariant `(∇φ)^ν = g^{νμ}∂_μφ`, coordinate `∂_μ J^μ`,
  flat Euclidean/Minkowski inverse metrics; `coordPartialDivergence_const` (flat hook wired).

### Algebra — the octonions as a genuine division algebra
- `Algebra.CayleyDickson`: `𝕆 = CayleyDickson³ ℝ`, dim 8.
- `Algebra.Octonion`: norm, two-sided inverse, alternativity, eight-square identity, Fano bridge.
- `Algebra.So8` / `Closure` / `G2` / `Gauge` / `Triality` / `Anomaly`: `so(8) = 28`, closure,
  `G₂` automorphisms, the `1+3+4` gauge split, triality, finite SM anomaly traces.
- `Algebra.StrongColor` / `StrongColorSu3` / `StrongColorSu3LieLaw` / `StrongColorEmbed`:
  Gell–Mann `λ₁–₈`, `f^{abc}`, global Lie law, `8×8` carrier embed (`colorGellMannEmbed`);
  `NonAbelianMatrixElement`: abelian kinetic × `C_A/C_F` pipeline.

### Physics
- `Physics.Shell`: `referenceM = 4`, `phi(m)=2(m+1)`, `latticeSimplexCount`, `alphaEM_eq : α = 3/5`,
  `gammaHQIV_eq`, `oneOverAlphaBare = 42`, shell-running coupling.
- `Physics.LockIn`: `referenceM = 4` is the **unique** discrete equilibrium (`referenceM_unique_balance`).
- **QM stack**: `Exclusion`, `SpinStatistics`, `Uncertainty`, `CCR` (finite-dim obstruction);
  `VonNeumann` + `GleasonBorn` + `KochenSpecker` + `Measurement` (Born normalization
  `sum_bornProbN_eq_one`, Gleason frame-function additivity `frame_sum`/basis-independence
  `frame_basis_independent`, KS contextuality `no_noncontextual_assignment`, first-principles
  uniqueness `bornProbN_unique_of_coherence`, collapse energy closure); `Evolution` (unitary digital
  flow conserves IP/norm + Born stats); `Monogamy`.
- **QFT patch**: `PatchObstruction` (no θ-vacuum, automatic microcausality), `FreeField` (smeared
  abelian field algebra, disjoint-support annihilation).
- **Cosmology/mass**: `Action`, `Gravity`, `Blackbody`, `Curvature`, `CurvatureKernel`, `NowSlice`,
  `ContinuousHorizon` (`ξ = m+1`, `sigmaXi`, brace readouts, `xiLockin = 5`),
  `RindlerDetuning` (δ-corrected surfaces, global detuning from lapse increment),
  `NowSliceHorizon` (now slice ↔ continuous chart ↔ detuning bridge),
  `NowSliceFromLattice` (discrete `(φ, Φ, Ω_k)` from temperature ladder, shell ledger,
  curvature integral + harmonic lower bound; lock-in `(1, 0, 1, 4)`, ages `(12, 3)`,
  `massUnit = 5`; balanced-horizon `Φ = 0`; parallel discrete/continuous `Ω_k` monotonicity),
  `ChartMaxwell` (flat lock-in `∇φ`, `div J` on the continuum hook),
  `Age`, `Baryogenesis`, `AlphaRunning`, `NeutrinoMixing` (`θ = π/4`, `δ = π/5`), `Forces` (1+3+4),
  `ColorCasimir` (`C_A=3`, `C_F=4/3`), `TrappedCasimir`, `Proton`, `MassLadder`, `Frontiers`.
- `Physics.NuclearCluster`: inside/outside cluster binding split, valley contacts (`A ≤ 4` cap),
  post-α well-deepening hook (`postAlphaWellDeepening`), positivity for `A ≥ 3`.
- `Physics.AlphaDecayTunneling`: cluster Q + curvature barrier → spine `Tunneling` Gamow law;
  Geiger–Nuttall monotonicity (`alphaHalfLife_antitone_Q`), certified bundle
  `alphaDecayTunnelingCertified`.
- `Physics.NucleonMoment`: `μ = 4Q_a − Q_b` ⇒ `μ_p = +3`, `μ_n = −2`, ratio `−3/2`
  (`proton_neutron_ratio`); dressed `μ_p = 120/43 ≈ 2.791` (`dressed_proton_moment`); Clebsch weights
  forced by orthonormality (`orthonormal_complement_swaps_sq`). Constants anchored to foundation.
- `Physics.PlaquetteHolonomy`: discrete gauge holonomy in `Function.End X`; homomorphism on path
  concatenation (`pathHolonomy_append`); the discrete seed of `F = [D,D]`.
- `Physics.PlaquetteCurvature`: the **concrete non-abelian `F = [D,D]`** on the octonion carrier
  `Fin 8 → ℝ`. Matrix transport `carrierTransport` is a monoid hom (`carrierTransport_mul`/`_one`),
  so plaquette holonomy = ordered matrix product (`quarterEdge_holonomy`); curvature
  `discreteCurvature = ⁅D₁,D₂⁆` is zero **iff** transports commute (`curvature_eq_zero_iff_commute`),
  with a commuting commutator-plaquette flat (`commutatorPlaquette_flat`). Witness: the phase-lift
  rotation `quarterTurn 1 7` (the `Δ` plane) and colour-axis `quarterTurn 0 7` share `e₇`, so
  `F ≠ 0` (`curvature_nonzero`) and the loop `Q₁₇·Q₀₇·Q₇₁·Q₇₀` sends `e₁↦e₀`
  (`holonomy_witness`, `holonomy_nontrivial`). `quarterTurn` is a foundation-anchored signed
  permutation in `SO(8)` (`quarterTurn_transpose : (Qᵢⱼ)ᵀ = Qⱼᵢ`); transport is a `MonoidHom`
  (`carrierTransportHom`). **Second witness** in the weak-isospin `SU(2)≅SO(3)` sector — the planes
  `(e₂,e₃)`,`(e₂,e₄)` of `Gauge.weakL₁,weakL₂` (`weakPlane_generator : planeGenerator 2 3 = −weakL₁`):
  `weak_curvature_nonzero`, `weak_holonomy_witness` (`e₂↦e₃`) — the finite/group-level face of
  `⁅weakL₁,weakL₂⁆ = −weakL₃`. Bundle `plaquetteCurvatureDischarged_holds`.
- `Physics.WilsonLoop`: **lattice Stokes** — the Wilson loop of a tiled region is the ordered product
  of its plaquette holonomies (`wilsonLoop`). Gluing tilings multiplies (`wilsonLoop_append`,
  discrete Stokes additivity); a curvature-free region has trivial loop (`wilsonLoop_flat`,
  `flat_tiling_trivial`); `n` copies of a plaquette accumulate as `holⁿ` (`wilsonLoop_replicate`, the
  discrete area seed). Witness `wilsonLoop_curvature_obstructs_flat`: a loop flat **except for one**
  curved colour plaquette still rotates `e₁↦e₀` — curvature cannot be tiled away. Bundle
  `wilsonLoopDischarged_holds`. (Kinematic Stokes/flatness only — *not* a statistical area law.)
- `Physics.CPHolonomyPhase`: **CP violation = holonomy phase** — the complex U(1) complexification of
  `WilsonLoop`. Link `link θ = e^{iθ}` (`link_mul`, `conj_link`); abelian plaquette holonomy is the
  flux phase `e^{iΦ}` (`u1Holonomy_eq_link_flux`), flat iff flux ∈ `2πℤ` (`u1Holonomy_eq_one_iff`),
  with `Φ=π ↦ −1` (`u1Holonomy_nontrivial`). The **Jarlskog invariant** `J = Im(V_us V_cb V*_ub V*_cs)`
  is the imaginary part of a closed flavour-space loop: **rephasing-invariant** (`jarlskog_rephasing`
  — the CP phase can't be rotated away), zero for a real CKM (`jarlskog_real`), and `J = (∏|V|)·sin δ`
  for one holonomy phase (`jarlskog_phase`, `jarlskog_phase_ne_zero`). The CP piece the real
  `MixingAngles`/`CabibboInterference` could not see. Bundle `cpHolonomyDischarged_holds`.
- `Physics.CKMMixingMatrix`: **the full `3×3` unitary CKM matrix.** Plane rotations `R₁₂,R₂₃` (real,
  mass-ratio angles) and `R₁₃(δ)` (holonomy phase) each unitary (`rot12/23/13_unitary`); the product
  `V = R₂₃·R₁₃·R₁₂` is unitary (`ckm_unitary`, `ckm_unitary_apply : VᴴV = 1`) — a `U(3)` element. Its
  four entries (`ckm_us/cb/ub/cs`) give the Jarlskog invariant in closed form
  `J = c₁₂c₁₃²c₂₃s₁₂s₁₃s₂₃·sin δ` (`ckm_jarlskog`). Assembled from spine mass-ratio angles
  (`ckmSpine`, `ckmSpine_unitary`) with CP violation `ckmSpine_cp_violation ≠ 0` iff the fibre
  holonomy is genuine — no PDG matrix fit. Bundle `ckmMixingDischarged_holds`.
- `Physics.FanoMixingWeights`: **overlap weights from Fano incidence** (not mass ratios). `overlap v w`
  = shared Fano lines, forced to `1` off-diagonal (`overlap_distinct`) / `3` diagonal
  (`overlap_self`); the leading mixing fraction is the graph ratio `sin²θ = overlap(v,w)/overlap(v,v)
  = 1/3` (`fano_sinSq_eq_overlap`) — no fitted sine. The Fano-weighted `ckmFano` is unitary
  (`ckmFano_unitary_apply`) and CP-violating (`ckmFano_cp_violation`). Bundle
  `fanoMixingDischarged_holds`. (Democratic baseline `1/3`; the hierarchy is the `LadderMixingHierarchy`
  ladder refinement.)
- `Physics.LadderMixingHierarchy`: **the derived mass ladder bends the democratic baseline.** Feeds the
  Beltrami eigenvalues `λ(g)=g+1` (`MassLadder`, derived — not free masses) into the GST fraction:
  `sin²θ(gₗ,gₕ) = (gₗ+1)/((gₗ+1)+(gₕ+1))` (`sinθLadder_sq`). The Fano `1/3` is exactly the leading rung
  `λ=1:2` (`democratic_eq_leading_ladder` — incidence and spectrum agree), and mixing strictly shrinks
  with separation (`ladder_mixing_strictAnti`), below `1/3` once rungs differ by two
  (`ladder_below_democratic`). Assembles a unitary (`ckmLadder_unitary`), CP-violating
  (`ckmLadder_cp_violation`) `ckmLadder` with **no free mass input**. Bundle
  `ladderMixingDischarged_holds`. (Right *direction*, derived; the linear ladder is too mild for the
  steep measured magnitudes — the true spectral weighting functional stays open.)
- `Physics.MassDrivenMixing`: **the residual hierarchy is the mass spectrum.** GST as an exact transfer
  function `sin²θ = (1+m_heavy/m_light)⁻¹` (`sinθMass_sq_eq_oneDiv`), strictly decreasing in the mass
  ratio (`angle_strictAnti_in_massRatio`). A geometric mass ladder `m(g)=m₀·rᵍ` gives the closed form
  `1/(1+r^{gₕ−gₗ})` (`geomMixing_sq`), decreasing in steepness `r` (`geomMixing_strictAnti_r`) and
  reaching any target (`geomMixing_lt_eps`); `r>2` beats the linear ladder (`geom_below_linear`).
  Bundle `massDrivenMixingDischarged_holds`. (Transfer function derived; the steepness `r` is the
  `MassLadder` absolute-scale frontier — the open mixing question is now one *mass* input.)
- `Physics.PMNSCrossCheck`: **the mixing question asked from two places.** Route A geometry/incidence
  (`θ₂₃ = π/4` maximal, `sin²θ₁₂ = 1/3` — tri-bimaximal) and Route B the mass transfer function
  (`MassDrivenMixing`) are equated, inverting it: maximal `θ₂₃` ⇔ neutrino degeneracy `mₗ=mₕ`
  (`atmospheric_forces_degeneracy`), democratic `θ₁₂` ⇔ leading rung `mₕ=2mₗ`
  (`solar_forces_leading_rung`). Both ⇒ a *mild* neutrino spectrum (ratios `1`,`2`); a *steep* quark
  spectrum gives small CKM angles through the same law (`steeper_is_smaller`) — large lepton / small
  quark mixing as two regimes of one mechanism. Bundle `pmnsCrossCheckDischarged_holds`. (Joint
  prediction: near-degenerate neutrino mass ratio — testable; absolute scale stays the frontier.)
- `Physics.SectorMixingFromComplexity`: **closes the loop with one spectral source.** Sets the mixing
  steepness to the content-class complexity `l² ∈ {1,4,9}` (`sectorSteepness c = intrinsicWaveComplexity
  c`), deriving both regimes: neutrinos `l²=1` ⇒ degenerate (`neutrino_mass_degenerate`) ⇒ maximal
  `sin²θ=1/2` (`neutrino_mixing_maximal`) = geometric `π/4` (`neutrino_matches_geometric_maximal`);
  quarks `l²=9` ⇒ `sin²θ=1/10` adjacent (`quark_adjacent_mixing`) strictly below neutrino
  (`quark_below_neutrino`); ordering `1<4<9` (`sectorSteepness_strictMono`). Bundle
  `sectorMixingDischarged_holds`. (*Why* lepton mixing is large / quark small is now a theorem; exact
  values need sub-leading splittings.) Charged-lepton sector `l²=4` gives intermediate `1/5`
  (`chargedLepton_adjacent_mixing`); adjacent mixing ordered `ν 1/2 > ℓ 1/5 > q 1/10`
  (`adjacent_mixing_sector_ordering`).
- `Physics.PMNSMatrix`: **lepton mixing matrix + derived `J_PMNS`.** PMNS from spine angles: solar
  `sin²θ₁₂=1/3` (Fano), atmospheric `θ₂₃=π/4` (shell), phase `δ=π/5` (monogamy). Tri-bimaximal leading
  order (`pmnsTBM`, unitary, CP-free `pmnsTBM_jarlskog` — CP gated by reactor angle); reactor angle on
  (`pmnsReactor`) ⇒ unitary + closed-form `J=(√2/6)(1−s₁₃²)s₁₃ sin δ` (`pmnsReactor_jarlskog_value`),
  CP real with derived `π/5` once `θ₁₃≠0` (`pmns_cp_from_derived_phase`). Bundle `pmnsDischarged_holds`.
  (Two large angles + phase derived; reactor magnitude `s₁₃` is the open input; `J≈0.02` at `s₁₃≈0.15`.)
- `Physics.CKMCPPhase`: **quark CP phase + numerical CKM `J`.** Quark companion of the lepton `π/5`:
  the CP-odd holonomy skew `γ/2³−γ/2⁵` normalised by `γ` (cancels) and lifted by `π` gives the derived
  `δ_CKM=3π/32` (`ckmCPPhase_eq`) — the *second-order* slot difference to the neutrino *first-order*
  `(γ/2)π`. `ckm_jarlskog` collapses (Fano angles) to `J=(4√3/81)sin δ` (`ckmFano_jarlskog_value`),
  non-zero at the derived phase (`ckmFano_cp_violation_derived`, `J≈0.025`). Bundle `ckmCPDischarged_holds`.
  (Closes the `δ` input flagged by `CKMMixingMatrix`; the `J` magnitude is the democratic baseline upper
  bound — measured `J≈3·10⁻⁵` needs the steep-quark angle suppression, the remaining fine structure.)
- `Physics.NucleonLadder`: **one anchor → real nucleon masses.** Instantiates the abstract `Binding`
  network: concrete nucleon trace (three valence carriers), `∑ w=3` (`nucleonWeight_sum`), closing
  `E_bind=3·count(m)·α_eff(m)` (`E_bind_nucleon`), positive and `≤count/14` (sub-2.2 MeV shift). One scale
  (proton readout): constituent `=readout+E_bind(4)`, ground reproduces anchor exactly
  (`ground_reproduces_anchor`, no new number). Excited baryons at the **exact rational**
  `M(n)=m_p·(n+5)(n+6)/30` (`radialMass_ratio`): rungs `m_p,(7/5)m_p,(28/15)m_p,(12/5)m_p,…` strictly
  increasing. **Orbital axis** from the foundational Rindler detuning `1+(γ/2)m` (`γ=2/5`, slope `1/5` is
  no new number): `step(ℓ)=3(ℓ+5)(ℓ+6)/(10(ℓ+9))` (`orbitalStep_eq`), `≥1`, strict-mono; **full `(n,ℓ)`
  grid** exact-rational `M(n,ℓ)=m_p·((n+5)(n+6)/30+step(ℓ)−1)` (`excitedMass_ratio`). Bare binding shown
  *opposite*: `E_bind` **strictly increases in shell for all m** (`E_bind_strictMono`, honest analytic
  `log(1+x)≤x` increment bound), so the naive tower *falls* for every `n+ℓ≥1` (`naive_excited_lt_ground`)
  — why the rising physical tower must be the operational surface law (both certified). **Meson** = 2-carrier composite vs baryon's 3; constituent and
  binding both scale with count → cancel → meson ground is the **exact** `2/3` proton (`mesonGround_eq`,
  `≈625.5` MeV = spin-avg `(π,ρ)`), same one anchor, same rational ladder (`mesonRadialMass_eq`). Bundle
  `nucleonLadderDischarged_holds`. (Whole two-axis
  spectrum is a parameter-free rational multiple of the single `referenceM=4` anchor; leading operational
  readout `≈5–10%` of the measured `Δ`/Roper region; relaxation fine structure + heavy-quark scales stay
  frontiers.)
- `Physics.ForceCarrier`: S2 carrier envelope `sin(½π(1−d))^k`, full at source, zero at causal edge,
  bounded in `[0,1]`; forward/back/net emission–absorption split.
- `Physics.DiscreteHeat`: `⟨u,Δu⟩ = −‖∇u‖² ≤ 0`, exact Euler energy law, `C₃` identity
  `‖Δu‖²=3‖∇u‖²`, CFL Lyapunov step `3·dt·ν ≤ 2 ⇒ ‖u⁺‖² ≤ ‖u‖²`.
- `Physics.DiscreteHeatCycle`: the **general cycle `Cₙ`** version on `ZMod n` (`[NeZero n]`) — same
  dissipation `⟨u,Δu⟩=−‖∇u‖²≤0` (`sum_u_lap_eq_neg_jumpEnergy`/`_nonpos`), Fourier-symbol bound
  `‖Δu‖²≤4‖∇u‖²` (`lapEnergy_le_four_mul_jumpEnergy`, `4=2·degree`; `C₃`'s `3` is the sharp case),
  exact Euler energy law (`eulerStep_energy_sub_eq`), and the standard cycle CFL
  `4·dt·ν≤2 ⇒ ‖u⁺‖²≤‖u‖²` (`eulerStep_energy_le_of_cfl`). Honest toy scope, all `n`.
- `Physics.HubbardDimer`: the **first interacting many-body model** — two-site spin-½ Ising dimer
  `H = −t(σx⊗I + I⊗σx) + λ(σz⊗σz)` as an explicit Hermitian `4×4` (`H_isHermitian`). Exactly solvable:
  eigenpairs `±λ` (`eigen_singlet`/`eigen_triplet`, hopping-independent) and the interacting pair
  `±√(4t²+λ²)` (`eigen_ground`/`eigen_top` via secular `eigen_of_sq`). Ground `E₀=−√(4t²+λ²)` is the
  minimum (`groundEnergy_le_lam/_neg_lam/_top`) with strictly positive **gap** `√(4t²+λ²)−|λ|` once
  `t≠0` (`spectralGap_pos`). Ising strength **shell-anchored** `λ(m)=λ₀·φ(m)/φ(referenceM)`
  (`lambdaShell_referenceM`). Honest scope: finite four-state toy, not the thermodynamic limit.
- `Physics.HubbardHalfFilling`: the **canonical half-filled Hubbard dimer** (charge sector). `H(t,U)`
  on `(|↑↓,0⟩,|0,↑↓⟩,|↑,↓⟩,|↓,↑⟩)`, Hermitian (`H_isHermitian`), spectrum `{0,U,(U±√(U²+16t²))/2}`:
  triplet zero mode (`eigen_triplet`), charge level `U` (`eigen_chargeAsym`), singlets via secular
  `E²=UE+4t²` (`eigen_ground`/`eigen_excited`). Ground `E₀=(U−√(U²+16t²))/2` is the minimum
  (`groundEnergy_le_zero/_U/_excited`); **superexchange** gap `J=(√(U²+16t²)−U)/2=8t²/(U+√(U²+16t²))`
  (`exchangeJ_eq`) obeys Anderson `J≤4t²/U` in the Mott regime (`superexchange_le`). `U` shell-anchored
  (`Ushell_referenceM`). Honest scope: finite model, not the Mott transition.
- `Physics.MonogamyWitness`: concrete **GHZ/W states realising CKW**, grounding `Monogamy`'s abstract
  tangles in explicit amplitude tensors `ψ : Fin 2³ → ℝ`. One-tangle `τ(A:BC)=4·det ρ_A` from the
  reduced density matrix (`oneTangle_ghz=4a²b²`, `oneTangle_w=4x²(y²+z²)`); three-tangle `τ_ABC=4·|Hdet|`
  from the Cayley `2×2×2` hyperdeterminant (`hyperdet_ghz=a²b²`, `hyperdet_w=0`). Residual
  `pairBudget=τ(A:BC)−τ_ABC` ⇒ monogamy everywhere (`ckw_monogamy`, also shell-weighted
  `corrected_ckw_monogamy`); **GHZ has zero pairwise tangle** (`ghz_pairBudget_zero`), **W saturates
  CKW** (`w_saturates_ckw`). Canonical endpoints `τ(A:BC)=τ_ABC=1` (GHZ), `8/9` & `0` (W). Honest
  scope: pairwise Wootters concurrences not re-derived, only the endpoints + CKW structure.
- `Physics.GleasonBorn`: the **Born functional as a Gleason frame function** on `ℂⁿ`. Overlap
  probability `bornFrame φ ψ = ‖⟪φ,ψ⟫‖²` is symmetric (`bornFrame_comm`), Cauchy–Schwarz-bounded
  (`bornFrame_le`, `bornFrame_le_one`), and **additive over every orthonormal measurement basis**
  `∑ᵢ bornFrame φ (b i)=‖φ‖²` (`frame_sum`, from Mathlib Parseval `sum_sq_norm_inner_left`); unit
  state ⇒ probabilities sum to `1` in any basis (`frame_sum_pure`), basis-independent /
  non-contextual (`frame_basis_independent`). Density mixtures `∑ₖ wₖ|φₖ⟩⟨φₖ|` stay frame functions
  (`mixFrame_sum`, `mixFrame_sum_pure`) — the representable / trace-rule Gleason direction in every
  finite dimension. The **`dim≥3` hypothesis is proved necessary** (`gleason_fails_in_dim_two`): on
  the real circle the sextic `cos 6θ` is a frame function (`sextic_isFrameFun`) that is *not* any
  quadratic/trace form (`sextic_not_qform`) — in `dim=2` additivity only pins `f θ + f(θ+π/2)`, so
  modes `cos kθ` with `k≡2 (mod 4)` survive while `xᵀMx` reaches only `k≤2`; the qutrit keeps
  representability (`qutrit_frame_sum`). Honest scope: the analytic `dim≥3` converse (every frame
  function = `tr(ρ·)`) is cited, not formalised; `Measurement.bornProbN_unique_of_coherence` is the
  finite substitute.
- `Physics.KochenSpecker`: **state-independent quantum contextuality** via the minimal
  Cabello–Estebaranz–García 18-ray KS set in `ℝ⁴`. 18 integer rays `V`, 9 orthogonal `contexts`
  certified by `decide` (`contexts_orthogonal`, `rays_nonzero`), each ray in exactly two contexts
  (`contexts_cover`). **No noncontextual `{0,1}` assignment** picks one true ray per context
  (`no_noncontextual_assignment`) — `omega` parity: `9` (odd) `= 2·#true` (even). The contextuality
  complement to `GleasonBorn` (no hidden-variable definite values, regardless of state). Honest
  scope: the `dim=3` minimal KS set (Conway–Kochen, 31 rays) has no parity proof — future work.
- `Physics.Thermodynamics`: the **four laws** from `Blackbody` + `DiscreteHeat`. Zeroth: equilibrium =
  equal `T_m = ω_m = 1/(m+1)`, equivalence + injective (`thermalEquilibrium_iff_eq`). First:
  `N_m·T_m = 8` shell-independent (`firstLaw_zeroPointSlice_conserved`), `U = 3P`
  (`firstLaw_equationOfState`), `T·s = (4/3)U` (`firstLaw_euler_relation`). Second: `−⟨u,Δu⟩ ≥ 0`
  (`secondLaw_entropyProduction_nonneg`), CFL energy non-increase, equilibrium entropy `≥ 0`. Third:
  `∀ε>0, ∃m, T_m < ε` (`thirdLaw_unattainable_cooling`) and inner shells hotter (`thirdLaw_hotter_inside`).
- `Physics.CMBBirefringence`: cosmic birefringence as the spin-2 rotation by `2β(m)` of the `(E,B)`
  pair. Power-conserving (`rot_norm_sq`), reproduces the `Blackbody` greybody split
  (`observed_{E,B}mode_power_eq_greybody`), parity-violating `EB = ½sin(4β)E²` vanishing iff
  `sin 4β = 0` (`EBcorrelation_pure_E_eq_zero_iff`); inter-shell angle `α·log((m_o+1)/(m_e+1))`
  (`birefringenceRotationAngle_eq`); drives `Measurement`'s redshift (`birefringence_drives_redshift`).
- `Physics.ThermalArrow`: the time arrow on the shell clock. Boltzmann entropy `S(m)=log N_m` strictly
  increases (`boltzmannEntropy_strictMono`, injective) while `T_m` strictly decreases
  (`shellTemp_strictAnti`); bundled `thermal_arrow`; equilibrium terminus = the zero-deficit
  `ShellBudget` reference (`arrow_terminus_equilibrium`).
- `Physics.StandardModelLagrangian`: the O-Maxwell action *is* the SM gauge kinetic term. Channel
  partition (`Forces`) splits `kinetic` into EM+weak+strong (`kinetic_sector_decomposition`, EM a lone
  abelian field `em_kinetic_single`); spacetime-constant channel shift is a gauge symmetry leaving `F`,
  `kinetic`, and the EOM invariant (`fieldStrength_gaugeShift`/`kinetic_gauge_invariant`/`EL_gauge_invariant`).
  Bundled `smLagrangian_closure`.
- `Physics.NuclearBinding`: bound states from the curvature network (constituent-only, PDG-free).
  Coupling positivity (`bindingCouplingAtShell_pos`) ⇒ binding sign (`E_bind_from_network_pos`); mass
  defect = binding (`networkMassDefect_eq`) ⇒ bound iff binding positive (`nucleus_bound_iff_binding_pos`,
  `nucleus_bound_of_positive_weight`). Curvature model `A·δ_E(m)`: per-nucleon binding `A`-independent
  (`bindingPerNucleon_saturates`, force saturation) and deeper inward (`bindingPerNucleon_deeper_inside`),
  always bound (`nucleus_always_bound`).
- `Physics.BBN`: primordial abundances from the frozen `n/p` ratio. Nucleon fractions partition
  (`fractions_sum_one`); `⁴He` mass fraction `Y_p = 2r/(1+r)` (`helium4MassFraction_eq_two_neutronFraction`),
  monotone in `r`, `< 1` iff `r < 1` (`helium4MassFraction_lt_one_iff`); the baryon-to-photon input is the
  `Baryogenesis` curvature readout `Ω_k·δ_E(referenceM)` (`baryonToPhoton_eq`, `baryonToPhoton_pos`).
- `Physics.WeakDecay`: closes BBN's `n/p` input from one positive `Q`-value. Sargent rule `Γ = g·Q⁵`
  strictly increasing (`sargentRate_strictMono_in_Q`), lifetime `τ=1/Γ` strictly decreasing
  (`lifetime_antitone_in_Q`); freeze-out ratio `r = e^{−Q/T} ∈ (0,1)` (`npRatio_lt_one`), on the shell
  clock `e^{−Q(m+1)}` (`npRatioAtShell_eq`), outward-suppressed (`npRatioAtShell_antitone`); feeds
  `BBN` to a physical `Y_p < 1` (`helium_fraction_lt_one_from_weak`).
- `Physics.GRFromMaxwell`: linearized Einstein = O-Maxwell. Weak-field `divergence Φ = 4π·G_eff(φ)·ρ`
  is the gauge stationarity for the rescaled current (`linearizedEinstein_iff_EL`); Friedmann ⇔ critical
  density `ρ_c(φ)=(3−γ)φ²/(8π G_eff φ)` (`friedmann_iff_critical`, `criticalDensity_pos`); `H(φ)=φ` ⇒
  linear Hubble law (`recessionVelocity_linear`). Bundle `gr_from_maxwell_closure`.
- `Physics.StellarStructure`: hydrostatic φ-shell star. `P(m)=K·shellShape m`, core-peaked
  (`stellarPressure_center`, `stellarPressure_le_center`), outward-softening (`stellarPressure_strictAnti`),
  in discrete balance `P(m)=P(m+1)+w(m)` with `w(m)>0` (`hydrostatic_balance`, `hydrostaticSupport_pos`);
  with `K=Ω_k·N₆₇` it is the now-slice imprint (`stellarPressure_eq_curvatureImprint`).
- `Physics.HadronSpectrum`: meson/baryon ratios off the mass ladder. Mass = core × closure scale
  (`hadronGroundMassMeV_eq_core`); meson : baryon `= 4/9` core-independently (`meson_baryon_ratio`),
  baryon always heavier (`baryon_heavier_than_meson`); lepton generation steps compose
  `(τ:μ)·(μ:e)=(τ:e)=2` (`generation_steps_compose`). All ratios use only `{1,2,3}`.
- `Physics.GravitationalLensing`: deflection `4·G_eff(φ)·M/b`, exactly twice Newtonian
  (`einstein_eq_two_newtonian`); positive, mass-linear, `1/b`, curvature-increasing
  (`einsteinDeflection_pos/_strictMono_in_M/_antitone_in_b/_strictMono_in_phi`). Bundle
  `gravitational_lensing_closure`.
- `Physics.StellarCollapse`: finite support budget. Per-shell supports telescope to `K·(1−shellShape N)`
  (`support_partialSum_eq`), rising (`support_partialSum_strictMono`) but `< K`
  (`support_partialSum_lt_central`); demand `D ≥ K` is never met (`collapse_above_budget`) — `K` is the
  Chandrasekhar-style ceiling.
- `Physics.HadronDecayWidths`: phase space + branching. Channel opens iff `Q>0` (`decayAllowed_iff`);
  `Γ=g·Q^p` grows with release (`decayWidth_strictMono_in_Q`); width ratios `(Q₁/Q₂)^p`
  (  `widthRatio_eq`); branching fractions partition unity (`branchingRatio_sum`).
- `Physics.RelativisticKinematics`: relativistic two-body HEP toolkit. Källén
  `λ(M²,m₁²,m₂²)=(M²−(m₁+m₂)²)(M²−(m₁−m₂)²)` (`kallen_factor`), `≥0` at threshold
  (`kallen_nonneg_of_threshold`); CM momentum `p*=√λ/2M` positive on open channels (`pStar_pos`,
  bridged via `pStar_pos_of_decayAllowed`), `√(M²−4m²)/2` (equal) / `M/2` (massless). Daughter energies
  conserve energy (`energy_conservation`) and are on-shell `E₁*²−p*²=m₁²` (`daughter1_onShell`).
  Breit–Wigner `1/((s−M²)²+M²Γ²)` peaks at `s=M²` (`breitWigner_le_peak`), half-max at `s=M²±MΓ`
  (`breitWigner_halfMax`) — PDG-free.
- `Physics.DecayMasterFormula`: multichannel master formula `Γ=Φ·W` (generalises the HEP decay-readout
  paper). Discharge product `W(e)=∏_k g_k^{e_k}` multiplicative (`dischargeProduct_add`), unit-on-inactive
  (`dischargeProduct_zero`), unique under factorization (`productLaw_unique`); master width positive
  (`masterWidth_pos`), branching partitions unity (`masterWidth_branching_partition`); phase space
  `p*/(8πM²)` (`relativisticPhaseSpace_pos`); `g·Q^p` is the single-slot case
  (`decayWidth_eq_masterWidth`); 8 derived γ-rational generators reproduce benchmark weights
  (`K⁺→π⁺=30576/101250`, `φ→KK=21/25`, `φ→3π=4/25`), species exponent pattern kept comparison-side.
- `Physics.MandelstamInvariants`: `2→2` scattering invariants. 4D Minkowski form polarises
  (`mink4_polarization`); under conservation `p₁+p₂=p₃+p₄` the sum rule `s+t+u=∑mᵢ²` holds
  (`mandelstam_sum`, `mandelstam_sum_onShell`); the Breit–Wigner variable is the Mandelstam `s`, so a
  cross-section peaks when the invariant mass hits the resonance (`resonance_peaks_at_invariant_mass`).
- `Physics.MultichannelReadout`: branching readout closure. Per-channel width `Γᵢ=Φᵢ·W(eᵢ)` positive
  (`channelWidth_pos`), total positive (`totalWidth_pos`), branchings in `[0,1]`
  (`branching_nonneg/_le_one`) and partition unity (`branching_partition`); relative strengths are pure
  discharge ratios — `φ` `KK̄:3π` coupling ratio `21/4` (`phi_KK_to_threePion_coupling_ratio`) — with
  per-channel ledgers the only inputs.
- `Physics.DalitzPlot`: three-body phase space. Pairwise invariants obey the Dalitz sum rule
  `s₁₂+s₁₃+s₂₃ = (p₁+p₂+p₃)²+∑mᵢ²` (`dalitz_sum`), on-shell `= M²+∑mᵢ²` (`dalitz_sum_onShell`); the
  third coordinate is fixed by the other two (`dalitz_constraint`) so the plot is 2D — PDG-free.
- `Physics.DecayLaw`: exponential decay law. Survival `S(t)=e^{−Γt}` starts certain (`survival_zero`),
  positive (`survival_pos`), memoryless `S(t+s)=S(t)S(s)` (`survival_add`), strictly decreasing
  (`survival_antitone`); width–lifetime reciprocity `Γτ=1` (`lifetime_mul_width`), half-life halves the
  population (`survival_halfLife`); branching `bᵢ=Γᵢτ` bridges the readout to the clock
  (`branching_eq_width_mul_lifetime`).
- `Physics.ColliderVariables`: rapidity is the additive boost coordinate. A `(mT,y)` momentum reads back
  `y` (`rapidity_momentum2`); a boost shifts `y↦y+η` (`rapidity_additive`) so rapidity *gaps* are
  boost-invariant (`rapidity_difference_boost_invariant`); invariant mass is preserved
  (`invariantMassSq_boost_invariant`) and `mT²=m²+p_T²≥m²` (`transverseMassSq_ge_massSq`) — reuses
  `Geometry.Lorentz`'s boost group.
- `Physics.CrossingSymmetry`: all-incoming `s/t/u` channels. Squared mass is reflection-invariant
  `Q(−p)=Q(p)` (`mink4_neg`); each channel equals its complementary pairing (`crossing_s/t/u`); the
  sum rule `s+t+u=∑mᵢ²` is manifestly leg-symmetric (`crossing_sum`, `crossing_sum_onShell`).
- `Physics.PartialWaves`: Legendre angular series `W(x)=∑aℓPℓ`. `P₀..P₃` normalise to `1`
  (`legendre_one_*`), obey the three-term recurrence (`legendre_recurrence_2/3`) and parity
  (`legendre_parity_*`); the forward–backward asymmetry isolates the odd waves
  `W(x)−W(−x)=2(a₁x+a₃P₃)` (`fb_asymmetry`), even distributions are FB-symmetric.
- `Physics.NBodyPhaseSpace`: the `Rₙ=R₂⊗R_{n−1}` recursion skeleton. Threshold `∑mᵢ` peels one particle
  (`threshold_succ`) down to the two-body base (`threshold_two`), an open channel contains its
  subsystem (`allowed_subsystem`); independent invariants `3n−7` rise by `3` per particle
  (`numInvariants_succ`), giving the Dalitz `2` at `n=3` (`numInvariants_three`).
- `Physics.StellarLuminosity`: bounded Stefan–Boltzmann. Planck mode energy rises with `T`
  (`planckMeanEnergy_strictMono_in_T`); windowed luminosity positive, hotter-brighter, capped by
  `T·∑N_m` (`luminosity_pos/_strictMono_in_T/_ceiling`); inner shells outshine outer
  (`shellLuminosity_antitone_in_bath`).
- `Physics.EinsteinRing`: `θ_E² = 4·G_eff(φ)·M·κ` = deflection × baseline (`einsteinRadiusSq_eq_deflection`),
  positive, squares back (`einsteinRadius_sq`), `θ_E ∝ √M` (`einsteinRadius_strictMono_in_M`).
- `Physics.GravitationalRedshift`: lapse-ratio shift `1+z = N_o/N_e`. Redshift out (`redshift_pos`),
  blueshift in (`redshift_neg`), zero iff equal (`redshift_zero_iff`), deeper-wells-more
  (`redshift_strictAnti_in_emit`), factors compose (`redshiftFactor_compose`); now-slice anchored
  (`nowSlice_redshift_eq`).
- `Physics.MixingUnitarity`: generation mixing matrix unitary *by derivation*. Flavour/mass bases are
  two orthonormal bases of the 3-generation space (`generations_eq_quark_triples`), so `V = U_u†·U_d`
  is a product of unitaries (`mixing_unitary`); unitarity triangles `∑_k V*_{ki}V_{kj}=δ_{ij}` close
  (`unitarity_triangle`), columns conserve probability `∑_k|V_{ki}|²=1` (`unit_column_norm`), aligned
  bases give `V=1` (`mixing_when_aligned`). Angles deferred to `MixingAngles`.
- `Physics.MixingAngles`: the **angle from the masses** (Gatto–Sartori–Tonin). Structural input = the
  **texture zero** (lightest generation has no leading-order self-mass — natural in the shell ladder),
  so `M = [[0, b], [b, m₂−m₁]]`. Masses *are* eigenvalues: `det=−m₁m₂`, `tr=m₂−m₁`
  (`textureMatrix_det`/`_trace`), `m₂,−m₁` solve the char. equation (`masses_are_eigenvalues`),
  `b=√(m₁m₂)`; mass basis orthonormal (`eigenvectors_orthogonal`). Headline: `tan²θ = m₁/m₂ =
  m_light/m_heavy` (`mixingTan_sq`, i.e. `θ_C≈√(m_d/m_s)`), below 45° (`mixingTanSq_lt_one`), shrinks
  with the hierarchy (`mixingTanSq_strictMono`). Bundle `mixing_angles_closure`. Plug ladder masses ⇒
  angle; no fitted CKM entry. Masses are eigenvalues *with explicit eigenvectors*
  (`textureMatrix_mulVec_heavy/_light`) and the angle is proven the eigenvector slope
  (`mixingTan_eq_lightVec_slope`) — diagonalising rotation, not a stipulation.
- `Physics.TextureZeroDerivation`: the texture zero **derived, not assumed** — canonical form of a
  seesaw. Symmetric sector `[[p,b],[b,q]]` carrying spectrum `{m₂,−m₁}` ⟺ `tr=m₂−m₁`, `det=−m₁m₂`
  (`carriesSpectrum`/`carriesSpectrum_roots`). Real texture-zero representative exists **iff** `det≤0`
  i.e. `0≤m₁m₂` (`textureZero_realizable_iff`, `seesaw_opposite_sign`): available precisely because the
  light gen is a lifted would-be-zero mode. `p=0` + spectrum ⇒ `q=m₂−m₁`, `b²=m₁m₂` uniquely
  (`textureZero_unique`) = `MixingAngles.textureMatrix`. Capstone `ansatz_forces_GST`: protection +
  seesaw ⇒ matrix fixed ⇒ `tan²θ=m₁/m₂`. Bundle `texture_zero_closure`. Only inputs: protected zero
  mode (`p=0`) + lift (`det<0`).
- `Physics.CabibboInterference`: `V_us` from **both** sectors. `sinθ=√(m₁/(m₁+m₂))`,
  `cosθ=√(m₂/(m₁+m₂))`, `sin²+cos²=1` (`sin_sq_add_cos_sq`), GST `(sinθ/cosθ)²=m₁/m₂`
  (`slopeSq_eq_massRatio`), orthonormal columns (`sectorRot_col_norm`). `V_us=(R_uᵀR_d)₀₁` = exact
  interference `sinθ_u·cosθ_d−cosθ_u·sinθ_d` (`Vus_eq_interference`, the `√(m_d/m_s)−√(m_u/m_c)`
  structure), `|V_us|≤sinθ_d+sinθ_u` (`abs_Vus_le`), down-dominant. Bundle `cabibbo_closure`.
- `Physics.NeutrinoSeesaw`: light-neutrino **mass** from the same texture zero. `[[0,m_D],[m_D,M_R]]`
  = `symMatrix 0 M_R m_D` carries `{m_heavy,−m_ν}` (`seesaw_carriesSpectrum`, `det=−m_D²<0`). Exact
  `m_heavy·m_ν=m_D²` (`seesaw_product` = the texture's `b²=m₁m₂`), suppression `m_ν<m_D²/M_R`
  (`seesaw_suppression`), below Dirac (`lightNeutrino_lt_dirac`), `→0` as `M_R→∞`
  (`lightNeutrino_lt_of_heavier_MR`). Bundle `neutrino_seesaw_closure`. **Scope:** `m_D, M_R` are free
  inputs (not HQIV-fixed) — this is the seesaw *relations* + texture-zero unification, NOT an absolute
  `m_ν`. The textbook seesaw is a graft; native mechanism is `NeutrinoCurvatureSuppression`.
- `Physics.NeutrinoCurvatureSuppression`: the **HQIV-native** ν-mass mechanism (the seesaw "pulled out
  of the structure"). Native action has no mass term; mass = `M_constituent−E_bind` (a curvature well).
  The neutrino is chargeless (`SMEmbedding` `ν_R`: `Y=Q=0`), minimal content (`l²=1`), the chirally-
  protected would-be-zero mode ⇒ no inner well ⇒ `neutrinoTreeMass=0`. Mass = outer-horizon residual:
  `m_ν = m_χ · γ/S(m)`, `S(m)=(m+1)(m+2)=latticeSimplexCount m`, `γ=2/5` the monogamy complement. The
  factor `γ/S(m)` is **parameter-free**: `neutrinoSuppression_pos`, `_lt_one`, `_strictAnti` (deeper
  horizon ⇒ lighter ν). **Uniquely derived** (`neutrinoSuppression_unique_from_foundations`): numerator
  `γ = 1−α` is the unique chargeless complement of the unit split (`gammaHQIV_eq_one_sub_alphaEM`);
  denominator is the area, strictly-monotone⇒injective (`latticeSimplexCount_strictMono`); closure shell
  `referenceM+2` is the *unique* shell whose horizon area = octonionic carrier surface `7·8 =
  imaginaryDim·carrierMultiplicity` (`outerHorizonArea_closure_eq_carrier`, `closureShell_radial_bracket`
  = radial bracket `(7,8)`, `neutrinoClosureShell_unique`) ⇒ `1/140` forced (`= (1−α)/(7·8)`).
  **Rhymes-not-identical** (`neutrino_rhymes_seesaw`): `m_ν = m_χ²/M_eff` with `M_eff = m_χ·S(m)/γ` a
  *derived* horizon scale (`effectiveHeavyScale_gt_charged`: `>m_χ`), never a free `M_R`. Bundle
  `NeutrinoCurvatureSuppressionClosure`. **Open:** absolute `m_χ` normalization + ordering (legacy
  `1/140·M_Z` overshoots `Σm_ν<0.12 eV` ~`10⁸`, inverts ordering). Factor uniquely pinned; `m_χ` open.

### Topology
- `Topology.NullLatticeComplex`: finite closed 3-complexes; no finite complex satisfies quadratic
  growth on all shells; canonical realiser `S3NullReference`; Euler-characteristic obstructions.
- `Topology.ShellBudget`: signed shell ledger as a thermodynamic arrow; early-closed shells
  `m ≤ 2` (`isEarlyClosedShell_iff_le_two`).

### Chemistry — the molecular ladder, every constant the geometry of the binding well
- `Chemistry.ShellStructure`: octet & subshell capacities **derived** — `2(2ℓ+1)=4ℓ+2`, `2n²` rule,
  periodic doubling, and `octetCapacity_eq_carrierMultiplicity` (the chemical octet **is** the so(8)
  carrier dimension).
- `Chemistry.Aufbau`: the Madelung `(n+ℓ)` filling **derived** as the network step-distance order —
  the canonical `1s…7p` subshell list is *exactly* the `(n+ℓ, n)`-lexicographic order
  (`madelung_sorted`, strictly increasing key), accounts for all `118` electrons
  (`principalList_length`), and its prefix sums are the noble-gas closures `2,10,18,36,54,86,118`
  (`noble_gas_closures`). Gives the concrete occupancy `principalBlock : Fin Z → ℕ` with period-3+
  witnesses (`sodium_valence_n_three`, `potassium_valence_n_four` — the `4s`-before-`3d` inversion)
  the legacy period-≤2 Compton guess could not produce. The **valence count** is now a function:
  `topPrincipal` = highest occupied shell (the period), `valenceCount` = electrons there, with
  `carbon_valence`/`oxygen_valence`/`sodium_valence`/`chlorine_valence`/`potassium_valence` and the
  valence octet `noble_valence_octet : valenceCount {10,18,36} = octetCapacity` (the carrier `8`,
  read off the filled configuration).
- `Chemistry.LonePairs`: electron budget `2L+B=V` closes; octet ⇒ four steric domains.
- `Chemistry.VSEPR`: bond angles from equilibrium, `c = −1/(d−1)` (`balanced_unit_contacts_cos`),
  sp³ `−1/3`.
- `Chemistry.Dipole`: subset Gram resultant `|S|(d−|S|)/(d−1)`; all-bond cancellation.
- `Chemistry.BondOrder`: bond order = saturated 2×2 Gram coupling (Cauchy–Schwarz saturation = rank-1).
- `Chemistry.Allotrope`: same atoms, different bond graph = one law. Octet budget `cap = octetCapacity
  − valence` partitioned over coordination `k`: `bondOrder_partition` (`p·k = cap`),
  `bondOrder_antitone_in_coordination` (diamond<graphite<carbyne), aromatic `3/2`
  (`aromaticRingOrder_three_halves`) and ozone `1≤√2≤2` (`ozone_bond_brackets`) via the spine
  `ShellStructure.geometricBondOrder`; the triple ceiling forbids 1-coordinate carbon
  (`carbon_k_one_exceeds_ceiling`); ring strain `polygonInteriorAngleDeg` with `hexagon_matches_sp2`
  (benzene strain-free), pentagon 108°, strict monotonicity; the σ-angle `−1/(d−1)` is the derived
  VSEPR equilibrium cosine (`bondAngleCos_eq_vsepr`); length contraction with `strong = monogamyHalf`.
- `Chemistry.Polarizability`: `α = q²/k`, harmonic floor `q²r²/(2I)`, hydrogenic `n⁶/z⁴`.
- `Chemistry.Spectroscopy`: rovibrational constants from `(rₑ, Dₑ, μ)`; Morse closure
  `ωₑxₑ·4Dₑ = ωₑ²`; VB ionic resonance bracket `k_ion ≤ k_eff ≤ k_cov`.
- `Chemistry.LineSpectra`: atomic line spectra as differences of the hydrogenic levels
  `Binding.hydrogenicBindingHartree` — the **Rydberg formula** `ΔE = R z²(1/n_f²−1/n_i²)` with
  `R = μ/2` (`transitionEnergy_eq_rydberg`), emission positivity (`transitionEnergy_pos`), Moseley
  `z²` scaling (`transitionEnergy_scales_zEff`), Lyman > Balmer ordering (`lyman_gt_balmer`), the
  `n_i→∞` series/ionization limit `R z²/n_f²` (`transitionEnergy_tendsto_seriesLimit`), and numeric
  anchors — hydrogen Rydberg `½ Ha = 13.6057 eV` (`rydbergEv_eq`), Balmer-α `5/72 Ha`, Lyman-α
  `3/8 Ha`. No new constant (unit label `Binding.hartreeToEv` only).
- `Chemistry.Binding`: Slater screening derived (`0.35/0.85/1.00` from `α/referenceM`) — now the full
  three-level placement `slaterShieldingIncrement` (`_same`/`_adjacent`/`_deep`/`_outer` ⇒
  `0.35/0.85/1.00/0` by Gauss enclosure, so the derived `slaterDeepShell` is used and outer shells
  no longer over-screen); hydrogenic `μZ²/(2n²)`; effective charge `≥ 1`; outside contact
  `G_eff(η)=η^α`. The abstract `block` occupancy is closed by the derived `Aufbau.principalBlock`:
  `slaterEffectiveChargeAufbau` **reproduces the textbook Slater `Z_eff`** — H `1`, He `1.65`,
  Li `1.30`, Be `1.95`, C `3.25`.
- `Chemistry.Electronegativity`: **Mulliken χ = (IE+EA)/2** from the hydrogenic binding (no empirical
  table). Closed form `χ = μ(z_ion²+z_aff²)/(4n²)` (`mullikenChi_eq`); uniform charge = hydrogenic IE
  (`atomElectronegativity_eq_ionization`). The **periodic trend is a theorem** — χ strictly increasing
  in `Z_eff` at fixed shell (`electronegativity_strictMono_in_zEff`) and decreasing down a group
  (`electronegativity_antitone_in_shell`). Closes the previously-abstract `pull` in
  `Spectroscopy.bondIonicCharacter`: pure covalent ⇔ equal χ (`pure_covalent_iff_equal_chi`), distinct
  `Z_eff` ⇒ polar (`polar_bond_of_distinct_zEff`); tied to `Binding.slaterEffectiveChargeAufbau` with
  the unit-charge floor (`atomElectronegativityAufbau_ge_hydrogenFloor`).
- `Chemistry.Biomolecule`: **Watson–Crick H-bond counts** from donor/acceptor complementarity (xor).
  The donor/acceptor state is the monogamy two-valuedness (`donor_states_eq_monogamyPair :
  card Donor = monogamyPairMultiplicity`); the canonical counts are computed, not assumed — A·T = 2
  (`adenine_thymine_two`), G·C = 3 (`guanine_cytosine_three`), G·C strictly more bonded
  (`gc_more_bonded_than_at`), wobble mismatch rejected (`guanine_thymine_not_canonical`). The
  **uniform helix width** is the constant purine(2)+pyrimidine(1) cyclomatic ring count
  (`canonical_rung_constant_width = 3`).
- `Chemistry.Reaction`: **stoichiometry + Hess's law**, no empirical heat literal. Element-vector
  `ReactionGate` with mass conservation (`apply_preserves_totalElementAtoms`); reaction energy is the
  change in the state function `stateEnergy E s = ∑ sᵢEᵢ` (`reactionEnergy_eq_stateEnergy_diff`), so
  path energy telescopes (`hess_path_energy`), is **path-independent** (`hess_path_independent`), and
  vanishes on a cycle (`hess_cycle_zero`). The water gate `2H+O→H₂O` balances
  (`waterSynthesisGate_balanced`) and is exothermic **conditioned on the spine binding ordering**
  `E(H₂O) < 2E(H)+E(O)` (`water_exothermic_of_binding`) — the `285.8 kJ/mol` literal is dropped.
- `Chemistry.BondEnergy`: **reaction energy from spine bond orders**, closing `Reaction`'s parametric
  `E`. Species energy is `−depthUnit·(bond order)` with the order read off
  `ShellStructure.geometricBondOrder`; substituting into `reactionEnergy` gives the bond-energy
  balance `ΔE = depthUnit·(reactant orders − product orders)` (`reactionEnergy_bondEnergy`), so a
  reaction is exothermic **iff** it raises total bond order (`exothermic_of_bondOrder_increase`,
  with `endothermic_*`/`thermoneutral_*` companions) — premise `depthUnit > 0`, no kJ/mol number. A
  single σ-bond is the homonuclear `geometricBondOrder 1 1 = 1` (`singleBondOrder_eq_one`), so water
  (two O–H bonds vs bondless atoms) **discharges** the `Reaction` hypothesis
  (`water_exothermic_from_bondOrder`); since `E` is now a state function, all of `Reaction`'s Hess
  machinery applies unchanged.
- `Chemistry.Molecule`: **worked molecules on the zero-point shell ladder.** The per-shell mode count
  is octonion-anchored `availableModes m = carrierMultiplicity·C(m+2,2) = 4(m+2)(m+1)`
  (`availableModes_eq`, the `4 = 8/2`), the per-mode zero point is `φ(m)/2 = m+1` (`perModeZeroPoint`),
  so the single-site budget closes to `siteModeEnergy m = 4(m+2)(m+1)²` (`siteModeEnergy_closed_form`,
  no fitted coefficient), positive and strictly outward-rising (`siteModeEnergy_strictMono`). A
  molecule is the additive trace `siteEnergyTrace = ∑ᵢ siteModeEnergy(shellᵢ)` (homonuclear
  `n·siteModeEnergy m`); the **diatomic H₂** at equal shells is `8(m+2)(m+1)²`
  (`h2SiteEnergy_same_shell_closed_form`), evaluating at the proton anchor `referenceM = 4` to the
  exact `1200` (`h2SiteEnergy_referenceM_numeric`). Bundle `moleculeH2Discharged_holds`. **Generalised
  for broader use:** the budget is stated for an *arbitrary carrier dimension* `c`
  (`siteModeEnergyOfCarrier c m = (c/2)(m+2)(m+1)²`, covering the Hopf ladder `c∈{1,2,4,8}`, octonion
  case `siteModeEnergy_eq_ofCarrier`, monotone `siteModeEnergyOfCarrier_mono_in_carrier`); a
  *polyatomic* closed form (`siteEnergyTrace_closed_form`) that is **extensive** — fragments compose
  over `Fin.append` (`siteEnergyTrace_append`) and `List` concat (`listSiteEnergy_append`,
  `siteEnergyTrace_eq_listSiteEnergy`); and a *heteronuclear* diatomic closed form
  (`h2SiteEnergy_closed_form`). Constants: `8 = carrierMultiplicity`, `φ`, `latticeSimplexCount`,
  `referenceM` — all foundation/shell. **Scope:** the dimensionless zero-point *mode-energy budget* of
  the separated-atom ladder, *not* the bond well — H₂/LiH/H₂O binding magnitude still needs the
  bonded-horizon Casimir layer.
- `Chemistry.BondedHorizon`: bond mode surplus `E_joint − E_frag₁ − E_frag₂` on `siteModeEnergy`
  (structural non-additivity; negative surplus = binding convention).
- `Chemistry.DynamicBinding`: factorization `E_bind = η·surplus·vev·κ(ξ)` with TUFT vev geometric
  mean and curvature feedback `γ·(4/8)·σ(ξ)/σ(ξ_lock)`; H₂ readout scaffold at lock-in shells.
- `Chemistry.AtomDischarge`: `(Z) →` discharge observables via derived `Aufbau` (C/N/Na witnesses,
  factorization uniqueness on the slot table — NIST masses comparison-only).

---

## 3. New targets (live list)

Ordered roughly by value × tractability. Keep the ethics in §1.

**Chemistry / atomic (close the remaining "abstract parameter" gaps)**
- [x] **Aufbau / Madelung ordering** onto the spine — landed as `Chemistry.Aufbau`: the `(n+ℓ, n)`
  filling is proved to be the canonical subshell order (`madelung_sorted`), gives the concrete
  `principalBlock : Fin Z → ℕ`, and `Chemistry.Binding.slaterEffectiveChargeAufbau` now substitutes
  it for the abstract `block`. Period-3+ valence (`sodium_valence_n_three`) works; the per-element
  **valence count** is the function `valenceCount`/`topPrincipal`. The Slater rule was upgraded to
  the correct three-level placement and now **reproduces textbook `Z_eff`** (H/He/Li/Be/C).
  *Next:* numeric `Z_eff` for a worked period-3 atom (Na `2.2`, Cl) — needs `Fin 11+` sum expansion
  (no `Fin.sum_univ_n` lemma past `eight`); and the IUPAC group-number map off `valenceCount`.
- [x] **Atomic line spectra** (Rydberg/Bohr) — landed as `Chemistry.LineSpectra`, built on
  `Binding.hydrogenicBindingHartree` (the heavy legacy `AtomicExcitations` rebuilt clean). Rydberg
  formula, series limit, Lyman/Balmer ordering, Moseley `z²`, numeric `13.6 eV`/Balmer-α/Lyman-α.
- [~] **Worked molecules** (LiH, H₂O) as numeric instances on `Physics.Binding` /
  `Chemistry.Spectroscopy`, anchored to the now-slice rather than legacy mass tables. *Clean first
  step landed* as `Chemistry.Molecule`: the **H₂ site-energy** closed form `8(m+2)(m+1)² = 1200 @
  referenceM` is spine-native — the per-shell mode count is octonion-anchored
  (`availableModes_eq`, `4 = carrierMultiplicity/2`), per-mode zero point `φ(m)/2 = m+1`, single-site
  budget `4(m+2)(m+1)²` (`siteModeEnergy_closed_form`), additive molecular trace, and the
  proton-anchor numeric `1200` (`h2SiteEnergy_referenceM_numeric`, bundle
  `moleculeH2Discharged_holds`). *Structural bonding layer landed* as `Chemistry.BondedHorizon`
  (mode surplus) + `Chemistry.DynamicBinding` (η·surplus·vev·κ factorization with H₂ scaffold).
  *Next:* LiH/H₂O numeric surplus inputs and eV calibration — still comparison-only, not GMTKN55 fit.

  *Remaining clean ports identified in the legacy `Hqiv/QuantumChemistry` survey (Mathlib-only,
  ethics-clean), ranked:*
- [x] **Allotrope network** — landed as `Chemistry.Allotrope`: octet partition `p·k=cap`, bond order
  antitone in coordination, aromatic `3/2`, ozone bracket, triple-bond ceiling, ring-strain
  `(n−2)·180/n` (hexagon = sp², strict monotone), σ-angle = derived VSEPR cosine. Re-anchored to
  `octetCapacity`/`geometricBondOrder`/`VSEPR`/`monogamyHalf`.
- [x] **Electronegativity / ionic character** — landed as `Chemistry.Electronegativity`: Mulliken
  `χ = (IE+EA)/2` from the hydrogenic binding, closed form `μ(z_ion²+z_aff²)/(4n²)`, the periodic trend
  as a theorem (↑ in `Z_eff`, ↓ in shell), and it closes the formerly-abstract `pull` in
  `Spectroscopy.bondIonicCharacter` (pure covalent ⇔ equal χ; distinct `Z_eff` ⇒ polar), tied to the
  derived `slaterEffectiveChargeAufbau`. *Next:* a concrete cross-period χ ordering (C<N<O numeric,
  F blocked by the `Fin 9` Slater sum) and a Pauling `ΔEN`→ionic-% calibration.
- [x] **Reaction stoichiometry + Hess's law** — landed as `Chemistry.Reaction`: element-balance
  conservation `apply_preserves_totalElementAtoms` + telescoping path energy via the state function
  `stateEnergy` (`hess_path_energy`/`hess_path_independent`/`hess_cycle_zero`); the empirical
  `285.8 kJ/mol` is dropped and water exothermicity is conditioned on the spine binding ordering
  (`water_exothermic_of_binding`). *Follow-on landed:* `Chemistry.BondEnergy` derives that energy
  from `geometricBondOrder` (`reactionEnergy_bondEnergy`), making exothermicity a bond-order theorem
  and **discharging** the water hypothesis (`water_exothermic_from_bondOrder`).
- [x] **Watson–Crick H-bond counts** — landed as `Chemistry.Biomolecule`: A·T=2, G·C=3, GC stronger,
  donor/acceptor = monogamy two-valuedness, uniform helix width — Mathlib-only `decide`/`omega` wins.

**Algebra / gauge**
- [ ] `Algebra.OctonionAxisAngles` (carrier rotation geometry) — golf onto `Algebra.Octonion`.
- [x] **Non-abelian plaquette curvature** — landed as `Physics.PlaquetteCurvature`: matrix
  transport on the carrier as a monoid hom (holonomy = ordered matrix product), curvature
  `F = ⁅D₁,D₂⁆` zero iff commuting, flat commutator-plaquette, and a concrete `SO(8)` witness — the
  phase-lift rotation `Q₁₇` and colour-axis rotation `Q₀₇` share `e₇`, giving `F ≠ 0` and a
  non-trivial Wilson loop `e₁↦e₀`. Anchored to the foundation's `planeGenerator`/`bracket`.
- [x] **Lattice Stokes / Wilson-loop composition** — landed as `Physics.WilsonLoop`: holonomy over a
  tiling is the ordered product of plaquette holonomies; gluing multiplies (Stokes additivity),
  flatness propagates from plaquettes to the loop, area enters as `holⁿ`, and a single curved
  plaquette obstructs flatness (`wilsonLoop_curvature_obstructs_flat`). Kinematic only — not a
  statistical area law.
- [~] **CKM/PMNS from Fano overlaps + holonomy phases** (see [CKM_PMNS_FANO_OVERLAP.md]) — the
  **CP-phase layer** (`Physics.CPHolonomyPhase`: rephasing-invariant Jarlskog `J ∝ sin δ`) **and the
  full `3×3` unitary matrix** (`Physics.CKMMixingMatrix`: `V = R₂₃R₁₃R₁₂` proved unitary,
  `VᴴV = 1`, Jarlskog closed form, assembled from spine mass-ratio angles `ckmSpine_unitary`) are
  **landed**, and the **overlap weights are now graph-theoretic** (`Physics.FanoMixingWeights`:
  `sin²θ = overlap/total = 1/3` forced by `PG(2,2)` incidence, feeding a unitary CP-violating
  `ckmFano`), and the **democratic `1/3` is now bent toward a hierarchy by the derived ladder**
  (`Physics.LadderMixingHierarchy`: `1/3` is the leading ladder rung `λ=1:2`, and mixing strictly
  shrinks with generational separation — feeding a mass-input-free `ckmLadder`), and the residual
  steepness is now pinned to the **mass spectrum itself** (`Physics.MassDrivenMixing`: GST as an exact
  monotone transfer function from the mass ratio, a geometric mass ladder reaching any observed angle),
  and the steepness is **derived from one source** — the content-class complexity `l² ∈ {1,4,9}`
  (`Physics.SectorMixingFromComplexity`: ν `l²=1` ⇒ degenerate ⇒ maximal = geometric `π/4`; quark
  `l²=9` ⇒ small; ordering `1<4<9`), cross-checked against the geometric/PMNS route, and **both CP
  phases are now derived from the one monogamy grading** — lepton `δ_PMNS=π/5=(γ/2)π` first order
  (`Physics.PMNSMatrix`), quark `δ_CKM=3π/32=π(γ/2³−γ/2⁵)/γ` second order (`Physics.CKMCPPhase`), each
  giving a non-zero closed-form Jarlskog. **Still open:** only the *sub-leading* mass splittings within a
  sector (exact `sin²θ₂₃≈0.57`, Cabibbo `≈0.05`, and hence the `J` *magnitudes* below their democratic
  baseline) and the absolute mass scale (`MassLadder` frontier). The *qualitative* mixing structure —
  three generations, democratic `1/3`, large lepton vs small quark mixing, and both CP phases — is now
  derived.

**Continuum / analysis**
- [~] Metric volume factor + covariant divergence `∇_μ J^μ` on `Geometry.ContinuumChart` — *partial
  port landed* as `Geometry.MetricGradient` (contravariant gradient, flat Minkowski inverse,
  coordinate divergence; constant-field lemmas) + `Physics.ChartMaxwell` (lock-in flat `∇φ = 0`,
  constant-current `div J = 0`). *Still open:* position-dependent metric / HQVM Christoffel connection
  and inhomogeneous coronal-stress jet (legacy `ModifiedMaxwell` plasma layer).
- [~] **Now-slice + continuous ξ + detuning bridge** — landed as `Physics.ContinuousHorizon`
  (`xiOfShell`, `sigmaXi`, brace readouts), `Physics.RindlerDetuning` (δ-corrected surfaces),
  `Physics.NowSliceHorizon` (lapse increment → global detuning; `gEffNow = φ^{3/5}`).
  **Discrete curvature closure landed** as `Physics.NowSliceFromLattice` (`lockinNowSlice`,
  `nowSliceFromLatticeDischarged_holds`; `Frontiers.now_slice_lockin_from_lattice_closed`,
  `now_slice_omegaK_lattice_structure_closed`, `now_slice_lockin_ages_closed`).
  *Still open:* dynamical `H(t)` from bulk hyperboloid; full continuous–discrete `Ω_k` identification
  on all horizons (parallel monotonicity + lock-in normalisation proved).
- [x] **`DiscreteHeat` generalized from `C₃` to `Cₙ`** — landed as `Physics.DiscreteHeatCycle` on the
  periodic mesh `ZMod n` (`[NeZero n]`), where the cyclic shift is a genuine `Fintype` bijection so
  the integration-by-parts reindexing holds for *every* mesh length: dissipation `⟨u,Δu⟩ = −‖∇u‖² ≤ 0`,
  the Fourier-symbol spectral bound `‖Δu‖² ≤ 4‖∇u‖²` (`4 = 2·degree`, the `C₃` `=3‖∇u‖²` a sharp
  special case), the exact Euler energy law, and the standard cycle CFL `4·dt·ν ≤ 2 ⇒ ‖u⁺‖² ≤ ‖u‖²`.
  *Next:* the optional discrete→semidiscrete continuum-limit statement (`h → 0` Fourier symbol `→ −k²`).

**Quantum mechanics**
- [x] **First interacting many-body model** — landed as `Physics.HubbardDimer`, mined from the legacy
  `Hqiv.QuantumMechanics.HubbardDimerFinite` and disentangled from its Kronecker /
  `FiniteManyBodyTensorScaffold` machinery to a single explicit Hermitian `4×4`. Exactly-solvable
  Ising dimer `H = −t(σx⊗I + I⊗σx) + λ(σz⊗σz)`: closed-form spectrum `{±λ, ±√(4t²+λ²)}` with explicit
  eigenvectors, ground energy `−√(4t²+λ²)`, a strictly positive gap for `t≠0`, and shell-anchored `λ`.
- [x] **Monogamy GHZ/W witnesses saturating CKW** — landed as `Physics.MonogamyWitness`, refining the
  legacy `Hqiv.QuantumMechanics.Monogamy{GHZ,W}Family` (which only *defined* the tangle values) into
  explicit amplitude tensors with *derived* tangles: one-tangle from `det ρ_A`, three-tangle from the
  Cayley hyperdeterminant. GHZ → purely tripartite (zero pairwise budget); W → CKW saturated
  (`τ_ABC = 0`). Connects back to the shell-weighted `correctedCkwMonogamy`.
- [x] **Half-filled Hubbard dimer + superexchange** — landed as `Physics.HubbardHalfFilling`, mined
  from `Hqiv.QuantumMechanics.HubbardDimerHalfFilledObservables`. Canonical charge-sector `H(t,U)`,
  exact spectrum `{0,U,(U±√(U²+16t²))/2}` with explicit eigenvectors, ground singlet, and the
  antiferromagnetic superexchange gap `J=(√(U²+16t²)−U)/2` with the Mott `J≤4t²/U` bound.
- [x] **Finite-dim Gleason/Born frame function + the dimension gap** — landed as
  `Physics.GleasonBorn`, upgrading the legacy `Hqiv.QuantumMechanics.BornGleasonDecisionScaffold`
  (pure roadmap markers, no theorems) to a real result on `ℂⁿ`: the overlap probability `‖⟪φ,ψ⟫‖²`
  is **additive over every orthonormal basis** (`frame_sum`, from Parseval) and **basis-independent
  / non-contextual** (`frame_basis_independent`), so unit states give measurement probabilities
  summing to `1` in any basis. Density mixtures stay frame functions (`mixFrame_sum_pure`) — the
  trace-rule Gleason direction. Crucially the **`dim≥3` hypothesis is proved necessary**:
  `gleason_fails_in_dim_two` exhibits the sextic `θ↦cos 6θ` as a frame function on the real circle
  (`sextic_isFrameFun`) that is provably **not** the quadratic form of any operator
  (`sextic_not_qform`, by over-determining `M` at `θ=0,π/2,π/4,π/3`). So a qubit-only model loses the
  rigidity that forces Born; the qutrit retains representability (`qutrit_frame_sum`). The analytic
  `dim≥3` converse stays cited, with `Measurement.bornProbN_unique_of_coherence` as finite substitute.
- [x] **Quantum contextuality (Kochen–Specker)** — landed as `Physics.KochenSpecker`, the
  contextuality complement to the Gleason work. Formalises the minimal Cabello–Estebaranz–García
  18-ray KS set in `ℝ⁴`: 9 orthogonal contexts certified by `decide` (`contexts_orthogonal`,
  `rays_nonzero`, `contexts_cover`), and **no noncontextual `{0,1}` value assignment exists**
  (`no_noncontextual_assignment`) by an `omega` parity argument (`9` odd `= 2·#true` even). This
  discharges the "genuinely-multidimensional contextuality" item: definite outcomes cannot be
  assigned to all projectors independently of context. The two remaining hard items are correctly
  left cited: the analytic `dim≥3` Gleason converse (a major standalone formalisation), and the
  `dim=3` minimal KS set (Conway–Kochen 31 rays, which lacks a parity proof).
  *Next candidates from the legacy QM tree:* the Hubbard double-occupancy / spin-correlation
  observables and their ground-state expectations; the qubit POVM (Busch) Gleason-type variant.

**Physics**
- [~] **Nuclear inside/outside + α-decay** — landed as `Physics.NuclearCluster` (inside/outside split,
  valley cap, post-α hook) + `Physics.AlphaDecayTunneling` (Q + barrier → Gamow, Geiger–Nuttall).
  *Next:* isotope panels, post-α cooperative network numerics, MeV Q calibration (comparison-only).
- [x] **Atom discharge pipeline** — landed as `Chemistry.AtomDischarge` (`(Z) →` observables via
  `Aufbau`; decay-uniqueness template on slot table).
- [x] **Strong SU(3) chart closure** — `StrongColorSu3` + `StrongColorSu3LieLaw` (full `f^{abc}`,
  64-pair Lie law), `StrongColorEmbed` (`8×8` carrier lift), `NonAbelianMatrixElement`
  (pipeline). *Still open:* real `𝔰𝔬(8)` / triality identification of embed image.
- [ ] `QuantumChemistry/ParticleShellStructure` is now ported; next, the **noble-gas closures** and
  valence count as Lean theorems (currently computational in Python).
- [ ] Lepton/quark mass-ratio readouts from `MassLadder` with explicit now-slice provenance.

**Hygiene / meta**
- [ ] Keep this doc and the `HqivSpine.lean` narrative in sync when modules land.
- [ ] Periodic `#print axioms` sweep over all headline theorems (CI guard idea: fail on any axiom
  outside the allowed three, or any `sorry`/`native_decide`/`import Hqiv`).

---

*Provenance:* this spine was mined and refined from the legacy `Hqiv.*` corpus across the
chemistry, nucleon-moment, gauge-holonomy, force-carrier, Maxwell-spectral, continuum-chart, and
discrete-heat threads, each disentangled to Mathlib-only and anchored to the foundation per §1.
