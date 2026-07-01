import HqivSpine.Foundation.ThreeGrowth
import HqivSpine.Foundation.Carrier
import HqivSpine.Foundation.Fano
import HqivSpine.Foundation.HopfLadder
import HqivSpine.Geometry.Lorentz
import HqivSpine.Geometry.DiscreteLaplacian
import HqivSpine.Geometry.SphericalHarmonics
import HqivSpine.Geometry.MaxwellSpectral
import HqivSpine.Geometry.ContinuumChart
import HqivSpine.Geometry.MetricGradient
import HqivSpine.Algebra.CayleyDickson
import HqivSpine.Algebra.Octonion
import HqivSpine.Algebra.So8
import HqivSpine.Algebra.Closure
import HqivSpine.Algebra.G2
import HqivSpine.Algebra.Gauge
import HqivSpine.Algebra.Triality
import HqivSpine.Algebra.Anomaly
import HqivSpine.Algebra.StrongColor
import HqivSpine.Algebra.StrongColorSu3
import HqivSpine.Algebra.StrongColorSu3LieCertificate
import HqivSpine.Algebra.StrongColorSu3LieLaw
import HqivSpine.Algebra.StrongColorEmbed
import HqivSpine.Algebra.SkewChartBridge
import HqivSpine.Algebra.SkewChartBridgeSu3Closure
import HqivSpine.Physics.Shell
import HqivSpine.Physics.Action
import HqivSpine.Physics.Gravity
import HqivSpine.Physics.Blackbody
import HqivSpine.Physics.LockIn
import HqivSpine.Physics.LockInMechanism
import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.CasimirClosureAction
import HqivSpine.Physics.BulkHyperboloidDynamics
import HqivSpine.Physics.JointClosureAction
import HqivSpine.Physics.Exclusion
import HqivSpine.Physics.SpinStatistics
import HqivSpine.Physics.Uncertainty
import HqivSpine.Physics.VonNeumann
import HqivSpine.Physics.GleasonBorn
import HqivSpine.Physics.KochenSpecker
import HqivSpine.Physics.Measurement
import HqivSpine.Physics.Evolution
import HqivSpine.Physics.Monogamy
import HqivSpine.Physics.CCR
import HqivSpine.Physics.PatchObstruction
import HqivSpine.Physics.FreeField
import HqivSpine.Physics.Binding
import HqivSpine.Physics.Curvature
import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Physics.RindlerDetuning
import HqivSpine.Physics.NowSliceHorizon
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.NowSliceCausalDiamond
import HqivSpine.Physics.ChartMaxwell
import HqivSpine.Physics.Age
import HqivSpine.Physics.Baryogenesis
import HqivSpine.Physics.BaryogenesisShellLadder
import HqivSpine.Physics.LeptonAbsoluteScale
import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.CarrierMonogamySuppression
import HqivSpine.Physics.SpineMassDischarge
import HqivSpine.Physics.HeavyQuarkAbsoluteScale
import HqivSpine.Physics.NeutrinoAbsoluteScale
import HqivSpine.Physics.AlphaRunning
import HqivSpine.Physics.NeutrinoMixing
import HqivSpine.Physics.Forces
import HqivSpine.Physics.ColorCasimir
import HqivSpine.Physics.TrappedCasimir
import HqivSpine.Physics.NonAbelianMatrixElement
import HqivSpine.Physics.CurvatureKernel
import HqivSpine.Physics.Proton
import HqivSpine.Physics.TuftBeltramiAnchor
import HqivSpine.Physics.TuftBeltramiMassFunctional
import HqivSpine.Physics.NestedHopfBinding
import HqivSpine.Physics.ContentClassCompositeTrace
import HqivSpine.Physics.SectorNestedHopfBinding
import HqivSpine.Physics.MassLadder
import HqivSpine.Physics.NucleonMoment
import HqivSpine.Physics.PlaquetteHolonomy
import HqivSpine.Physics.PlaquetteCurvature
import HqivSpine.Physics.WilsonLoop
import HqivSpine.Physics.CPHolonomyPhase
import HqivSpine.Physics.CKMMixingMatrix
import HqivSpine.Physics.FanoMixingWeights
import HqivSpine.Physics.LadderMixingHierarchy
import HqivSpine.Physics.MassDrivenMixing
import HqivSpine.Physics.PMNSCrossCheck
import HqivSpine.Physics.SectorMixingFromComplexity
import HqivSpine.Physics.PMNSMatrix
import HqivSpine.Physics.CKMCPPhase
import HqivSpine.Physics.NucleonLadder
import HqivSpine.Physics.ForceCarrier
import HqivSpine.Physics.DiscreteHeat
import HqivSpine.Physics.DiscreteHeatCycle
import HqivSpine.Physics.HubbardDimer
import HqivSpine.Physics.HubbardHalfFilling
import HqivSpine.Physics.MonogamyWitness
import HqivSpine.Physics.Thermodynamics
import HqivSpine.Physics.CMBBirefringence
import HqivSpine.Physics.ThermalArrow
import HqivSpine.Physics.StandardModelLagrangian
import HqivSpine.Physics.NuclearBinding
import HqivSpine.Physics.NuclearCluster
import HqivSpine.Physics.AlphaDecayTunneling
import HqivSpine.Physics.BBN
import HqivSpine.Physics.WeakDecay
import HqivSpine.Physics.GRFromMaxwell
import HqivSpine.Physics.StellarStructure
import HqivSpine.Physics.HadronSpectrum
import HqivSpine.Physics.GravitationalLensing
import HqivSpine.Physics.StellarCollapse
import HqivSpine.Physics.HadronDecayWidths
import HqivSpine.Physics.RelativisticKinematics
import HqivSpine.Physics.DecayMasterFormula
import HqivSpine.Physics.MandelstamInvariants
import HqivSpine.Physics.MultichannelReadout
import HqivSpine.Physics.DalitzPlot
import HqivSpine.Physics.DecayLaw
import HqivSpine.Physics.ColliderVariables
import HqivSpine.Physics.CrossingSymmetry
import HqivSpine.Physics.PartialWaves
import HqivSpine.Physics.NBodyPhaseSpace
import HqivSpine.Physics.StellarLuminosity
import HqivSpine.Physics.EinsteinRing
import HqivSpine.Physics.GravitationalRedshift
import HqivSpine.Physics.MixingUnitarity
import HqivSpine.Physics.MixingAngles
import HqivSpine.Physics.TextureZeroDerivation
import HqivSpine.Physics.CabibboInterference
import HqivSpine.Physics.NeutrinoSeesaw
import HqivSpine.Physics.NeutrinoCurvatureSuppression
import HqivSpine.Physics.Tunneling
import HqivSpine.Physics.Frontiers
import HqivSpine.Topology.NullLatticeComplex
import HqivSpine.Topology.ShellBudget
import HqivSpine.Chemistry.ShellStructure
import HqivSpine.Chemistry.Aufbau
import HqivSpine.Chemistry.LonePairs
import HqivSpine.Chemistry.VSEPR
import HqivSpine.Chemistry.Dipole
import HqivSpine.Chemistry.BondOrder
import HqivSpine.Chemistry.Polarizability
import HqivSpine.Chemistry.Spectroscopy
import HqivSpine.Chemistry.Binding
import HqivSpine.Chemistry.LineSpectra
import HqivSpine.Chemistry.Allotrope
import HqivSpine.Chemistry.Electronegativity
import HqivSpine.Chemistry.Biomolecule
import HqivSpine.Chemistry.Reaction
import HqivSpine.Chemistry.BondEnergy
import HqivSpine.Chemistry.Molecule
import HqivSpine.Chemistry.BondedHorizon
import HqivSpine.Chemistry.DynamicBinding
import HqivSpine.Chemistry.AtomDischarge

/-!
# HqivSpine — a clean, ground-up HQIV mass spine

A Mathlib-only restatement of the HQIV derivation path, built from scratch with the
benefit of hindsight: no imports from the legacy `Hqiv.*` tree, no `sorry`, no new
`axiom`, and a single physical anchor — the observer's **now slice**, which carries
the curvatures (`φ`, `Φ`, `Ω_k`) explicitly rather than masking them inside a hard
proton mass.

## The path, in order

1. **Foundation** — `transverseDim = 3` is the only combinatorial input.
   * `Foundation.ThreeGrowth`: null-shell counting, the quadratic/cubic hinge, and
     `(α, γ) = (3/5, 2/5)`.
   * `Foundation.Carrier`: the `8`-channel carrier, `7` imaginary directions,
     `so(8)` dimension `28 = 14 + 7 + 7` — all derived.
   * `Foundation.Fano`: the `PG(2,2)` incidence forced on the `7` directions.
   * `Foundation.HopfLadder`: the topological selection — the carrier `8` is the
     **maximum** Hopf-invariant-one dimension `{1, 2, 4, 8}` (Adams) and the next
     Cayley–Dickson rung (`16`, sedenions) leaves it, so the ladder terminates at `𝕆`.

2. **Geometry** — special relativity from the discrete null chart.
   * `Geometry.Lorentz`: rapidity boosts on the radial `1+1` Minkowski chart form a
     one-parameter group (`Λ(η)Λ(ξ) = Λ(η+ξ)`), are isometries (`ΛᵀgΛ = g`, so the
     quadratic form and bilinear pairing are invariant), preserve the forward null ray
     of the discrete cone, act equivariantly on the rapidity-labelled lattice carrier,
     and extend to a partial `3+1` boost on the embedded radial plane. Spatial `O(3)`
     rotations fix time and preserve `minkowskiSq4`, the Euclidean inner product, and the
     cross-product norm — boosts and rotations bundle into `full_lorentz_closure`.
   * `Geometry.DiscreteLaplacian`: the discrete-analysis layer — the 7-point central
     second-difference Laplacian `Δ_h` on the observer chart `ℝ³`. Additivity and `h ↦ −h`
     symmetry are stencil algebra; domain rescaling `x ↦ c•x` makes the Laplacian pick up `c²`
     (`HQVM_discreteLaplacian_comp_smul`), and on a separable cosine mode `Δ_h` acts with the
     **Fourier symbol** `2(cos kh − 1) = −(4/h²)sin²(kh/2)`
     (`HQVM_discreteLaplacian_cosModeOnAxis_sin_sq`), the standard discrete Helmholtz symbol
     (continuum limit `−k²`).
   * `Geometry.SphericalHarmonics`: the discrete ↔ continuum **mode-count bridge**. On `S²` the
     cumulative spherical-harmonic degeneracy is `∑_{ℓ≤L}(2ℓ+1) = (L+1)²`
     (`sum_two_mul_add_one_range_succ_sq`); the spine's shell capacity `cumulativeModes m =
     4(m+1)(m+2)` is the same `Θ(m²)` class up to the octonion factor `4`, and indeed
     `cumulativeModes m/(m+1)² → 4` (`tendsto_cumulativeModes_div_sphericalHarmonicCumulative`).
     The `64 = 8×8` real-dof threshold (one fermion generation) is first reached at shell
     `m = 3` (`minimal_shell_ge_sixty_four`).
   * `Geometry.MaxwellSpectral`: the EM/quaternion Maxwell carrier on its compact phase manifold.
     The four-component `Fin 4` block lives on the unit quaternions `S³` (intrinsic dim
     `transverseDim = 3`), with Laplace–Beltrami eigenvalues `λ_ℓ = ℓ(ℓ+2)` and degeneracy `(ℓ+1)²`
     (`harmonicDimS3_eq_succ_sq`) — the *same* `(ℓ+1)²` the `S²` bridge runs against. The O-Maxwell
     extension adds one Cayley–Dickson direction to land on `S⁴` with `λ_ℓ = ℓ(ℓ+3)`; all
     degeneracies are positive (`harmonicDimS3_pos`, `harmonicDimS4_pos`).
   * `Geometry.ContinuumChart`: a *computable continuum-calculus* hook. The flat
     `EuclideanSpace ℝ (Fin 4)` model (`spacetimeDim = 4`, `chart_dim`) gives well-typed Fréchet
     `coordsGradient` and coordinate divergence `coordsDivergence` pulled back onto the discrete
     `Fin 4 → ℝ` slots; constants are flat (`coordsGradient_const`, `coordsDivergence_const`). This
     is the bridge from the discrete action slots to continuum calculus — deliberately flat
     Riemannian, *not* a Lorentzian metric or the null-lattice embedding (separate layers).

3. **Algebra** — the octonions as a genuine algebra.
   * `Algebra.CayleyDickson`: `𝕆 = CayleyDickson³ ℝ`, dimension `8` proved.
   * `Algebra.Octonion`: norm, two-sided inverse (division algebra), the basis,
     alternativity, the eight-square identity, and the bridge onto the Fano
     incidence.
   * `Algebra.So8`: the genuine rotation algebra `𝔰𝔬(n)` from the standard skew
     basis — `finrank 𝔰𝔬(8) = 28` by `decide` (no determinant, no `native_decide`),
     with a real Lie bracket-closure certificate.
   * `Algebra.Closure`: the skew-symmetric phase-lift `Δ` and plane generators as
     members of the genuine `𝔰𝔬(8)`; the `28 = 14 + 7 + 7` branching.
   * `Algebra.G2`: the rotation chain `𝔰𝔬(8) ⊃ 𝔰𝔬(7) ⊃ 𝔤₂` with genuine dims
     `28 ⊃ 21 ⊃ 14` and the branchings `21 = 14 + 7`, `28 = 14 + 7 + 7`.
   * `Algebra.Gauge`: the SM gauge generators inside `𝔰𝔬(8)` — `u(1)` hypercharge,
     `su(2) ≅ so(3)` with proven closure, `su(3)` colour in the `so(6)` block, and
     the SM gauge dimension `8 + 3 + 1 = 12`.
   * `Algebra.Triality`: the three fermion generations forced by the three 8-dim
     `Spin(8)` slots and their order-3 triality cycle — `24` carrier / `48` chiral slots.
   * `Algebra.Anomaly`: the finite SM anomaly traces (`U(1)³`, grav, mixed, `SU(N)³`)
     vanish per generation and over the three triality slots.

4. **Physics** — from carrier to masses without smuggling.
   * `Physics.Shell`: `referenceM = 4`, `φ(m) = 2(m+1)`, `1/α_GUT = 42 = 6·7`,
     `α = 3/5`, and the shell-running coupling.
   * `Physics.Action`: the discrete O-Maxwell Lagrangian on the `8`-channel carrier ×
     `Fin 4` spacetime — antisymmetric field strength `F = dA`, kinetic `−¼F²`, and the
     Euler–Lagrange covector whose vanishing **is** the inhomogeneous Maxwell equation
     `∑_μ F = 4πJ`; the gauge channel count is tied to the derived `carrierMultiplicity`.
   * `Physics.Gravity`: the Friedmann sector and the **total action** — `γ = 1−α = 2/5`,
     `H(φ) = φ`, varying-G `G_eff(φ) = φ^α`, and the constraint `(3−γ)φ² = 8π G_eff·ρ`
     whose action form `S_grav = 0` **is** Friedmann; `totalAction = S_OMaxwell + S_grav`
     with joint stationarity (`total_action_closure`), anchored to the now-slice `φ`.
     **Horizon vs Planck-pole tug of war:** the varying-G map `φ ↦ φ^α` (`α = 3/5`)
     has *exactly two* non-negative fixed points (`gEff_fixed_iff_nonneg`) — `φ = 0`,
     the **horizon** (outer), and `φ = 1`, the **Planck pole** (inner). The flow runs
     both ways: on `0 < φ < 1` inward Ricci contraction `φ^(3/5) > φ` pulls toward the
     Planck pole while outward expansion `φ^(5/3) < φ` pulls toward the horizon
     (`tug_of_war_interior`). Every interior shell is squeezed between the two
     attractors; the lock-in is the *discrete* balance, not a continuum limit — the
     lattice carries constant discrete curvature (`Foundation.shellNumer_second_difference`,
     second difference `≡ 2`) and an incompressible per-shell zero-point slice
     `N_m·ω_m = 8` (`Blackbody.shell_zeroPoint_slice_const`), so it cannot be smoothed away.
   * `Physics.Blackbody`: the Planck spectrum on the finite shell mode list —
     `ω_m = 1/(m+1)`, Bose occupation `n_B`, and the **Rayleigh–Jeans ceiling**
     `planckMeanEnergy < T` (one line from `x+1 < eˣ`, the discrete cure for the UV
     catastrophe) with the Wien-tail bound `n_B ≤ 1/(e−1)`; mode count `N_m = 8(m+1)`
     gives the **Stefan–Boltzmann ceiling** `U(T) ≤ T·∑N_m` (no `σT⁴` integral);
     the **Wien displacement constant is exactly `1`** in Planck units via the
     transition shell `m*(T) = ⌊1/T⌋−1` (at the lock-in bath `m* = referenceM`);
     a *derived* greybody split `cos²(2β)+sin²(2β)=1` with `β = α·log(m+1)`; **Kirchhoff's
     law** (emissivity = absorptivity, with the Planck spectrum as equilibrium witness);
     and photon-gas `P = U/3`, `s = (4/3)U/T`. **Lock-in stability**
     (`proton_lockin_stable`): shell `m` is its own emission-resonance fixed point
     (`transitionShellIndex ω_m = m`), its emission count is the horizon radius
     `⌊1/ω_m⌋ = m+1` (a standing/trapped mode, no outward drift), and the inner shell
     is strictly hotter — so the proton at `4` radiates at count `5` and cannot
     collapse to `3` without absorbing the gap `ω₃ − ω₄ = 1/20`.
   * `Physics.LockIn`: **why `referenceM = 4`** — the discrete horizon ⇄ Planck-pole
     tug of war. Unlocked modes `N(m) = 8(m+1)` grow strictly outward; a closed sector
     needs capacity `C = 40`. Below `4` they fall short (under-capacity → outward pull
     to unlock modes); above `4` they exceed it (over-capacity → inward pull to shed the
     surplus); at `4` they match exactly (`referenceM_lockin_balance`). `N(m) = C` has a
     **unique** solution (`referenceM_unique_balance`), and the signed `modeDeficit C−N(m)`
     is a restoring force (positive below, negative above, zero at `4`). So `4` is the
     *balanced* lock-in, not merely the minimal feasible shell — the discrete face of
     `Gravity`'s two fixed points (horizon `φ=0`, Planck pole `φ=1`). The capacity is
     **derived, not posited**: `C = 40 = dim 𝔰𝔬(8) + carrier + base = 28 + 8 + 4`
     (`sectorClosureCapacity_eq_so8_carrier_base`, with `𝔰𝔬(8)` the genuine
     `finrank (skewMatrices 8)` and `28 = 14+7+7`), so `referenceM = 4` is pinned with
     **no posited integer** (`lockin_fully_closed`).
   * `Physics.LockInMechanism`: **the three-layer lock-in mechanism** — bundles selector
     (`lockInDrive` / `modeDeficit` restoring drive, `referenceMLockInMechanism`),
     monogamy inward wall vs. Pauli floor at shell `2` (`monogamy_floor_below_lockin`),
     blackbody stability (`proton_lockin_stable`), democratic `η_mode(4) = 1/3`, and the
     continuous ⇄ discrete tug-of-war parallel (`lockin_continuous_discrete_parallel`).
   * `Physics.ClosureAction`: **variational shell lock-in** — closure budget
     `V(m)=(N(m)−C)²/(2C)` with unique minimum at `referenceM` (`closureBudgetPotential_eq_zero_iff`),
     gradient `∂V/∂m = −8·modeDeficit/C` (`closureBudgetGradient_eq_neg_eight_modeDeficit`),
     overdamped flow aligned with `lockInDrive` (`shellGradientDrive_eq_lockInDrive`), Hopf
     chart `hopfLockinWinding+1 = referenceM`, phase lift `φ(m)/6` on `Δ`, and capstone
     `referenceMClosureAction` (mechanism + action). No spring toward `4` — the last freeish
     shell parameter is discharged as sector-closure stationarity.
   * `Physics.Exclusion`: **why it can't collapse to the Planck pole** — the inward wall is
     *spin-statistics*, the face of informational monogamy (`γ = 2/5`), not the capacity
     number. (1) **Degeneracy pressure**: monogamy = injective occupation, so pigeonhole
     (`pauli_pigeonhole`, via `Fintype.card_le_of_injective`) forces `N` quanta to need
     `N ≤ cumulativeModes m = 4(m+1)(m+2)` states; the pole offers only `cumulativeModes 0 =
     8` so the chiral content `48` provably cannot sit there (`chiral_content_no_collapse_to_pole`).
     (2) **Pair conservation**: a net quantum number changes only via charge-neutral `(+q,−q)`
     partner pairs (`netCharge_pairExtend`), invariant under any move sequence
     (`netCharge_applyPairs`), so a nonzero net never reaches the vacuum
     (`pair_moves_cannot_reach_vacuum`). Bundled in `spin_statistics_no_collapse`. Honest
     scope: this earns the inward wall as a *theorem* (degeneracy floor is monotone in the
     content), but does not by itself single out `4` — `48` chiral slots already fit by
     shell `2`; the value `4` still rides on `LockIn`'s mode balance.
   * `Physics.SpinStatistics`: the **quantum mechanics behind the wall** — spin from the
     `Spin(8)` double cover. The chiral spinors `8s±` flip sign under `2π`
     (`rotation2piPhase = −1`), the two-valuedness *is* half-integer spin, with the concrete
     `su(2) ≅ so(3)` angular-momentum closure (`spin_su2_closure`). That `2π` sign **equals**
     the fermionic exchange sign (`spin_statistics_connection`), and exchange antisymmetry is
     the antisymmetric Fock space of dimension `C(K,N)`: **Pauli exclusion is a vanishing
     dimension** — `0 < fermionicDim K N ↔ N ≤ K` (`pauli_exclusion`), zero when `K < N`,
     while bosons never exclude (`bosonicDim_pos`). The carrier being fermionic makes the
     inward wall a zero-dimensional space (`chiral_fermionicDim_pole_zero`: `C(8,48)=0`),
     the QM form of `Exclusion`'s no-collapse (`spin_statistics_spine`).
   * `Physics.Uncertainty`: the **dynamical** companion — non-commuting spin observables
     cannot both be sharp. On the qubit `ℂ²` with Pauli `σₓ,σᵧ,σ_z` and `[σₓ,σ_z] = −2iσᵧ`
     (`Qubit.pauli_comm_xz`), the **Robertson bound** `Var(σₓ)·Var(σ_z) ≥ |⟨σᵧ⟩|²`
     (`Qubit.pauli_robertson`) and its Heisenberg product form `Δσₓ·Δσ_z ≥ |Re⟨σᵧ⟩|`
     (`Qubit.pauli_heisenberg_product`) — the Cauchy–Schwarz/commutator skeleton behind
     Heisenberg, specialised to spin-½ (no finite-dim `[x,p]=iħ`, by the trace obstruction).
   * `Physics.CCR`: that trace obstruction made a theorem — **no exact `[A,B]=1` on a fixed
     finite matrix algebra** (`Tr` of a commutator is `0`, but `Tr 1 = n>0`):
     `not_exists_matrix_CCR_one`, with the qubit case `not_exists_qubit_CCR_one`. This is
     *why* `Uncertainty` carries the mechanism via the Robertson bound on the (traceless)
     Pauli observables rather than a literal canonical pair.
   * `Physics.PatchObstruction`: the same finite-patch ontology made to **discharge continuum
     obligations**. A finite abelian patch field has a single (`Unit`) topological sector, so the
     instanton / Pontryagin / first-Chern / `U(1)`-winding slots vanish and the θ-term is
     θ-independent — **no θ-vacuum** (`patchThetaTerm_independent`). And the local patch algebra
     is **abelian** (diagonal operators on `ℂ^n`), so every commutator vanishes
     (`patch_microcausality`) — Haag–Kastler microcausality for free. Bundled in
     `obstructions_discharged`.
   * `Physics.FreeField`: the Hilbert-space realisation of that microcausality. A fixed-time
     Cauchy slice is `LatticeHilbert n = EuclideanSpace ℂ (Fin n)` with **diagonal smeared field**
     operators `Φ(w)ψ i = wᵢψ i`; composition multiplies weights (`smearedField_comp`), so the
     algebra is abelian and the **operator** commutator vanishes
     (`smearedField_opCommutator_eq_zero`). The commutator `[A,B]=A∘B−B∘A` is bilinear in both
     factors (`opCommutator_sum_univ_first/second`), and fields with **disjoint sampling supports**
     annihilate (`smearedField_comp_eq_zero_of_disjoint`) — the lattice shadow of spacelike
     separation.
   * `Physics.VonNeumann`: the **measurement** layer — observable ↔ self-adjoint
     (`Observable` = `Matrix.IsHermitian`), expectation `⟨O⟩_ψ = ⟪ψ,Oψ⟫`, and the **Born
     rule**: computational-basis probabilities `‖ψ i‖²` sum to `‖ψ‖²`
     (`sum_bornProbCompBasis_eq_norm_sq`), hence to `1` on a pure state
     (`sum_bornProbCompBasis_pure`); the rank-one projector `|ψ⟩⟨ψ|` is Hermitian with unit
     trace, giving the pure-state density matrix (`DensityMatrix.fromPure`).
   * `Physics.GleasonBorn`: the **Born functional as a Gleason frame function** on `ℂⁿ`.
     The overlap probability `bornFrame φ ψ = ‖⟪φ,ψ⟫‖²` is additive over *every* orthonormal
     measurement basis, `∑ᵢ bornFrame φ (b i) = ‖φ‖²` (`frame_sum`, from Parseval), so for a unit
     state the outcome probabilities sum to `1` in any basis (`frame_sum_pure`) and the total is
     basis-independent / non-contextual (`frame_basis_independent`). Convex mixtures
     `∑ₖ wₖ|φₖ⟩⟨φₖ|` stay frame functions (`mixFrame_sum`, `mixFrame_sum_pure`) — the
     representable / trace-rule direction of Gleason in every finite dimension. The `dim≥3`
     hypothesis is shown **necessary**: `gleason_fails_in_dim_two` exhibits the sextic `cos 6θ` as a
     frame function on the real circle that is *not* any quadratic form (`sextic_not_qform`),
     whereas the qutrit keeps      representability (`qutrit_frame_sum`). The hard `dim≥3` converse
     itself is cited (ratio-uniqueness in `Measurement` is the finite substitute).
   * `Physics.KochenSpecker`: the **contextuality** complement — the minimal Cabello–Estebaranz–
     García 18-ray Kochen–Specker set in `ℝ⁴`. The 9 contexts are certified orthogonal bases
     (`contexts_orthogonal`, `rays_nonzero`) with each ray in exactly two of them
     (`contexts_cover`), and **no noncontextual `{0,1}` value assignment** can pick one true ray
     per context (`no_noncontextual_assignment`) — a parity contradiction (`9` odd `= 2·#true`
     even). State-independent: definite outcomes cannot be assigned to all projectors regardless of
     context.
   * `Physics.Measurement`: the **real-carrier** Born layer and collapse as energy
     conservation. Weights `(ψ i)²/normSq ψ` sum to `1` (`sum_bornProbN_eq_one`) and are
     **forced from first principles** — the unique normalised amplitude-square-coherent
     probability vector, with *no* nonnegativity assumption (`bornProbN_unique_of_coherence`).
     Collapsing to
     outcome `i` routes the realised energy `(ψ i)²` to the basis component and the remainder to
     a nonnegative **auxiliary channel**, so `normSq ψ = normSq(collapse) + auxTransfer` with
     `auxTransfer ≥ 0` (`measurement_energy_closure`, `auxTransfer_nonneg`) — measurement
     repartitions informational energy, it never destroys it. The collapsed energy is exactly
     recoverable through a birefringence redshift `z = e^{β/κ}−1`
     (`measurement_observed_energy_with_redshift`).
   * `Physics.Evolution`: the **dynamics** layer — digital time steps are inner-product-
     preserving bijections (`Gate`, discrete unitaries), composed as a list with no PDE.
     Evolution preserves the inner product and hence the informational energy `normSq`
     (`evolution_preserves_ip`, `evolution_preserves_energy` — a discrete Schrödinger
     conservation law). Outcome relabellings `σ` are gates (`permGate`) that merely permute
     Born weights (`bornWeight_permGate`), so the **total** Born probability is conserved under
     any evolution (`sum_bornProbN_evolution`): measurement statistics are stable in time.
   * `Physics.Monogamy`: the **monogamy axiom as monogamy of entanglement** — the CKW
     three-party tangle inequality `τ(A:B)+τ(A:C) ≤ τ(A:BC)` (`ckwMonogamy`), weighted by the
     spine's own mode budget `etaMode m = newModes m / cumulativeModes referenceM =
     8(m+1)/120` (so `etaMode 4 = 1/3`, `etaMode_referenceM`). The weighting preserves CKW
     (`corrected_monogamy_of_ckw`) and, when `≤ 1`, **tightens** the pairwise budget
     (`corrected_pair_sum_le_uncorrected`); a φ-augmented factor gives a decoherence proxy
     non-increasing outward (`coherenceProxy_step_nonincreasing`). The same axiom that is
     Pauli exclusion in `Exclusion` is entanglement-sharing here.
   * `Physics.MonogamyWitness`: **concrete three-qubit GHZ/W states realising CKW**, grounding the
     abstract tangles of `Monogamy` in explicit amplitude tensors `ψ : Fin 2³ → ℝ` whose tangles are
     *derived*. The **one-tangle** `τ(A:BC) = 4·det ρ_A` is computed from the reduced density matrix
     (`oneTangle_ghz = 4a²b²`, `oneTangle_w = 4x²(y²+z²)`); the **three-tangle** `τ_ABC = 4·|Hdet|` is
     computed from the Cayley `2×2×2` hyperdeterminant (`hyperdet_ghz = a²b²`, `hyperdet_w = 0`). The
     CKW residual `pairBudget = τ(A:BC) − τ_ABC` then gives: monogamy on every state (`ckw_monogamy`,
     also through the shell-weighted `corrected_ckw_monogamy`); **GHZ has no pairwise entanglement**
     (`ghz_pairBudget_zero`, all of it genuinely tripartite); and **W saturates CKW**
     (`w_saturates_ckw`, `τ_ABC = 0`). Canonical normalised endpoints `τ(A:BC)=τ_ABC=1` (GHZ at
     `1/√2`) and `τ(A:BC)=8/9`, `τ_ABC=0` (W at `1/√3`). Honest scope: individual pairwise
     concurrences (Wootters) are not re-derived — only the one- and three-tangle endpoints and the
     CKW structure between them.
   * `Physics.Binding`: the 8×8 composite-trace binding network on `Fin 8` / `Fin 28`.
   * `Physics.Curvature`: the imprint `δ_E(m) = N₆₇ · (1/(m+1))(1 + α·ln(m+1))` with
     `N₆₇ = 6⁷√3` every factor a foundation integer (`6 = 2·3`, `7 = imaginaryDim`, `√3`).
     **Shell selection (closed-curvature leg):** the `1/(m+1)` decay beats the
     `1 + α·ln(m+1)` growth at `α = 3/5`, so `δ_E` is *strictly antitone* hence
     **injective** — a closed-curvature value pins a unique shell
     (`curvature_pins_unique_shell`). Together with the emission-resonance fixed
     point `transitionShellIndex (ω_m) = m` in `Blackbody`, this is the
     "why information lives on shell `m`" pair: a scale lights up its shell, a
     closed curvature pins it.
   * `Physics.NowSlice`: the sole physical anchor — curvatures `φ`, `Φ`, `Ω_k`, the
     dimensionless now-scale (lapse `N = 1 + Φ + φ·t`), and the slice imprint `Ω_k·δ_E`.
   * `Physics.Age`: wall-clock vs apparent age and the ratio `1 + φ·t/2` from the lapse.
   * `Physics.Baryogenesis`: the baryon asymmetry as a now-slice curvature readout
     `Ω_k·δ_E(m)` (positive, shell-decaying); the `6.10×10⁻¹⁰` value is comparison-only.
   * `Physics.AlphaRunning`: `1/α_GUT = 42 = 6·imaginaryDim`, the monotone running, and
     the **naked high-scale** coupling `1/α_eff(EW) = 42·(1 + c·(3/5)·log 13)` ("naked on
     the W", `O(1/128)`) — the screened `1/137` is a chemistry-layer number, not a target.
   * `Physics.NeutrinoMixing`: maximal mixing `θ = π/4` from the lock-in shell `4 = 2²`
     (`Ω = 2`, so `sin 2θ = 1`) and the CP phase `δ = (γ/2)π = π/5`.
   * `Physics.Forces`: the force-sector map — `1` EM, `3` weak, `4` strong octonion
     channels partitioning the `8` carrier channels (no independent gluon field).
   * `Physics.ColorCasimir`: colour Casimirs from `N_c = transverseDim = 3` —
     `C_A = 3`, `C_F = 4/3`, `C_A/C_F = 9/4`.
   * `Physics.TrappedCasimir`: strong binding as `trapped zero-point budget × normalised
     SO(8) selection`; the per-mode `φ/2` cancels, so the cell is exactly `α_eff`.
   * `Physics.CurvatureKernel`: the unified curvature log kernel `K(x,c) = 1 + c·α·log x`;
     `1/α_eff = 1/α_GUT · K(φ+1,c)`, with contact below ladder by monotonicity.
   * `Physics.Proton`: the proton as a now-slice readout (`massUnit × factor`), tied
     to the binding network — not a hard MeV literal.
   * `Physics.MassLadder`: now-scale-normalized hadrons, leptons, nuclei, atoms.
   * `Physics.NucleonMoment`: nucleon magnetic moments as the same network readout on the 3-quark
     frame, every constant read off the foundation (constituent magneton = `transverseDim = 3`,
     `B = 1/transverseDim`, dressing `1 + α/8` with `α = alphaRat transverseDim = 3/5` over the
     `carrierMultiplicity = 8` octonion directions). Closed form `μ = 4Q_a − Q_b` gives `μ_p = +3`,
     `μ_n = −2`, ratio exactly `−3/2` (`proton_neutron_ratio`); dressed `μ_p = 120/43 ≈ 2.791`
     (PDG 2.793, `dressed_proton_moment`). Gell-Mann–Nishijima charges, no PDG/current-mass inputs;
     the SU(6) Clebsch weights are *forced* by orthonormality (`orthonormal_complement_swaps_sq`,
     `clebschWeights_unique`) and the `−3/2` ratio is a fixed point of every uniform dressing.
   * `Physics.PlaquetteHolonomy`: the discrete gauge layer. Parallel transports live in the monoid
     `Function.End X`; the closed plaquette holonomy `e₀·e₁·e₂·e₃` (`discreteSquareHolonomy`) and
     the Wilson-line `pathHolonomy` are genuinely non-commutative for non-abelian transports — the
     discrete seed of curvature `F = [D,D]`. Holonomy is a homomorphism on path concatenation
     (`pathHolonomy_append`) and trivial transports give trivial holonomy (the flat discrete-Stokes
     limit). Cutoff-native: finitely many edges on a `Fin 4` cycle.
   * `Physics.PlaquetteCurvature`: the **concrete non-abelian curvature** `F = [D, D]`. Matrix
     transport `carrierTransport M` (acting on the octonion carrier `Fin 8 → ℝ` by `mulVec`) is a
     **monoid homomorphism** (`carrierTransport_mul`/`_one`), so the plaquette holonomy *is* the
     ordered matrix product `M₀M₁M₂M₃` (`quarterEdge_holonomy`). The discrete field strength
     `discreteCurvature D₁ D₂ = ⁅D₁, D₂⁆` vanishes **iff** the transports commute
     (`curvature_eq_zero_iff_commute`), and a commuting commutator-plaquette `(g,h,g⁻¹,h⁻¹)` has
     trivial holonomy (`commutatorPlaquette_flat`) — the flat/abelian limit. The witness is built
     from `quarterTurn i j` (the `π/2` rotation in the `(eᵢ,eⱼ)` plane, a foundation-anchored signed
     permutation in `SO(8)` with `(Qᵢⱼ)ᵀ = Qⱼᵢ`): the phase-lift rotation `quarterTurn 1 7` (the `Δ`
     plane `(e₁,e₇)`)      and the colour-axis rotation `quarterTurn 0 7` **share the colour axis `e₇`**
     and do not commute, so `F ≠ 0` (`curvature_nonzero`) and the Wilson loop
     `Q₁₇·Q₀₇·Q₇₁·Q₇₀` is non-trivial (`holonomy_witness` sends `e₁ ↦ e₀`, `holonomy_nontrivial`).
     A **second witness** runs the same machinery in the weak planes `(e₂,e₃)`, `(e₂,e₄)` — the
     planes of `Gauge.weakL₁`, `weakL₂` whose bracket is `⁅L₁,L₂⁆ = −L₃` (`weakPlane_generator`
     ties the rotation to `weakL₁`): the SU(2)≅SO(3) curvature `weak_curvature_nonzero` and Wilson
     loop `weak_holonomy_witness` (`e₂ ↦ e₃`), the group-level face of that non-abelian bracket.
     Transport is packaged as a `MonoidHom` (`carrierTransportHom`). Bundled in
     `plaquetteCurvatureDischarged_holds`.
   * `Physics.WilsonLoop`: **lattice Stokes** over a tiling. The Wilson loop of a tiled region is the
     ordered product of its plaquette holonomies (`wilsonLoop`); gluing two tilings multiplies them
     (`wilsonLoop_append`, discrete Stokes additivity); a curvature-free region has trivial loop
     (`wilsonLoop_flat`, `flat_tiling_trivial`); `n` copies of a plaquette accumulate as `holⁿ`
     (`wilsonLoop_replicate`, the discrete area seed). The witness
     `wilsonLoop_curvature_obstructs_flat` shows a loop flat everywhere **except one** curved colour
     plaquette still rotates `e₁ ↦ e₀` — curvature cannot be tiled away. Bundled in
     `wilsonLoopDischarged_holds`. Kinematic Stokes/flatness only — not a statistical area law.
   * `Physics.CPHolonomyPhase`: **CP violation as a holonomy phase** — the complex U(1)
     complexification of `WilsonLoop`. The link `link θ = e^{iθ}` is a unit transport (`link_mul`,
     `conj_link`); the abelian plaquette holonomy is its flux phase `e^{iΦ}`
     (`u1Holonomy_eq_link_flux`), trivial iff the flux is quantized in `2π` (`u1Holonomy_eq_one_iff`,
     `u1Holonomy_nontrivial` sends `Φ=π ↦ −1`). The **Jarlskog invariant**
     `J = Im(V_us V_cb V*_ub V*_cs)` is the imaginary part of a closed flavour-space loop:
     **rephasing-invariant** (`jarlskog_rephasing` — the CP phase cannot be rotated away), zero for a
     real CKM (`jarlskog_real`, CP conserved), and `J = (∏|V|)·sin δ` for one holonomy phase `δ`
     (`jarlskog_phase`, `jarlskog_phase_ne_zero`). The missing CP piece the real `MixingAngles`/
     `CabibboInterference` could not see. Bundled in `cpHolonomyDischarged_holds`.
   * `Physics.CKMMixingMatrix`: **the full `3×3` unitary CKM matrix**, assembling the spine pieces.
     Three plane rotations `R₁₂, R₂₃` (real, mass-ratio angles) and `R₁₃(δ)` (carrying the holonomy
     phase) are each proved unitary (`rot12_unitary`, `rot23_unitary`, `rot13_unitary`); their product
     `V = R₂₃·R₁₃(δ)·R₁₂` is unitary by composition (`ckm_unitary`, `ckm_unitary_apply : VᴴV = 1`) —
     a genuine `U(3)` element. The four entries (`ckm_us/cb/ub/cs`) give the Jarlskog invariant in
     closed form `J = c₁₂c₁₃²c₂₃s₁₂s₁₃s₂₃·sin δ` (`ckm_jarlskog`). Assembled from spine mass-ratio
     angles (`ckmSpine`, `ckmSpine_unitary`), CP violation `ckmSpine_cp_violation` is non-zero iff the
     fibre holonomy is genuine — no PDG matrix fit. Bundle `ckmMixingDischarged_holds`.
   * `Physics.FanoMixingWeights`: **mixing weights from Fano incidence, not mass ratios.** The overlap
     weight `overlap v w` counts shared Fano lines; it is forced by the `Foundation.Fano` incidence —
     `1` off-diagonal (`overlap_distinct`), `3` diagonal (`overlap_self`) — so the leading mixing
     fraction is the graph ratio `sin²θ = overlap(v,w)/overlap(v,v) = 1/3` (`fano_sinSq_eq_overlap`),
     a single rational with no fitted sine. Feeding it into all three planes gives `ckmFano`, unitary
     (`ckmFano_unitary_apply`) and CP-violating (`ckmFano_cp_violation`) — the *angle* now pinned by
    incidence counts. Bundle `fanoMixingDischarged_holds`. (Democratic overlap baseline `1/3`, not
    the measured hierarchy — that is the mass-ratio refinement of `MixingAngles`.)
  * `Physics.LadderMixingHierarchy`: **bends the democratic baseline with the derived mass ladder.**
    Feeds the Beltrami ladder eigenvalues `λ(g) = g+1` (`MassLadder`, *derived* — not free masses)
    into the GST mixing fraction, so `sin²θ(gₗ,gₕ) = (gₗ+1)/((gₗ+1)+(gₕ+1))` (`sinθLadder_sq`) is a
    fixed rational. The Fano democratic `1/3` is exactly the leading rung `λ = 1:2`
    (`democratic_eq_leading_ladder`) — incidence and spectrum agree at leading order — and the ladder
    strictly suppresses mixing with generational separation (`ladder_mixing_strictAnti`), dropping
    below `1/3` once rungs differ by two (`ladder_below_democratic`): the correct *direction* of the
    hierarchy, derived. The angles assemble a unitary (`ckmLadder_unitary`), CP-violating
    (`ckmLadder_cp_violation`) CKM matrix `ckmLadder` with **no free mass input**. Bundle
    `ladderMixingDischarged_holds`. (Right direction, derived; the linear ladder is too mild to match
    the steep measured magnitudes — the true spectral weighting functional remains the open physics.)
  * `Physics.MassDrivenMixing`: **the residual hierarchy *is* the mass spectrum.** Makes GST an exact
    transfer function: `sin²θ = m_light/(m_light+m_heavy) = (1+m_heavy/m_light)⁻¹` (`sinθMass_sq`,
    `sinθMass_sq_eq_oneDiv`), strictly decreasing in the mass ratio (`angle_strictAnti_in_massRatio`)
    — a steeper hierarchy *is* a smaller angle. For a geometric mass ladder `m(g)=m₀·rᵍ` the fraction
    is the closed form `1/(1+r^{gₕ−gₗ})` (`geomMixing_sq`), strictly decreasing in the steepness `r`
    (`geomMixing_strictAnti_r`) and reaching **any** target angle (`geomMixing_lt_eps`); a steep ladder
    `r>2` strictly beats the mild linear ladder (`geom_below_linear`). Bundle
    `massDrivenMixingDischarged_holds`. (The transfer function is derived; the steepness `r` — the
    absolute/steep mass spectrum — is the remaining `MassLadder` frontier, so the open mixing question
    is now a single sharply-stated *mass* input, not a separate mechanism.)
  * `Physics.PMNSCrossCheck`: **the mixing question, asked from two places.** The geometric/incidence
    route (`NeutrinoMixing.θ₂₃ = π/4` maximal, `FanoMixingWeights.sin²θ₁₂ = 1/3` — the tri-bimaximal
    values) and the mass-transfer-function route (`MassDrivenMixing`) are made to meet, inverting the
    transfer function: maximal `θ₂₃` ⇔ neutrino **mass degeneracy** `mₗ = mₕ`
    (`sinθMass_sq_eq_half_iff`, `atmospheric_forces_degeneracy`), and democratic `θ₁₂` ⇔ the **leading
    ladder rung** `mₕ = 2mₗ` (`sinθMass_sq_eq_third_iff`, `solar_forces_leading_rung`). Both routes thus
    demand a *mild* neutrino spectrum (ratios `1`, `2`), while a *steep* quark spectrum gives small CKM
    angles through the identical law (`steeper_is_smaller`): one mechanism, two regimes — large lepton
    and small quark mixing. Bundle `pmnsCrossCheckDischarged_holds`. (Routes and meeting points derived;
    the joint *prediction* is the near-degenerate neutrino mass ratio, a testable consequence.)
  * `Physics.SectorMixingFromComplexity`: **closes the loop with one spectral source.** Identifies the
    geometric mixing steepness with the content-class intrinsic wave complexity `l² ∈ {1,4,9}`
    (`MassLadder.intrinsicWaveComplexity`; `sectorSteepness c = l²`), deriving *both* regimes from one
    number: neutrinos (`l²=1`) are degenerate (`neutrino_mass_degenerate`) ⇒ maximal `sin²θ = 1/2`
    (`neutrino_mixing_maximal`), which **equals the geometric `π/4`** (`neutrino_matches_geometric_maximal`)
    — the two-place cross-check satisfied by a derived source; quarks (`l²=9`) are steep ⇒ `sin²θ = 1/10`
    for adjacent generations (`quark_adjacent_mixing`), strictly below the neutrino value
    (`quark_below_neutrino`); and the complexity ordering `1<4<9` (`sectorSteepness_strictMono`) orders
    the mixing. Bundle `sectorMixingDischarged_holds`. (Regime and ordering derived — *why* lepton mixing
    is large and quark mixing small is now a theorem; exact values need sub-leading splittings, scale
    stays the frontier.) The charged-lepton sector (`l²=4`) gives the intermediate `1/5`
    (`chargedLepton_adjacent_mixing`), so adjacent mixing is strictly ordered `ν 1/2 > charged-ℓ 1/5 >
    quark 1/10` (`adjacent_mixing_sector_ordering`).
   * `Physics.PMNSMatrix`: **the lepton mixing matrix and a derived `J_PMNS`.** Assembles the PMNS matrix
    from spine angles — solar `sin²θ₁₂=1/3` (Fano), atmospheric `θ₂₃=π/4` (shell), phase `δ=π/5`
    (monogamy). Tri-bimaximal at leading order (`pmnsTBM`, unitary, CP-free `pmnsTBM_jarlskog` — CP is
    gated by the reactor angle); turning on `θ₁₃` (`pmnsReactor`) keeps unitarity and gives the
    closed-form Jarlskog `J = (√2/6)(1−s₁₃²)s₁₃ sin δ` (`pmnsReactor_jarlskog_value`). With the derived
    phase `π/5`, lepton CP violation is real once `θ₁₃≠0` (`pmns_cp_from_derived_phase`). Bundle
    `pmnsDischarged_holds`. (Two large angles + phase derived; only the reactor magnitude `s₁₃` is the
    open sub-leading input; `J ≈ 0.02` at the physical `s₁₃≈0.15`.)
   * `Physics.CKMCPPhase`: **the quark CP phase + a numerical CKM Jarlskog** — the quark companion of the
    lepton `π/5`. The CP-odd holonomy skew `γ/2³ − γ/2⁵`, normalised by `γ` (which cancels) and lifted by
    `π`, gives the derived quark phase `δ_CKM = 3π/32` (`ckmCPPhase_eq`) — the *second-order* slot
    difference where the neutrino phase was the *first-order* `(γ/2)π`. With the Fano angles
    `ckm_jarlskog` collapses to `J = (4√3/81)·sin δ` (`ckmFano_jarlskog_value`), non-zero at the derived
    phase (`ckmFano_cp_violation_derived`, `J ≈ 0.025`). Bundle `ckmCPDischarged_holds`. (Closes the open
    `δ` input flagged by `CKMMixingMatrix`; the `J` magnitude is the democratic baseline upper bound —
    the measured `J ≈ 3·10⁻⁵` needs the steep-quark angle suppression, the remaining fine structure.)
   * `Physics.NucleonLadder`: **one anchor, real nucleon masses.** The abstract `Binding` network is finally
    instantiated honestly: a concrete nucleon composite trace (three valence carriers) whose weights sum to
    `3` (`nucleonWeight_sum`), closing the binding to `E_bind = 3·count(m)·α_eff(m)` (`E_bind_nucleon`),
    positive and `≤ count/14` (sub-`2.2` MeV shift, so the ground *is* the anchor). With one scale — the
    proton readout — the constituent `= readout + E_bind(4)` and the ground reproduces the anchor exactly
    (`ground_reproduces_anchor`, no new number). The excited baryons then sit at the **exact rational**
    `M(n) = m_p·(n+5)(n+6)/30` (`radialMass_ratio`): rungs `m_p, (7/5)m_p, (28/15)m_p, (12/5)m_p, …`
    strictly increasing (`radialMass_strictMono`). The **orbital axis** uses the foundational Rindler
    detuning `1+(γ/2)m` (`γ=2/5`, so slope `1/5` is no new number): `step(ℓ)=3(ℓ+5)(ℓ+6)/(10(ℓ+9))`
    (`orbitalStep_eq`), `≥1`, strictly increasing, and the **full `(n,ℓ)` grid** is the exact rational
    `M(n,ℓ)=m_p·((n+5)(n+6)/30 + step(ℓ)−1)` (`excitedMass_ratio`).     The bare-binding readout is shown
    *opposite*: `E_bind` is **strictly increasing in shell for every shell** (`E_bind_strictMono`, via the
    honest analytic `log(1+x)≤x` increment bound), so the naive composite-trace tower *falls* below ground
    for every excitation `n+ℓ≥1` (`naive_excited_lt_ground`) — which is why the rising physical tower must
    be the operational surface law, both now certified. A **meson**
    is a 2-carrier composite vs the baryon's 3; constituent and binding both scale with carrier count, so
    they cancel and the meson ground is the **exact** `2/3` of the proton (`mesonGround_eq`, `≈625.5` MeV =
    spin-averaged `(π,ρ)` region), riding the *same* one anchor, with excitations on the same rational
    ladder (`mesonRadialMass_eq`). Bundle `nucleonLadderDischarged_holds`.
    (The whole two-axis spectrum is a parameter-free rational multiple of the single `referenceM=4` proton
    anchor; only the one scale is input. Leading operational readout `≈5–10%` of the measured `Δ`/Roper
    region; sub-leading relaxation fine structure and heavy-quark scales stay quarantined frontiers.)
   * `Physics.ForceCarrier`: the S2 carrier amplitude envelope `sin(½π(1−d))^k` over normalized
     chain distance `d ∈ [0,1]` — full at the source (`s2Envelope_at_source`), vanishing at the
     causal edge (`s2Envelope_at_far_end`), bounded in `[0,1]` (`s2Envelope_le_one`). With
     exponential range attenuation it is the carrier amplitude, and `ampForward/Backward/Net` is the
     emission–absorption split (`ampNet_beta_zero`). Golfed from the physics core of the legacy
     `ForceCarrierWhip` (solver-side whip/objective heuristics left out of the spine).
   * `Physics.DiscreteHeat`: the parabolic-dynamics layer on the 3-cycle `C₃`. Discrete
     integration-by-parts gives the dissipation sign `⟨u,Δu⟩ = −‖∇u‖² ≤ 0`
     (`sum_u_laplacianCycle3_nonpos`), the exact explicit-Euler energy law
     (`eulerHeatStep3_sum_sq_sub_eq`), the `C₃` spectral identity `‖Δu‖² = 3‖∇u‖²`, and the **CFL
     Lyapunov step**: `3·dt·ν ≤ 2 ⇒ ‖u⁺‖² ≤ ‖u‖²`
     (`eulerHeatStep3_sum_sq_le_sum_sq_of_three_mul_dt_nu_le_two`). Honest toy scope — the
     dissipation/stability sign of semidiscrete heat, not a continuum PDE or Navier–Stokes claim.
   * `Physics.DiscreteHeatCycle`: the **general cycle `Cₙ`** generalization of `DiscreteHeat`, on the
     periodic mesh `ZMod n` (`[NeZero n]`) where the cyclic shift `i ↦ i+1` is a genuine `Fintype`
     bijection. The same structure holds for *every* mesh length: discrete integration by parts
     `⟨u,Δu⟩ = −‖∇u‖² ≤ 0` (`sum_u_lap_eq_neg_jumpEnergy`, `sum_u_lap_nonpos`); the Fourier-symbol
     spectral bound `‖Δu‖² ≤ 4‖∇u‖²` (`lapEnergy_le_four_mul_jumpEnergy`, with `4 = 2·degree` the
     ceiling of `|2(cos θ−1)|`, the `C₃` identity `= 3‖∇u‖²` being the sharp special case); the exact
     explicit-Euler energy law (`eulerStep_energy_sub_eq`); and the standard cycle **CFL Lyapunov
     step** `4·dt·ν ≤ 2 ⇒ ‖u⁺‖² ≤ ‖u‖²` (`eulerStep_energy_le_of_cfl`, i.e. `dt·ν ≤ 1/2`). Same
     honest toy scope as its `C₃` parent.
   * `Physics.HubbardDimer`: the **first interacting many-body model** on the spine — a two-site,
     spin-½ Ising-coupled dimer `H = −t(σx⊗I + I⊗σx) + λ(σz⊗σz)` as an explicit Hermitian `4×4`
     matrix (`H_isHermitian`). It is genuinely interacting (`λ` couples the sites) yet exactly
     solvable: two hopping-independent eigenpairs `±λ` (`eigen_singlet`, `eigen_triplet`) and the
     interacting bonding/antibonding pair `±√(4t²+λ²)` (`eigen_ground`, `eigen_top` via the secular
     lemma `eigen_of_sq`). The ground energy `E₀ = −√(4t²+λ²)` sits below every level
     (`groundEnergy_le_lam/_neg_lam/_top`) with a strictly positive **spectral gap** `√(4t²+λ²)−|λ|`
     whenever the hopping `t ≠ 0` (`spectralGap_pos`) — interaction cannot close the gap while
     particles hop. The Ising strength is **shell-anchored**, not free: `λ(m) = λ₀·φ(m)/φ(referenceM)`
     normalised at the lock-in shell      (`lambdaShell_referenceM`). Honest scope: a finite four-state
     toy, the dimer spectrum/gap, not a thermodynamic-limit Hubbard model.
   * `Physics.HubbardHalfFilling`: the **canonical half-filled Hubbard dimer** (charge sector), the
     textbook two-site model `H(t,U)` on `(|↑↓,0⟩,|0,↑↓⟩,|↑,↓⟩,|↓,↑⟩)` with hopping `t` and on-site
     repulsion `U` (`H_isHermitian`). Exactly solvable with spectrum `{0, U, (U±√(U²+16t²))/2}`: the
     spin **triplet** `|↑,↓⟩+|↓,↑⟩` is a zero mode (`eigen_triplet`), the antisymmetric charge state
     has energy `U` (`eigen_chargeAsym`), and the two **singlets** `(E,E,−2t,2t)` solve the secular
     `E²=UE+4t²` (`eigen_ground`/`eigen_excited` via `eigen_secular`). The ground singlet
     `E₀=(U−√(U²+16t²))/2` lies below every level (`groundEnergy_le_zero/_U/_excited`), and the
     **singlet–triplet gap** `J=(√(U²+16t²)−U)/2` (`exchangeJ`) is the antiferromagnetic
     **superexchange**: `J=8t²/(U+√(U²+16t²))` (`exchangeJ_eq`), obeying the Mott-regime Anderson
     scaling `J ≤ 4t²/U` (`superexchange_le`). Repulsion **shell-anchored**
     `U(m)=U₀·φ(m)/φ(referenceM)` (`Ushell_referenceM`). Honest scope: finite four-state model, not
     the thermodynamic-limit Mott transition.
   * `Physics.Thermodynamics`: the **four laws** packaged from `Blackbody` + `DiscreteHeat`, no new
     input. **Zeroth**: equilibrium = equal shell temperature `T_m = ω_m = 1/(m+1)`, an equivalence
     relation, and *injective* so equilibrium ⇔ same shell (`thermalEquilibrium_iff_eq`). **First**:
     the zero-point slice `N_m·T_m = 8 = carrierMultiplicity` is shell-independent
     (`firstLaw_zeroPointSlice_conserved`), with the photon-gas equation of state `U = 3P`
     (`firstLaw_equationOfState`) and Euler relation `T·s = (4/3)U` (`firstLaw_euler_relation`).
     **Second**: entropy production `−⟨u,Δu⟩ ≥ 0` (`secondLaw_entropyProduction_nonneg`), the CFL
     Euler step never raises the quadratic energy (`secondLaw_euler_energy_nonincreasing`), and the
     equilibrium entropy density is nonnegative. **Third**: ladder cooling — for every `ε > 0` some
     shell has `T_m < ε` (`thirdLaw_unattainable_cooling`) and every inner shell is strictly hotter
     (`thirdLaw_hotter_inside`). Honest scope inherited from its two parents.
   * `Physics.CMBBirefringence`: cosmic birefringence as the **spin-2 rotation** of the `(E,B)`
     polarisation pair by `2β(m)`, with `β(m) = α·log(m+1)` from `Blackbody`. Power-conserving
     (`rot_norm_sq`); the pure-`E` leakage reproduces the `Blackbody` greybody split
     (`observed_{E,B}mode_power_eq_greybody`); the **parity-violating** `EB` signal is `½·sin(4β)·E²`,
     vanishing iff `sin(4β) = 0` (`EBcorrelation_pure_E_eq_zero_iff`); the inter-shell rotation is
     `α·log((m_o+1)/(m_e+1))` (`birefringenceRotationAngle_eq`) and feeds the now-slice redshift
     (`birefringence_drives_redshift`).
   * `Physics.ThermalArrow`: the **arrow of time** on the shell clock. Boltzmann entropy
     `S(m) = log N_m` strictly increases (`boltzmannEntropy_strictMono`, hence monotone and
     *injective* — the ladder never returns) while the temperature strictly decreases
     (`shellTemp_strictAnti`); bundled outward as `thermal_arrow`. The equilibrium terminus is the
     zero-deficit `Topology.ShellBudget` reference (`arrow_terminus_equilibrium`).
   * `Physics.StandardModelLagrangian`: the discrete O-Maxwell **action is the SM gauge kinetic
     term**. The `Forces` channel partition splits `kinetic` into EM+weak+strong sector Yang–Mills
     terms (`kinetic_sector_decomposition`), the EM sector a lone abelian Maxwell field
     (`em_kinetic_single`), each `≤ 0`. A spacetime-constant per-channel shift `A a ν ↦ A a ν + c a`
     is a **discrete gauge symmetry**: it leaves the field strength (`fieldStrength_gaugeShift`),
     the kinetic Lagrangian (`kinetic_gauge_invariant`), the divergence, and the equation of motion
     (`EL_gauge_invariant`) invariant. Bundled in `smLagrangian_closure`.
   * `Physics.NuclearBinding`: **bound states from the curvature network** (constituent-only, no PDG).
     The forward-running shell coupling is strictly positive (`bindingCouplingAtShell_pos`), so a
     positive-weight network has positive binding (`E_bind_from_network_pos`); the mass defect equals
     the binding (`networkMassDefect_eq`), so a nucleus is bound iff its binding is positive
     (`nucleus_bound_iff_binding_pos`, `nucleus_bound_of_positive_weight`). Modelling per-nucleon
     binding by the curvature imprint gives `A·δ_E(m)`: **saturation** (binding per nucleon is
     `A`-independent, `bindingPerNucleon_saturates`) and **deeper binding inward**
     (`bindingPerNucleon_deeper_inside`), with the nucleus always bound (`nucleus_always_bound`).
   * `Physics.BBN`: **primordial light-element abundances** from the frozen neutron-to-proton ratio
     `r`. The nucleon fractions `X_n = r/(1+r)`, `X_p = 1/(1+r)` partition the baryons
     (`fractions_sum_one`); the `⁴He` mass fraction is `Y_p = 2r/(1+r) = 2X_n`
     (`helium4MassFraction_eq_two_neutronFraction`), monotone in `r` and `< 1` exactly when `r < 1`
     (`helium4MassFraction_lt_one_iff`). BBN's one cosmological input, the baryon-to-photon ratio, is
     the `Baryogenesis` curvature readout `Ω_k·δ_E(referenceM)` (`baryonToPhoton_eq`,
     `baryonToPhoton_pos`) — downstream of the now slice, never an input.
   * `Physics.WeakDecay`: the weak sector that **closes BBN's `n/p` input**, from one positive
     `Q`-value. Sargent's rule `Γ = g·Q⁵` is strictly increasing in `Q`
     (`sargentRate_strictMono_in_Q`), so the lifetime `τ = 1/Γ` strictly decreases
     (`lifetime_antitone_in_Q`). The freeze-out ratio is the Boltzmann factor `r = e^{−Q/T}` —
     always in `(0,1)` (`npRatio_pos`, `npRatio_lt_one`), decreasing in `Q`, increasing in `T`; on
     the shell clock `T_m = 1/(m+1)` it is `e^{−Q(m+1)}` (`npRatioAtShell_eq`), suppressed on colder
     outer shells (`npRatioAtShell_antitone`). Feeding it into `BBN` gives a physical `Y_p < 1`
     (`helium_fraction_lt_one_from_weak`).
   * `Physics.GRFromMaxwell`: **linearized Einstein gravity is the O-Maxwell operator.** The
     weak-field equation `divergence Φ = 4π·G_eff(φ)·ρ` is exactly the gauge Euler–Lagrange
     stationarity for the rescaled mass current (`linearizedEinstein_iff_EL`). The Friedmann
     constraint holds iff the density is critical `ρ_c(φ) = (3−γ)φ²/(8π G_eff φ)`
     (`friedmann_iff_critical`, `criticalDensity_pos`), and `H(φ)=φ` gives a linear Hubble law
     (`recessionVelocity_linear`, `recessionVelocity_strictMono`). Bundled in `gr_from_maxwell_closure`.
   * `Physics.StellarStructure`: the **hydrostatic φ-shell star.** Pressure `P(m) = K·shellShape m`
     peaks at the core (`stellarPressure_center`, `stellarPressure_le_center`) and softens strictly
     outward (`stellarPressure_strictAnti`); each shell is genuinely held up, with the inner pressure
     equal to the outer pressure plus the shell's positive weight (`hydrostatic_balance`,
     `hydrostaticSupport_pos`). Taking `K = Ω_k·N₆₇`, the profile **is** the now-slice curvature
     imprint (`stellarPressure_eq_curvatureImprint`) — no new input.
   * `Physics.HadronSpectrum`: **meson/baryon ratios off the mass ladder.** Every hadron mass factors
     as core × closure scale (`hadronGroundMassMeV_eq_core`); the meson : baryon ratio is the
     PDG-free `4/9` independent of the core (`meson_baryon_ratio`) with the baryon always heavier
     (`baryon_heavier_than_meson`), and bare Beltrami spectral steps compose `(τ:μ)·(μ:e) = (τ:e) = 2`
     (`generation_steps_compose`; absolute lepton readouts use `GenerationResonanceLadder`).
   * `Physics.GravitationalLensing`: light deflection off the same coupling. A ray grazing mass `M`
     at impact parameter `b` bends by `4·G_eff(φ)·M/b`, exactly **twice** the Newtonian value
     (`einstein_eq_two_newtonian`); positive (`einsteinDeflection_pos`), mass-linear
     (`einsteinDeflection_strictMono_in_M`), `1/b` (`einsteinDeflection_antitone_in_b`), and stronger
     for deeper curvature (`einsteinDeflection_strictMono_in_phi`). Bundle `gravitational_lensing_closure`.
   * `Physics.StellarCollapse`: the **finite support budget** (Chandrasekhar-style). The per-shell
     supports telescope to `K·(1−shellShape N)` (`support_partialSum_eq`), strictly rising
     (`support_partialSum_strictMono`) yet always below the central pressure `K`
     (`support_partialSum_lt_central`); a binding demand `D ≥ K` exceeds the whole budget and can
     never be met at any finite shell count (`collapse_above_budget`) — `K` is the collapse ceiling.
   * `Physics.HadronDecayWidths`: phase space and branching off the ladder. A channel opens iff
     `Q = M_parent − ∑M_daughters > 0` (`decayAllowed_iff`); the width `Γ = g·Q^p` grows with the
     release (`decayWidth_strictMono_in_Q`), width ratios are phase-space ratios `(Q₁/Q₂)^p`
     (`widthRatio_eq`), and branching fractions `Γ_i/Γ_tot` partition unity (`branchingRatio_sum`).
   * `Physics.RelativisticKinematics`: the **relativistic HEP toolkit** upgrading the crude `Q`-value.
     The Källén function `λ(M²,m₁²,m₂²)` factorises as `(M²−(m₁+m₂)²)(M²−(m₁−m₂)²)` (`kallen_factor`),
     so it is `≥ 0` exactly at/above threshold (`kallen_nonneg_of_threshold`); the centre-of-mass
     momentum `p* = √λ/2M` is positive on an open channel (`pStar_pos`, bridged to the crude threshold
     by `pStar_pos_of_decayAllowed`), reducing to `√(M²−4m²)/2` (equal masses) and `M/2` (massless).
     The daughter energies `E₁* = (M²+m₁²−m₂²)/2M` conserve energy (`energy_conservation`) and are
     on-shell `E₁*²−p*² = m₁²` (`daughter1_onShell`). The Breit–Wigner lineshape
     `BW(s) = 1/((s−M²)²+M²Γ²)` peaks at the resonance `s = M²` (`breitWigner_le_peak`,
     `breitWigner_lt_peak_of_ne`) and drops to half-maximum at `s = M² ± MΓ` (`breitWigner_halfMax`).
   * `Physics.DecayMasterFormula`: the **multichannel decay master formula** `Γ = Φ·W`, generalising
     the HEP decay-readout paper. The discharge product `W(e) = ∏_k g_k^{e_k}` is multiplicative in the
     ledger exponents (`dischargeProduct_add`), unity on the inactive pattern (`dischargeProduct_zero`),
     and **unique** under slotwise factorization (`productLaw_unique`). The master width
     `Φ·W` is positive on an open channel (`masterWidth_pos`) with branching fractions partitioning
     unity (`masterWidth_branching_partition`); `Φ = p*/(8πM²)` is the Källén phase space
     (`relativisticPhaseSpace_pos`). The non-relativistic `g·Q^p` is the single-slot case
     (`decayWidth_eq_masterWidth`), and the eight derived γ-rational generators reproduce the paper's
     benchmark weights — e.g. `K⁺→π⁺ = 30576/101250`, `φ→KK = 21/25`, `φ→3π = 4/25` — from the product
     law alone, with the species exponent pattern kept in the comparison layer.
   * `Physics.MandelstamInvariants`: the **`2 → 2` scattering invariants.** The 4D Minkowski form
     polarises (`mink4_polarization`), and under energy–momentum conservation `p₁+p₂ = p₃+p₄` the
     Mandelstam variables obey the sum rule `s + t + u = ∑mᵢ²` (`mandelstam_sum`,
     `mandelstam_sum_onShell`). The Breit–Wigner variable *is* the Mandelstam `s`, so a cross-section
     peaks when the invariant mass reaches the resonance (`resonance_peaks_at_invariant_mass`).
   * `Physics.MultichannelReadout`: the **branching readout closure.** A parent's competing channels
     each carry a phase space and a discharge ledger; the per-channel master width `Γᵢ = Φᵢ·W(eᵢ)` is
     positive (`channelWidth_pos`), the total is positive (`totalWidth_pos`), and the branching
     fractions live in `[0,1]` (`branching_nonneg/_le_one`) and partition unity (`branching_partition`).
     Relative strengths are pure discharge-product ratios — the `φ` `K\bar K : 3π` coupling ratio is
     `21/4` (`phi_KK_to_threePion_coupling_ratio`) — with the per-channel ledgers the only inputs.
   * `Physics.DalitzPlot`: **three-body phase space.** The pairwise invariants obey the Dalitz sum rule
     `s₁₂+s₁₃+s₂₃ = (p₁+p₂+p₃)²+∑mᵢ²` (`dalitz_sum`, on-shell `= M²+∑mᵢ²`), and the third coordinate is
     fixed by the other two (`dalitz_constraint`) — the plot is genuinely two-dimensional.
   * `Physics.DecayLaw`: the **exponential decay law.** Survival `S(t)=e^{−Γt}` starts certain, stays
     positive, is memoryless (`survival_add`) and strictly decreasing (`survival_antitone`); the width
     and lifetime are reciprocal `Γτ=1` (`lifetime_mul_width`), one half-life halves the population
     (`survival_halfLife`), and the branching fraction `bᵢ=Γᵢτ` bridges the readout to the clock.
   * `Physics.ColliderVariables`: **rapidity, the additive boost coordinate.** A `(mT,y)` momentum reads
     back `y` (`rapidity_momentum2`); a boost shifts `y↦y+η` (`rapidity_additive`), so rapidity *gaps*
     are boost-invariant (`rapidity_difference_boost_invariant`), the invariant mass is preserved
     (`invariantMassSq_boost_invariant`), and `mT²=m²+p_T²≥m²` — all from `Geometry.Lorentz`'s boost.
   * `Physics.CrossingSymmetry`: **the `s/t/u` channels and crossing.** Squared mass is
     reflection-invariant `Q(−p)=Q(p)` (`mink4_neg`); each channel equals its complementary pairing
     (`crossing_s/t/u`); the sum rule `s+t+u=∑mᵢ²` is manifestly symmetric across the legs.
   * `Physics.PartialWaves`: **Legendre angular distributions.** `P₀..P₃` normalise, obey the three-term
     recurrence and parity, and the forward–backward asymmetry isolates the odd partial waves
     `W(x)−W(−x)=2(a₁x+a₃P₃)` (`fb_asymmetry`).
   * `Physics.NBodyPhaseSpace`: **the `Rₙ=R₂⊗R_{n−1}` recursion skeleton.** Threshold `∑mᵢ` peels one
     particle at a time (`threshold_succ`); an open channel contains its subsystem
     (`allowed_subsystem`); independent invariants `3n−7` rise by `3` per particle, hitting the Dalitz
     dimension `2` at `n=3` (`numInvariants_three`).
   * `Physics.StellarLuminosity`: **bounded Stefan–Boltzmann luminosity.** Each Planck mode energy
     rises with temperature (`planckMeanEnergy_strictMono_in_T`), so the windowed luminosity is
     positive (`luminosity_pos`), strictly hotter-brighter (`luminosity_strictMono_in_T`), and capped
     by the finite envelope `T·∑N_m` (`luminosity_ceiling`) — no `σ`, no divergence. On the shell
     temperature ladder the hotter inner shells outshine the outer (`shellLuminosity_antitone_in_bath`).
   * `Physics.EinsteinRing`: the ring radius off the lensing deflection. `θ_E² = 4·G_eff(φ)·M·κ` is
     the deflection folded with the lens geometry (`einsteinRadiusSq_eq_deflection`), positive
     (`einsteinRadius_pos`), squaring back (`einsteinRadius_sq`), with the `θ_E ∝ √M` law
     (`einsteinRadius_strictMono_in_M`).
   * `Physics.GravitationalRedshift`: the shift from the **lapse ratio** `1+z = N_o/N_e`. Redshift
     climbing out (`redshift_pos`), blueshift falling in (`redshift_neg`), none iff equal lapse
     (`redshift_zero_iff`); deeper wells shift more (`redshift_strictAnti_in_emit`) and the factors
     compose along a relay (`redshiftFactor_compose`); between slices it is the lapse ratio
     (`nowSlice_redshift_eq`) — anchored to the now slice, no new input.
   * `Physics.MixingUnitarity`: the generation mixing matrix is **unitary by derivation, not
     assumption.** Flavour and mass eigenstates are two orthonormal bases of the three-generation
     space (`generations_eq_quark_triples`: `card = conservedTripleCount .quark = 3`), so the mixing
     matrix is their overlap `V = U_u†·U_d`. A product of unitaries is unitary (`mixing_unitary`),
     hence the **unitarity triangles** `∑_k V*_{ki}V_{kj} = δ_{ij}` close (`unitarity_triangle`) and
     each column conserves probability `∑_k|V_{ki}|² = 1` (`unit_column_norm`); aligned bases give no
     mixing (`mixing_when_aligned`). Only the angles `|V_ij|` would need dynamics — see below.
   * `Physics.MixingAngles`: the **angle from the masses** (Gatto–Sartori–Tonin) — the angles the
     unitarity layer left open. One structural input, the **texture zero** (the lightest generation
     has no leading-order self-mass, natural in the shell ladder), fixes the sector mass matrix to
     `M = [[0, b], [b, m₂−m₁]]`. Then the masses *are* the eigenvalues: `det = −m₁m₂`, `tr = m₂−m₁`
     (`textureMatrix_det`, `textureMatrix_trace`) so `m₂, −m₁` solve the characteristic equation
     (`masses_are_eigenvalues`), fixing `b = √(m₁m₂)`; the mass basis is orthonormal
     (`eigenvectors_orthogonal`). The light-eigenvector slope then gives the headline relation
     `tan²θ = m₁/m₂ = m_light/m_heavy` (`mixingTan_sq`) — i.e. `θ_C ≈ √(m_d/m_s)` — below `45°`
     (`mixingTanSq_lt_one`) and **shrinking with the mass hierarchy** (`mixingTanSq_strictMono`).
     The masses are eigenvalues *with explicit eigenvectors* (`textureMatrix_mulVec_heavy/_light`)
     and the angle is proven to be that eigenvector's slope (`mixingTan_eq_lightVec_slope`) — the
     diagonalising rotation, not a stipulation. Plug in spine-ladder masses: no fitted CKM entry.
   * `Physics.TextureZeroDerivation`: the texture zero is **derived, not assumed** — it is the
     *canonical form of a seesaw-lifted mass matrix*. A general symmetric sector `[[p, b], [b, q]]`
     carrying the spectrum `{m₂, −m₁}` means `tr = m₂−m₁`, `det = −m₁m₂` (`carriesSpectrum`, with
     `carriesSpectrum_roots` certifying those are the eigenvalues). A *real* texture-zero
     representative exists **iff** `det ≤ 0`, i.e. `0 ≤ m₁m₂` (`textureZero_realizable_iff`): the
     ansatz is available precisely because the light generation is a lifted would-be-zero mode
     (opposite-sign eigenvalues, `seesaw_opposite_sign`). Texture zero `p = 0` plus the spectrum then
     *force* `q = m₂−m₁`, `b² = m₁m₂` (`textureZero_unique`) — no freedom — giving exactly
     `MixingAngles.textureMatrix`. Capstone `ansatz_forces_GST`: chiral protection (`p=0`) + seesaw
     spectrum ⇒ the matrix is fixed **and** the angle is forced to `tan²θ = m₁/m₂`. The only physical
     inputs are the two ladder statements (protected zero mode; lifted by mixing).
   * `Physics.CabibboInterference`: `V_us` from **both** sectors. Each sector rotation is built from
     its masses — `sinθ = √(m₁/(m₁+m₂))`, `cosθ = √(m₂/(m₁+m₂))` — with `sin²+cos²=1`
     (`sin_sq_add_cos_sq`) and GST `(sinθ/cosθ)² = m₁/m₂` (`slopeSq_eq_massRatio`); columns are
     orthonormal (`sectorRot_col_norm`), an `SO(2)` shadow of `MixingUnitarity`. The Cabibbo element
     is the overlap `V_us = (R_uᵀR_d)₀₁`, the **exact two-term interference**
     `sinθ_u·cosθ_d − cosθ_u·sinθ_d` (`Vus_eq_interference`) — the `√(m_d/m_s) − √(m_u/m_c)`
     structure — bounded by the sum of the sector angles (`abs_Vus_le`), down-sector dominant. Both
     sectors fed by ladder masses: no fitted entry.
   * `Physics.NeutrinoSeesaw`: the light-neutrino **mass scale** — the *same* texture-zero structure,
     read for neutrinos. A right-handed mode with heavy Majorana `M_R` and Dirac coupling `m_D` gives
     the matrix `[[0, m_D], [m_D, M_R]]`, i.e. `TextureZeroDerivation.symMatrix 0 M_R m_D`
     (`seesaw_carriesSpectrum`: it carries `{m_heavy, −m_ν}`, `det = −m_D² < 0`, a genuine seesaw).
     Exact relation `m_heavy·m_ν = m_D²` (`seesaw_product`, the `b²=m₁m₂` of the texture read as
     `m_ν = m_D²/m_heavy`); suppression `m_ν < m_D²/M_R` (`seesaw_suppression`), below the Dirac
     scale (`lightNeutrino_lt_dirac`), vanishing as `M_R→∞` (`lightNeutrino_lt_of_heavier_MR`).
     **Honest scope:** `m_D, M_R` are *free inputs* (tied to nothing in HQIV), so this gives the seesaw
     *relations* and the texture-zero unification, **not** an absolute `m_ν`. The textbook seesaw is a
     graft; for the HQIV-native mechanism see `NeutrinoCurvatureSuppression`.
   * `Physics.NeutrinoCurvatureSuppression`: the **HQIV-native** neutrino-mass mechanism — pulled out
     of the structure, not grafted. The native action has no mass term; mass is `M_constituent − E_bind`,
     a *curvature well* dug by charge/colour. The neutrino is chargeless (`SMEmbedding`: `ν_R` has
     `Y=Q=0`), the minimal-content (`l²=1`) chirally-protected would-be-zero mode — **no inner well**, so
     `neutrinoTreeMass = 0`. Its only mass is the residual it feels from the *outer horizon* of area
     `S(m) = (m+1)(m+2) = latticeSimplexCount m`, coupled through the monogamy complement `γ = 2/5`. The
     suppression `γ/S(m)` is **parameter-free** and **uniquely derived from foundations**
     (`neutrinoSuppression_unique_from_foundations`): numerator `γ = 1−α` is the unique chargeless
     complement of the unit split (`gammaHQIV_eq_one_sub_alphaEM`); the area is strictly monotone hence
     injective (`latticeSimplexCount_strictMono`); and the closure shell `m=referenceM+2` is the *unique*
     shell whose horizon area equals the octonionic carrier surface `7·8 = imaginaryDim·carrierMultiplicity`
     — equivalently the shell radially bracketed by `(7,8)` (`closureShell_radial_bracket`,
     `neutrinoClosureShell_unique`). These force `1/140 = (1−α)/(imaginaryDim·carrierMultiplicity)`. The
     factor is positive, `< 1`, strictly decreasing (deeper horizon ⇒ lighter ν). **It rhymes with the
     seesaw but is not identical**
     (`neutrino_rhymes_seesaw`): `m_ν = m_χ²/M_eff` with `M_eff = m_χ·S(m)/γ` a *derived horizon scale*
     (`effectiveHeavyScale_gt_charged`: `M_eff > m_χ`), never a free `M_R` — HQIV *forces* the value the
     seesaw inserts by hand. **Absolute scale closed** in `NeutrinoAbsoluteScale`: one-slot nested
     Hopf readout `= massUnit·λ_min/4`; physical mass `= m_ℓ/140` with charged anchor from the matched
     lepton nested Hopf row and suppression at the closure shell. **Still open:** MeV labels and
     cosmological `Σm_ν` comparison only. Combined with `NeutrinoMixing`
     (`θ=π/4`, `δ=π/5`, native numbers): native angle + phase + mass scale. No PMNS, no measured `m_ν`.
   * `Physics.NeutrinoAbsoluteScale`: neutrino one-slot nested Hopf trace wired to absolute mass —
     readout `λ_min/4`, anchor = matched charged lepton, suppression `1/140` at closure shell;
     lock-in `(m_ν,e, m_ν,μ, m_ν,τ) = (1/14, 3/28, 1/7)` in dimensionless spine units.
   * `Physics.Tunneling`: 3D quantum tunneling on the *same* 7-point stencil
     (`Geometry.DiscreteLaplacian`), spine-native (Planck units, `ħ ≡ 1`, lock-in step
     `1/(referenceM+1) = 1/5`). The evanescent slab mode `cosh(κx₀)cos(k₁x₁)cos(k₂x₂)` is a
     genuine stencil eigenfunction (`discreteLaplacian_evanescentSlabMode`); in a forbidden slab
     `cosh(κh) > 1` so `κ ≠ 0` (`evanescentSlabMode_genuinely_evanescent`), and transverse momentum
     exponentially suppresses transmission (`transverse_momentum_suppresses_transmission`) — a 3D
     effect absent in 1D. Full textbook parity (exact barrier `T+R=1`, energy/width monotonicity,
     Gamow half-life, WKB additivity, Breit–Wigner resonance, STM, Fowler–Nordheim, Hartman) plus
     the `h → 0` continuum limit `→ κ²`. **Chemistry layer**: the kinetic isotope effect
     (`heavier_isotope_tunnels_less`, `kineticIsotopeEffect_ge_one` — D tunnels less than H from the
     reduced mass in `κ = √(2μ(V−E))`), double-well proton transfer & the ammonia-inversion doublet
     (`resonant_double_well_perfect_transfer`, `inversion_doublet_split`), STM corrugation of
     conductive allotropes (`stm_images_atomic_corrugation`), field-emission ionization tied to
     `Chemistry.Binding`'s hydrogenic energy (`higher_ionization_suppresses_field_emission`), and
     sub-barrier reactivity beyond classical Arrhenius (`subBarrier_reactivity_positive`).
   * `Physics.Frontiers`: every remaining anchor stated as an explicit open boundary;
     the proton MeV value appears only as a comparison/unit label.

7. **Topology** — discrete topology as an *output* of the shell programme, not an input.
   * `Topology.NullLatticeComplex`: finite closed 3-complexes (`Discrete3Complex`) on the
     null-shell substrate, where shell `m` carries `latticeSimplexCount m = (m+2)(m+1)`
     tags (the spine's own `Physics.Shell.latticeSimplexCount`). The signed
     `shellBudgetMismatch M m = #(vertices at m) − latticeSimplexCount m` vanishes exactly on
     the quadratic null-shell growth law. Two structural facts: **no finite complex** can
     satisfy the law on *all* shells (`not_quadratic_null_shell_growth` — the shell above the
     top occupied one is empty but owed positive budget), while the **finite-horizon** law has
     a canonical realiser `S3NullReference n` (one vertex per tag on shells `0…n`); on-horizon
     quadratic growth pins the vertex set to it (`quadraticOnHorizon_is_S3NullReference`).
     Euler-characteristic readouts make the vertex-only reference **not** combinatorially
     spherical (`χ = |V| > 0`) and turn a positive shell excess into an obstruction to `χ = 0`
     (`shell_budget_excess_obstructs_chi_zero`).
   * `Topology.ShellBudget`: the **signed shell ledger** as a thermodynamic arrow. Negative
     mismatch = closed/under-occupied shell; the `ℕ`-valued deficit sum `totalNegativeBudget`
     is a Lyapunov front that is **zero on the reference** (`S3NullReference_totalNegativeBudget_zero`).
     A deficit-only complex with no negative shells *is* on-horizon quadratic growth
     (`deficitOnly_no_negative_budget_imp_quadraticOnHorizon`). The early-closed regime uses
     the horizon coordinate `ξ = m+1` with half-step anchor `ξ = 7/2`, so the closed shells are
     exactly `m ≤ 2` (`isEarlyClosedShell_iff_le_two`).

8. **Chemistry** — the molecular ladder, every constant the *geometry* of a binding well the
   spine already derives (`rₑ`, depth `Dₑ`, reduced mass `μ`); no fitted coefficients, no
   empirical inputs, each module Mathlib-only.
   * `Chemistry.ShellStructure`: *derives* the octet and subshell capacities that `LonePairs`
     assumes. From monogamy pairing `2` and angular degeneracy `2ℓ+1`, the subshell capacity is
     `2(2ℓ+1) = 4ℓ+2` (`subshellCapacity_closed`, giving `2,6,10,14`), the full principal shell holds
     `2n²` (`principalShellCapacity`), and the periodic doubling `2,2,8,8,18,18,…` is a floor/ceil
     pairing (`generationCapacity_doubling`). The octet `cap(0)+cap(1) = 8` is exactly the so(8)
     carrier multiplicity (`octetCapacity_eq_carrierMultiplicity`) — chemistry's octet rule *is* the
     carrier dimension. The triple-bond ceiling `3` and a unified geometric-mean bond order
     (homonuclear collapse `√(c·c)=c`, heteronuclear bracketing) close the bond-order story.
   * `Chemistry.Aufbau`: the **Madelung `(n+ℓ)` filling**, derived. Subshells fill by the network
     step-distance `shellGeneration = n+ℓ` (ties by principal radius `n`), and the canonical `1s…7p`
     list is *exactly* that `(n+ℓ, n)`-lexicographic order (`madelung_sorted`, strictly increasing
     key). Each subshell holds the derived `subshellCapacity ℓ = 4ℓ+2`, the filling accounts for all
     `118` electrons (`principalList_length`), and the prefix sums at the period boundaries are the
     noble-gas closures `2,10,18,36,54,86,118` (`noble_gas_closures`). The concrete occupancy
     `principalBlock : Fin Z → ℕ` gets period-3+ valence right (`sodium_valence_n_three`, and the
     `4s`-before-`3d` inversion `potassium_valence_n_four`) — closing the abstract `block` gap that
     `Chemistry.Binding.slaterEffectiveChargeAufbau` now fills. The **valence count** is a function:
     `topPrincipal` (highest occupied shell = period), `valenceCount` (electrons there), with the
     valence octet `noble_valence_octet : valenceCount {10,18,36} = octetCapacity`.
   * `Chemistry.LonePairs`: the closed valence shell is `s` pair-slots; bonding capacity
     `B = min(V, 2s − V)` fixes the shared slots and the leftover pairs into lone pairs
     `L = (V − B)/2`. The budget `2L + B = V` closes exactly (`electron_budget_closes`), so the
     lone-pair and steric-domain counts are a *consequence* of electron conservation
     (octet `s = 4` ⇒ four domains, `octet_domains_right`) — not an injected Lewis rule.
   * `Chemistry.VSEPR`: the steric-domain angle is **Kirchhoff balance**, not chemistry. For `d`
     symmetric unit contact directions in equilibrium (`∑ vᵢ = 0`) the Gram trace forces
     `d(1 + (d−1)c) = 0`, so the common cosine is `c = −1/(d−1)`
     (`balanced_unit_contacts_cos`); sp³ tetrahedral gives `−1/3` (`tetrahedral_cos`).
   * `Chemistry.Dipole`: the molecular dipole rides the balanced frame. The subset Gram identity
     `‖∑_{S} v̂‖² = |S| + |S|(|S|−1)c` (`subset_frame_norm_sq`) with the balanced cosine gives the
     resultant `|S|(d−|S|)/(d−1)` (`balanced_partial_resultant_sq`); all-bond molecules cancel
     (`all_bonds_resultant_zero` — CO₂/CH₄/BF₃ nonpolar by the *same* balance), lone pairs break it.
   * `Chemistry.BondOrder`: bond order is the **saturated 2×2 coupling**, not a posited geometric
     mean. A real shared channel `[[a,b],[b,c]]` is PSD ⇔ Cauchy–Schwarz `b ≤ √(ac)`
     (`bond_order_le_geometric_mean`); full coherent sharing saturates the bound, making the
     channel rank-1 (`geometric_mean_zero_det`, `zero_det_iff_geometric_mean`) — one shared pair.
   * `Chemistry.Allotrope`: same atoms, different bond graph (diamond vs graphite vs carbyne; the
     benzene ring; ozone) as **one geometric law**. The octet budget `cap = octetCapacity − valence`
     is partitioned over the coordination `k`: `bondOrder_partition` (`p·k = cap`), antitone order in
     coordination (`bondOrder_antitone_in_coordination`), the aromatic `3/2`
     (`aromaticRingOrder_three_halves`) and the asymmetric ozone bracket `1 ≤ √2 ≤ 2`
     (`ozone_bond_brackets`) via the spine `ShellStructure.geometricBondOrder`, and the triple-bond
     ceiling forbidding one-coordinate carbon (`carbon_k_one_exceeds_ceiling`). Ring strain is the
     polygon interior angle `(n−2)·180/n` — benzene strain-free at sp² (`hexagon_matches_sp2`),
     pentagon `108°`, strictly monotone. The σ-framework angle `−1/(d−1)` is the *derived* VSEPR
     equilibrium cosine (`bondAngleCos_eq_vsepr`), and the length contraction carries the monogamy
     half (`monogamyHalf = 1/monogamyPairMultiplicity = 1/2`).
   * `Chemistry.Polarizability`: the field–displacement response of the well. Force balance gives
     `α = q²/k` (`polarizability_response`); pinning the curvature to the derived depth `I` at
     radius `r` gives the harmonic floor `α = q²r²/(2I)` (`polarizability_floor`), hydrogenic
     `n⁶/z⁴` (`hydrogenic_floor`) — no new constant.
   * `Chemistry.Spectroscopy`: the rovibrational constants as the geometry of the same well.
     Force constants by several routes with the exact agreement condition
     (`forceConstants_agree_iff`), harmonic wavenumber monotone in stiffness
     (`harmonicWavenumber_mono_in_k`), Morse closure `ωₑxₑ·4Dₑ = ωₑ²`
     (`morseAnharmonicity_closure`), centrifugal/ZPE/Pekeris bridges, and the VB covalent↔ionic
     resonance as a convex bracket `k_ion ≤ k_eff ≤ k_cov` (`ionicResonanceForceConstant_brackets`)
     with homonuclear bonds carrying zero ionic character (`ionicResonance_eq_covalent_of_homonuclear`).
   * `Chemistry.LineSpectra`: **atomic line spectra** as differences of the hydrogenic levels the
     spine already derives. The transition energy `ΔE(n_f,n_i)` obeys the **Rydberg formula**
     `R z²(1/n_f² − 1/n_i²)` with `R = μ/2` (`transitionEnergy_eq_rydberg`); emission lines are
     positive (`transitionEnergy_pos`), scale as `z²` (Moseley, `transitionEnergy_scales_zEff`), and
     order Lyman > Balmer (`lyman_gt_balmer`); the `n_i→∞` series limit is the ionization energy
     `R z²/n_f²` (`transitionEnergy_tendsto_seriesLimit`). Numeric anchors: hydrogen Rydberg
     `½ Ha = 13.6057 eV` (`rydbergEv_eq`), Balmer-α `5/72 Ha`, Lyman-α `3/8 Ha`. No new constant.
   * `Chemistry.Binding`: the **electronic binding energy** disentangled onto the spine. Slater
     screening from first principles — `leak = α/referenceM = 0.15` (`screenPenetrationLeak_eq`),
     same-shell `1/2 − leak = 0.35` (`slaterSameShell_eq`), adjacent `1 − leak = 0.85`
     (`slaterAdjacentShell_eq`), gap exactly the monogamy half (`slater_same_adjacent_gap`). The
     three-level placement `slaterShieldingIncrement` (`_same`/`_adjacent`/`_deep`/`_outer` ⇒
     `0.35/0.85/1.00/0` by Gauss enclosure) fed by the derived `Aufbau.principalBlock` makes
     `slaterEffectiveChargeAufbau` **reproduce the textbook Slater `Z_eff`** (H `1`, He `1.65`,
     Li `1.30`, Be `1.95`, C `3.25`).
     Hydrogenic magnitude `μ Z_eff²/(2n²)` with the textbook scaling laws (`∝ Z_eff²`, `∝ 1/n²`,
     linear in `μ`) and a Slater effective charge over an abstract occupancy that never drops below
     unit (`slaterEffectiveCharge_ge_one`). The outside curvature contact is the same-`α` lattice
     power law `G_eff(η) = η^α`: nonnegative, monotone, fixed point `G_eff 1 = 1`. Tied to the
     so(8) network via the no-binding baseline `M_composite = constituent` (`composite_mass_no_binding`).
   * `Chemistry.Electronegativity`: **Mulliken χ = (IE + EA)/2** built entirely from the hydrogenic
     binding — no empirical electronegativity table. The closed form is `χ = μ(z_ion² + z_aff²)/(4n²)`
     (`mullikenChi_eq`), and the uniform-charge value is just the hydrogenic ionization energy
     (`atomElectronegativity_eq_ionization`). **The periodic trend is a theorem**: at fixed valence
     shell χ strictly increases with effective nuclear charge (`electronegativity_strictMono_in_zEff`,
     so left→right where Slater `Z_eff` rises) and strictly decreases down a group with larger `n`
     (`electronegativity_antitone_in_shell`). Feeding the derived χ into the previously-abstract
     `Spectroscopy.bondIonicCharacter` closes that gap: zero ionic character ⇔ equal electronegativity
     (`pure_covalent_iff_equal_chi`) and distinct `Z_eff` forces a polar bond
     (`polar_bond_of_distinct_zEff`). Tied to the derived occupancy via `atomElectronegativityAufbau`
     over `Binding.slaterEffectiveChargeAufbau`, bounded below by the unit-charge hydrogen floor
     (`atomElectronegativityAufbau_ge_hydrogenFloor`).
   * `Chemistry.Biomolecule`: **Watson–Crick base pairing** as donor/acceptor complementarity. A
     hydrogen bond is a half-monogamy spectator contact; the donor/acceptor state is the monogamy
     two-valuedness (`donor_states_eq_monogamyPair`: `card Donor = monogamyPairMultiplicity`). With
     each base edge encoded as the only input, the canonical H-bond counts are *computed*: A·T = 2
     (`adenine_thymine_two`), G·C = 3 (`guanine_cytosine_three`), G·C strictly more bonded
     (`gc_more_bonded_than_at`, the basis of GC-rich stability), and an edge-length mismatch is no
     canonical pair (`guanine_thymine_not_canonical`). The double helix's **uniform width** is the
     constant purine(2)+pyrimidine(1) cyclomatic ring count `canonical_rung_constant_width = 3`.
   * `Chemistry.Reaction`: **stoichiometry, mass conservation, and Hess's law**. An element-vector
     `ReactionGate` (compositions `Fin k → Fin n → ℕ`, integer `consume`/`produce`) preserves every
     element's atom count when balanced (`apply_preserves_totalElementAtoms`). Reaction energy is the
     change in the *state function* `stateEnergy E s = ∑ sᵢ Eᵢ`
     (`reactionEnergy_eq_stateEnergy_diff`), so the energy of any applicable path telescopes to
     endpoint difference (`hess_path_energy`) — hence **path-independent** (`hess_path_independent`)
     and zero around a cycle (`hess_cycle_zero`): Hess's law. The water gate `2H+O→H₂O` balances
     (`waterSynthesisGate_balanced`); its exothermicity is a **theorem conditioned on the spine
     binding ordering** `E(H₂O) < 2E(H)+E(O)` (`water_exothermic_of_binding`), the deeper composite
     well the binding network delivers — the legacy `285.8 kJ/mol` literal is dropped.
   * `Chemistry.BondEnergy`: **reaction energy from bond orders**, closing the parametric `E` left by
     `Reaction`. A species' energy relative to its separated atoms is `−depthUnit·(total bond order)`,
     the order read off `ShellStructure.geometricBondOrder`; substituted into `reactionEnergy` this is
     the bond-energy balance `ΔE = depthUnit·(reactant orders − product orders)`
     (`reactionEnergy_bondEnergy`), so a reaction is exothermic **iff** it raises the total bond order
     (`exothermic_of_bondOrder_increase`, with endothermic/thermoneutral companions) — the only
     premise the positivity `depthUnit > 0`, never a `kJ/mol` number. A single σ-bond is the
     homonuclear `geometricBondOrder 1 1 = 1` (`singleBondOrder_eq_one`), so forming water (two O–H
     bonds from bondless atoms) raises the bond order and **discharges** the hypothesis that
     `Reaction.water_exothermic_of_binding` had to assume (`water_exothermic_from_bondOrder`). Because
     `E` is now a genuine state function, all of `Reaction`'s Hess machinery carries over verbatim.
   * `Chemistry.Molecule`: **worked molecules on the zero-point shell ladder**, mined from the legacy
     `Hqiv.QuantumChemistry.H2` / `FiniteSiteQuantumChemistry` site-energy substrate and disentangled to
     the spine constants. The per-shell mode count is octonion-anchored `availableModes m =
     carrierMultiplicity·C(m+2,2) = 4(m+2)(m+1)` (`availableModes_eq`, the `4 = 8/2`), the per-mode
     zero-point energy is `φ(m)/2 = m+1` (`perModeZeroPoint`), so the single-site budget closes to
     `siteModeEnergy m = 4(m+2)(m+1)²` (`siteModeEnergy_closed_form`) with no fitted coefficient —
     positive and strictly outward-rising (`siteModeEnergy_strictMono`). A molecule is the additive
     site trace `siteEnergyTrace shell = ∑ᵢ siteModeEnergy(shellᵢ)` (homonuclear `n·siteModeEnergy m`,
     `siteEnergyTrace_homonuclear`), and the **diatomic H₂** at equal shells is `8(m+2)(m+1)²`
     (`h2SiteEnergy_same_shell_closed_form`), evaluating at the proton anchor `referenceM = 4` to the
     exact `1200` (`h2SiteEnergy_referenceM_numeric`, bundled in `moleculeH2Discharged_holds`). The
     equations are stated at full generality for reuse: an arbitrary carrier dimension
     `siteModeEnergyOfCarrier c m = (c/2)(m+2)(m+1)²` (the Hopf ladder `c∈{1,2,4,8}`, octonion the
     `siteModeEnergy_eq_ofCarrier` instance), an extensive polyatomic closed form composing over
     `Fin.append`/`List` (`siteEnergyTrace_append`, `listSiteEnergy_append`), and a heteronuclear
     diatomic (`h2SiteEnergy_closed_form`). Honest
     scope: this is the dimensionless zero-point *mode-energy budget* of the separated-atom ladder, not
     the molecular bond well — H₂/LiH/H₂O *binding* magnitude still needs the bonded-horizon Casimir
     layer (the sign already follows from `Chemistry.BondEnergy`).

Build: `lake build HQIVCleanSpine`.
-/
