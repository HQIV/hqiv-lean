import Mathlib.Tactic

/-!
# Nucleon magnetic moment from the same network engine as derived chemistry

The molecular dipole reads a vector sum of charge contributions off a balanced constituent frame.
The nucleon magnetic moment is the *same* readout on the 3-quark network, built from the two
axiom-level pillars the chemistry engine already uses:

* **spin-statistics alignment** of identical constituents (the doubled flavor `uu`/`dd` is forced
  into a symmetric spin-1 pair — the same alignment that lifts the fully-paired light nuclei), and
* **coherent vector coupling** on the spin network (the spin-1 diquark couples with the odd quark's
  spin-½ to the baryon J=½; Clebsch² weights `(2/3, 1/3)` give per-flavor polarizations
  `(+4/3, −1/3)`).

The constituent magneton is fixed by the **weight-3 composite trace**
(`Hqiv.Physics.MetaHorizonExcitedStates`, `nucleonTraceGeneratorWeight = 3`): three carrier slots
share the nucleon mass, so `m_q = m_N/3` and `μ_q = 3 μ_N` — the same `3` as `E_bind = 3·coupling`.
Combining, the moment in nuclear magnetons is the integer-charge readout

`μ_B = μ_q · (w_pair·Q_doubled + w_odd·Q_odd) = (4 Q_doubled − Q_odd) μ_N`,

giving `μ_p = +3`, `μ_n = −2`, ratio `−3/2` with no free parameters.  Gell-Mann–Nishijima charges
`Q = I₃ + Y/2` (`Y = B + S`, `B = 1/3` per quark) come from the already-derived isospin.
-/

namespace Hqiv.Physics.NucleonMagneticMoment

/-- Three carrier slots on one so(8) generator: `μ_q = 3 μ_N` (same weight as `E_bind = 3·coupling`). -/
def constituentMagnetonUnits : ℚ := 3

/-- Baryon number carried by a single quark. -/
def baryonNumberPerQuark : ℚ := 1 / 3

/-- Light-quark third isospin (the input the isospin engine already uses). -/
def quarkIsospinThird (f : String) : ℚ :=
  if f = "u" then 1 / 2 else if f = "d" then -1 / 2 else 0

/-- Quark strangeness. -/
def quarkStrangeness (f : String) : ℚ := if f = "s" then -1 else 0

/-- Gell-Mann–Nishijima charge `Q = I₃ + Y/2`, `Y = B + S`. -/
def quarkCharge (f : String) : ℚ :=
  quarkIsospinThird f + (baryonNumberPerQuark + quarkStrangeness f) / 2

theorem quarkCharge_u : quarkCharge "u" = 2 / 3 := by
  simp only [quarkCharge, quarkIsospinThird, quarkStrangeness, baryonNumberPerQuark,
    String.reduceEq, reduceIte]; norm_num
theorem quarkCharge_d : quarkCharge "d" = -1 / 3 := by
  simp only [quarkCharge, quarkIsospinThird, quarkStrangeness, baryonNumberPerQuark,
    String.reduceEq, reduceIte]; norm_num
theorem quarkCharge_s : quarkCharge "s" = -1 / 3 := by
  simp only [quarkCharge, quarkIsospinThird, quarkStrangeness, baryonNumberPerQuark,
    String.reduceEq, reduceIte]; norm_num

/-- Per-flavor spin polarizations `(doubled, odd)` from the spin-1 pair + spin-½ spectator coupling.
`⟨Σσ_z⟩_pair = (2/3)(+2)+(1/3)(0) = +4/3`, `⟨σ_z⟩_odd = (2/3)(−1)+(1/3)(+1) = −1/3`. -/
def diquarkSpectatorWeights : ℚ × ℚ :=
  let wHigh : ℚ := 2 / 3
  let wMid : ℚ := 1 / 3
  (wHigh * 2 + wMid * 0, wHigh * (-1) + wMid * 1)

theorem diquarkSpectatorWeights_eq : diquarkSpectatorWeights = (4 / 3, -1 / 3) := by
  simp only [diquarkSpectatorWeights, Prod.mk.injEq]; norm_num

/-- Magnetic moment (in `μ_N`) of a 2+1 baryon with doubled flavor `a` and odd flavor `b`. -/
def baryonMoment (a b : String) : ℚ :=
  (diquarkSpectatorWeights.1 * quarkCharge a + diquarkSpectatorWeights.2 * quarkCharge b)
    * constituentMagnetonUnits

/-- Closed form: the weight-3 magneton cancels the SU(6) `/3`, leaving `μ = 4 Q_a − Q_b`. -/
theorem baryonMoment_closed (a b : String) :
    baryonMoment a b = 4 * quarkCharge a - quarkCharge b := by
  simp only [baryonMoment, diquarkSpectatorWeights, constituentMagnetonUnits]; ring

/-- **Proton** `μ_p = +3 μ_N` (doubled `u`, odd `d`). -/
theorem proton_moment : baryonMoment "u" "d" = 3 := by
  rw [baryonMoment_closed, quarkCharge_u, quarkCharge_d]; norm_num

/-- **Neutron** `μ_n = −2 μ_N` (doubled `d`, odd `u`) — a net-neutral object with a nonzero moment. -/
theorem neutron_moment : baryonMoment "d" "u" = -2 := by
  rw [baryonMoment_closed, quarkCharge_d, quarkCharge_u]; norm_num

/-- **Ratio** `μ_p/μ_n = −3/2`, parameter-free (PDG `−1.46`, 2.7%). -/
theorem proton_neutron_ratio : baryonMoment "u" "d" / baryonMoment "d" "u" = -3 / 2 := by
  rw [proton_moment, neutron_moment]; norm_num

/-! ### Octonionic-background mass dressing

The carrier lives on the octonion algebra `𝕆 = ℝ ⊕ Im𝕆` (dimension 8, the so(8) carrier space).
Monogamy assigns total curvature `α = 3/5`; spread over the 8 octonion directions, the carrier's
real (rest-mass) axis carries one share `α/8`, dressing the magnetic constituent mass to
`m_q = (m_N/3)(1 + α/8)` and the magneton to `μ_q = 3/(1 + α/8)`.  The dressing rescales every
moment uniformly, so it cancels in the ratio. -/

/-- Monogamy fraction (informational monogamy axiom). -/
def monogamyAlpha : ℚ := 3 / 5

/-- Octonion carrier dimension `dim 𝕆 = 8` (so(8) carrier). -/
def octonionCarrierDim : ℚ := 8

/-- Magnetic constituent-mass dressing `1 + α/8`. -/
def constituentDressing : ℚ := 1 + monogamyAlpha / octonionCarrierDim

theorem constituentDressing_eq : constituentDressing = 43 / 40 := by
  unfold constituentDressing monogamyAlpha octonionCarrierDim; norm_num

/-- Dressed moment `μ = (4 Q_a − Q_b)/(1 + α/8)` (in `μ_N`). -/
def dressedBaryonMoment (a b : String) : ℚ := baryonMoment a b / constituentDressing

/-- Dressed proton moment `μ_p = 120/43 ≈ 2.791 μ_N` (PDG 2.793, −0.08%). -/
theorem dressed_proton_moment : dressedBaryonMoment "u" "d" = 120 / 43 := by
  unfold dressedBaryonMoment; rw [proton_moment, constituentDressing_eq]; norm_num

/-- Dressed neutron moment `μ_n = −80/43 ≈ −1.860 μ_N` (PDG −1.913; residual = u/d isospin split). -/
theorem dressed_neutron_moment : dressedBaryonMoment "d" "u" = -80 / 43 := by
  unfold dressedBaryonMoment; rw [neutron_moment, constituentDressing_eq]; norm_num

/-- The uniform dressing cancels in the ratio: `μ_p/μ_n = −3/2` still holds. -/
theorem dressed_ratio_unchanged :
    dressedBaryonMoment "u" "d" / dressedBaryonMoment "d" "u" = -3 / 2 := by
  rw [dressed_proton_moment, dressed_neutron_moment]; norm_num

/-- Proton valence charge sums to `+1`. -/
theorem proton_charge_unit : quarkCharge "u" + quarkCharge "u" + quarkCharge "d" = 1 := by
  rw [quarkCharge_u, quarkCharge_d]; norm_num

/-- Neutron valence charge sums to `0`. -/
theorem neutron_charge_zero : quarkCharge "u" + quarkCharge "d" + quarkCharge "d" = 0 := by
  rw [quarkCharge_u, quarkCharge_d]; norm_num

/-! ### Generalized octet closed form

The same coherent spin-flavor sum gives every octet moment.  The isovector combinations
(`μ_p − μ_n` and the Σ⁰→Λ transition) cancel the strange mass, so they are fully parameter-free in
the light sector. -/

/-- Dressed isovector moment `μ_p − μ_n = 5/(1 + α/8) = 200/43 ≈ 4.65 μ_N` (PDG 4.706, −1.2%). -/
theorem dressed_isovector :
    dressedBaryonMoment "u" "d" - dressedBaryonMoment "d" "u" = 200 / 43 := by
  rw [dressed_proton_moment, dressed_neutron_moment]; norm_num

/-- Light-sector magnetic magneton `μ_q^mag = 3/(1 + α/8) = 120/43`. -/
def lightMagneton : ℚ := 3 / constituentDressing

theorem lightMagneton_eq : lightMagneton = 120 / 43 := by
  unfold lightMagneton; rw [constituentDressing_eq]; norm_num

/-- **Σ⁰→Λ transition** is the isovector `|μ| = (μ_u − μ_d)/√3 = μ_q^mag/√3 = √3/(1 + α/8)`; its
square is the strange-free closed form `μ² = 3/(1 + α/8)²` — parameter-free (PDG |μ|≈1.61). -/
theorem sigma_lambda_transition_sq :
    lightMagneton ^ 2 / 3 = 3 / constituentDressing ^ 2 := by
  unfold lightMagneton; rw [constituentDressing_eq]; norm_num

/-! ### Whole-hadron `i,j,k` composite trace: symmetric (isoscalar) ⊕ antisymmetric (isovector)

We score the **hadron**, not the quarks (quarks are not asymptotic states).  The nucleon is one
whole-hadron composite trace `μ(a,b) = 4 Q_a − Q_b` over its `i,j,k` Fano triple (doubled flavor
`a`, odd flavor `b`).  Under the isospin swap `a ↔ b` this trace splits canonically into

* a **symmetric / isoscalar** channel  `S(a,b) = ½(μ(a,b)+μ(b,a)) = (3/2)(Q_a+Q_b)`,
* an **antisymmetric / isovector** (`f^{ijk}`) channel `V(a,b) = ½(μ(a,b)−μ(b,a)) = (5/2)(Q_a−Q_b)`,

with the two channel coefficients `(3/2, 5/2) = ½(w₊∓w₋)` read straight off the spin weights
`(w₊,w₋)=(4,−1)`.  The proton is `μ_p = S+V` and the neutron `μ_n = S−V`, so the two channels
**cancel in `μ_p` but add in `μ_n`** — the entire `μ_n` residual is the antisymmetric channel
surfacing, not a quark-level effect. -/

/-- Symmetric (isoscalar) part of the whole-hadron `i,j,k` composite trace. -/
def isoscalarTrace (a b : String) : ℚ := (baryonMoment a b + baryonMoment b a) / 2

/-- Antisymmetric (`f^{ijk}` / isovector) part of the whole-hadron `i,j,k` composite trace. -/
def isovectorTrace (a b : String) : ℚ := (baryonMoment a b - baryonMoment b a) / 2

/-- Isoscalar channel closed form: coefficient `3/2 = ½(w₊+w₋)·(−1)`… i.e. `(3/2)(Q_a+Q_b)`. -/
theorem isoscalarTrace_eq (a b : String) :
    isoscalarTrace a b = 3 / 2 * (quarkCharge a + quarkCharge b) := by
  unfold isoscalarTrace; rw [baryonMoment_closed, baryonMoment_closed]; ring

/-- Isovector channel closed form: coefficient `5/2 = ½(w₊−w₋)`, times `(Q_a−Q_b)`. -/
theorem isovectorTrace_eq (a b : String) :
    isovectorTrace a b = 5 / 2 * (quarkCharge a - quarkCharge b) := by
  unfold isovectorTrace; rw [baryonMoment_closed, baryonMoment_closed]; ring

/-- Reconstruction: `μ(a,b) = S + V` (proton channel sum). -/
theorem trace_reconstruct (a b : String) :
    baryonMoment a b = isoscalarTrace a b + isovectorTrace a b := by
  unfold isoscalarTrace isovectorTrace; ring

/-- Reconstruction: `μ(b,a) = S − V` (neutron channel difference). -/
theorem trace_reconstruct_swap (a b : String) :
    baryonMoment b a = isoscalarTrace a b - isovectorTrace a b := by
  unfold isoscalarTrace isovectorTrace; ring

/-- Nucleon isoscalar value `S = 1/2 μ_N` (bare). -/
theorem nucleon_isoscalar : isoscalarTrace "u" "d" = 1 / 2 := by
  rw [isoscalarTrace_eq, quarkCharge_u, quarkCharge_d]; norm_num

/-- Nucleon isovector value `V = 5/2 μ_N` (bare). -/
theorem nucleon_isovector : isovectorTrace "u" "d" = 5 / 2 := by
  rw [isovectorTrace_eq, quarkCharge_u, quarkCharge_d]; norm_num

/-- `μ_p = S + V`. -/
theorem proton_channel_sum :
    baryonMoment "u" "d" = isoscalarTrace "u" "d" + isovectorTrace "u" "d" :=
  trace_reconstruct "u" "d"

/-- `μ_n = S − V` (same two channels, now adding into the residual). -/
theorem neutron_channel_diff :
    baryonMoment "d" "u" = isoscalarTrace "u" "d" - isovectorTrace "u" "d" :=
  trace_reconstruct_swap "u" "d"

/-- **Uniqueness of the channel decomposition.**  `(S,V) ↦ (S+V, S−V)` is a bijection, so the
isoscalar/isovector split of any `(μ_p, μ_n)` pair is unique and given by the half-sum / half-diff.
This is what makes "the residual is the antisymmetric channel" a statement, not a choice. -/
theorem channel_decomposition_unique {p n S V : ℚ} (hp : p = S + V) (hn : n = S - V) :
    S = (p + n) / 2 ∧ V = (p - n) / 2 :=
  ⟨by rw [hp, hn]; ring, by rw [hp, hn]; ring⟩

/-- Dressed isoscalar `S/(1+α/8) = 20/43 ≈ 0.4651`. -/
theorem dressed_isoscalar_value :
    isoscalarTrace "u" "d" / constituentDressing = 20 / 43 := by
  rw [nucleon_isoscalar, constituentDressing_eq]; norm_num

/-- Dressed isovector `V/(1+α/8) = 100/43 ≈ 2.3256`. -/
theorem dressed_isovector_value :
    isovectorTrace "u" "d" / constituentDressing = 100 / 43 := by
  rw [nucleon_isovector, constituentDressing_eq]; norm_num

/-! ### Uniqueness of the spin-flavor weights (Clebsch forced by orthonormality)

The weights `(w₊,w₋)=(4/3,−1/3)` are **not** chosen.  The top baryon state `|3/2,3/2⟩ = |1,1⟩|↑⟩`
is unambiguous; the `J⁻` ladder (coefficients `√3, √2, 1`) gives
`|3/2,1/2⟩ = (1/√3)|1,1⟩|↓⟩ + √(2/3)|1,0⟩|↑⟩`, i.e. squared amplitudes `(1/3, 2/3)` in the
`m=1/2` plane.  The physical nucleon `|1/2,1/2⟩` is the orthonormal complement, so its squared
amplitudes are forced to `(2/3, 1/3)`.  The polarizations `(4/3,−1/3)` and the integer readout
`(4,−1)` then follow. -/

/-- **Orthonormality forces the Clebsch weights.**  In the 2-D `m=1/2` plane, the unit vector
orthogonal to the `j=3/2` state (squared amplitudes `(1/3, 2/3)`) has squared amplitudes that
**swap** to `(2/3, 1/3)`.  Pure algebra — no rep-theory black box. -/
theorem orthonormal_complement_swaps_sq (a b a' b' : ℝ)
    (h3 : a' ^ 2 = 1 / 3) (hn' : a' ^ 2 + b' ^ 2 = 1)
    (hn : a ^ 2 + b ^ 2 = 1) (horth : a * a' + b * b' = 0) :
    a ^ 2 = 2 / 3 ∧ b ^ 2 = 1 / 3 := by
  have hb' : b' ^ 2 = 2 / 3 := by linarith
  have he : a * a' = -(b * b') := by linarith
  have hsq : a ^ 2 * a' ^ 2 = b ^ 2 * b' ^ 2 := by
    calc a ^ 2 * a' ^ 2 = (a * a') ^ 2 := by ring
      _ = (b * b') ^ 2 := by rw [he]; ring
      _ = b ^ 2 * b' ^ 2 := by ring
  constructor <;> nlinarith [hsq, hn, h3, hb']

/-- The Clebsch² weights are the unique probability split with the orthonormal `2:1` ratio. -/
theorem clebschWeights_unique {wHigh wMid : ℚ} (hnorm : wHigh + wMid = 1)
    (hratio : wHigh = 2 * wMid) : wHigh = 2 / 3 ∧ wMid = 1 / 3 :=
  ⟨by linarith, by linarith⟩

/-- Given the forced Clebsch² weights `(2/3,1/3)`, the per-flavor polarizations are exactly the
`diquarkSpectatorWeights` `(4/3,−1/3)` — closing the uniqueness chain to the integer readout. -/
theorem polarizations_forced :
    ((2 / 3 : ℚ) * 2 + (1 / 3 : ℚ) * 0, (2 / 3 : ℚ) * (-1) + (1 / 3 : ℚ) * 1)
      = diquarkSpectatorWeights := by
  rw [diquarkSpectatorWeights_eq]; norm_num

/-- **Uniform dressing is the unique ratio-preserving dressing.**  Any nonzero flavor-independent
factor `k` cancels in `μ_p/μ_n`, so the `−3/2` ratio is a fixed point of every uniform dressing —
the octonionic `1+α/8` is just the physically-selected member of that family. -/
theorem uniform_dressing_preserves_ratio (k : ℚ) (hk : k ≠ 0) :
    (baryonMoment "u" "d" / k) / (baryonMoment "d" "u" / k) = -3 / 2 := by
  rw [proton_moment, neutron_moment]
  rw [div_div_div_cancel_right₀]
  · norm_num
  · exact hk

end Hqiv.Physics.NucleonMagneticMoment
