import HqivSpine.Physics.Proton

/-!
# `HqivSpine.Physics.MassLadder` — the proton-normalized mass ladder

With the proton fixed at the lock-in shell, the rest of the spectrum is
*structural*: the same 8×8 composite-trace binding network, scaled by content
classification, drives hadrons, leptons, nuclei, and atoms.

* **Content classes** ν / charged-ℓ / quark carry `1 / 2 / 3` conserved Fano
  triples; the squared count `l² ∈ {1, 4, 9}` is the intrinsic wave complexity.
* **Hadrons:** baryon vs meson differ by the closure-rank ratio `4/9`; baryon
  ground mass is exactly the proton-style `constituent − network binding`.
* **Leptons:** the generation ladder follows the `S³` Beltrami minimal-eigenvalue
  spectrum `λ_min(n) = n + 1`, giving the dimensionless steps `4/3` (τ:μ) and
  `3/2` (μ:e). The absolute lepton scale is an explicit frontier.
* **Nuclei / atoms:** the same `constituents − binding` form, one level up.

No top/bottom GeV anchors, no electroweak vev literal, no PDG tables.
-/

namespace HqivSpine.Physics

/-! ## Content classification (1 / 2 / 3 conserved triples) -/

/-- Fermion sector by how many SM quantum numbers must close on the wave. -/
inductive FermionContentClass
  | neutrino
  | chargedLepton
  | quark
  deriving DecidableEq, Repr

/-- Independent Fano triples required (ν:1, charged ℓ:2, quark:3). -/
def conservedTripleCount : FermionContentClass → ℕ
  | .neutrino => 1
  | .chargedLepton => 2
  | .quark => 3

theorem conservedTripleCount_strict_chain :
    conservedTripleCount .neutrino < conservedTripleCount .chargedLepton ∧
      conservedTripleCount .chargedLepton < conservedTripleCount .quark := by
  decide

/-- Squared triple count: intrinsic wave complexity `l² ∈ {1, 4, 9}`. -/
noncomputable def intrinsicWaveComplexity (c : FermionContentClass) : ℝ :=
  (conservedTripleCount c : ℝ) ^ 2

theorem intrinsicWaveComplexity_values :
    intrinsicWaveComplexity .neutrino = 1 ∧
      intrinsicWaveComplexity .chargedLepton = 4 ∧
      intrinsicWaveComplexity .quark = 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [intrinsicWaveComplexity, conservedTripleCount] <;> norm_num

/-- **Quark : charged-lepton complexity ratio = 9/4** — the same number as the colour
adjoint/fundamental Casimir ratio `C_A/C_F` (see `Frontiers`). -/
theorem intrinsicWaveComplexity_quark_over_chargedLepton :
    intrinsicWaveComplexity .quark / intrinsicWaveComplexity .chargedLepton = (9 : ℝ) / 4 := by
  simp [intrinsicWaveComplexity, conservedTripleCount]; norm_num

/-- **Quark : neutrino complexity ratio = 9.** -/
theorem intrinsicWaveComplexity_quark_over_neutrino :
    intrinsicWaveComplexity .quark / intrinsicWaveComplexity .neutrino = 9 := by
  simp [intrinsicWaveComplexity, conservedTripleCount]; norm_num

/-! ## Hadrons -/

/-- Hadron structure class. -/
inductive HadronStructure
  | baryon
  | meson
  deriving DecidableEq, Repr

/-- Closure rank of a hadron: baryon = colour-composed (3), meson = charge-decorated (2). -/
def hadronClosureRank : HadronStructure → ℕ
  | .baryon => 3
  | .meson => 2

/-- `l²` mass-scaling factor relative to baryon: baryon `1`, meson `4/9`. -/
noncomputable def hadronIntrinsicScale (h : HadronStructure) : ℝ :=
  (hadronClosureRank h : ℝ) ^ 2 / (hadronClosureRank .baryon : ℝ) ^ 2

theorem hadronIntrinsicScale_baryon : hadronIntrinsicScale .baryon = 1 := by
  simp [hadronIntrinsicScale, hadronClosureRank]

theorem hadronIntrinsicScale_meson : hadronIntrinsicScale .meson = (4 : ℝ) / 9 := by
  simp [hadronIntrinsicScale, hadronClosureRank]; norm_num

/-- Nucleon composite-trace channel count = quark triple count = 3. -/
def nucleonTraceChannelCount : ℕ := 3

/-- Fraction of the tri-channel composite trace active for `n` valence quarks. -/
noncomputable def valenceChannelFraction (n : ℕ) : ℝ :=
  (n : ℝ) / (nucleonTraceChannelCount : ℝ)

theorem valenceChannelFraction_baryon : valenceChannelFraction 3 = 1 := by
  simp [valenceChannelFraction, nucleonTraceChannelCount]

theorem valenceChannelFraction_meson : valenceChannelFraction 2 = (2 : ℝ) / 3 := by
  simp [valenceChannelFraction, nucleonTraceChannelCount]

/-- QCD binding at shell `m`, scaled to `n` valence channels. -/
noncomputable def hadronBindingMeV
    (m n : ℕ) (diag : So8TraceDiagonal) (state : OctonionState) (c : ℝ := 1) : ℝ :=
  E_bind_from_composite_trace m diag state c * valenceChannelFraction n

/-- **Hadron ground mass (MeV):** `(constituent − scaled binding) · intrinsic scale`. -/
noncomputable def hadronGroundMassMeV
    (m : ℕ) (constituentMeV : ℝ) (h : HadronStructure) (valenceQuarks : ℕ)
    (diag : So8TraceDiagonal) (state : OctonionState) (c : ℝ := 1) : ℝ :=
  (constituentMeV - hadronBindingMeV m valenceQuarks diag state c) * hadronIntrinsicScale h

/-- **Baryon ground mass is exactly the proton-style network mass:** the baryon
triple uses the full trace (fraction `1`) and intrinsic scale `1`. -/
theorem hadronGroundMassMeV_baryon_eq_network
    (m : ℕ) (constituentMeV : ℝ) (diag : So8TraceDiagonal)
    (state : OctonionState) (c : ℝ) :
    hadronGroundMassMeV m constituentMeV .baryon 3 diag state c =
      M_composite_from_network m constituentMeV
        (networkWeightFromCompositeTrace diag state) c := by
  simp [hadronGroundMassMeV, hadronBindingMeV, valenceChannelFraction_baryon,
    hadronIntrinsicScale_baryon, M_composite_from_network, E_bind_from_composite_trace]

/-! ## Leptons: generation ladder from the `S³` Beltrami spectrum -/

/-- Minimal coexact Beltrami eigenvalue on `S³` at fiber winding `n`: `λ_min = n + 1`. -/
def beltramiMinEigenvalue (n : ℕ) : ℝ := (n : ℝ) + 1

/-- Spectral resonance step between two windings (dimensionless). -/
noncomputable def leptonSpectralRatio (nFrom nTo : ℕ) : ℝ :=
  beltramiMinEigenvalue nFrom / beltramiMinEigenvalue nTo

/-- **τ:μ step = 4/3.** -/
theorem leptonSpectralRatio_tau_mu : leptonSpectralRatio 3 2 = (4 : ℝ) / 3 := by
  norm_num [leptonSpectralRatio, beltramiMinEigenvalue]

/-- **μ:e step = 3/2.** -/
theorem leptonSpectralRatio_mu_e : leptonSpectralRatio 2 1 = (3 : ℝ) / 2 := by
  norm_num [leptonSpectralRatio, beltramiMinEigenvalue]

/-- The three integrable windings give a strictly increasing minimal-eigenvalue ladder. -/
theorem beltramiMinEigenvalue_strict :
    beltramiMinEigenvalue 1 < beltramiMinEigenvalue 2 ∧
      beltramiMinEigenvalue 2 < beltramiMinEigenvalue 3 := by
  constructor <;> norm_num [beltramiMinEigenvalue]

/-! ## Nuclei and atoms (one level up, same form) -/

/-- **Nuclear mass:** `A · M_nucleon_avg − network binding` at shell `m`. -/
noncomputable def M_nucleus_from_network
    (m : ℕ) (A : ℕ) (M_nucleon_avg : ℝ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * M_nucleon_avg - E_bind_from_network m w c

/-- **Atomic mass:** nucleus `+ Z·m_e − electronic binding`. -/
noncomputable def M_atom
    (M_nucleus : ℝ) (Z : ℕ) (electronMass electronicBinding : ℝ) : ℝ :=
  M_nucleus + (Z : ℝ) * electronMass - electronicBinding

theorem M_nucleus_from_network_eq (m A : ℕ) (M_nucleon_avg : ℝ)
    (w : NetworkWeight) (c : ℝ) :
    M_nucleus_from_network m A M_nucleon_avg w c =
      (A : ℝ) * M_nucleon_avg - E_bind_from_network m w c := rfl

end HqivSpine.Physics
