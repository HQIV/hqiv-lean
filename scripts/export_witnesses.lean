import Lean
import Std
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.DerivedNucleonMass

open Lean
open Hqiv
open Hqiv.Physics

/-- Render `ℝ` as a JSON-safe string via pretty-printing.
Note: `Real`'s `Repr` is marked unsafe in Lean; exporting is therefore an
`unsafe` formatting step only (we are not changing any physics definitions). -/
unsafe def showReal (x : ℝ) : String :=
  Format.pretty (repr x) 80

/--
Export *pure-derived* HQIV gauge/lepton witnesses.
No external mass tables are used here; values come from the derived module.
-/
unsafe def main : IO Unit := do
  let dataDir := "data"
  IO.FS.createDirAll dataDir
  let outPath := dataDir ++ "/hqiv_witnesses.json"

  -- We write only derived outputs requested by the pure-derivation pipeline.
  let json :=
    "{\n" ++
    "  \"scale_witness_default\": \"proton_lockin\",\n" ++
    "  \"referenceM\": " ++ toString referenceM ++ ",\n" ++
    "  \"geV_per_MeV\": 0.001,\n" ++
    "  \"CODATA_inv_alpha\": 137.035999177,\n" ++
    "  \"m_H\": " ++ showReal m_H_derived ++ ",\n" ++
    "  \"M_W\": " ++ showReal M_W_derived ++ ",\n" ++
    "  \"M_Z\": " ++ showReal M_Z_derived ++ ",\n" ++
    "  \"m_nu_e\": " ++ showReal m_nu_e_derived ++ ",\n" ++
    "  \"m_nu_mu\": " ++ showReal m_nu_mu_derived ++ ",\n" ++
    "  \"m_nu_tau\": " ++ showReal m_nu_tau_derived ++ ",\n" ++
    "  \"resonanceK_outer_0_1\": " ++ showReal (resonanceStepK referenceM (referenceM + 1)) ++ ",\n" ++
    "  \"resonanceK_outer_1_2\": " ++ showReal (resonanceStepK (referenceM + 1) (referenceM + 2)) ++ ",\n" ++
    "  \"derivedProtonMass_MeV\": " ++ showReal derivedProtonMass ++ ",\n" ++
    "  \"derivedNeutronMass_MeV\": " ++ showReal derivedNeutronMass ++ ",\n" ++
    "  \"derivedDeltaM_MeV\": " ++ showReal derivedDeltaM ++ ",\n" ++
    "  \"proton_neutron_delta\": " ++ showReal derivedDeltaM ++ "\n" ++
    "}\n"

  IO.FS.writeFile outPath json
  IO.println s!"Wrote resonance witnesses to {outPath}"

