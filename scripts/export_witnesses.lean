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
Export *pure-derived* HQIV gauge/lepton witnesses (bosons + nucleons).

Neutrino masses and PMNS angles are **not** exported here (retired `m_nu_e_derived`
ladder). Run `python3 scripts/sync_hqiv_witness_neutrinos.py` after this step to
patch TUFT T10 neutrino fields into `data/hqiv_witnesses.json`.
-/
unsafe def main : IO Unit := do
  let dataDir := "data"
  IO.FS.createDirAll dataDir
  let outPath := dataDir ++ "/hqiv_witnesses.json"

  let json :=
    "{\n" ++
    "  \"scale_witness_default\": \"proton_lockin\",\n" ++
    "  \"referenceM\": " ++ toString referenceM ++ ",\n" ++
    "  \"geV_per_MeV\": 0.001,\n" ++
    "  \"CODATA_inv_alpha\": 137.035999177,\n" ++
    "  \"m_H\": " ++ showReal m_H_derived ++ ",\n" ++
    "  \"M_W\": " ++ showReal M_W_derived ++ ",\n" ++
    "  \"M_Z\": " ++ showReal M_Z_derived ++ ",\n" ++
    "  \"m_nu_e_derived_status\": \"retired\",\n" ++
    "  \"neutrino_source\": \"tuft_outer_t8_t10\",\n" ++
    "  \"resonanceK_outer_0_1\": " ++ showReal (resonanceStepK referenceM (referenceM + 1)) ++ ",\n" ++
    "  \"resonanceK_outer_1_2\": " ++ showReal (resonanceStepK (referenceM + 1) (referenceM + 2)) ++ ",\n" ++
    "  \"derivedProtonMass_MeV\": " ++ showReal derivedProtonMass ++ ",\n" ++
    "  \"derivedNeutronMass_MeV\": " ++ showReal derivedNeutronMass ++ ",\n" ++
    "  \"derivedDeltaM_MeV\": " ++ showReal derivedDeltaM ++ ",\n" ++
    "  \"proton_neutron_delta\": " ++ showReal derivedDeltaM ++ "\n" ++
    "}\n"

  IO.FS.writeFile outPath json
  IO.println s!"Wrote resonance witnesses to {outPath} (run sync_hqiv_witness_neutrinos.py for T10 neutrinos)"
