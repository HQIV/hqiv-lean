import Lean
import Std
import Hqiv.QuantumChemistry.H2

open Lean
open Hqiv
open Hqiv.QuantumChemistry

def showNat (n : Nat) : String :=
  toString n

/-- Proof checks consumed by this exporter (keeps JSON constants theorem-aligned). -/
example : Hqiv.referenceM = 4 := referenceM_eq_four
example : h2SiteEnergyTrace Hqiv.referenceM Hqiv.referenceM = 1200 := h2SiteEnergyTrace_referenceM_numeric

unsafe def main : IO Unit := do
  let dataDir := "data"
  IO.FS.createDirAll dataDir
  let outPath := dataDir ++ "/quantum_chem_witnesses.json"

  let json :=
    "{\n" ++
    "  \"referenceM\": " ++ showNat 4 ++ ",\n" ++
    "  \"h2_trace_referenceM\": 1200,\n" ++
    "  \"site_energy_referenceM\": 600,\n" ++
    "  \"h2_trace_referenceM_expected\": 1200,\n" ++
    "  \"closed_form\": {\n" ++
    "    \"site_energy_m\": \"4*(m+2)*(m+1)^2\",\n" ++
    "    \"h2_equal_shell_trace_m\": \"8*(m+2)*(m+1)^2\"\n" ++
    "  }\n" ++
    "}\n"

  IO.FS.writeFile outPath json
  IO.println s!"Wrote quantum-chemistry witnesses to {outPath}"
