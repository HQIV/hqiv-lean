import Lean

/-!
Patch scale-witness metadata into `data/hqiv_witnesses.json` without evaluating
noncomputable derived masses.
-/

unsafe def dropThroughFirst (s : String) (needle : String) : String :=
  match s.splitOn needle with
  | _ :: rest => needle ++ String.intercalate needle rest
  | [] => s

unsafe def main : IO Unit := do
  let path := "data/hqiv_witnesses.json"
  let prior ← IO.FS.readFile path
  let header :=
    "{\n" ++
    "  \"scale_witness_default\": \"proton_lockin\",\n" ++
    "  \"referenceM\": 4,\n" ++
    "  \"geV_per_MeV\": 0.001,\n" ++
    "  \"CODATA_inv_alpha\": 137.035999177,\n"
  let body := dropThroughFirst prior "\"m_H\""
  let out := header ++ body
  IO.FS.createDirAll "data"
  IO.FS.writeFile path out
  IO.println s!"Updated witness metadata in {path}"
