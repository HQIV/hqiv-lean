import Lean
import Std
import Hqiv.QuantumMechanics.HubbardDimerWitnessTable

open Lean
open Hqiv.QM

def showNat (n : Nat) : String :=
  toString n

def showFloat1 (n : Nat) : String :=
  toString (Float.ofNat n)

def rowJson (r : HubbardShellRow) : String :=
  "{\n" ++
  "      \"m\": " ++ showNat r.m ++ ",\n" ++
  "      \"phi_of_shell\": " ++ showFloat1 r.phi_num ++ ",\n" ++
  "      \"u_ratio_num\": " ++ showNat r.lambda_ratio_num ++ ",\n" ++
  "      \"u_ratio_den\": " ++ showNat r.lambda_ratio_den ++ "\n" ++
  "    }"

def rowsJson : String :=
  String.intercalate ",\n" (expectedHubbardShellRows.map rowJson)

unsafe def main : IO Unit := do
  let dataDir := "data"
  IO.FS.createDirAll dataDir
  let outPath := dataDir ++ "/hubbard_dimer_half_filled_witnesses.json"

  let json :=
    "{\n" ++
    "  \"referenceM\": 4,\n" ++
    "  \"phi_formula\": \"2*(m+1)\",\n" ++
    "  \"u_shell_ratio_formula\": \"(m+1)/5\",\n" ++
    "  \"canonical_gap_formula\": \"(sqrt(U^2 + 16*t^2) - U)/2\",\n" ++
    "  \"rows\": [\n" ++
    rowsJson ++ "\n" ++
    "  ]\n" ++
    "}\n"

  IO.FS.writeFile outPath json
  IO.println s!"Wrote canonical half-filled Hubbard witnesses to {outPath}"
