import Lean
import Std
import Hqiv.Geometry.AuxiliaryField

open Lean
open Hqiv

def showNat (n : Nat) : String :=
  toString n

def showFloat1 (n : Nat) : String :=
  toString (Float.ofNat n)

def rowJson (m : Nat) : String :=
  let phi := 2 * (m + 1)
  let ratioNum := m + 1
  "{\n" ++
  "      \"m\": " ++ showNat m ++ ",\n" ++
  "      \"phi_of_shell\": " ++ showFloat1 phi ++ ",\n" ++
  "      \"lambda_ratio_num\": " ++ showNat ratioNum ++ ",\n" ++
  "      \"lambda_ratio_den\": 5\n" ++
  "    }"

def rowsJson : String :=
  let ms : List Nat := [2, 3, 4, 5, 6, 7, 8]
  String.intercalate ",\n" (ms.map rowJson)

unsafe def main : IO Unit := do
  let dataDir := "data"
  IO.FS.createDirAll dataDir
  let outPath := dataDir ++ "/hubbard_dimer_witnesses.json"

  let json :=
    "{\n" ++
    "  \"referenceM\": 4,\n" ++
    "  \"phi_formula\": \"2*(m+1)\",\n" ++
    "  \"lambda_ratio_formula\": \"(m+1)/5\",\n" ++
    "  \"rows\": [\n" ++
    rowsJson ++ "\n" ++
    "  ]\n" ++
    "}\n"

  IO.FS.writeFile outPath json
  IO.println s!"Wrote Hubbard dimer witnesses to {outPath}"
