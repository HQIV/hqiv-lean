#!/usr/bin/env bash
# Compile Circom, Groth16 setup (dev powers of tau), prove, verify.
# Usage:
#   ./build_and_prove.sh              # uses input.json in this directory
#   ./build_and_prove.sh path/to/input.json
#
# Trusted setup here is for development only (local powers of tau + single groth16 setup).
#
# Requires: npm ci; Circom 2 on PATH or ./bin/circom (see README).

set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

INPUT_JSON="${1:-$ROOT/input.json}"
if [[ ! -f "$INPUT_JSON" ]]; then
  echo "Missing $INPUT_JSON — generate with:" >&2
  echo "  python3 export_witness.py 221 --circom-out input.json" >&2
  exit 1
fi

if [[ ! -d node_modules ]]; then
  echo "Run: npm ci" >&2
  exit 1
fi

mkdir -p build
CIRCOM="${CIRCOM:-}"
if [[ -z "$CIRCOM" && -x "$ROOT/bin/circom" ]]; then
  CIRCOM="$ROOT/bin/circom"
elif [[ -z "$CIRCOM" ]]; then
  CIRCOM="circom"
fi
"$CIRCOM" circuits/first_divisor_at_step.circom --r1cs --wasm --sym -l node_modules -o build

PTAU="$ROOT/build/pot12_final.ptau"
ZKEY_SETUP="$ROOT/build/circuit_0000.zkey"
ZKEY_FINAL="$ROOT/build/circuit_final.zkey"
if [[ ! -f "$PTAU" ]]; then
  npx snarkjs powersoftau new bn128 12 "$ROOT/build/pot12_0000.ptau" -v
  npx snarkjs powersoftau contribute "$ROOT/build/pot12_0000.ptau" "$ROOT/build/pot12_0001.ptau" --name=hqiv-dev -v -e="$(date +%s)"
  npx snarkjs powersoftau prepare phase2 "$ROOT/build/pot12_0001.ptau" "$PTAU" -v
fi

if [[ ! -f "$ZKEY_SETUP" ]]; then
  npx snarkjs groth16 setup build/first_divisor_at_step.r1cs "$PTAU" "$ZKEY_SETUP"
fi

if [[ ! -f "$ZKEY_FINAL" ]]; then
  # `snarkjs zkey contribute` prompts for entropy on stdin; piping avoids hangs.
  ZKEY_ENTROPY="${ZKEY_ENTROPY:-hqiv-dev-$(date +%s)}"
  printf "%s\n" "$ZKEY_ENTROPY" | npx snarkjs zkey contribute \
    "$ZKEY_SETUP" \
    "$ZKEY_FINAL" \
    --name=hqiv-circuit -v -e="${ZKEY_ENTROPY}"
fi

npx snarkjs wtns calculate build/first_divisor_at_step_js/first_divisor_at_step.wasm "$INPUT_JSON" witness.wtns

if [[ ! -f "$ROOT/verification_key.json" ]] || [[ ! -f "$ZKEY_FINAL" ]]; then
  npx snarkjs zkey export verificationkey "$ZKEY_FINAL" verification_key.json
fi

npx snarkjs groth16 prove "$ZKEY_FINAL" witness.wtns proof.json public.json
npx snarkjs groth16 verify verification_key.json public.json proof.json

echo "OK: proof.json and public.json written; verification passed."
