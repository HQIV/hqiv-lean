#!/usr/bin/env bash
# Fetch SATLIB GCP DIMACS files from the Rutgers DIMACS archive (.cnf.Z → .cnf).
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE="http://archive.dimacs.rutgers.edu/pub/challenge/sat/benchmarks/volume/Cnf"
FILES=(g125.18.cnf.Z g125.17.cnf.Z g250.15.cnf.Z g250.29.cnf.Z)

cd "$DIR"
for z in "${FILES[@]}"; do
  echo "fetching $z ..."
  curl -fsSL -o "$z" "$BASE/$z"
  uncompress -f "$z"
done
echo "done. Files:"
ls -la *.cnf
