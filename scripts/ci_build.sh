#!/usr/bin/env bash
# Mirror .github/workflows/lean_action_ci.yml build job locally before pushing.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

echo "==> Factor oracle unit tests"
python3 -m unittest scripts.test_factor_from_curvature -v

echo "==> Default lean-action build target"
lake build

echo "==> HQIVMeaningfulPhysics"
lake build HQIVMeaningfulPhysics

echo "==> LeanDojoMillennium (vendored Problems.* for story spine)"
lake build LeanDojoMillenniumIndex

echo "==> HQIVStory"
lake build HQIVStory

echo "==> HQIVStrongColorSu3Certificate"
lake build HQIVStrongColorSu3Certificate

echo "CI build job passed."
