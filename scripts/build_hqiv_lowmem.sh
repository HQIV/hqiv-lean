#!/usr/bin/env bash
# Low-RAM builds for HQIV: one target at a time, minimal Lean parallelism.
#
# Lake 5 has no `lake build -j`. Set LEAN_NUM_THREADS before `lake build`.
# For ad-hoc modules not in a named target, pass a `.lean` path (typecheck only).
#
# Do not run multiple instances of this script in parallel with other lake builds.
#
# Usage:
#   scripts/build_hqiv_lowmem.sh HQIVPhysics
#   scripts/build_hqiv_lowmem.sh Hqiv/Physics/OrbitalTrajectoryJ2Scaffold.lean
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
if [[ "$#" -eq 0 ]]; then
  echo "usage: $0 <lake-target | path/to/Module.lean>..." >&2
  exit 2
fi
for target in "$@"; do
  if [[ "${target}" == *.lean ]]; then
    echo "==> lean -j1 ${target}"
    lake env lean -j1 "${target}"
  else
    echo "==> lake build ${target} (LEAN_NUM_THREADS=${LEAN_NUM_THREADS})"
    lake build "${target}"
  fi
done
