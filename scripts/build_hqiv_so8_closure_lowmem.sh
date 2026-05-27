#!/usr/bin/env bash
# Build the heavy SO(8) matrix Lie-closure library with minimal peak RAM.
# Parallel elaboration of 784 LieBracketCell modules + norm_num blows past ~100GB
# on large -j; use single-threaded Lake + single Lean elaboration thread.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
exec lake build HQIVSO8Closure -j 1 "$@"
