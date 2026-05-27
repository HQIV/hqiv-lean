#!/usr/bin/env bash
# Compile selected manuscripts twice and fail if the log contains common warnings
# (LaTeX/package warnings, overfull boxes). Run from repo root or via path below.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PATTERN='LaTeX Warning|Package hyperref Warning|Package .* Warning|Overfull \\hbox'

check_tex () {
  local rel="$1"
  local dir base logpath
  dir="$(dirname "$rel")"
  base="$(basename "$rel")"
  logpath="$ROOT/$dir/${base%.tex}.log"
  (cd "$ROOT/$dir" && pdflatex -interaction=nonstopmode "$base" >/dev/null)
  (cd "$ROOT/$dir" && pdflatex -interaction=nonstopmode "$base" >/dev/null)
  if rg -n "$PATTERN" "$logpath" >/tmp/hqiv_latex_warn.txt 2>/dev/null; then
    echo "FAILED: warnings/overfull boxes in $rel" >&2
    cat /tmp/hqiv_latex_warn.txt >&2
    exit 1
  fi
  echo "OK $rel"
}

check_tex papers/closure.tex
check_tex papers/so8_closure_full_appendix.tex
