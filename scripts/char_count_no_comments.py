#!/usr/bin/env python3
"""UTF-8 byte size of `.py` sources minus `#` comments, docstrings, and standalone gloss strings."""

from __future__ import annotations

import argparse
import ast
import json
import tokenize
from io import BytesIO
from pathlib import Path
from typing import Iterable


def _utf8_line_starts(text: str) -> list[int]:
    b = text.encode("utf-8")
    starts = [0]
    for i, c in enumerate(b):
        if c == 10:
            starts.append(i + 1)
    return starts


def _byte_span(text: str, node: ast.AST, line_starts: list[int]) -> tuple[int, int] | None:
    if node.lineno is None or node.col_offset is None:
        return None
    el = node.end_lineno or node.lineno
    ec = node.end_col_offset
    if ec is None:
        return None
    raw = text.encode("utf-8")
    lo = line_starts[node.lineno - 1] + node.col_offset
    hi = line_starts[el - 1] + ec
    return (lo, min(hi, len(raw)))


def _merge(ranges: list[tuple[int, int]]) -> list[tuple[int, int]]:
    if not ranges:
        return []
    ranges = sorted(ranges)
    out = [ranges[0]]
    for a, b in ranges[1:]:
        la, lb = out[-1]
        if a <= lb:
            out[-1] = (la, max(lb, b))
        else:
            out.append((a, b))
    return out


def _merged_total_len(ranges: list[tuple[int, int]], cap: int) -> int:
    t = 0
    for a, b in ranges:
        a = max(0, min(a, cap))
        b = max(0, min(b, cap))
        if b > a:
            t += b - a
    return t


def _docstring_spans(text: str, line_starts: list[int], tree: ast.Module) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []

    def first_doc(body: list[ast.stmt]) -> None:
        if not body:
            return
        st0 = body[0]
        if isinstance(st0, ast.Expr) and isinstance(st0.value, ast.Constant) and isinstance(st0.value.value, str):
            sp = _byte_span(text, st0, line_starts)
            if sp:
                spans.append(sp)

    first_doc(tree.body)
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            first_doc(node.body)
    return spans


def _gloss_string_spans(text: str, line_starts: list[int], tree: ast.Module, doc_spans: list[tuple[int, int]]) -> list[tuple[int, int]]:

    def inside_any(lo: int, hi: int, bag: list[tuple[int, int]]) -> bool:
        for a, b in bag:
            if lo >= a and hi <= b:
                return True
        return False

    spans: list[tuple[int, int]] = []

    def walk_body(body: list[ast.stmt]) -> None:
        skip0 = False
        if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
            if isinstance(body[0].value.value, str):
                skip0 = True
        for j, st in enumerate(body):
            if skip0 and j == 0:
                continue
            if isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant) and isinstance(st.value.value, str):
                sp = _byte_span(text, st, line_starts)
                if sp and not inside_any(*sp, doc_spans):
                    spans.append(sp)

    walk_body(tree.body)
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            walk_body(node.body)
    return spans


def _comment_spans_tokenize(text: str, line_starts: list[int]) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    readline = BytesIO(text.encode("utf-8")).readline
    for tok in tokenize.tokenize(readline):
        if tok.type == tokenize.COMMENT:
            lo = line_starts[tok.start[0] - 1] + tok.start[1]
            hi = line_starts[tok.end[0] - 1] + tok.end[1]
            spans.append((lo, hi))
    return spans


def count_effective_bytes(text: str) -> tuple[int, int, int]:
    """Return (raw_utf8, effective_bytes, dropped_bytes)."""
    raw_b = text.encode("utf-8")
    raw = len(raw_b)
    line_starts = _utf8_line_starts(text)
    tree = ast.parse(text)
    doc = _docstring_spans(text, line_starts, tree)
    gloss = _gloss_string_spans(text, line_starts, tree, _merge(doc))
    comments = _comment_spans_tokenize(text, line_starts)
    merged = _merge(doc + gloss + comments)
    dropped = _merged_total_len(merged, raw)
    eff = raw - dropped
    return raw, eff, dropped


def _iter_paths(paths: Iterable[str]) -> list[Path]:
    out: list[Path] = []
    for p in paths:
        path = Path(p)
        if path.is_dir():
            out.extend(sorted(path.rglob("*.py")))
        else:
            out.append(path)
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="+", help="files or dirs (recursive *.py for dirs)")
    ap.add_argument("--json", action="store_true", help="one JSON line per file")
    args = ap.parse_args(argv)
    files = _iter_paths(args.paths)
    tot_raw = tot_eff = 0
    for fp in files:
        text = fp.read_text(encoding="utf-8")
        raw, eff, dropped = count_effective_bytes(text)
        tot_raw += raw
        tot_eff += eff
        if args.json:
            print(
                json.dumps(
                    {
                        "path": str(fp),
                        "raw_bytes": raw,
                        "effective_bytes": eff,
                        "dropped_bytes": dropped,
                    }
                )
            )
        else:
            print(f"{fp}\traw={raw}\teffective={eff}\tdropped={dropped}")
    if len(files) > 1 and not args.json:
        print(f"TOTAL\traw={tot_raw}\teffective={tot_eff}\tdropped={tot_raw - tot_eff}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
