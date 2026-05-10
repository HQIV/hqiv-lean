#!/usr/bin/env python3
"""Solo Stage 2 single-file solver: stdin JSON → judge line (Lean bundled).

Quantum pipeline (full story): papers/paper/octonion_lightcone_to_oshoracle.tex — light-cone axioms
→ auxiliary/rapidity ladder → octonionic digital states → sparse horizon-causal gates (OSHoracle).
This file’s XOR/INV shell map is only a **classical reversible shadow** of the DigitalGates layer
(see Hqiv/QuantumComputing/{DigitalGates,OSHoracle,OSHoracleHQIVNative}.lean); no octonion carrier here.

**Countermodels (inverse of ∀ proof):** search for a finite magma with eq1 universal and eq2 failing uses
`rapidity_first_atsp_oracle.rapidity_first_solver` to order encoding trials—not full n^(n²) enumeration when
that exceeds a cap. Before that, **SO(n)-style twiddle** magmas (plane transposition + twisted Z_n combine,
plus an optional (a−b) mod n layer) probe phase-like equations. True certificates remain singleton + LLM.
"""

from __future__ import annotations

import importlib.util
import json
import math
import re
import sys
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Any, Callable, Mapping

# --- Lean judge export (must stay in this file for Stage 2 single-file submission) ---

BANNED_LEAN_IDENTIFIERS: tuple[str, ...] = (
    "sorryAx",
    "sorry",
    "admit",
    "dbg_trace",
    "dbgTrace",
    "run_tac",
    "mkSorry",
    "builtin_initialize",
    "initialize",
)

_BANNED_RE = re.compile(
    r"\b(?:" + "|".join(re.escape(t) for t in BANNED_LEAN_IDENTIFIERS) + r")\b"
)


def check_no_banned_lean(code: str) -> None:
    m = _BANNED_RE.search(code)
    if m:
        raise ValueError(f"lean: banned token {m.group(0)!r} at offset {m.start()}")


def escape_lean_double_quoted_payload(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def validate_square_op_table(op: list[list[int]]) -> int:
    n = len(op)
    if n < 1:
        raise ValueError("op_table: need at least Fin 1")
    for i, row in enumerate(op):
        if len(row) != n:
            raise ValueError(f"op_table: row {i} length {len(row)} != n {n}")
        for j, v in enumerate(row):
            if not isinstance(v, int) or isinstance(v, bool):
                raise ValueError(f"op_table[{i}][{j}] must be int (non-bool)")
            if not (0 <= v < n):
                raise ValueError(f"op_table[{i}][{j}] = {v} out of range for Fin {n}")
    return n


def indent_tactic_body(body: str, spaces: int = 2) -> str:
    pref = " " * spaces
    lines = body.strip("\n").splitlines()
    out: list[str] = []
    for ln in lines:
        out.append(pref + ln if ln.strip() else "")
    return "\n".join(out)


def export_true_certificate(tactic_body: str) -> str:
    tb = tactic_body.strip()
    if not tb:
        raise ValueError("export_true: empty tactic_body")
    block = indent_tactic_body(tb)
    return f"import JudgeProblem\n\ndef submission : Goal := by\n{block}\n"


def export_false_certificate(op_table: list[list[int]]) -> str:
    n = validate_square_op_table(op_table)
    js = json.dumps(op_table, separators=(",", ":"))
    esc = escape_lean_double_quoted_payload(js)
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{ op := finOpTable \"{esc}\" }}\n"
        f"  refine ⟨Fin {n}, m, ?_⟩\n"
        "  decideFin!\n"
    )


def check_submission_size(
    code: str,
    *,
    verdict: str,
    max_code_length: int,
    max_false_cert_bytes: int,
) -> None:
    if len(code) > max_code_length:
        raise ValueError(f"lean: len(code)={len(code)} > max_code_length={max_code_length}")
    if verdict == "false":
        b = len(code.encode("utf-8"))
        if b > max_false_cert_bytes:
            raise ValueError(
                f"lean: false cert utf-8 bytes={b} > max_false_cert_bytes={max_false_cert_bytes}"
            )


def validate_submission_lean(
    code: str,
    *,
    verdict: str,
    max_code_length: int,
    max_false_cert_bytes: int,
) -> None:
    check_no_banned_lean(code)
    check_submission_size(
        code,
        verdict=verdict,
        max_code_length=max_code_length,
        max_false_cert_bytes=max_false_cert_bytes,
    )


def build_judge_line(verdict: str, code: str) -> str:
    if verdict not in ("true", "false"):
        raise ValueError(f"verdict must be 'true' or 'false', got {verdict!r}")
    return json.dumps({"call": "judge", "verdict": verdict, "code": code})


# --- Solo proxy (stdin lines after startup envelope) + magma search (baseline-derived) ---

PROMPT = """You are solving equational theory problems in Lean 4 (magma ◇).

Does law {problem.eq1_id} imply law {problem.eq2_id}?
Hypothesis (∀ G [Magma G]): {problem.equation1}
Goal: {problem.equation2}

If true, output tactic lines only (no imports, no `def` / `theorem`; body after `intro G _ h` is fine).
If false, output a finite counterexample as JSON table for `finOpTable`.

Previous attempts:
{history.attempts}

Respond with ONLY JSON, no markdown:
{"verdict": "true", "proof": "<tactic body>"}
or
{"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""


def normalize_magma_text(text: str) -> str:
    "Competition normalizes `*` to ◇; keep parser on Unicode ◇."
    return text.strip().replace("*", "\u25c7")


def send_json_line(obj: Mapping[str, Any]) -> None:
    print(json.dumps(obj), flush=True)


def read_json_line() -> dict[str, Any]:
    line = sys.stdin.readline()
    if line == "" or not line.strip():
        return {}
    return json.loads(line.strip())


def call_judge(verdict: str, code: str) -> dict[str, Any]:
    send_json_line({"call": "judge", "verdict": verdict, "code": code})
    return read_json_line()


def call_llm(context: Mapping[str, Any]) -> dict[str, Any]:
    send_json_line({"call": "llm", "context": dict(context)})
    return read_json_line()


def parse_equation(text: str) -> tuple[list[str], Callable[..., int], Callable[..., int]]:
    variables: list[str] = []
    seen: set[str] = set()
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    lhs_str, rhs_str = text.split("=", 1)

    def _to_expr(s: str) -> Callable[..., int]:
        s = s.strip()
        while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
            depth = 0
            matched = True
            for i, c in enumerate(s):
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                if depth == 0 and i < len(s) - 1:
                    matched = False
                    break
            if matched:
                s = s[1:-1].strip()
            else:
                break
        depth = 0
        last_op = -1
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            elif c == "\u25c7" and depth == 0:
                last_op = i
        if last_op >= 0:
            left = _to_expr(s[:last_op])
            right = _to_expr(s[last_op + 1 :])

            def bin_ap(env: Mapping[str, Any], l: Callable = left, r: Callable = right) -> int:
                return int(env["op"](l(env), r(env)))

            return bin_ap
        s = s.strip()
        if len(s) == 1 and s in seen:

            def var_ap(env: Mapping[str, Any], v: str = s) -> int:
                return int(env[v])

            return var_ap
        raise ValueError(f"Cannot parse: {s}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def _equation_holds_on_table(
    variables: list[str], lhs: Callable[..., int], rhs: Callable[..., int], n: int, op: Callable[[int, int], int]
) -> bool:
    for vals in product(range(n), repeat=len(variables)):
        env: dict[str, Any] = {"op": op}
        for v, val in zip(variables, vals):
            env[v] = int(val)
        if lhs(env) != rhs(env):
            return False
    return True


# --- SO(n)-style twiddle magmas (discrete analogue of exp(t Δ_{ij}); paper holonomy exp(2πΔ)=I) ---


def equation_rotation_heuristic(text: str) -> bool:
    "True if nesting / repeats / asymmetry suggest trying plane-twiddle magmas before ATSP sampling."
    s = normalize_magma_text(text)
    toks = re.findall(r"\b([a-z])\b", s)
    if len(toks) > len(set(toks)):
        return True
    if s.count("\u25c7") >= 2 and s.count("(") >= 2:
        return True
    parts = s.split("=", 1)
    if len(parts) == 2:
        lhs, rhs = parts[0].strip(), parts[1].strip()
        if lhs != rhs and abs(len(lhs) - len(rhs)) >= 4:
            return True
    return False


def _swap_plane_coord(x: int, i: int, j: int) -> int:
    "Transposition on labels i,j (discrete Weyl reflection for that plane)."
    if x == i:
        return j
    if x == j:
        return i
    return x


def so_n_twiddle_op(n: int, i: int, j: int, twist: int) -> Callable[[int, int], int]:
    """Binary op: plane swap on each argument, then Z_n ``twisted linear'' combine.

    Continuum story (octonion / SO paper): skew generator Δ_{ij} rotates the (i,j) plane;
    exp(2π Δ_{ij}) = I gives 2π-periodic holonomy; trace on that block is n−2+2 cos(t) in the n×n picture.
    Here we use integer mod-n arithmetic instead of cos/sin floats.
    """
    tw = int(twist) % n
    if tw == 0:
        tw = 1

    def op(a: int, b: int) -> int:
        sa = _swap_plane_coord(int(a) % n, i, j)
        sb = _swap_plane_coord(int(b) % n, i, j)
        return (tw * sa + (n - tw) * sb) % n

    return op


def _dedupe_planes(planes: list[tuple[int, int]], n: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for i, j in planes:
        if i >= n or j >= n or i == j or i < 0 or j < 0:
            continue
        a, b = (min(i, j), max(i, j))
        if (a, b) in seen:
            continue
        seen.add((a, b))
        out.append((i, j))
    return out


def default_twiddle_planes(n: int, *, extra: bool) -> list[tuple[int, int]]:
    base = [(0, 1), (0, min(2, n - 1)), (1, min(2, n - 1))]
    if extra and n >= 4:
        base.extend([(0, n - 1), (1, n - 1), (2, min(3, n - 1))])
    return _dedupe_planes(base, n)


def default_twist_integers(n: int) -> list[int]:
    cand = [1, 2, max(1, n // 2), max(1, n - 1)]
    if n > 3:
        cand.append(max(2, n // 3))
    out = sorted({c % n for c in cand if c % n != 0})
    return out or [1]


def so_n_twiddle_counterexample(
    eq1_text: str,
    eq2_text: str,
    n: int,
    *,
    planes: list[tuple[int, int]] | None = None,
    twists: list[int] | None = None,
) -> tuple[int | None, list[list[int]] | None]:
    "Try structured SO(n)-inspired twiddle magmas on Fin n; return explicit table if E1 universal ∧ ¬E2."
    lhs_vars, lhs_l, lhs_r = parse_equation(eq1_text)
    rhs_vars, rhs_l, rhs_r = parse_equation(eq2_text)
    pl = planes if planes is not None else default_twiddle_planes(n, extra=False)
    tws = twists if twists is not None else default_twist_integers(n)
    for i, j in _dedupe_planes(pl, n):
        for tw in tws:
            op = so_n_twiddle_op(n, i, j, tw)
            if _equation_holds_on_table(lhs_vars, lhs_l, lhs_r, n, op) and not _equation_holds_on_table(
                rhs_vars, rhs_l, rhs_r, n, op
            ):
                tab = [[op(a, b) for b in range(n)] for a in range(n)]
                return n, tab
    return None, None


_ratsp_mod: Any | None = False


def load_rapidity_first_atsp_oracle() -> Any | None:
    "Load `scripts/rapidity_first_atsp_oracle.py` (needs `scripts/` on `sys.path` for `directed_torus_*`)."
    global _ratsp_mod
    if _ratsp_mod is not False:
        return _ratsp_mod
    scripts = Path(__file__).resolve().parent.parent
    path = scripts / "rapidity_first_atsp_oracle.py"
    if not path.is_file():
        _ratsp_mod = None
        return None
    if str(scripts) not in sys.path:
        sys.path.insert(0, str(scripts))
    spec = importlib.util.spec_from_file_location("_hqiv_rapidity_atsp_stage2", path)
    if spec is None or spec.loader is None:
        _ratsp_mod = None
        return None
    mod = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(mod)
    except Exception:
        _ratsp_mod = None
        return None
    _ratsp_mod = mod
    return mod


def encoding_to_table(n: int, enc: int) -> list[list[int]]:
    "Row-major decoding of a magma table from a single integer encoding."
    return [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]


def build_encoding_samples(total: int, cap: int, seed: int) -> list[int]:
    "Evenly spaced encodings through [0, total); full range if total <= cap."
    if total <= cap:
        return list(range(total))
    stride = max(1, total // cap)
    return [(seed + k * stride) % total for k in range(cap)]


def asymmetric_dist_for_encodings(encs: list[int], salt: int) -> list[list[float]]:
    "Directed costs between candidate encodings (ATSP input; asymmetry from salt + indices)."
    s = len(encs)
    dist = [[0.0] * s for _ in range(s)]
    for i in range(s):
        for j in range(s):
            if i == j:
                continue
            ei, ej = encs[i], encs[j]
            dist[i][j] = float((ei ^ ej) & 0x3FFF) + 0.01 * float((salt + 31 * i + 17 * j) % 97) + 0.001 * float(i - j)
    return dist


def encoding_visit_orders_atsp(encs: list[int], dist: list[list[float]], mod: Any | None) -> list[list[int]]:
    "Rapidity-first ATSP yields permutations of sample indices → visit orders over encodings."
    s = len(encs)
    if s < 2 or mod is None:
        return [list(encs)]
    sc = max(4, min(22, s))
    slots = max(2, min(8, max(2, s // 2)))
    r = mod.rapidity_first_solver(
        dist,
        top_k=6,
        shell_count=sc,
        slots_per_shell=slots,
        pool_limit=min(48, s * 2),
        keep_per_shell=max(2, min(4, max(2, s // 3))),
        local_search_mode="off",
        flip_prune=True,
    )
    orders: list[list[int]] = []
    seen: set[tuple[int, ...]] = set()
    for bucket in ("top_k_by_research_score", "top_k_by_cost"):
        for cand in r.get(bucket, [])[:8]:
            tour = cand.get("tour")
            if not isinstance(tour, (list, tuple)) or len(tour) != s:
                continue
            seq = [encs[int(c)] for c in tour]
            key = tuple(seq)
            if key in seen:
                continue
            seen.add(key)
            orders.append(seq)
    if not orders:
        orders.append(list(encs))
    return orders


def search_counterexample_atsp(
    eq1_text: str, eq2_text: str, max_n: int = 3, *, enc_seed: int, visit_cap: int = 15_000
) -> tuple[int | None, list[list[int]] | None]:
    """Inverse task vs proof: ∃ magma on Fin n with eq1 universal and eq2 not (countermodel).

    Uses HQIV `rapidity_first_solver` to order a **spread sample** of table encodings (not full
    n^(n²) sweep when that exceeds `visit_cap`). Falls back to sample list order if oracle missing.

    First, for each n, tries **SO(n)-style twiddle** magmas (plane swap + twisted linear mod n) when
    a cheap heuristic flags phase-like structure—or a small default plane set regardless.
    """
    lhs_vars, lhs_l, lhs_r = parse_equation(eq1_text)
    rhs_vars, rhs_l, rhs_r = parse_equation(eq2_text)
    mod = load_rapidity_first_atsp_oracle()
    salt = (enc_seed ^ (hash(eq1_text) & 0xFFFFFFFF) ^ (hash(eq2_text) << 1)) & 0xFFFFFFFF
    rot_hint = equation_rotation_heuristic(eq1_text) or equation_rotation_heuristic(eq2_text)

    for n in range(2, max_n + 1):
        pl = default_twiddle_planes(n, extra=rot_hint)
        tw_hit = so_n_twiddle_counterexample(eq1_text, eq2_text, n, planes=pl, twists=None)
        if tw_hit[0] is not None:
            return tw_hit
        if n > 2:
            alt_pl = _dedupe_planes([(0, 1), (n // 2, max(n // 2 + 1, n - 1))], n)
            tw_alt = so_n_twiddle_counterexample(eq1_text, eq2_text, n, planes=alt_pl, twists=None)
            if tw_alt[0] is not None:
                return tw_alt

        def op_lin_sub(a: int, b: int) -> int:
            "Integer π/2-fold (a,b) ↦ (a−b) mod n — holonomy-friendly commutative layer."
            return (a - b) % n

        if _equation_holds_on_table(lhs_vars, lhs_l, lhs_r, n, op_lin_sub) and not _equation_holds_on_table(
            rhs_vars, rhs_l, rhs_r, n, op_lin_sub
        ):
            return n, [[op_lin_sub(a, b) for b in range(n)] for a in range(n)]

        total = n ** (n * n)
        # Rapidity-first ATSP cost grows superlinearly in city count; cap samples for responsiveness.
        atsp_cap = min(visit_cap, total, max(96, 36 * n * n))
        encs = build_encoding_samples(total, atsp_cap, enc_seed)
        dist = asymmetric_dist_for_encodings(encs, salt)
        orders = encoding_visit_orders_atsp(encs, dist, mod)
        tried: set[int] = set()
        for order in orders:
            for enc in order:
                if enc in tried:
                    continue
                tried.add(enc)
                t = encoding_to_table(n, enc)
                op = lambda a, b, tb=t: int(tb[a][b])
                if _equation_holds_on_table(lhs_vars, lhs_l, lhs_r, n, op) and not _equation_holds_on_table(
                    rhs_vars, rhs_l, rhs_r, n, op
                ):
                    return n, t
    return None, None


def try_singleton_proof(eq1_text: str, eq2_text: str) -> str | None:
    "Degenerate 1-element model: if eq1 is `x = …` with x not on RHS, collapse via `h`."
    lhs_parts = eq1_text.split("=", 1)
    if len(lhs_parts) != 2 or lhs_parts[0].strip() != "x":
        return None
    rhs_of_lhs = set(re.findall(r"\b([a-z])\b", lhs_parts[1]))
    if "x" in rhs_of_lhs:
        return None
    eq1_vars: list[str] = []
    seen: set[str] = set()
    for v in re.findall(r"\b([a-z])\b", eq1_text):
        if v not in seen:
            seen.add(v)
            eq1_vars.append(v)
    eq2_vars: list[str] = []
    seen2: set[str] = set()
    for v in re.findall(r"\b([a-z])\b", eq2_text):
        if v not in seen2:
            seen2.add(v)
            eq2_vars.append(v)
    rhs_lhs, rhs_rhs = eq2_text.split("=", 1)
    filler = " ".join(["a"] * (len(eq1_vars) - 1))
    return (
        f"intro {' '.join(eq2_vars)}\n"
        f"have singleton : ∀ (a b : G), a = b := fun a b => (h a {filler}).trans (h b {filler}).symm\n"
        f"exact singleton ({rhs_lhs.strip()}) ({rhs_rhs.strip()})"
    )


def extract_json_from_llm(text: str) -> dict[str, Any] | None:
    text = re.sub(r"<think>[\s\S]*?</think>", "", text).strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    try:
        return json.loads(text.strip())
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            pass
    return None


def clean_llm_proof_body(raw: str) -> str:
    body = raw.strip()
    if ":= by" in body:
        body = re.sub(r"^.*?:=\s*by\s*\n?", "", body, count=1, flags=re.DOTALL)
    body = re.sub(r"^\s*by\s+", "", body)
    body = re.sub(r"^\s*import\s+.*\n?", "", body, flags=re.MULTILINE)
    body = body.strip()
    if re.match(r"^\s*intro\s+G\s+_\s+h\b", body):
        return body
    return "intro G _ h\n" + body


def solve_envelope(env: SoloEnvelope) -> None:
    "Stage 1 ATSP-guided countermodel search → singleton true → LLM (proxy protocol)."
    meta = rapidity_reversible_gate_metadata(env)
    p = env.problem
    b = env.budget
    eq1 = normalize_magma_text(p.equation1)
    eq2 = normalize_magma_text(p.equation2)
    # Stable seed for ATSP encoding order (must match exhaustive-style coverage expectations).
    enc_seed = hash((p.id, eq1, eq2)) & 0xFFFFFFFF

    visit_cap = min(25_000, max(5_000, b.timeout_seconds * 8))
    n, table = search_counterexample_atsp(eq1, eq2, max_n=3, enc_seed=enc_seed, visit_cap=visit_cap)
    if n is not None and table is not None:
        code = export_false_certificate(table)
        validate_submission_lean(
            code, verdict="false", max_code_length=b.max_code_length, max_false_cert_bytes=b.max_false_cert_bytes
        )
        if call_judge("false", code).get("status") == "accepted":
            return

    singleton = try_singleton_proof(eq1, eq2)
    if singleton:
        code = export_true_certificate("intro G _ h\n" + singleton)
        validate_submission_lean(
            code, verdict="true", max_code_length=b.max_code_length, max_false_cert_bytes=b.max_false_cert_bytes
        )
        if call_judge("true", code).get("status") == "accepted":
            return

    rnd = 0
    while True:
        llm = call_llm(
            {
                "round": str(rnd),
                "problem_id": p.id,
                "rapidity_final_bin": meta.get("final_state_bin", ""),
                "rapidity_gate_count": str(meta.get("gate_count", "")),
            }
        )
        rnd += 1
        if "error" in llm:
            break
        answer = extract_json_from_llm(llm.get("response", ""))
        if answer is None:
            continue
        verdict = answer.get("verdict")
        if verdict not in ("true", "false"):
            continue
        if verdict == "true":
            proof_raw = answer.get("proof", "")
            if not proof_raw:
                continue
            code = export_true_certificate(clean_llm_proof_body(proof_raw))
        else:
            tbl = answer.get("counterexample_table")
            if not isinstance(tbl, list) or not tbl:
                continue
            try:
                code = export_false_certificate(tbl)
            except ValueError:
                continue
        try:
            validate_submission_lean(
                code,
                verdict=verdict,
                max_code_length=b.max_code_length,
                max_false_cert_bytes=b.max_false_cert_bytes,
            )
        except ValueError:
            continue
        if call_judge(verdict, code).get("status") == "accepted":
            return


# --- Rapidity + discrete gates (paper Sec. roadmap items 1–2 schedule; 4–5 = gate-shaped heuristic) ---


def rapidity_phase_angles(
    shell_count: int,
    slots_per_shell: int,
    *,
    shell_phase_scale: float = 1.0,
    shell_phase_stride: float = 1.0,
) -> list[float]:
    "Monotone shell accumulator + per-slot ripple; angles in radians mod 2π."
    out: list[float] = []
    phase_acc = 0.0
    for s in range(max(1, shell_count)):
        phase_acc += shell_phase_scale * float(s)
        for t in range(max(1, slots_per_shell)):
            ang = phase_acc + shell_phase_stride * float(t)
            out.append(math.fmod(ang, 2.0 * math.pi))
    return out


def problem_rapidity_schedule(env: SoloEnvelope) -> tuple[int, int, int]:
    "Deterministic (shells, slots, register_bits) from problem text — drives search ordering."
    h = hash((env.problem.id, env.problem.equation1, env.problem.equation2)) & 0xFFFFFFFF
    shells = 4 + (h % 20)
    slots = 2 + ((h >> 8) % 8)
    reg_bits = 1 + ((h >> 16) % 8)
    return shells, slots, reg_bits


# --- Reversible gate map: Bristol-style out ^= f (aligns with hqiv_reversible_gate_runner.py / DigitalGates) ---


@dataclass(frozen=True)
class RevGate:
    "One Bristol-style line: XOR(a,b)->out or INV(a)->out (target ^= f(controls))."

    op: str
    inputs: tuple[int, ...]
    output: int


@dataclass(frozen=True)
class RevGateMap:
    num_wires: int
    gates: tuple[RevGate, ...]


def _wire_bit(val: int, wire: int) -> int:
    return (val >> wire) & 1


def _gate_flip_value(val: int, g: RevGate) -> int:
    if g.op == "XOR":
        a, b = g.inputs[0], g.inputs[1]
        return _wire_bit(val, a) ^ _wire_bit(val, b)
    if g.op == "INV":
        return 1 ^ _wire_bit(val, g.inputs[0])
    raise ValueError(g.op)


def apply_rev_gate(val: int, nw: int, g: RevGate) -> int:
    flip = _gate_flip_value(val, g)
    if flip & 1:
        return val ^ (1 << g.output)
    return val


def run_rev_gate_map_forward(gm: RevGateMap, initial: int) -> int:
    v = initial & ((1 << gm.num_wires) - 1)
    for g in gm.gates:
        v = apply_rev_gate(v, gm.num_wires, g)
    return v


def build_rapidity_shell_gate_map(num_wires: int, shell_count: int, slots_per_shell: int, h: int) -> RevGateMap:
    "One XOR triple per (shell, slot) + one INV per shell — rapidity shell ladder as reversible layers."
    nw = max(3, num_wires)
    gates: list[RevGate] = []
    for s in range(max(1, shell_count)):
        for t in range(max(1, slots_per_shell)):
            salt = (h + s * 9973 + t * 7919) & 0xFFFFFFFF
            a = (salt + s + t) % nw
            b = (salt // 3 + s + 2 * t + 1) % nw
            if a == b:
                b = (b + 1) % nw
            out = (salt // 7 + 2 * s + t + 2) % nw
            if out == a or out == b:
                out = (out + 1) % nw
                if out == a or out == b:
                    out = (out + 2) % nw
            gates.append(RevGate("XOR", (a, b), out))
        inv_in = s % nw
        inv_out = (s + 1) % nw
        if inv_in != inv_out:
            gates.append(RevGate("INV", (inv_in,), inv_out))
    return RevGateMap(nw, tuple(gates))


def rapidity_reversible_gate_metadata(env: SoloEnvelope) -> dict[str, Any]:
    "Shell schedule + XOR/INV layer metrics for search heuristics (cf. paper sparse expand/evolve/prune narrative)."
    shells, slots, reg = problem_rapidity_schedule(env)
    h = hash((env.problem.id, env.problem.equation1, env.problem.equation2)) & 0xFFFFFFFF
    nw = max(reg, 3)
    gm = build_rapidity_shell_gate_map(nw, shells, slots, h)
    init = h & ((1 << nw) - 1)
    final = run_rev_gate_map_forward(gm, init)
    xor_ct = sum(1 for g in gm.gates if g.op == "XOR")
    inv_ct = sum(1 for g in gm.gates if g.op == "INV")
    return {
        "shell_count": shells,
        "slots_per_shell": slots,
        "register_wires": reg,
        "num_wires": nw,
        "gate_count": len(gm.gates),
        "xor_gates": xor_ct,
        "inv_gates": inv_ct,
        "initial_state_bin": format(init, f"0{nw}b"),
        "final_state_bin": format(final, f"0{nw}b"),
        "phase_angles_sample": rapidity_phase_angles(shells, slots)[:8],
    }


# --- stdin envelope ---


@dataclass(frozen=True)
class ProblemSpec:
    id: str
    eq1_id: int
    eq2_id: int
    equation1: str
    equation2: str


@dataclass(frozen=True)
class BudgetSpec:
    timeout_seconds: int
    max_code_length: int
    max_false_cert_bytes: int


@dataclass(frozen=True)
class SoloEnvelope:
    problem: ProblemSpec
    budget: BudgetSpec


def read_stdin_line() -> str | None:
    line = sys.stdin.readline()
    if line == "":
        return None
    if line.endswith("\r\n"):
        line = line[:-2]
    elif line.endswith("\n"):
        line = line[:-1]
    elif line.endswith("\r"):
        line = line[:-1]
    return line


def _req_str(d: Mapping[str, Any], key: str, *, ctx: str) -> str:
    if key not in d:
        raise ValueError(f"{ctx}: missing {key!r}")
    v = d[key]
    if not isinstance(v, str):
        raise ValueError(f"{ctx}: {key!r} must be str, got {type(v).__name__}")
    return v


def _req_int(d: Mapping[str, Any], key: str, *, ctx: str) -> int:
    if key not in d:
        raise ValueError(f"{ctx}: missing {key!r}")
    v = d[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(f"{ctx}: {key!r} must be int (non-bool), got {type(v).__name__}")
    return v


def problem_from_dict(raw: Mapping[str, Any]) -> ProblemSpec:
    ctx = "problem"
    return ProblemSpec(
        id=_req_str(raw, "id", ctx=ctx),
        eq1_id=_req_int(raw, "eq1_id", ctx=ctx),
        eq2_id=_req_int(raw, "eq2_id", ctx=ctx),
        equation1=_req_str(raw, "equation1", ctx=ctx),
        equation2=_req_str(raw, "equation2", ctx=ctx),
    )


def budget_from_dict(raw: Mapping[str, Any] | None) -> BudgetSpec:
    d = dict(raw or {})
    return BudgetSpec(
        timeout_seconds=int(d.get("timeout_seconds", 3600)),
        max_code_length=int(d.get("max_code_length", 100_000)),
        max_false_cert_bytes=int(d.get("max_false_cert_bytes", 20_000)),
    )


def envelope_from_dict(env: Mapping[str, Any]) -> SoloEnvelope:
    if "problem" not in env:
        raise ValueError("envelope: missing 'problem'")
    p = env["problem"]
    if not isinstance(p, Mapping):
        raise ValueError(f"envelope: 'problem' must be object, got {type(p).__name__}")
    b = env.get("budget")
    if b is not None and not isinstance(b, Mapping):
        raise ValueError(f"envelope: 'budget' must be object or absent, got {type(b).__name__}")
    return SoloEnvelope(problem=problem_from_dict(p), budget=budget_from_dict(b))


def read_solo_envelope_stdin() -> SoloEnvelope | None:
    line = read_stdin_line()
    if line is None:
        return None
    if not line.strip():
        raise ValueError("envelope: empty line")
    try:
        obj = json.loads(line)
    except json.JSONDecodeError as e:
        raise ValueError(f"envelope: invalid JSON: {e}") from e
    if not isinstance(obj, Mapping):
        raise ValueError(f"envelope: root must be object, got {type(obj).__name__}")
    return envelope_from_dict(obj)


def main() -> None:
    try:
        env = read_solo_envelope_stdin()
    except ValueError as e:
        print(str(e), file=sys.stderr)
        raise SystemExit(2) from e
    if env is None:
        return
    try:
        solve_envelope(env)
    except ValueError as e:
        print(str(e), file=sys.stderr)
        raise SystemExit(2) from e


if __name__ == "__main__":
    main()
