# zk-SNARK: first-factor step count (mask disclosure)

This folder proves a **public statement** about a **deterministic ordered scan**:

- **Public inputs:** `n`, `step_index` (1-based), `factor_d`
- **Private witness:** per-row quotients `q[i]` and remainders `r[i]` for the padded candidate list `c[i]`, with `n = q[i]*c[i] + r[i]` in the BN254 field.

**What the Groth16 circuit proves:** For the fixed unrolling `MAX_STEPS = 64`, there exists a trace such that:

1. Rows `0 … step_index-2` are “active” probes with **nonzero** remainder (no proper divisor yet).
2. Row `step_index-1` is the **winning** row: remainder `0`, and `c == factor_d`.
3. Padding rows `step_index … MAX_STEPS-1` are inactive dummies (`c=1`, `q=n`, `r=0`).

Together with publishing **`export_witness.py`** and `factor_from_curvature.py`, this discloses *how many mask-sorted nontrivial candidates were tried* before hitting a factor, without putting float trig in the circuit.

**What it does *not* prove:** That `c[i]` came from the 3-spiral geometry (only that the division trace is consistent). Bind geometry by publishing `ordered_candidates` / `disclosure_commitment_sha256` next to the proof.

## Why “221 in 12 steps” is a bad headline

Trial division up to √221 is trivial on a laptop. The interesting claim is **not** “fewer steps than scanning every integer up to √n”, but:

- **Structured disclosure:** the exact oracle params and the **trace** through the mask’s ordered list; and  
- **Non-toy integers:** choose `n` and `factor_d` large enough that raw guess-and-check over all residues up to √n is not the right comparison.

**Recommended default example** (built into `export_witness.py`):

- `n = 118472447 = 9319 × 12713` (smallest factor ≈ **14 bits**)
- `phi`, `t`, `window` from `--example-large-params` (mask hits at **step 25**)

```bash
python3 export_witness.py 118472447 --example-large-params --circom-out input.json
```

If your composite does not hit a factor in the mask list with default `phi,t,window`, use **`--auto-tune`** (random search over parameters) until a witness exists, or tune by hand.

**Limits:**

- **Python oracle alignment:** `factor_from_curvature.MAX_PRIME_SIEVE_BOUND` is **64**, matching this circuit’s `MAX_STEPS` unrolling (same disclosure budget: mask-sorted steps vs. prime-step / trial guard cap).
- **BN254 field:** All witnesses must lie in `[0, p)` with `p` the BN254 scalar modulus (~253.9 bits). The exporter checks this; larger integers need a bigint / limb circuit.
- **Mask may miss huge random semiprimes:** There is no guarantee that arbitrary large `n` admit *any* `(φ,t,ω)` with a divisor in the first `MAX_STEPS` candidates — that is an empirical property of the oracle, not of the SNARK.
- **Trusted setup:** `build_and_prove.sh` uses a **local** powers of tau — fine for development only. Production needs a proper ceremony or reusable `ptau` + fixed `zkey`.

## Setup

```bash
cd scripts/zk_factor_steps
npm ci
```

Install **Circom 2** (one of):

- Download `circom-linux-amd64` from [iden3/circom releases](https://github.com/iden3/circom/releases) → `bin/circom` (gitignored), or
- `cargo install circom` if you use Rust.

## Generate witness + proof

```bash
python3 scripts/zk_factor_steps/export_witness.py 118472447 --example-large-params \
  --circom-out scripts/zk_factor_steps/input.json

cd scripts/zk_factor_steps
./build_and_prove.sh input.json
```

Outputs: `proof.json`, `public.json` (public signals), `verification_key.json`.

## Files

| File | Role |
|------|------|
| `export_witness.py` | Runs the mask with `use_sieve=False`, builds filtered ordered scan + padding |
| `circuits/first_divisor_at_step.circom` | Groth16 constraints |
| `build_and_prove.sh` | `circom` → `snarkjs` setup → prove → verify |
