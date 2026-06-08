pragma circom 2.1.0;

// circomlib from npm: `npm install` in this directory, then compile with
//   circom first_divisor_at_step.circom --r1cs --wasm --sym -l node_modules -o ../build

include "circomlib/circuits/comparators.circom";

/**
 * Proves a public step count for a fixed ordered scan:
 *   - n, step_index (1-based), factor_d are public;
 *   - private c[i], q[i], r[i] satisfy n = q[i]*c[i] + r[i];
 *   - rows 0..step_index-2 are "active" non-wins: remainder r[i] ≠ 0;
 *   - row step_index-1 wins: r=0 and c = factor_d;
 *   - padded rows i ≥ step_index are inactive dummies (c=1, q=n, r=0).
 *
 * Field: BN254 (snarkjs default). Keep n and intermediates so that q*c fits in-field
 * (roughly n < ~2^127 for worst-case product bounds — see README).
 */
template FirstDivisorAtStep(MAX_STEPS) {
    signal input n;
    signal input step_index;
    signal input factor_d;
    signal input c[MAX_STEPS];
    signal input q[MAX_STEPS];
    signal input r[MAX_STEPS];

    // step_index >= 1
    component gt0 = GreaterThan(8);
    gt0.in[0] <== step_index;
    gt0.in[1] <== 0;
    gt0.out === 1;

    signal active[MAX_STEPS];
    signal isLast[MAX_STEPS];
    signal inactive[MAX_STEPS];
    signal mid[MAX_STEPS];
    component gt[MAX_STEPS];
    component eq[MAX_STEPS];
    component rz[MAX_STEPS];

    for (var i = 0; i < MAX_STEPS; i++) {
        n === q[i] * c[i] + r[i];

        gt[i] = GreaterThan(8);
        gt[i].in[0] <== step_index;
        gt[i].in[1] <== i;
        active[i] <== gt[i].out;

        eq[i] = IsEqual();
        eq[i].in[0] <== step_index;
        eq[i].in[1] <== i + 1;
        isLast[i] <== eq[i].out;

        inactive[i] <== 1 - active[i];
        inactive[i] * (c[i] - 1) === 0;
        inactive[i] * (q[i] - n) === 0;
        inactive[i] * r[i] === 0;

        mid[i] <== active[i] - active[i] * isLast[i];
        rz[i] = IsZero();
        rz[i].in <== r[i];
        mid[i] * rz[i].out === 0;

        isLast[i] * r[i] === 0;
        isLast[i] * (c[i] - factor_d) === 0;
    }
}

component main { public [n, step_index, factor_d] } = FirstDivisorAtStep(64);
