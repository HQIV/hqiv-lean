# Third-Party Benchmark Notes

## QASMBench basis_change

QASMBench `small/basis_change_n3/basis_change_n3.qasm` is an OpenFermion/Cirq basis-change
circuit. It requires OpenQASM 2 single-qubit rotations (`u3`, with `u2`, `rx`, `ry`, and `rz` as
special cases) plus entangling `cz` layers. Treating this family as CZ-only is an unsupported
partial circuit, not a norm failure of the intended benchmark.

Lean certifies the HQIV side through `Hqiv/QuantumComputing/DigitalGates.lean`:

- `TwoLevelOctonionUnitary` is the proof-carrying witness for a local two-level mix.
- `twoLevelUnitaryGate` lifts such a witness to an `HQIVGate` and proves preservation of
  `discreteIp` and `discreteNormSq`.
- `realPlaneRotationGate` is the real `SO(2)` shadow used as the first compiled rotation example.

Python should parse QASMBench `basis_change` only after realifying the OpenQASM complex `u3`
matrix onto the embedded octonion components and carrying the sparse metadata as
`SparseGateKind.local_mix`. Until that bridge is wired, benchmark reports should mark
`basis_change_n3.qasm` as `unsupported`.

Reference: QASMBench describes `basis_change` as transforming the single-particle basis of a
linearly connected electronic-structure problem.
