# Script audit (top-level `scripts/*.py`)

- Timeout per script: 30s
- CWD for each run: `scripts/`
- Total: 129 | **pass (0)**: 76 | **fail / timeout**: 53

## Passed (exit 0)

- `scripts/benchmark_atsp_stepdown.py` (15.724s)
- `scripts/benchmark_bonded_horizon_molecules.py` (0.06s)
- `scripts/benchmark_protein_osh_vs_dense.py` (9.135s)
- `scripts/bonded_horizon_casimir_float.py` (0.021s)
- `scripts/build_semiprime_u64_list.py` (0.047s)
- `scripts/check_rapidity_prune_safety.py` (1.669s)
- `scripts/cubic_phase_relax_probe.py` (0.057s)
- `scripts/default3d_coeff_zeta3_partial_sum.py` (0.062s)
- `scripts/directed_torus_atsp_oracle.py` (0.091s)
- `scripts/edge_space_atsp_oracle.py` (6.392s)
- `scripts/export_fractional_channel_certificate.py` (0.041s)
- `scripts/export_oracle_bridge_certificate.py` (28.907s)
- `scripts/export_worst_case_envelope_certificate.py` (15.394s)
- `scripts/factor_grok.py` (0.085s)
- `scripts/fator_grok.py` (0.057s)
- `scripts/fluid_f2_chart_alignment.py` (0.028s)
- `scripts/fragment_aware_bonded_horizon.py` (0.029s)
- `scripts/frame_well_curvature_probe.py` (0.072s)
- `scripts/ft_patch_closed_target_probe.py` (0.087s)
- `scripts/generate_symbolic_so4_certificate.py` (0.359s)
- `scripts/geometric_tsp_oracle.py` (0.068s)
- `scripts/grace_acceleration_anomaly.py` (0.045s)
- `scripts/hqiv_cartesian_gaussian.py` (16.784s)
- `scripts/hqiv_curvature_information_ontology.py` (0.055s)
- `scripts/hqiv_geometric_3sat_demo.py` (0.113s)
- `scripts/hqiv_isotope_hydrogenic_scales.py` (0.03s)
- `scripts/hqiv_isotope_inventory.py` (0.047s)
- `scripts/hqiv_lean_encoding_pegs.py` (0.092s)
- `scripts/hqiv_molecular_hamiltonian.py` (0.137s)
- `scripts/hqiv_quantum_gate_alias_probe.py` (0.043s)
- `scripts/hqiv_sat_atsp_lift_experiment.py` (0.144s)
- `scripts/hqiv_spin_charge_mass_explore.py` (0.03s)
- `scripts/hqiv_targets_h2_lih.py` (8.032s)
- `scripts/lih_derivation_scan.py` (0.422s)
- `scripts/n3_geometric_degeneracy_probe.py` (0.152s)
- `scripts/nuclear_torus_casimir_float.py` (0.018s)
- `scripts/omaxwell_torus_ode.py` (0.032s)
- `scripts/physics_lib_globs.py` (0.022s)
- `scripts/plastic_arity_twiddle_cancellation.py` (0.062s)
- `scripts/plastic_spiral_v3.py` (0.043s)
- `scripts/plastic_twisted_euler_certificate_exporter.py` (0.068s)
- `scripts/plastic_zeta_phase_probe.py` (0.219s)
- `scripts/plot_arity_spiral_meets.py` (0.054s)
- `scripts/print_lean_generators.py` (0.143s)
- `scripts/print_lean_octonion_L.py` (0.095s)
- `scripts/print_lie_bracket_closure.py` (0.142s)
- `scripts/print_linear_independence.py` (0.141s)
- `scripts/qm_finite_tensor_toy.py` (0.106s)
- `scripts/qm_general_finite_core.py` (0.084s)
- `scripts/qm_hubbard_dimer.py` (0.118s)
- `scripts/qm_hubbard_dimer_half_filled.py` (0.122s)
- `scripts/rapidity_first_atsp_oracle.py` (0.121s)
- `scripts/rapidity_polar_probe.py` (0.046s)
- `scripts/rationalize_active_lie_closure_data.py` (0.08s)
- `scripts/run_bulk_equivalent.py` (0.013s)
- `scripts/run_tsplib_atsp_named.py` (0.046s)
- `scripts/self_clock_rapidity_update.py` (0.012s)
- `scripts/test_bonded_horizon_casimir_float.py` (0.089s)
- `scripts/test_euclidean_factor_peel_enhancements.py` (0.068s)
- `scripts/test_factor_from_curvature.py` (0.076s)
- `scripts/test_factor_grok.py` (0.096s)
- `scripts/test_fator_grok.py` (18.135s)
- `scripts/test_fluid_f2_chart_alignment.py` (0.047s)
- `scripts/test_fragment_aware_bonded_horizon.py` (0.054s)
- `scripts/test_hqiv_geometric_3sat_demo.py` (0.082s)
- `scripts/test_hqiv_geometric_3sat_heuristics.py` (0.163s)
- `scripts/test_hqiv_geometric_3sat_optional_omega_trial_div.py` (0.07s)
- `scripts/test_hqiv_satcomp_benchmark.py` (0.091s)
- `scripts/test_integer_lattice_shell_count8.py` (0.364s)
- `scripts/test_nuclear_torus_casimir_float.py` (0.06s)
- `scripts/test_octonion_sphere_construction.py` (0.012s)
- `scripts/test_qm_finite_tensor_toy.py` (0.139s)
- `scripts/test_qm_general_finite_core.py` (0.161s)
- `scripts/test_qm_hubbard_dimer.py` (0.184s)
- `scripts/test_qm_hubbard_dimer_half_filled.py` (0.161s)
- `scripts/universal_dynamics_equations.py` (0.045s)

## Failed or timeout

- `scripts/benchmark_atsp_dual_oracles.py` exit=-124 (30.033s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/benchmark_edge_topology_calibration.py` exit=-124 (30.031s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/benchmark_geometric_factorization_solver.py` exit=-124 (30.064s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/benchmark_omaxwell_torus_ode.py` exit=-124 (30.032s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/benchmark_rapidity_first_atsp.py` exit=-124 (30.032s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/generate_symbolic_lie_closure_certificate.py` exit=-124 (30.027s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/scan_factor_grok_semiprimes.py` exit=-124 (30.032s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/test_mgf3_semiprimes.py` exit=-124 (30.038s)
  ```
  TIMEOUT after 30s
  ```
- `scripts/bench_factor_grok_semiprimes.py` exit=1 (0.153s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/bench_factor_grok_semiprimes.py", line 84, in <module>
      main()
      ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/bench_factor_grok_semiprimes.py", line 65, in main
      print(f"_dynamic_p_max(10**6) = {mod._dynamic_p_max(10**6)}")
                                       ^^^^^^^^^^^^^^^^^^
  AttributeError: module 'factor_gr
  ```
- `scripts/benchmark_euclidean_factor_peel_u64.py` exit=1 (0.082s)
  ```
  missing corpus file: data/semiprimes_u64.json
  
  ```
- `scripts/benchmark_hqiv_rapidity_sat_solver.py` exit=1 (0.106s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/benchmark_hqiv_rapidity_sat_solver.py", line 242, in <module>
      raise SystemExit(main())
                       ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/benchmark_hqiv_rapidity_sat_solver.py", line 147, in main
      bench_pysat(cw, args.pysat_solver)
      ~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^^^^
    File "/home/jr/Repos/HQIV_
  ```
- `scripts/check_fano_mass_coherence.py` exit=1 (0.11s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/check_fano_mass_coherence.py", line 553, in <module>
      main()
      ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/check_fano_mass_coherence.py", line 538, in main
      rep = run_checks(
          lapse_lambda=args.lapse_lambda,
      ...<2 lines>...
          t_coord=args.lapse_t,
      )
    File "/home/jr/Repos/HQIV_LEAN/scripts/
  ```
- `scripts/compare_hubbard_dimer_half_filled_scan.py` exit=1 (0.027s)
  ```
  Missing data/hubbard_dimer_half_filled_witnesses.json. Run: lake env lean --run scripts/export_hubbard_dimer_half_filled_witnesses.lean
  
  ```
- `scripts/compare_hubbard_dimer_scan.py` exit=1 (0.026s)
  ```
  Missing data/hubbard_dimer_witnesses.json. Run: lake env lean --run scripts/export_hubbard_dimer_witnesses.lean
  
  ```
- `scripts/compare_quantum_chem_witnesses.py` exit=1 (0.025s)
  ```
  Missing data/quantum_chem_witnesses.json. Run: lake env lean --run scripts/export_quantum_chem_witnesses.lean
  
  ```
- `scripts/competition_solver.py` exit=1 (0.052s)
  ```
  missing DIMACS input path (positional or --dimacs)
  
  ```
- `scripts/docgen_metadata.py` exit=1 (0.094s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/docgen_metadata.py", line 68, in <module>
      main()
      ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/docgen_metadata.py", line 40, in main
      with open(root / "lakefile.toml", "rb") as f:
           ~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  FileNotFoundError: [Errno 2] No such file or directory: 'lakefile.toml'
  
  ```
- `scripts/frame_well_curvature_batch.py` exit=1 (3.127s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/frame_well_curvature_batch.py", line 202, in <module>
      main()
      ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/frame_well_curvature_batch.py", line 162, in main
      with open(out_csv, "w", newline="", encoding="utf-8") as f:
           ~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  FileNotFoundError: [Errno 2] No suc
  ```
- `scripts/generalized_geometric_oracle.py` exit=1 (0.1s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/generalized_geometric_oracle.py", line 1223, in <module>
      main()
      ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/generalized_geometric_oracle.py", line 1182, in main
      f"candidates_generated={payload['candidates_generated']} search_mode={payload['search_mode']}"
                              ~~~~~~~^^^^^^^^^^^^^^^^^
  ```
- `scripts/propagate_hqiv_uncertainties.py` exit=1 (0.03s)
  ```
  Missing witness JSON. Run both Lean exporters first:
    lake env lean --run scripts/export_witnesses.lean
    lake env lean --run scripts/export_quantum_chem_witnesses.lean
  
  ```
- `scripts/test_mgf4_semiprimes.py` exit=1 (0.324s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/test_mgf4_semiprimes.py", line 113, in <module>
      main()
      ~~~~^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/test_mgf4_semiprimes.py", line 77, in main
      mgf4 = load_factorizer()
    File "/home/jr/Repos/HQIV_LEAN/scripts/test_mgf4_semiprimes.py", line 27, in load_factorizer
      spec.loader.exec_module(mod)
      ~~~~~~~~~
  ```
- `scripts/test_zk_export_witness.py` exit=1 (0.109s)
  ```
  Traceback (most recent call last):
    File "/home/jr/Repos/HQIV_LEAN/scripts/test_zk_export_witness.py", line 15, in <module>
      import export_witness as ez  # noqa: E402
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^
    File "/home/jr/Repos/HQIV_LEAN/scripts/zk_factor_steps/export_witness.py", line 44, in <module>
      DEFAULT_MAX_STEPS = ffc.MAX_PRIME_SIEVE_BOUND
                          ^^^^^^^^^^^^^^^^^^^^^^^^^
  ```
- `scripts/bristol_solver.py` exit=2 (0.063s)
  ```
  usage: bristol_solver.py [-h] [--target TARGET] [--max-steps MAX_STEPS]
                           circuit_file
  bristol_solver.py: error: the following arguments are required: circuit_file
  
  ```
- `scripts/bristol_to_dimacs.py` exit=2 (0.066s)
  ```
  usage: bristol_to_dimacs.py [-h] [-o OUTPUT] [--fix-output-hex FIX_OUTPUT_HEX]
                              [--fix-output-md5 FIX_OUTPUT_MD5]
                              [--n-output-bits N_OUTPUT_BITS]
                              bristol
  bristol_to_dimacs.py: error: the following arguments are required: bristol
  
  ```
- `scripts/char_count_no_comments.py` exit=2 (0.045s)
  ```
  usage: char_count_no_comments.py [-h] [--json] paths [paths ...]
  char_count_no_comments.py: error: the following arguments are required: paths
  
  ```
- `scripts/euclidean_factor_peel.py` exit=2 (0.065s)
  ```
  usage: euclidean_factor_peel.py [-h] [--no-fermat-lehman]
                                  [--fermat-max-steps FERMAT_MAX_STEPS]
                                  [--lehman-k-max LEHMAN_K_MAX]
                                  [--no-residue-gate]
                                  [--residue-gate-prime-limit RESIDUE_GATE_PRIME_LIMIT]
                                  [--max-probes-per-step MAX_PROBES_PER_ST
  ```
- `scripts/factor_from_curvature.py` exit=2 (0.053s)
  ```
  usage: factor_from_curvature.py [-h] [--curvature-rational CURVATURE_RATIONAL]
                                  [--omega-imprint OMEGA_IMPRINT]
                                  [--omega-mode {rational,ramanujan_arity}]
                                  [--json] [--phi PHI] [--t T] [--window WINDOW]
                                  [--mode {mask,prime_gradient}] [--arity ARITY]
                           
  ```
- `scripts/factor_grok_probe.py` exit=2 (0.04s)
  ```
  usage: factor_grok_probe.py [-h] [--odd-sieve] [--max-trial-ref MAX_TRIAL_REF]
                              N
  factor_grok_probe.py: error: the following arguments are required: N
  
  ```
- `scripts/factor_old.py` exit=2 (0.046s)
  ```
  usage: factor_old.py [-h] [--curvature-rational CURVATURE_RATIONAL]
                       [--omega-imprint OMEGA_IMPRINT]
                       [--omega-mode {rational,ramanujan_arity}] [--json]
                       [--phi PHI] [--t T] [--window WINDOW]
                       [--mode {mask,prime_gradient}] [--arity ARITY]
                       [--max-depth MAX_DEPTH] [--visualize-text]
                  
  ```
- `scripts/factor_peel_intercept.py` exit=2 (0.108s)
  ```
  usage: factor_peel_intercept.py [-h] [--max-arity K] [--wrap-k K] [--json]
                                  [--debug]
                                  nums [nums ...]
  factor_peel_intercept.py: error: the following arguments are required: nums
  
  ```
- `scripts/fano_slice_fft_probe.py` exit=2 (0.044s)
  ```
  usage: fano_slice_fft_probe.py [-h] --input INPUT [--output OUTPUT]
                                 [--max-decay-slope MAX_DECAY_SLOPE]
                                 [--min-points MIN_POINTS]
  fano_slice_fft_probe.py: error: the following arguments are required: --input
  
  ```
- `scripts/frame_well_curvature_plot.py` exit=2 (0.039s)
  ```
  usage: frame_well_curvature_plot.py [-h] --input-json INPUT_JSON
                                      --output-png OUTPUT_PNG
                                      [--show-no-rindler | --no-show-no-rindler]
                                      [--mark-minima | --no-mark-minima]
  frame_well_curvature_plot.py: error: the following arguments are required: --input-json, --output-png
  
  ```
- `scripts/gate_map_to_quantum.py` exit=2 (0.043s)
  ```
  usage: gate_map_to_quantum.py [-h] [--qasm-out QASM_OUT] [--print-circuit]
                                input
  gate_map_to_quantum.py: error: the following arguments are required: input
  
  ```
- `scripts/generate_phase_transition_3cnf.py` exit=2 (0.039s)
  ```
  usage: generate_phase_transition_3cnf.py [-h] --out-dir OUT_DIR
                                           [--count COUNT] [--start-id START_ID]
  generate_phase_transition_3cnf.py: error: the following arguments are required: --out-dir
  
  ```
- `scripts/geometric_factorization_solver.py` exit=2 (0.045s)
  ```
  usage: geometric_factorization_solver.py [-h] [--max-steps MAX_STEPS]
                                           [--max-seconds MAX_SECONDS]
                                           [--search-mode {standard,symmetric-tip,auto}]
                                           [--q-span-mode {single-arc,double-pole-reflector}]
                                           [--q-list-mode {shoreline,gate-frontier}]
  ```
- `scripts/hqiv_geometric_ksat_benchmark.py` exit=2 (0.103s)
  ```
  usage: hqiv_geometric_ksat_benchmark.py [-h] [--suite] [--cnf CNF] [--json]
  hqiv_geometric_ksat_benchmark.py: error: need --suite and/or --cnf
  
  ```
- `scripts/hqiv_osh_integrated (1).py` exit=2 (0.062s)
  ```
  usage: hqiv_osh_integrated (1).py [-h] [--max-steps MAX_STEPS] [--json] n
  hqiv_osh_integrated (1).py: error: the following arguments are required: n
  
  ```
- `scripts/hqiv_osh_integrated.py` exit=2 (0.062s)
  ```
  usage: hqiv_osh_integrated.py [-h] [--max-steps MAX_STEPS] [--json] n
  hqiv_osh_integrated.py: error: the following arguments are required: n
  
  ```
- `scripts/hqiv_osh_integrated_driver.py` exit=2 (0.071s)
  ```
  usage: hqiv_osh_integrated_driver.py [-h] [--max-steps MAX_STEPS] [--L L]
                                       [--reference-m REFERENCE_M] [--json]
                                       n
  hqiv_osh_integrated_driver.py: error: the following arguments are required: n
  
  ```
- `scripts/hqiv_osh_sparse_factorization.py` exit=2 (0.045s)
  ```
  usage: hqiv_osh_sparse_factorization.py [-h] [--L L] [--max-steps MAX_STEPS]
                                          [--max-seconds MAX_SECONDS]
                                          [--reference-m REFERENCE_M]
                                          [--prime-factorization]
                                          [--factor-max-seconds-per-node FACTOR_MAX_SECONDS_PER_NODE]
                         
  ```
- `scripts/hqiv_rapidity_frontier_sat_solver.py` exit=2 (0.049s)
  ```
  usage: hqiv_rapidity_frontier_sat_solver.py [-h] [--self-test] [--cnf CNF]
                                              [--backend {dpll,pysat}] [--json]
                                              [--compare-backends]
                                              [--max-nodes N]
                                              [--dpll-var-order {index,reverse_index,clause_frequency,jeroslow_wang,atsp_ear
  ```
- `scripts/hqiv_reversible_gate_runner.py` exit=2 (0.05s)
  ```
  usage: hqiv_reversible_gate_runner.py [-h] [--initial INITIAL]
                                        [--inputs INPUTS] [--check]
                                        input
  hqiv_reversible_gate_runner.py: error: the following arguments are required: input
  
  ```
- `scripts/hqiv_satcomp_benchmark.py` exit=2 (0.084s)
  ```
  usage: hqiv_satcomp_benchmark.py [-h] [--cnf CNF] [--dir DIR] [--glob GLOB]
                                   [--recursive] [--skip-non-3cnf]
                                   [--max-files N] [--bruteforce-max-vars N]
                                   [--json]
  hqiv_satcomp_benchmark.py: error: need --cnf and/or --dir
  
  ```
- `scripts/monolithic_geometric_factorizer (1).py` exit=2 (0.06s)
  ```
  usage: monolithic_geometric_factorizer (1).py [-h] n
  monolithic_geometric_factorizer (1).py: error: the following arguments are required: n
  
  ```
- `scripts/monolithic_geometric_factorizer (2).py` exit=2 (0.061s)
  ```
  usage: monolithic_geometric_factorizer (2).py [-h] n
  monolithic_geometric_factorizer (2).py: error: the following arguments are required: n
  
  ```
- `scripts/monolithic_geometric_factorizer.py` exit=2 (0.055s)
  ```
  usage: monolithic_geometric_factorizer.py [-h] [--progress-every N] n
  monolithic_geometric_factorizer.py: error: the following arguments are required: n
  
  ```
- `scripts/monolithic_geometric_factorizer3.py` exit=2 (0.059s)
  ```
  usage: monolithic_geometric_factorizer3.py [-h] [--max-steps N] n
  monolithic_geometric_factorizer3.py: error: the following arguments are required: n
  
  ```
- `scripts/osh_gate_factorization.py` exit=2 (0.042s)
  ```
  usage: osh_gate_factorization.py [-h] [--max-steps MAX_STEPS]
                                   [--max-seconds MAX_SECONDS]
                                   [--prime-factorization]
                                   [--factor-max-seconds-per-node FACTOR_MAX_SECONDS_PER_NODE]
                                   [--json]
                                   n
  osh_gate_factorization.py: error: the following ar
  ```
- `scripts/phase_channel_dynamic_precision (1).py` exit=2 (0.058s)
  ```
  usage: phase_channel_dynamic_precision (1).py [-h] [--max-steps MAX_STEPS]
                                                [--json]
                                                n
  phase_channel_dynamic_precision (1).py: error: the following arguments are required: n
  
  ```
- `scripts/phase_channel_dynamic_precision.py` exit=2 (0.063s)
  ```
  usage: phase_channel_dynamic_precision.py [-h] [--max-steps MAX_STEPS]
                                            [--json]
                                            n
  phase_channel_dynamic_precision.py: error: the following arguments are required: n
  
  ```
- `scripts/run_fano_to_peak_pipeline.py` exit=2 (0.046s)
  ```
  usage: run_fano_to_peak_pipeline.py [-h] --input INPUT
                                      [--fft-report FFT_REPORT]
                                      [--peak-input PEAK_INPUT]
                                      [--peak-witness PEAK_WITNESS]
                                      [--max-decay-slope MAX_DECAY_SLOPE]
                                      [--min-points MIN_POINTS] [--N N]
               
  ```
- `scripts/search_slice_defect_peak.py` exit=2 (0.045s)
  ```
  usage: search_slice_defect_peak.py [-h] --input INPUT [--output OUTPUT]
  search_slice_defect_peak.py: error: the following arguments are required: --input
  
  ```
- `scripts/shor_angle_period_factorization.py` exit=2 (0.042s)
  ```
  usage: shor_angle_period_factorization.py [-h] [--max-steps MAX_STEPS]
                                            [--max-seconds MAX_SECONDS]
                                            [--prime-factorization]
                                            [--factor-max-seconds-per-node FACTOR_MAX_SECONDS_PER_NODE]
                                            [--json]
                                          
  ```