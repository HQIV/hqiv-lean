# Archived Compton-Theta Detuning Experiment

This note archives the short-lived experiment that injected a Compton phase
participation factor into relaxed detuning readouts.

## Archived idea

- Define `eta_theta = (omega_shell * t_shared) / (pi/2)`.
- Modify relaxed detuning as:
  - `D_relaxed_theta(m) = D_relaxed(m) * (1 + eta_theta(m))`.
- Use detuning-sourced lapse to choose shared time:
  - `lapse_fraction = 1 / (rindler_den(referenceM) + delta_global)`.

## Why archived

- In diagnostics, this globally worsened key mass readouts (notably charm from
  top/charm relaxed ratio), even though it improved some Koide-side values.
- The active pipeline was reverted to the pre-experiment relaxed detuning path.

## Files touched during experiment

- `Hqiv/Physics/ModalFrequencyHorizon.lean`
- `scripts/cubic_phase_relax_probe.py`

The active code now excludes this theta-aware detuning coupling.
