#!/usr/bin/env python3
"""
Meson flavor content — re-exports the global `TuftExcitationChannel` grid.

All masses use `hqiv_tuft_global_hadron_readout.tuft_excited_mass_global_at_xi_mev`.
"""

from __future__ import annotations

from hqiv_tuft_global_hadron_readout import (
    MESON_LIGHT_EXCITATION_WEIGHT,
    MESON_EXCITED_CHANNELS,
    TuftExcitationChannel,
    tuft_content_excitation_weight,
)

# Back-compat aliases
MESON_INTRINSIC_SCALE = 4.0 / 9.0
MESON_VALENCE_CHANNEL_FRACTION = 2.0 / 3.0
TUFT_MESON_LIGHT_EXCITATION_WEIGHT = MESON_LIGHT_EXCITATION_WEIGHT
tuft_meson_flavor_excitation_weight = tuft_content_excitation_weight  # channel arg
MesonExcitedSlot = TuftExcitationChannel
MESON_EXCITED_GRID = MESON_EXCITED_CHANNELS


def meson_flavor_weight(n_strange: int) -> float:
    """Back-compat: weight from strangeness count only."""
    return tuft_content_excitation_weight(TuftExcitationChannel.meson(0, 0, n_strange))
