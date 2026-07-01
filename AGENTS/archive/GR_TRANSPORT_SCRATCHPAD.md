# GR Transport Scratchpad

Target manuscript: `paper/octonion_lightcone_to_oshoracle.tex`

## What the current Lean corpus can now honestly say

The strongest GR-shaped statement currently supported is not "Einstein equations from the full O-Maxwell sector" in a constructive Schuller sense. What *is* now available is a theorem-backed bridge showing that the same doubled observer-time mode budget used in the continuum cluster/transport witness can also be used as a valid homogeneous HQVM gravity input.

Lean hook:

- `Hqiv.Physics.timeAngleBudgetScaleN`
- `Hqiv.Physics.timeAngleBudgetTransportN`
- `Hqiv.Physics.timeAngleBudgetScale_feeds_HQVM_GR`
- `Hqiv.Physics.timeAngleBudgetTransport_and_HQVM_GR`

In words:

1. The doubled observer-time budget `accessibleModeBudgetUpToTimeAngle (4 (n+1))` collapses exactly to the shell budget `accessibleModeBudgetUpToShell (2n+1)`.
2. That same scale drives the photon transport factor as an exponential attenuation law.
3. The same scale can be fed into homogeneous HQVM gravity, where it simultaneously satisfies:
   - the lapse identity `N = 1 + Φ + timeAngle φ t`,
   - the identification `H_of_phi φ = φ`,
   - the varying-coupling law `G_eff(φ) = φ^alpha`,
   - and the gravitational action equivalence `S_HQVM_grav = 0 <-> HQVM_Friedmann_eq`.

This is a meaningful "GR-shaped" bridge because the transport scale is no longer just a QFT-side decay parameter; it becomes a legitimate homogeneous gravitational field input in the current formal stack.

## Rapidity-normalization clarification

The next theorem rung should **not** be phrased as "exact GR recovered from the null lattice". The cleaner statement is:

- the discrete null lattice remains the invariant bookkeeping substrate;
- relativistic observers skew how that substrate is read back;
- `rapidity` is the observer-side **normalization mechanism** for that skew;
- the IR gravity sector is therefore **GR-shaped**, while the UV completion stays on the discrete ladder.
- there is **no** claim here that a physically primary sub-Planck smooth continuum underlies the lattice; the continuum formulas are IR/readout language above the null-lattice cutoff.

Lean now has a perturbation-side version of that claim:

- `Hqiv.Physics.rapidityNormalizedShellPhiIncrement`
- `Hqiv.Physics.linearizedLapse_from_shell_rapidityNormalized`
- `Hqiv.Physics.HQVM_lapse_increment_shell_rapidityNormalized`
- `Hqiv.Physics.HQVM_g_tt_increment_shell_rapidityNormalized`
- `Hqiv.Physics.HQVM_g_tt_increment_shell_rapidityNormalized_phiChannel`
- `Hqiv.Physics.HQVM_spatial_coeff_increment_zero_of_pure_phi_channel`
- `Hqiv.Physics.HQVM_metric_shell_rapidityNormalized_phiChannel_timelikeOnly`
- `Hqiv.Physics.rapidityNormalizedPotentialIncrement`
- `Hqiv.Physics.HQVM_spatial_coeff_increment_rapidityNormalizedPotential`
- `Hqiv.Physics.HQVM_metric_shell_rapidityNormalized_withPotentialChannel`

These say that a shell-derived `δφ` from `phi_of_T` is weighted by the same doubled observer-time transport law used in the light-cone/QFT bridge, and then enters the exact homogeneous lapse increment with the same bilinear remainder as the base observer-centric lapse algebra. So rapidity is being used as a **normalizer of observer skew**, not as a separate ontic field.

The geometry-facing upgrade is now explicit: because `HQVM_g_tt = -N^2`, the observer-skew-normalized lapse increment induces an exact timelike metric-coefficient increment with a linearized part `-2 N δN` and quadratic remainder `-δN^2`. This is a particularly clean place to stop before over-claiming full curvature dynamics.

The matching spatial statement is now also explicit: at this theorem rung, pure shell/`φ`
rapidity normalization does **not** alter `HQVM_spatial_coeff`, because that coefficient depends
only on `(a, Φ)`. So the present bridge is best read as a **timelike-first** geometry readout,
not yet a full metric perturbation package.

The next minimal extension is now also formalized: if one separately supplies a Newtonian-potential
increment `δΦ`, the same observer-budget transport law can normalize that channel as well. This gives
a theorem-backed spatial movement law with `δa = 0`, without pretending that shell/`φ` response alone
already determines the whole spatial metric.

## Limit language worth preserving

Suggested phrasing:

> The present continuum expressions should be read as effective observer-side geometry above the null-lattice cutoff, not as evidence that HQIV posits a physically fundamental sub-Planck smooth manifold. The UV object in this program is the discrete null ladder; the continuum metric/lapse language is the IR normalization readout seen by relativistic observers.

And, when needed:

> In particular, these theorems do not claim exact textbook GR at arbitrarily short distances. They only show that the rapidity-normalized null-lattice bookkeeping has a clean large-scale landing in the HQVM lapse and timelike metric coefficient.

## Suggested paper wording

### Candidate replacement/addition near the current gravitational-action paragraph

Insert after the paragraph ending with `The formal total action action_total combines S_O with S_grav so that φ and α link gauge and cosmology in one variational stack.`

Proposed text:

> The present library now goes one step beyond stating that the same symbols occur in both sectors. In `LightConeMaxwellQFTBridge`, the doubled observer-time budget
> \[
>   \mathcal{B}_t(n) := \mathrm{accessibleModeBudgetUpToTimeAngle}(4(n+1))
> \]
> is proved to agree exactly with the shell budget
> \[
>   \mathcal{B}_t(n) = \mathrm{accessibleModeBudgetUpToShell}(2n+1).
> \]
> The same quantity also drives the photon transport witness through the exact attenuation law
> \[
>   T_\gamma(n;\kappa_\beta)=\exp\!\left(-\frac{\mathcal{B}_t(n)}{\kappa_\beta}\right).
> \]
> Crucially, this is not only a continuum-QFT bookkeeping scale: the theorem
> `timeAngleBudgetScale_feeds_HQVM_GR` shows that the same `\mathcal{B}_t(n)` can be inserted as the homogeneous HQVM field input, so that the lapse law, the varying coupling `G_{\mathrm{eff}}(\phi)=\phi^\alpha`, and the equivalence
> \[
>   S_{\mathrm{HQVM,grav}}(\phi,\rho_m,\rho_r)=0
>   \;\Longleftrightarrow\;
>   (13/5)\phi^2 = 8\pi \phi^\alpha (\rho_m+\rho_r)
> \]
> all hold at that observer-time budget scale. In that precise Lean-backed sense, the transport ladder now feeds a homogeneous GR-shaped sector rather than merely sitting beside it.

### Candidate tightening of the "honest status" language

Proposed text:

> This remains a homogeneous/constraint-level gravity statement, not yet a full derivation of Einstein dynamics from the octonionic gauge sector. The formal advance is narrower and cleaner: a theorem-backed light-cone transport scale now lands in the HQVM lapse and Friedmann slots without adding new fitted structure, and the perturbation layer now treats rapidity as the observer-side skew normalization of shell-induced lapse response rather than as a claim of exact classical GR recovery.

## Suggested theorem-summary sentence for the manuscript

> The new bridge theorem packages a single observer-time budget as both a redshift/decoherence transport scale and a homogeneous HQVM gravity input, thereby tightening the route from null-lattice bookkeeping to a GR-shaped constraint law.

## What still remains open

- A genuinely constructive Schuller-style theorem deriving gravitational field equations from matter compatibility, rather than only matching the homogeneous HQVM slot.
- A non-homogeneous theorem connecting the transport budget or directional kernel to perturbative HQVM geometry beyond the lapse identities already proved in `HQVMPerturbations`.
- A stronger curvature statement tying the transport budget directly to `g_tt`, perturbative curvature, or a redshift-forced geometric rigidity claim.
