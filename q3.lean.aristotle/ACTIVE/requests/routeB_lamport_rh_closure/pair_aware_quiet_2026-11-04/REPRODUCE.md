# Reproduction

Use the pinned repository at cdb84497; install numpy, scipy, mpmath, gmpy2,
GMP/MPFR and a C compiler. Set PAIR_BASE and PAIR_SEPARATOR_BASE to
`docs/routeB_bus/stitch_conditioning_2026-11-03/zero_separator` in the checkout,
and PAIR_LOCAL, PAIR_CONTROL_LOCAL and PAIR_ENVELOPE_LOCAL to scratch paths.
Restore the three source archives using `unpack_scan.py`,
`extension_121_300/unpack_data.py` and `spike_trend_310_600/unpack_data.py`.

The compact delivered data can be checked without numerical regeneration:

    python verify.py
    python restore_controls.py

To repeat the bounded calculation, run baseline_replay.py and verify all seven
replays before any dependent calculation. Then run common.py, restrict.py,
adaptive.py and finalize.py. control_delta.py and control_delta_validate.py
regenerate the missing control residuals; envelope_complete.py uses its frozen
requests CSV. Rerun finalize.py, overlay.py, clusters.py and plot_results.py.
hermite_pilots.py, hermite_batch.py and hermite_coverage.py reproduce the
bounded coordinate checks. Matrices and frames are generated only in scratch;
source arrays are not in this artifact. Do not infer full-grid numerical
Hermite coverage from the finite pilot checks.

The source settings are fixed at400 bits, GL192 for the middle packet and
GL256 for the high packet, eight panels and 768-bit frames. Paired GL256
caches for plant248/300 are recorded as such. No interval certification or
higher-precision chase is implied.
