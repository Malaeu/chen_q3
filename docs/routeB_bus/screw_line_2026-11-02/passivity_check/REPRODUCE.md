# Reproduction and numerical scope

DIAGNOSTIC_NEVER_A_PROOF. Run from this directory.

Dependencies: Python with mpmath; NumPy/SciPy for aligned float controls;
Matplotlib for the two optional plots. Native solves use a C++17 compiler
and GMP development headers/libraries. No network, paid service or new zero
search is needed once the pinned repository inputs are present.

## Restore original evidence

    python materialize_inputs.py --repo /path/to/repo --out ./inputs
    python restore_native.py --out ./native_cells

Both restorers verify SHA-256 and refuse conflicting existing files.
The original zero lists remain numerical, not interval-certified.

## Recompute native algebraic inverse forms

    c++ -O3 -std=c++17 native.cpp -lgmpxx -lgmp -o native
    SCREW_FORCE=1 SCREW_WORKERS=4 python native_scan.py ./inputs

Defaults:220 source decimal digits, eight-panel GL256,768-bit GMP.
The code creates the high-precision Legendre rule by Newton recurrence,
builds the complete source matrix, constructs the full native rowspace by
twice-reorthogonalized MGS, and uses LDL solves for all four queries.
No rank cutoff, pseudoinverse or float eigenvalue sign is substituted.
Existing result files are reused; use a fresh output checkout to force
an independent full recomputation. SCREW_EXE can select the compiled binary.

Precision controls:

    SCREW_DPS=300 SCREW_ORDER=320 SCREW_BITS=1024 SCREW_WORKERS=2 python native_scan.py ./inputs 51 52 53 54 55 120 240
    python validate_native_python.py ./inputs

The independent Python path uses its own source quadrature, Householder
rowspace and LU solves on20/55, rather than the GMP MGS/LDL path. It also
checks the constant derivative-measure pullback from the screw source.

Coordinate stresses, preserving reflected pairs, do NOT claim new zeros:

    SCREW_NODE_PERTURB=1e-77 SCREW_SUFFIX=_nodeplus SCREW_WORKERS=2 python native_scan.py ./inputs 120 240
    SCREW_NODE_PERTURB=-1e-77 SCREW_SUFFIX=_nodeminus SCREW_WORKERS=2 python native_scan.py ./inputs 120 240

These deterministic stresses apply to DH coordinates only; accompanying
zeta records are unchanged controls. They are not exhaustive error boxes.

## Recompute genuine curve geometries

    python curve.py zeta
    python curve.py dh
    python curve_refined.py dh
    OPENBLAS_NUM_THREADS=1 python aligned_sections.py zeta
    OPENBLAS_NUM_THREADS=1 python aligned_sections.py dh
    OPENBLAS_NUM_THREADS=1 python aligned_mesh.py zeta
    OPENBLAS_NUM_THREADS=1 python aligned_mesh.py dh
    python source_sections.py
    python impedance_control.py ./inputs > IMPEDANCE_CONTROL.json

The uniform source/LDL calculations use85 dps; the480-node DH control keeps
the SAME target as the240-node run. Aligned controls use float64 with
GL64/128 comparisons and separate MP source spots. Their runtime matrices
are local caches only; the public JSON/CSV contains all tested updates.
No finite-end canonical impedance is asserted by impedance_control.py:
it evaluates the actual global completed logarithmic derivative.

## Aggregate and plot

    python summarize.py
    python geometry_summary.py
    OPENBLAS_NUM_THREADS=1 python plot_results.py

summarize.py verifies case counts, source stresses, precision controls,
nonnegative reciprocal squares and creates the lossless numeric archive.
The committed archive is split into fixed-size parts to keep uploads bounded;
NATIVE_ARCHIVE.json records their exact hashes. Repacking on another Python/
zlib platform can change compressed bytes; restored per-cell hashes identify
the actual evidence. Native numeric results are not interval certificates.

The compiled executable, large runtime source streams, private
matrices, caches and materialized inputs are intentionally not committed.
All committed artifacts live under screw_line_2026-11-02/ only.

## Compare the preserved canonical packet

Restore its data first with `python ../restore_data.py`, then run:

    python compare_canonical.py --canonical-root ..

This independently checks442 inertias,1768 endpoint/Fourier kernels and1768
endpoint cross-kernels against the unchanged canonical CSV member hashes.
The canonical interior-cosine gauge is additional and is not recomputed here.

## Exact arithmetic support labels

`DH_EXACT_COEFFICIENTS.json` records formal Dirichlet-log polynomials, including
exact zeros; SymPy is required only to regenerate it with `python exact_atoms.py`.
`python exact_label_records.py` annotates restored historical cells before
aggregation, preserving original numeric birth decimals. Native recomputation
performs that annotation automatically. Numeric matrix input streams retain
the original unthresholded floating recurrence. See `EXACT_SUPPORT.md`.

    python verify_addendum.py

This verifies the committed checksums, split archive,464 per-cell records,
442 base cases, geometry controls and independent overlap summary.
