# C conditioning: source matrix supplier

DIAGNOSTIC_NEVER_A_PROOF. All315 literal even cells for m16..120 are supplied: ζ,DH,planted world, N=m, lengthL=logm. No eigenvalue clipping, PSD repair or replacement by a zero-value Gram matrix was used.

Files `cell_{world}_m{m}.npz` contain `A`, sorted floating `eigenvalues`, `L`, `m`, `numeric_radius`. Planted files also contain the complex physical row `plant_E`. Companion JSON carries source hashes, basis, cached MP eigenvalues as decimal strings, provenance and float-sign classification. The saved floating spectrum always belongs to the saved floating matrix; cached MP eigenvalues are kept separately.

The source is `suzuki_W_2026-11-02/W/prototype.py::build`, with its DH coefficient array replaced by `dh_matrix.py::coeffs(120)` evaluated once at80 decimal digits and then converted to float. This avoids the unstable binary64 Dirichlet recurrence. Both archimedean completions and the ζ pole are retained. Existing MP source matrices are reused when available, with their source paths and hashes. Cached MP spectra are available in69 cells.

The planted update is exactly the requested numerical construction

`A_plant=A_zeta+4[Re E(w) Re E(w)^T−Im E(w) Im E(w)^T]`,

where `w=2π/log2+i/4` and `E` is the raw physical Fourier row from `capacity.py::Erow`. There is **no extra√2** in E. The basis is `e0=1/√L`, `en=√(2/L)(−1)^n cos(2πnx/L)`, extended by zero outside the window.

Each companion records a conservative **diagnostic, non-interval** radius

`numeric_radius=128*eps64*(m+1)*max(1,||A||_F)`.

Every float eigenvalue whose magnitude is below that radius must be treated as UNRESOLVED. This radius is a numerical guard, not a proved enclosure or a validated error bound for all cells.

Twenty selected comparisons at m16,24,40,55,65,70,75,80,85,120, both ζ/DH, compare192-point source quadrature against the saved96-point or rounded-MP source matrix. All Frobenius differences fall below the guard; the largest discrepancy/radius is0.061258. Available MP source comparisons at other cells also pass the guard during assembly. Raw results are in `quadrature_validation.json` and per-cell JSON. Full construction completed in3.24s with single-thread BLAS.

All105 ζ floating ground signs are UNRESOLVED. The planted world is strongly negative throughout the requested range, from≈−0.21685 at m16 to≈−1.25320 at m120. DH's first **float-guard-resolved** negative here is m55,≈−0.66392. This is **not** its mathematical onset: cached MP spectra already contain negative m51≈−1.32686e−47, m52≈−2.81929e−19, m53≈−1.18369e−41, m54≈−3.55294e−11; those tiny signs are correctly unresolved in the float layer. Consult the existing separate DH certificate for certified onset claims.

No additional eigenproblem is required for tiny ζ/DH cells already covered by cached MP spectra. A consumer must not silently combine a floating eigenvector/compression with high-precision scalar eigenvalues as though the whole calculation were high precision. Near-threshold projector/Schur computations require their own residual and precision controls.
