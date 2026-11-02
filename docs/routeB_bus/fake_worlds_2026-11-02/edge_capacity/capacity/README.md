# Saved-complement endpoint capacity reproduction

DIAGNOSTIC_NEVER_A_PROOF. No route-state or RH exports.

`cells.json` names all eight zeta cells and thirteen DH controls. Restore the
archived lower cells under `INPUT_ROOT/matched_cells/`; reconstruct the nine
high A/E/U/Q caches using the accompanying shared source builder under
`INPUT_ROOT/dense/`. The source pins and exact input hashes are maintained by
the parent package INPUTS manifest. No full-carrier eigenproblem is required.

From this directory, with mpmath and NumPy installed:

```bash
python3 capacity.py --manifest cells.json --input-root INPUT_ROOT --output . --dps 80 \
  --validate dense/zeta_m240_q139_rebuild.json
python3 report.py
```

`EDGE_CAPACITY_INPUT_ROOT` can replace `--input-root`. Relative manifest paths
default to the manifest's own directory. Output defaults to the script's
directory; there are no required machine-specific absolute paths.

The physical endpoint is `f(log(m)/2)` with modal row
`d_b=(1,sqrt(2),...)/sqrt(log(m))`. The inverse quadratic quantity is
`cap=1/(t^T G^-1 t)`, `t=U^T d_b`, `G=U^T A U`. The LU solve is performed at
the stated precision and retains a relative solve residual. It is a positive
affine variational capacity only if the reduced G is positive definite.
An indefinite DH G is reported as an algebraic inverse quantity; its sign
does not establish coercivity.

The endpoint-zero restriction uses a stable Householder nullbasis for
`t^perp`. Its minimum and the reduced G spectrum are computed at high
precision. Lower cells retain their already-saved reduced G spectra; high
cells compute those reduced spectra from the reconstructed caches. A separate
float replay of lambda2 is flagged as unresolved when below its stated
numerical scale, rather than used to replace a tiny high-precision value.

All capacity, endpoint-ratio, scaled-R and endpoint-zero minimum values for
the highest zeta cell are rerun at110 decimal digits. Comparisons and the
explicit1e-40 relative validation criterion are in `precision_validation.json`.
The result remains floating diagnostics, not an interval certificate.

Outputs: `capacity.json`, `capacity.csv`, per-cell JSONs, `capacity_scored.json`,
`precision_validation.json`, and `RESULT.md`. `report.py` scores the exact
pre-registered P2/P3 criteria; it does not change thresholds or choose a fit.
