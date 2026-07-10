# Route B TwoLevelSpectralLadder N-Stability Audit

Status: diagnostic only. Not a proof of RH. Not a Route B failure claim.
Phase 2 was not run. Slopes were not refit. Mathematical definitions were not
changed.

## Verdict

Primary verdict: `NUMERICAL_FLOOR_IN_NU`.

Secondary finding: `BASIS_TRUNCATION_NOT_STABLE` is also visible for
`mu1`, `mu2`, `Delta`, `eta1`, `LB_3D`, and `W_actual`, but the specific
negative `nu ~ 1e-15` signal is a numerical/projection floor, not evidence for
a negative tail spectrum.

## Files inspected

- `ACTIVE/requests/routeB_twolevel_spectral_ladder/report.md`
- `ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_ladder_pilot.py`
- `ACTIVE/requests/routeB_twolevel_spectral_ladder/out/lambda_sq_{12,13,14}_N_{60,90,120}.json`
- `ACTIVE/requests/routeB_twolevel_spectral_ladder/out/phase1_summary.json`

## Unstable quantities

Drift is relative drift from `N=90` to `N=120`.

| lambda_sq | quantity | N60 | N90 | N120 | drift 90->120 |
|---:|---|---:|---:|---:|---:|
| 12 | mu1 | 9.190727e-54 | 5.880656e-54 | 5.122020e-54 | 0.148113 |
| 12 | mu2 | 7.112597e-50 | 4.456298e-50 | 4.038815e-50 | 0.103368 |
| 12 | Delta | 7.111678e-50 | 4.455710e-50 | 4.038303e-50 | 0.103362 |
| 12 | eta1 | 1.154946e-14 | 3.227321e-14 | 4.965661e-14 | 0.350072 |
| 12 | b | 4.694544e-01 | 4.694544e-01 | 4.694544e-01 | 0 |
| 12 | LB_3D | -1.551342e-14 | -3.642490e-14 | -6.092541e-14 | 0.402139 |
| 12 | nu | -1.659359e-15 | -3.393297e-15 | -3.457512e-15 | 0.018573 |
| 12 | W_actual | 1.418987e+35 | 6.328692e+35 | 1.074402e+36 | 0.410957 |
| 13 | mu1 | 1.013563e-58 | 4.190536e-59 | 3.483988e-59 | 0.202799 |
| 13 | mu2 | 8.546877e-55 | 3.548492e-55 | 3.055913e-55 | 0.161189 |
| 13 | Delta | 8.545863e-55 | 3.548072e-55 | 3.055565e-55 | 0.161184 |
| 13 | eta1 | 1.430846e-14 | 3.319127e-14 | 4.870022e-14 | 0.318458 |
| 13 | b | 4.693475e-01 | 4.693475e-01 | 4.693475e-01 | 0 |
| 13 | LB_3D | -1.870319e-14 | -4.107964e-14 | -6.594300e-14 | 0.377043 |
| 13 | nu | -1.760518e-15 | -3.013210e-15 | -2.515597e-15 | 0.197811 |
| 13 | W_actual | 1.492166e+40 | 8.337038e+40 | 1.420430e+41 | 0.413062 |
| 14 | mu1 | 2.838585e-63 | 1.842204e-64 | 1.459813e-64 | 0.261946 |
| 14 | mu2 | 2.281219e-59 | 2.002162e-60 | 1.668002e-60 | 0.200335 |
| 14 | Delta | 2.280935e-59 | 2.001978e-60 | 1.667856e-60 | 0.200330 |
| 14 | eta1 | 1.248361e-14 | 3.153381e-14 | 5.692903e-14 | 0.446086 |
| 14 | b | 4.692578e-01 | 4.692578e-01 | 4.692578e-01 | 0 |
| 14 | LB_3D | -1.711123e-14 | -4.232027e-14 | -6.807464e-14 | 0.378325 |
| 14 | nu | -2.509496e-15 | -3.068272e-15 | -4.535840e-15 | 0.323549 |
| 14 | W_actual | 4.967878e+44 | 1.429752e+46 | 3.098266e+46 | 0.538532 |

Conclusion: `b` is stable across N for each lambda. `W_actual` instability is
driven by both `eta1` growth and `Delta` shrinkage; it is not driven by `b`.

## Arithmetic path

`mu1`, `mu2`, and `Delta` use multiprecision arithmetic:

- `build_tau_matrix` builds an `mp.matrix` at requested `dps`.
- `eigsy_sorted` calls `mp.eigsy(T)`.
- `run_ladder_cell` sets `mu1, mu2, mu3 = vals[0], vals[1], vals[2]`.

`nu` does not use multiprecision after the matrix is assembled:

- The packet basis is built in `numpy`/`scipy` double precision.
- `K = np.column_stack(...)`, `Q, _ = np.linalg.qr(K)`.
- `T_np = np.array([[float(T[i,j]) ...]], dtype=float)` explicitly downcasts
  the high precision matrix to `float64`.
- `Pperp = I - Q Q*` is a full-size `complex128` projection.
- `nu = eigvalsh(Pperp* T_np Pperp)[0]` is a `float64` eigenvalue.

This is not a high-precision tail-block eigensolve.

## Projection and conditioning

`Gram(M)` is well conditioned:

| lambda_sq | N | Gram_condition |
|---:|---:|---:|
| 12 | 60 | 1.2605 |
| 12 | 90 | 1.2605 |
| 12 | 120 | 1.2605 |
| 13 | 60 | 1.2565 |
| 13 | 90 | 1.2565 |
| 13 | 120 | 1.2565 |
| 14 | 60 | 1.2531 |
| 14 | 90 | 1.2531 |
| 14 | 120 | 1.2531 |

The problem is not Gram degeneracy. The problem is the `Mperp` representation:
`Pperp = I - Q Q*` is a rank-deficient projection on the full space, so
`Pperp*T*Pperp` has the three packet directions as exact zero modes in exact
arithmetic. Calling full `eigvalsh` on that matrix makes the reported smallest
eigenvalue a roundoff-level zero, which appears as a negative `~1e-15` floor.

This also explains why `tail_margin = nu - lambda3_G` is negative at `~1e-15`
even though `lambda3_G` is only `~1e-18`.

## One precision diagnostic

Diagnostic target: `lambda_sq=14`, `N=120`; no Phase 2; no slope refit.

Independent repeat at current `dps = 197`:

```json
{
  "dps": 197,
  "mu1": "1.45981295163056810659041907528697672740832363545514856423338985846462177293643297348350679e-64",
  "mu2": "1.66800225835889555472835851713524924580677530176468952905677239936341480225283166979823235e-60",
  "Delta": "1.667856277063732497917699475227720548134034469401144014200349060377568340075538026500884e-60",
  "nu_float64_projected_full": -4.0049875337510944e-15
}
```

Repeat at `dps+80 = 277`:

```json
{
  "dps": 277,
  "mu1": "1.45981295163056085743586092649221790717971137438785822065563584799504336083667785607863281e-64",
  "mu2": "1.66800225835888695966540567277360965225903033099935184336440852532823796680775493903140165e-60",
  "Delta": "1.66785627706372390357966208668096043046831235986191305754234296174343846247167127124579379e-60",
  "nu_float64_projected_full": -4.535840335640321e-15
}
```

The `mu`/`Delta` values are stable under `dps+80` to about current numerical
resolution, and the accepted Phase 1 `dps=197` JSON is reproduced by the
`dps+80` run to the displayed precision. The reported `nu` remains a
`~1e-15` negative floor because the `nu` path downcasts to `float64` before
the projected eigensolve. Increasing `mp.dps` therefore cannot repair the
`nu ~ 1e-15` floor in the current implementation.

## Diagnosis

1. `N_LIMIT_NOT_STABLE` is real for the reported Phase 1 packet quantities:
   `mu1`, `mu2`, `Delta`, `eta1`, `LB_3D`, and `W_actual` do not stabilize
   from `N=90` to `N=120`.
2. `b` is stable and is not the source of `W_actual` drift.
3. `W_actual` drift is mainly from `eta1` increasing with N and `Delta`
   decreasing with N.
4. `nu` is not a reliable tail-gap quantity in this implementation. It is a
   full projected `float64` matrix eigenvalue with exact null directions in
   exact arithmetic, so the negative value is a numerical zero floor.
5. This audit does not support a Route B mathematical failure claim. It supports
   a numerical implementation diagnosis: the packet truncation is not yet
   stable, and the reported `nu` needs a true complement-basis eigensolve before
   it can be interpreted as a tail gap.

## Next local fix shape

Do not change the mathematical definitions. For a future run, compute `nu` on
an explicit orthonormal basis of `Mperp` instead of on the full singular
projection matrix, and keep that tail block in high precision or at least
separate it from the three forced zero modes. Then re-evaluate N-stability
without changing the registered formulas.
