# Part A — smooth Mobius taper fit

## Contract and inputs

- Frozen preregistration: commit `60ea7f7d3`; blob `712c14b9fe5d68b8e8f124326afc1e7391af2482`.
- One native full Vasyunin Gram was built at N=10000 (799,920,020 bytes; 5.968s measured for the native build/read step). All smaller targets use its leading principal prefixes.
- Free variables are n=2..N with physical optimum read directly from ec1 `c_opt` (the negative of the older projection coefficients); the residual convention is `1 + sum c_n r_n`.
- For both exported vectors, raw coefficient n=1 is 1. For n>=2, `log=mu(n)*x` and `best=mu(n)*P(x)`, x=log(N/n)/logN.
- Polynomial fits use P(0)=0, degree 1..4, both free P(1) and fixed P(1)=1; splines use the frozen three basis functions and five x0 values. No positivity or monotonicity constraints were imposed.
- Best Part A/Part B profile is selected per N from degree<=3 polynomial variants and all five splines. Degree 4 is reported but excluded. Energy ties within 1e-12*max(1,|E_min|) use ascending family name.
- SVD least-squares solves are used for singular and rank-deficient systems. CSVs report basis/Hessian rank and condition numbers; these floating-point computations are not interval certificates.

## J1 and J3 validation

- J1: PASS; max absolute E(log)-archived E(a) difference = 3.06422e-14.
- J3: PASS; minimum E(fit)-E(opt) = 0.00078021 across every fitted family at the four main N.

| N | best family | E(best) | E(best) log N | closure | cosine(c_opt,best) | P'(0) | P(1) | rank / dimension |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 500 | poly_d3_free | 0.00907061289795 | 0.0563703043733 | 0.950901 | 0.914925530 | 1.55340489 | 1.06262205 | 3/3 |
| 1000 | poly_d3_free | 0.00803324603189 | 0.0554916976842 | 0.946519 | 0.901118464 | 1.48131331 | 1.0648118 | 3/3 |
| 2000 | poly_d3_free | 0.00721687649947 | 0.054854774335 | 0.951022 | 0.889327986 | 1.38121925 | 1.06686461 | 3/3 |
| 5000 | spline_x0_0.05 | 0.00630902487785 | 0.0537351837341 | 0.944424 | 0.926373568 | 5.4059641 | 1.13513608 | 3/3 |

## Prediction checks available in Part A

- R1: **HIT** (p=0.55); best degree<=3 polynomial gap closure >= 0.5 at N=5000
- R2: **MISS** (p=0.5); each degree-3 winner coefficient changes by <20% from N=2000 to N=5000
  - N=2000 winner `poly_d3_free`; N=5000 winner `poly_d3_free`; coefficient relative changes `[0.011502994354516419, 1.0697119694273127, 0.3272666111936785]`.
- R3: **HIT** (p=0.6); selected best Pprime(0) outside [0.8,1.25] at N=5000

J2/J4, boundary scalars, head arithmetic, and the core calculation are handled separately. The literal/corrected head identity prediction R4 is not scored here.

## Artifacts

- `fit_all.csv`: E and numerical conditioning for every fitted family at every requested N, including log taper.
- `fit_coefficients.csv`: all fitted polynomial/spline coefficients.
- `fit_selected.csv`, `selected_profiles.json`, `selected_vectors.csv`: per-N Part B interface. The latter has exactly `N,n,log,best` columns and raw n=1 entries.
- `fit_energy_splits.csv`: the same eight delta-energy masks as the prior Gram comparison; threshold masks can overlap arithmetic masks.
- `fit_profile_N*.png` and `fit_delta_energy_N*.png`: main-N profile and remaining-delta plots.
