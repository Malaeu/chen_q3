# Smooth Mobius taper fit: finite results

Task commit `45af4a837e9a183d2405d91bf7df0f002f56acde`, blob `6bc455bf4859c160b08b69fe483661edbdb649bc`. Preregistration was committed before numerical runs as `60ea7f7d3` and pushed to rh_clean as `c11b1f5a9`. Exact source commits and blobs are in [SOURCES.json](SOURCES.json).

## Result

At N=5000 the best cubic polynomial closes **94.43677%** of the gap between the log taper and the unrestricted full-Gram optimum. The selected spline with x0=0.05 closes **94.44237%**. The cubic and spline errors are respectively 0.00631003487605 and 0.00630902487785, versus log-taper 0.0233363799923 and optimum 0.00530702068301. Thus the spline's advantage over the cubic is small, though above the numerical checks' error scale.

This supports the finite-N smooth-profile hypothesis on the tested data. It does not provide one fixed profile with an asymptotic bound. The best cubic coefficients are not stable under the frozen 20% coordinate test (R2 MISS).

At N=10000, a freshly refitted selected profile gives head ratio **0.233318**, shoulder ratio **2.435151**, and full finite-core ratio **0.283444** relative to the log taper. The head becomes cheaper while the shoulder becomes more expensive. The Fourier norm falls as shown below; it is a different norm from the NB objective.

## Frozen choices and source correction

Polynomials have P(0)=0, degrees 1 through4, with P(1) free or fixed at 1. Splines have P(0)=0, P(1) free, and C1 matching at the five prescribed knots. The spline endpoint condition was unspecified in the task; it was explicitly stated and frozen before runs. Best-profile selection excludes degree4 and minimizes E among degree<=3 polynomials and the five splines, independently at each N. No positivity or monotonicity constraint is imposed.

Only n>=2 are free coordinates. Raw a1=1 stays fixed even when P(1) differs from 1; the centered Dirichlet coefficient is q1=1-s. This preserves the source definitions and E=B-pi L(F). See [CONVENTIONS.md](CONVENTIONS.md) for the exact algebra.

Task B.2 is false as written. The standard convolution Lambda_j=mu*log^j requires lower-order shifted terms. The exact formula is

```text
A_P(r)=1-P(1)+sum_j p_j/L^j * sum_{k=0}^j binom(j,k) log(N/r)^(j-k) Lambda_k(r),
Lambda_k(r)=sum_{d|r} mu(d) log(r/d)^k, Lambda_0(r)=1_{r=1}.
```

The additive correction 1-P(1) applies to every r, since 1 divides every r. An exact counterexample to the literal task formula is P=x^2,N=4,r=2: direct value 3/4 versus literal 1/4. This issue was identified before the numerical run. Literal R4 remains MISS; the corrected identity is not substituted into its score.

## Judges

| Judge | Outcome | Evidence |
|:---|:---|:---|
| J1 | PASS | Four main N; max log-taper error 3.06422e-14 <1e-10 |
| J2 | PASS | Direct midpoint cotangent functional at N=50,200,1000; max error 8.95117e-16 <1e-9 |
| J3 | PASS | Every fitted family at four main N, including degree4, stays above the archived optimum within 1e-10 tolerance |
| J4 | PASS | Eight log/best comparisons at N=50,200,500,1000; max norm discrepancy 9.88792e-14 <1e-6 |

Corrected polynomial head identity: all 32 fitted polynomial cases pass, max absolute difference **5.10703e-15**. Literal formula maximum discrepancy: **1**.

All judges are finite floating-point diagnostics. J2 directly evaluates L from rational F samples, and J4 integrates the piecewise affine-plus-sine function independently of its Parseval formula. They are not interval certificates.

## All fitted-family errors

| family | N=500 | N=1000 | N=2000 | N=5000 |
|:---|---:|---:|---:|---:|
| log_taper | 0.0409065213784 | 0.0340826753891 | 0.0285384854212 | 0.0233363799923 |
| poly_d1_fixed1 | 0.0409065213784 | 0.0340826753891 | 0.0285384854212 | 0.0233363799923 |
| poly_d1_free | 0.00982642194184 | 0.00860685000305 | 0.00762302837586 | 0.00660972470835 |
| poly_d2_fixed1 | 0.00955060686175 | 0.00855208772116 | 0.00781348593222 | 0.0068739199087 |
| poly_d2_free | 0.00909886566623 | 0.0080606071117 | 0.00724618700611 | 0.00632290734997 |
| poly_d3_fixed1 | 0.00913356404609 | 0.0081150632335 | 0.0073186246759 | 0.00644807660725 |
| poly_d3_free | 0.00907061289795 | 0.00803324603189 | 0.00721687649947 | 0.00631003487605 |
| poly_d4_fixed1 | 0.0088672434211 | 0.00782773868706 | 0.0070342452384 | 0.00610485997894 |
| poly_d4_free | 0.00876077805268 | 0.0077556040647 | 0.00700251056339 | 0.00608723054158 |
| spline_x0_0.05 | 0.00922914275068 | 0.00814546791113 | 0.00730491753689 | 0.00630902487785 |
| spline_x0_0.10 | 0.00923088330677 | 0.00821688156667 | 0.00733425301802 | 0.00631822148253 |
| spline_x0_0.20 | 0.00930737683523 | 0.00822411831467 | 0.0073556133844 | 0.00633446298598 |
| spline_x0_0.35 | 0.00932315644787 | 0.00823412275748 | 0.00737595244702 | 0.00637316009126 |
| spline_x0_0.50 | 0.00929674806665 | 0.00822565656594 | 0.00737215533045 | 0.00639694387241 |

All coefficients, E logN, conditioning, and the 98-N selection table are retained in CSV/JSON. The four main selected profiles and their ordinary coefficients are:

| N | selected family | coefficients |
|---:|:---|:---|
| 500 | poly_d3_free | x^1: 1.55340489014; x^2: -0.0255603963131; x^3: -0.465222441075 |
| 1000 | poly_d3_free | x^1: 1.48131331379; x^2: 0.0391248180056; x^3: -0.455626335797 |
| 2000 | poly_d3_free | x^1: 1.3812192511; x^2: 0.153969894097; x^3: -0.468324536287 |
| 5000 | spline_x0_0.05 | x: 1.04445853039; (x0-x)_+^2-x0^2: -21.5829509565; (x0-x)_+^3-x0^3: -293.76139597 |

Spline basis is x, (x0-x)_+^2-x0^2, (x0-x)_+^3-x0^3. Its edge slope is alpha-2*x0*beta-3*x0^2*gamma. Degree3 polynomial coefficients are in the ordinary x,x^2,x^3 basis.

## Remaining delta energy

| mask | N=500 | N=1000 | N=2000 | N=5000 |
|:---|---:|---:|---:|---:|
| n_le_sqrtN | 0.01915438 | 0.00980296 | 0.00693865 | 0.00156817 |
| n_gt_sqrtN | 0.98084562 | 0.99019704 | 0.99306135 | 0.99843183 |
| n_gt_N_over_2 | 0.76087313 | 0.71199371 | 0.68938689 | 0.63064390 |
| squarefree | 0.84431686 | 0.75442775 | 0.78166891 | 0.69778693 |
| non_squarefree_mu_zero | 0.15568314 | 0.24557225 | 0.21833109 | 0.30221307 |
| primes | 0.12034493 | 0.09853010 | 0.10029323 | 0.05979062 |
| proper_prime_powers | 0.00785580 | 0.00333496 | 0.00208297 | 0.00213897 |
| other | 0.87179928 | 0.89813494 | 0.89762380 | 0.93807041 |

Shares are fractions of the remaining squared coefficient difference. Different location and arithmetic masks overlap; only each stated complementary partition sums to 1.

## Core ratios and prediction scores

| N | head(best)/head(log) | shoulder(best)/shoulder(log) | H(best)/H(log) |
|---:|---:|---:|---:|
| 500 | 0.173457527 | 1.96253537 | 0.22011211 |
| 1000 | 0.188293752 | 1.97512895 | 0.234589753 |
| 2000 | 0.215196357 | 1.8368114 | 0.25218958 |
| 5000 | 0.220517566 | 2.72793709 | 0.269787631 |
| 10000 | 0.233317796 | 2.43515099 | 0.283443796 |

| prediction | p | outcome |
|:---|---:|:---|
| R1 | 0.55 | HIT |
| R2 | 0.5 | MISS |
| R3 | 0.6 | HIT |
| R4 | 0.9 | MISS |
| R5 | 0.5 | HIT |

Mean Brier score: **0.3345**. R4 is a literal-formula failure, not a failure of the corrected algebra. R2 coefficient relative changes are 1.15030%, 106.97120%, 32.72666%.

## Validation, reproduction and limitations

The independent reviewer checked the scaled constrained solve, all nested-family inequalities, and directly summed the original remainder formula for every k=1..10000 for both N=10000 vectors. Those heads agree with the divisor-sieve output within 4e-17. The root validator reproduces all 98 selected profiles as 135780 coefficient rows, including raw a1=1 and exact zero on nonsquarefree free indices. See [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) and [OUTPUT_VALIDATION.json](OUTPUT_VALIDATION.json).

One Sol escalation completed fit-output assembly after two late schema failures in the Luna run; it also corrected the scaled-coordinate gradient diagnostic. The same frozen model families and objective were retained. The final fit run and interface validation succeeded.

```sh
uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/input_audit.py
uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/fit.py
uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/objects.py
uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/validate_outputs.py
uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/build_report.py
```

One full Vasyunin Gram at N=10000 supplies all leading principal blocks; it is not a sequence of full-dimensional optimization solves. No free optimum at N=10000 is claimed. The core uses exactly the inherited 92-point log grid, plus the four main N values, and stops at K-1 for K=ceil(N^(3/2)). Boundary and Fourier objects cover all 98 supplied N. The infinite NB objective E and finite core H are kept distinct.

The fitted profiles and selection depend on N. A numerical norm below 7/logN does not transfer the log-taper theorem to this family. No uniform bound for the cotangent functional, asymptotic rate, convergence theorem, or RH claim is established. RH remains OPEN; PX_RH_CLAIM: NOT_MADE.

## Detailed Part A

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

## Detailed Part B

This is a finite floating-point diagnostic, not an interval certificate, proof of an asymptotic bound, or RH claim.

## Fixed-vector convention

For every profile the physical free coefficients use `a_1=1` and `a_n=mu(n)P(log(N/n)/log(N))` for `n>=2`. The induced centered coefficients are `q_1=1-s`, `q_n=a_n` for `n>=2`; `q_1` is not replaced by `P(1)`. The computed boundary objects use `S=sum a_n`, `s=sum a_n/n`, `u=sum a_n log(n)/n`, `b=1+(S-s)/2`, and `B=2b(1+u)-s`.

The Parseval evaluation uses `gcd(h,k)^2=sum_{d|h,d|k} J_2(d)` and
`||F||_2^2 = sum_d J_2(d)(sum_{d|n} q_n/n^2)^2/12 + (1/2-q_1)/pi^2`. The CSV also compares `||F||_2` with the log-taper benchmark `7/log(N)`; that benchmark is not assumed for best profiles.

## J2 — direct cotangent functional

For log tapers at `N=50,200,1000`, `F(r/k)` was evaluated with integer residues: if `k` divides `n*r`, the Bernoulli term is exactly zero; otherwise it is `(n*r mod k)/k - 1/2`. Then `L_N` was summed directly from the cotangent formula (14), and compared with the independent full-Gram reference `E` supplied by Part A. The `L_N` column was not inferred from `E`.

| N | E full Gram | B | direct L_N | B - pi L_N | absolute error |
|---:|---:|---:|---:|---:|---:|
| 50 | 0.096478549878305 | -0.0563545512559121 | -0.0486482870271485 | 0.0964785498783052 | 2.22e-16 |
| 200 | 0.0548040164991075 | -0.085661655177373 | -0.0447116119640705 | 0.0548040164991084 | 8.95e-16 |
| 1000 | 0.0340826753890912 | -0.0698786046660152 | -0.033091903221862 | 0.034082675389091 | 1.94e-16 |

J2: **PASS**, maximum absolute discrepancy `8.95117e-16` (tolerance `1e-9`).

## J4 — independent piecewise quadrature

The rational breakpoints are the reduced fractions `r/n` for `n<=N`. An event sweep updates the affine offset of `sum(q_n/n) B_1(n*x)` by the exact jump `-q_n/n`; on each open interval, `F(x)=x sum(q_n)+offset+sin(2*pi*x)/pi`. Independent 8- and 12-point Gauss-Legendre integrations were compared with the Jordan-2 Parseval norm. Exact rational probes use the stipulated `B_1(integer)=0` convention.

| N | profile | Parseval norm | direct J4 norm | absolute norm error | intervals |
|---:|---|---:|---:|---:|---:|
| 50 | log_taper | 0.0651791666906925 | 0.0651791666906928 | 3.05e-16 | 512 |
| 50 | best | 0.0323862325554597 | 0.0323862325554596 | 4.86e-17 | 512 |
| 200 | log_taper | 0.0484736761317604 | 0.0484736761317625 | 2.07e-15 | 8532 |
| 200 | best | 0.0212187530619771 | 0.0212187530619774 | 2.81e-16 | 8532 |
| 500 | log_taper | 0.0413966802053078 | 0.0413966802053075 | 2.5e-16 | 53890 |
| 500 | best | 0.0172244144033155 | 0.0172244144033152 | 2.67e-16 | 53890 |
| 1000 | log_taper | 0.0372897628399432 | 0.0372897628400421 | 9.89e-14 | 213268 |
| 1000 | best | 0.0151458175005588 | 0.0151458175005628 | 4.05e-15 | 213268 |

J4: **PASS**, maximum norm discrepancy `9.88792e-14` (tolerance `1e-6`).

## Literal and corrected head identity (R4)

For `P(x)=sum_{j>=1} p_j x^j`, the literal requested formula omits both the logarithmic shift and the fixed raw-`a_1` correction. The corrected identity tested here is

```text
A_P(r) = 1 - P(1) + sum_j p_j/L^j * sum_{k=0}^j binom(j,k) log(N/r)^(j-k) Lambda_k(r),
Lambda_k(r) = sum_{d|r} mu(d) log(r/d)^k,  Lambda_0(r)=1_{r=1}.
```

Across `32` fitted polynomial rows at the four main Ns, the corrected formula's largest absolute error is `5.10703e-15` (**PASS**, threshold `1e-10`). The literal expression is a preregistered **MISS** (largest fit-row discrepancy `1`), kept separate from the corrected pass.

The explicit witness is `P=x^2,N=4,r=2`: direct divisor sum `3/4`, literal expression `1/4`, corrected expression `3/4`. For `P=x`, the corrected formula gives `1_{r=1}+Lambda(r)/log(N)`; the literal version still omits the `r=1` term.

Detailed per-row and per-r data are in `objects_head_checks.csv` and `objects_head_polynomials.csv`.

## Boundary objects and R8 core

Boundary objects and Parseval norms were computed for all supplied log/best vectors. The finite core was computed on the exact pinned `a180142f` log-grid (92 Ns), with each best vector freshly supplied for its N, plus the four main Ns. The cutoff is the exact integer `K=ceil(sqrt(N^3))`; `A(d)=sum_{n|d,n<=N}a_n` is built by divisor sieve and `R(k)=1+k*s-sum_{d<=k}A(d)`. Direct remainder-form checks at sampled k had maximum error `3.17342e-11` (tolerance `2e-10`). The log-profile head/shoulder/full-core comparison against pinned `a180142f` has maximum absolute differences `2.37e-14`, `1.32e-16`, `2.38e-14` respectively.

| N | profile | b | s | u | B | norm(F) | norm(F)/(7/logN) |
|---:|---|---:|---:|---:|---:|---:|---:|
| 500 | log_taper | 0.1936244804 | 0.160830797683 | -0.814746404378 | -0.0890915352934 | 0.0413966802053 | 0.0367520205788 |
| 500 | best | -0.00182103942536 | -0.00613718201894 | -0.990929387102 | 0.00610414613154 | 0.0172244144033 | 0.0152918550345 |
| 1000 | log_taper | 0.223676784318 | 0.144823735596 | -0.83247002777 | -0.069878604666 | 0.0372897628399 | 0.0367983651585 |
| 1000 | best | 0.0713699837639 | -0.00686735213687 | -0.991966753968 | 0.00801401741461 | 0.0151458175006 | 0.0149462286849 |
| 2000 | log_taper | 0.153782778949 | 0.131538235323 | -0.848307481715 | -0.0848828413072 | 0.0338813726863 | 0.0367898584263 |
| 2000 | best | -0.00523820262508 | -0.00617947101951 | -0.992783123501 | 0.00610386409666 | 0.0137663665089 | 0.0149481155795 |
| 5000 | log_taper | 0.153209131688 | 0.117406058823 | -0.86448683586 | -0.075882350403 | 0.0302450895959 | 0.0368004673115 |
| 5000 | best | 0.0301828784606 | -0.0125229939421 | -0.993690975122 | 0.0129038430043 | 0.0156299973213 | 0.0190176723953 |

Core ratios `head(best)/head(log)` and `shoulder(best)/shoulder(log)` for the full grid and main Ns are in `objects_core_ratios.csv`; raw head and shoulder values are in `objects_core.csv`.
At `N=10000`, the selected profile reduces the head to `0.233318x` the log-taper head, while the shoulder rises to `2.43515x`; combined `H_N` is `0.283444x`. This is a finite proof-cost tradeoff: the head becomes cheaper, the shoulder more expensive, and the computed full core is smaller.

## Scope and evidence boundary

These checks validate the finite numerical implementation of the listed objects only. Floating-point agreement does not certify the corresponding identities for arbitrary real profiles, establish the bound `||F||_2<=7/log(N)` for fitted profiles, or imply an RH result. Route B remains `CHALLENGER_NOT_RH`; `PX_RH_CLAIM` remains `NOT_MADE`.
