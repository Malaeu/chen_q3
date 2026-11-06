# R8 rational certificate and core on the crossing set

**Finite computations completed.** P1/P3 MISS; P2 HIT. P4 has an empty test set and is scored MISS, not a false upper-bound counterexample. P5/P6 HIT under the preregistered finite-range rules. J1/J2 passed; J3 is explicitly a clarified finite identity check; J4 passed. No cofinal conclusion or RH claim is made.

## Source and preregistration

Task commit `9d8a6d48a0efdeaea7987748d242a3844e91a6dc`, task blob `190e2c60c9699a0ff3c76f4fdba768fd938b97b4`. Source verdict commit `70c4e6b097bc714689fb9226aeaea12a46127c95`, blob `e0c22e09de31ce8c3ee37e8c53343477168b2063`; freeze `6d50c6f9`. [SOURCE_PINS.json](SOURCE_PINS.json) records exact paths, commits, blobs, and SHA-256. Working task/reused files were checked against these pins.

[PREREGISTRATION.json](PREREGISTRATION.json) was committed before new numerical runs: isolated commit `94ec9ac25`, published on `rh_clean` as `55ae4e1af51a7b8e144f16f89944020c6ac53be1`. The previous Vasyunin/Gram code and optimal values come from `ba5654b4`. Its decimal e_N values remain labeled diagnostic; new Arb comparisons at N<=200 are separate evidence.

## Part 1: certificate

K_N=ceil(sqrt(N³)) uses integer cutoff arithmetic. For N<=200, the complete numerator/denominator of the exact rational Schur complement is in [certificate_results.csv](certificate_results.csv) and the corresponding `certificate_witness_N*.json`. Large-N endpoints below are rounded **outwards** from exact rational certified bounds. Small-N decimals and displayed products/ratios are summaries; the CSV and witnesses retain rigorous enclosures.

| N | K | ehat_N (exact-derived decimal or certified interval) | reused e_N, diagnostic | ehat/e_N, diagnostic ≈ | ehat log N ≈ | <=1/2 certified |
|---:|---:|---:|---:|---:|---:|:---:|
| 10 | 32 | 0.0520666880545 | 0.0238525533189 | 2.182856 | 0.11988798 | YES |
| 20 | 90 | 0.0315043267599 | 0.0165382521094 | 1.904937 | 0.09437853 | YES |
| 50 | 354 | 0.0196593988427 | 0.0118869704185 | 1.653861 | 0.07690802 | YES |
| 100 | 1000 | 0.0151637504567 | 0.0102019192845 | 1.486363 | 0.06983165 | YES |
| 200 | 2829 | 0.0122843978329 | 0.00893077778776 | 1.375513 | 0.06508664 | YES |
| 500 | 11181 | [0.0095797900, 0.0095798474] | 0.00742678807184 | 1.289901 | 0.05953482 | YES |
| 1000 | 31623 | [0.0081497140, 0.0081502013] | 0.00656137429817 | 1.242115 | 0.05629791 | YES |
| 2000 | 89443 | [0.0072125714, 0.0072236844] | 0.00611880278021 | 1.180332 | 0.05486429 | YES |

For large N the displayed ratio uses the numerical candidate objective and reused e_N, so it is a diagnostic approximation, not a certified quotient of two exact minima. The certified ehat interval is the authoritative result. [certificate_method.md](certificate_method.md) derives the enclosure: U(a) is an upper bound, and U(a)-||g||²/lambda_B is a lower bound, with outward error budgets and an exact Jordan inverse-trace lower bound for B. The candidate floating Gram is not a premise for certification.

### J1 and J2

J1: all eight grid points have a strict positive verified separation. At N<=200, Arb encloses the full Vasyunin minimum and is compared with exact rational ehat. At large N, a certified upper bound for E(a) from the source Young slack lies below the certified lower bound for ehat, so e_N<=E(a)<ehat. This does not relabel the reused point e_N as an interval.

J2: inequality (11) **does apply** to the true optimum a*. The comparison is ehat-e <= U(a*)-E(a*) <= RHS(11). Both the gap and RHS are enclosed using the Arb true-minimizer coefficients.

| N | ehat-e, rigorous Arb enclosure | RHS(11), rigorous Arb enclosure | Result |
|---:|---|---|:---:|
| 10 | [0.0282141347356538881513132351490 +/- 1.70e-32] | [0.0594149046669200831218095686603 +/- 4.36e-32] | PASS |
| 20 | [0.0149660746505445900955601051382 +/- 9.82e-33] | [0.0350094037622645114436344776076 +/- 1.12e-32] | PASS |
| 50 | [0.00777242842415736942877629788016 +/- 4.65e-33] | [0.0210791009787250475619612699116 +/- 3.55e-32] | PASS |

## Part 2: crossing set and core

Every N=3..10^7 was evaluated; b_(10^7+1) was also evaluated to classify the final endpoint. There are **27 certified crossings**, first at **43297**. Every sign interval excluded zero at 192-bit MPFR precision. The complete set is listed in [core_crossings.csv](core_crossings.csv), with values in [core_crossing_values.csv](core_crossing_values.csv). All 9,999,998 head rows and 9,999,999 sign rows are retained in gzip CSVs. No missing row is interpreted as a non-crossing.

Full H=head+shoulder was requested only through 10^4. Since S intersect [3,10^4] is empty, there is **no measured full-H value on S** in that requested domain. The complete 92-point rounded logarithmic grid was still evaluated. Full-H/shoulder extrema on S above 10^4 are **unavailable**, not replaced with head extrema.

| N range | count S | min head on S | max head on S | min head log N | max head log N | full H on S |
|---|---:|---:|---:|---:|---:|---|
| 3–9 | 0 | — | — | — | — | empty set |
| 10–99 | 0 | — | — | — | — | empty set |
| 100–999 | 0 | — | — | — | — | empty set |
| 1000–9999 | 0 | — | — | — | — | empty set |
| 10000–99999 | 5 | 0.0135622389 | 0.0154222129 | 0.156070474 | 0.164645056 | shoulder outside computed domain |
| 100000–999999 | 10 | 0.0100910379 | 0.0132572573 | 0.138270455 | 0.154454748 | shoulder outside computed domain |
| 1000000–10000000 | 12 | 0.00785503325 | 0.00988553163 | 0.125441103 | 0.137118656 | shoulder outside computed domain |

All grid head/shoulder values are in [core_full_H.csv](core_full_H.csv). Selected rows:

| N | K | head | shoulder | full H |
|---:|---:|---:|---:|---:|
| 3 | 6 | 0.554573396408 | 0.0721660988424 | 0.626739495251 |
| 10 | 32 | 0.224800176688 | 0.0201846613463 | 0.244984838034 |
| 250 | 3953 | 0.0500192704928 | 0.00124796470223 | 0.051267235195 |
| 10000 | 1000000 | 0.019900472975 | 0.000463599843892 | 0.0203640728188 |

### Plots

- [Full H vs N](core_full_H_vs_N.svg) and [full H log N vs N](core_full_Hlog_vs_N.svg): all 92 computed grid points; no S marks exist below 10^4.
- [Head vs N with S marked](core_head_H_vs_N.svg) and [head log N vs N with S marked](core_head_Hlog_vs_N.svg): display sampling is logarithmic, all 27 crossings are marked, and all integer rows remain in CSV. These plots are labeled head, not full H.

### J3: clarified finite identity

For every N=3..200, an independent literal residue sum through K_N-1 agrees with the prefix head plus floor-block shoulder within 1e-10. Maximum discrepancy: **2.456368441983159e-15**. See [core_j3.csv](core_j3.csv).

The original wording “direct norm minus the paid tail” cannot mean subtracting 5/log² N: that is a bound, not the exact tail. The source states |E-H-b²/K|<=5/log² N. The infinite tail was **not independently summed**, and no such equality is claimed. J3 PASS here names only the preregistered clarified finite normalization subjudge. [JUDGE_ANALYSIS.md](JUDGE_ANALYSIS.md) explains this distinction.

### J4: plant

Use f(k)=2 Re(k^(5/6+7i)/(5/6+7i)) literally, with unchanged s_N. f(1)=60/1789 is retained; no additive offset or recentering is introduced. Before the run, the planted self-energy was derived as (108/1789) N^(2/3)/log² N times a periodic factor of relative amplitude 1/sqrt(442), plus O(log^-2 N). The full head also includes the original residual and cross term; its dominance was not assumed.

On the common 101-point grid in [10^5,10^7], raw fitted slopes are **0.5191977397533443** (full planted head) and **0.5216222853522573** (exact discrete plant self-energy). Difference **0.0024245455989130305 < 0.05**, so J4 PASS. After multiplication by log² N, slopes are 0.6647929112398049 and 0.667217456838718, respectively. See [core_j4_analysis.json](core_j4_analysis.json).

## Prediction scores

| ID | p | Score | Evidence / boundary |
|---|---:|:---:|---|
| P1 | 0.60 | MISS | Ratios at N=10,20,50 exceed 1.5. |
| P2 | 0.85 | HIT | All eight upper endpoints times log N are strictly below 1/2. |
| P3 | 0.70 | MISS | Zero crossings through 10^4; early decades are empty. |
| P4 | 0.75 | MISS | NOT_TESTABLE_EMPTY_SET: S intersect [1000,10000] is empty; max undefined, not a numerical counterexample. |
| P5 | 0.45 | HIT | Preregistered finite-band rule: all 27 head*log N values lie in [0.1254411033,0.1646450563], within [0.02,0.3]. No asymptotic equivalence inferred. |
| P6 | 0.90 | HIT | J4 finite-window slope gate and no-offset construction pass. |

## Rounding, truncation, and verification

- The certificate finite sum is exactly 1<=k<K, with the **full infinite tail dominated**, not dropped, by (10)-(12). N<=200 Schur minima are exact rational numbers. Larger minima have rational endpoints justified by bounded basic-operation/decimal-output errors and exact residual/trace formulas; Arb handles transcendental comparisons. Witnesses retain the actual candidate coefficients and error budgets.
- Full e_N at N<=200 uses outward Arb Vasyunin formulas, inherited from the previous implementation. Larger reused e_N values and all displayed quotient estimates remain diagnostic. The large-N comparison needs only a certified candidate norm upper bound, not a precise full e_N enclosure.
- All b_N signs use directed MPFR RNDD/RNDU, including logarithms and both signs of the Möbius coefficients. There are zero unresolved intervals. Head, shoulder, and planted values use compensated native long double; on this Apple arm system it has **53 mantissa bits**. These values are numerical diagnostics, not interval certificates.
- Proper prime powers are included in psi. Every integer head row through 10^7 is computed, not sampled. Full shoulders are complete over N<k<K for the requested N<=10^4 grid; no full shoulder above that range is silently extrapolated. The logarithmic display sample does not replace the saved full scan.
- [OUTPUT_VALIDATION.json](OUTPUT_VALIDATION.json) independently verifies row continuity, gzip integrity, sign-derived crossing completeness, cutoff arithmetic, all 92 core rows, and direct positive-square head recomputation at decade endpoints through 10^7. Maximum endpoint discrepancy is 5.41997263042715e-12. This check is diagnostic and does not upgrade head arithmetic to intervals.
- Numerical scripts and relevant source formulas received an independent read-only review; final disposition is in [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md). No Lean sources or theorem status were changed.

## Reproduction

From the repository root (native core requires the already-present MPFR/GMP/zlib; the supplied runner uses Homebrew paths on this Mac):

```sh
D=docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06
uv run --no-project "$D/certificate.py" --preflight-only
uv run --no-project "$D/certificate.py"
uv run --no-project "$D/core_run.py" scan --log "$D/core_scan_run.log"
uv run --no-project "$D/core_run.py" full --log "$D/core_full_run.log"
uv run --no-project "$D/core_analyze.py"
uv run --no-project "$D/validate_outputs.py"
```

Run logs, native/Python sources, machine witnesses, and runtime metadata are retained alongside the CSVs. [BLOBS.tsv](BLOBS.tsv) and [SHA256SUMS](SHA256SUMS) identify delivered artifacts.

**Boundary:** boundedness of the full H on an unbounded subset of S, convergence of ehat, and RH remain unproved. `CHALLENGER_NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
