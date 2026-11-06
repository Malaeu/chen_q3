# Part B — smooth taper objects and finite checks

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
