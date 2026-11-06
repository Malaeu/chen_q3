# CODEX TASK — BEST SMOOTH MÖBIUS TAPER μ(n)·P(log(N/n)/log N): HOW MUCH GAP CLOSES, AND WHAT GETS CHEAPER (2026-11-06)

Repository: https://github.com/Malaeu/chen_q3 (public)

## Sources and output

Branch `rh_clean`:
- this task file;
- `docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/` (commit ec1e2e96): full Vasyunin Gram (`gram_native.cpp`), E(v) = 1 + 2bᵀv + vᵀGv, b_n = log(n)/n, sign convention c_opt = −x, optimal coefficients;
- `docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06/` (commit a180142f): the core H_N code (head + shoulder).

Branch `proshka_inbox_2026-10-31`, for definitions:
- R8, commit 70c4e6b0: H_N (24), S, b_N, s_N;
- reciprocity verdict, commit aabf1a70: (1)–(3) a_n, q_n, b_N, s_N, u_N; (10) F_N; (11) the head identity; (14)–(15) L_N and E_N = B_N − πL_N(F_N).

Result: push to `rh_clean` per AGENTS.md.

## Background

Codex run ec1e2e96 shows that the optimal NB vector is close to the Möbius taper a_n = μ(n)·log(N/n)/log N (cos 0.875). 99.5% of the difference sits at n > √N, about half at n > N/2. The gap is E(a)/e_opt ≈ 4.4 at N = 5000.

Hypothesis: most of the gap is the SHAPE of the smooth profile, not the arithmetic. Keep μ(n) exactly and change only P.

## PART A — fit the profile

Write x = log(N/n)/log N ∈ [0, 1], so that x = 0 at n = N. The family is a_n(P) = μ(n)·P(x_n), n = 2..N. The n = 1 term follows the centring used in ec1e2e96.

Since E is quadratic in a and a is linear in the parameters of P, each fit is a small least-squares problem on the existing Gram.

1. **Polynomial P of degree d = 1, 2, 3, 4** with P(0) = 0, so the taper vanishes at the edge. Fit both with P(1) free and with P(1) = 1.
2. **Edge-spline P:** linear on [x₀, 1] plus a free cubic on [0, x₀], C¹ at x₀, for x₀ ∈ {0.05, 0.1, 0.2, 0.35, 0.5}.
3. For N ∈ {500, 1000, 2000, 5000} report:
   - E(P_best) and E(P_best)·log N;
   - the gap closure (E(a) − E(P_best)) / (E(a) − e_opt);
   - cos(c_opt, a(P_best));
   - where the remaining δ = c_opt − a(P_best) sits, using the same energy splits as ec1e2e96;
   - the fitted coefficients of P, and P′(0) against the log taper's P′(0) = 1.

## PART B — what gets cheaper for the proof objects

For the log taper and for the best P (one per N, chosen as degree ≤ 3 polynomial or spline by the smallest E):

1. **Boundary scalars.** b_N, s_N, u_N, generalised to P exactly as defined in aabf1a70 (1) with a_n replaced. Also B_N = 2b_N(1 + u_N) − s_N.
2. **Head arithmetic.** For r ≤ N, A_N(r) = Σ_{n|r} a_n. For the log taper this equals 1_{r=1} + Λ(r)/log N (aabf1a70 (11)). For polynomial P, verify numerically that A_N(r) = Σ_j p_j·Λ_j(r)/(log N)^j, with Λ_j = μ * log^j the generalised von Mangoldt function. State the exact formula used.
3. **Core.** H_N, head and shoulder separately, as in a180142f, on the 92-point log grid with N ≤ 10⁴. Report the ratio head(P_best)/head(log taper) and shoulder(P_best)/shoulder(log taper).
4. **Fourier energy.** ||F_N||₂ by Parseval, for both tapers, compared against 7/log N.

## JUDGES (build first)

- **J1.** P(x) = x reproduces E(a) of ec1e2e96 to 1e−10 at all four N.
- **J2.** For the log taper at N ∈ {50, 200, 1000}, the identity E_N = B_N − π·L_N(F_N) of aabf1a70 (15) holds to 1e−9, with L_N computed directly from (14) using the midpoint convention for F_N. This validates the implementation of every Proshka object.
- **J3.** E(P_best) ≥ e_opt at every N: no fit may beat the optimum.
- **J4.** ||F_N||₂ by Parseval agrees with direct quadrature on (0, 1) to 1e−6 at N ≤ 1000.

## PRE-REGISTERED PREDICTIONS (Mythos, before any run; scored after)

| ID | Prediction | p |
|---|---|---|
| R1 | The best polynomial with d ≤ 3 closes ≥ 50% of the gap at N = 5000 | 0.55 |
| R2 | The best d = 3 coefficients are stable: each coefficient changes by < 20% between N = 2000 and N = 5000 | 0.5 |
| R3 | P′(0) of the best fit lies outside [0.8, 1.25]: the edge slope differs from the log taper | 0.6 |
| R4 | The generalised head identity in B.2 holds exactly, to 1e−10 | 0.9 |
| R5 | Head of H_N at N = 10⁴ for P_best ≤ 0.5 × head for the log taper | 0.5 |

## OUTPUT

Folder `docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/` with:
- PREREGISTRATION.json, committed before any numbers;
- scripts (uv, ASCII progress with ETA);
- CSVs;
- plots of P_best(x) against x for each N, and the δ energy maps;
- REPORT.md with J1–J4, the tables, and HIT/MISS for R1–R5.

Give the commit, the paths and the blobs in the final message.
