# CODEX TASK — NB RATE THERMOMETER + MERTENS HEAD THERMOMETER (2026-11-06)

Repository: https://github.com/Malaeu/chen_q3 (public)

- Branch `rh_clean` holds this task file and the earlier thermometer `docs/routeB_bus/corner_thermometer_2026-11-04/`, commit a33870cb. Reuse its sieve and Kahan infrastructure.
- Branch `proshka_inbox_2026-10-31` holds the sources below.
- Result: push to `rh_clean` (or `codex/<name>` + PR into `rh_clean`) per AGENTS.md.

## SOURCES (proshka_inbox_2026-10-31)

1. **R6 C.** Commit 0005623e. File `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_C.md`. Use it for the definitions: H = ℓ²(ℕ, w_k), w_k = 1/[k(k+1)], target v(k) = 1, r_n(k) = (k mod n)/n, V_N = span(r_2, …, r_N), e_N = dist_H(v, V_N)².
2. **R7 B.** Commit 8a994500. File `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md`. Use:
   - §2: d_N² ≤ e_N ≤ (log 2π − γ_E)·d_N²;
   - §7.1: the sufficient condition e_m ≤ 1/(2 log m);
   - §7.4: the explicit V_N and the identity R_N^V(k) = k·b_N − ψ(k)/log N for k ≤ N.
3. **R6 C, Limit 9.** Commit c09713ed. File `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_LIMIT9_2026-11-06_C.md`. Use:
   - (L6)–(L10): the exact-head interpolant H_N, its error E_N^h, and γ(N) = Σ_{k<N} M(k)/[k(k+1)];
   - the lower bound √E_N^h ≥ √N·|γ(N)| − 2/√N;
   - condition (B): liminf E_N^h < ∞.
4. **Literature (verify):** Bettin–Conrey–Farmer arXiv:1211.5191 (V_N, constant 2 + γ_E − log 4π ≈ 0.046191); Burnol arXiv:math/0103058 (lower bound).

## PART A — NB rate: e_N · log N against the threshold 1/2

For N in {10, 20, 50, 100, 200, 500, 1000, 2000}, and 5000 if feasible:

1. Compute e_N by weighted least squares over k ≤ K.
   - Choose K so that the tail bound (1 + Σ|c_n|)²/(K + 1) is below 1e−3·e_N. Report K and the bound.
   - Use float64 with a cross-check at mpmath 30 dps for N ≤ 200.
2. Compute the explicit Bettin–Conrey–Farmer polynomial error E(V_N) in the same norm. Use the centred form from R7 B §7.4.
3. Report e_N, e_N·log N, E(V_N), E(V_N)·log N, and the ratio e_N / (1/(2 log N)).

## PART B — Mertens head thermometer for condition (B)

1. **Cheap lower bound.** Compute γ(N) and √N·γ(N) for every N ≤ 10⁸. Reuse the sieve; M(k) comes from μ by a running sum. Report:
   - the maximum and minimum;
   - the uniform-log mean of |√N γ(N)|²;
   - per-dyadic-block min and max of |√N γ(N)|;
   - a log-scale plot.
2. **Full head error.** Compute E_N^h exactly with its tail for N ≤ 10⁵ on a log grid of about 200 points. Report max E_N^h and liminf-type statistics (min over each decade).

## JUDGES (build first; any failure voids the run)

- **J1 (monotonicity).** e_N is non-increasing in N on the grid. This is exact, because the subspaces are nested.
- **J2 (optimality).** e_N ≤ E(V_N) and e_N ≤ E_N^h for every N computed. The infimum must lie below every explicit approximant.
- **J3 (head identity).** H_N(k) = 1 for 1 ≤ k < N to 1e−12, per R6 C Limit 9 (L6). Also R_N^V(k) = k·b_N − ψ(k)/log N for k ≤ N to 1e−10, per R7 B (7.10).
- **J4 (Mertens sanity).** Spot-check M(x) at x = 10^k against published values (OEIS A084237). Check that γ(N) → 0 in trend, since Σμ(n)/n = 0.
- **J5 (planted control for Part B).** Replace M(k) by M(k) + 0.01·k^{0.8}·cos(14 log k). The planted √N·γ(N) must show visible power growth, a log-log slope ≈ 0.3 on [10⁶, 10⁸]. Without this the detector is blind, so report INCONCLUSIVE for Part B.

## PRE-REGISTERED PREDICTIONS (Mythos, before any run; scored after, no retro-editing)

- **A1** (p ≈ 0.85): e_N ≤ 1/(2 log N) for every N ≥ 50 on the grid. The RH-world value of e_N·log N is about 0.05–0.06, a margin of about 10 below the threshold 0.5.
- **A2** (p ≈ 0.6): at N = 1000, e_N·log N ∈ [0.03, 0.15].
- **A3** (p ≈ 0.55): E(V_N)·log N decreases along the grid toward the band [0.04, 0.10]. Lower-order terms may keep it above the band at small N.
- **B1** (p ≈ 0.75): max over N ≤ 10⁸ of √N·|γ(N)| ≤ 0.6.
- **B2** (p ≈ 0.6): max over the grid N ≤ 10⁵ of E_N^h ≤ 3, i.e. bounded on the grid.
- **B3** (p ≈ 0.9): J5 shows the planted growth. The detector is not blind.

## OUTPUT

Folder `docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/`, containing:
- the scripts, run with uv, with an ASCII progress bar with ETA for long loops;
- the CSVs;
- the plots;
- `REPORT.md` with:
  - tables for A and B;
  - J1–J5 pass/fail;
  - the score of A1–A3 and B1–B3 (HIT / MISS);
  - all truncations and tail bounds, stated explicitly.

Give the commit hash, the paths and the blobs in the final message.
