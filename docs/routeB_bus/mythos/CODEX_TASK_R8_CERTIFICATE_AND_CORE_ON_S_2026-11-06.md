# CODEX TASK — ROUND 8 B: RATIONAL CERTIFICATE ê_N AND THE CORE H_N ON THE CROSSING SET S (2026-11-06)

Repository: https://github.com/Malaeu/chen_q3 (public)

- Branch `rh_clean` holds this task and the previous NB run, `docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/` (commit ba5654b4). Reuse its Gram/Vasyunin code and its optimal e_N values.
- Branch `proshka_inbox_2026-10-31` holds the source: commit 70c4e6b0, `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md` (freeze 6d50c6f9). Read it in full; the sections needed are:
  - §4, (10)–(13): the rational upper Gram G_up and the certificate ê_N;
  - §5–§6: the Möbius taper, the pole coefficient b_N, and the sign-crossing set S = {N ≥ 3 : b_N·b_{N+1} ≤ 0};
  - §7, (24): the core H_N;
  - the Appendix: the reproducible rational construction.
- Output: push to `rh_clean` (or `codex/<name>` + PR into `rh_clean`) per AGENTS.md.

## PART 1 — Certificate ê_N

1. For N in {10, 20, 50, 100, 200}, compute ê_N exactly in rational arithmetic, with K_N = ⌈N^{3/2}⌉. Use Python `fractions` or flint.
2. For N in {500, 1000, 2000}, compute ê_N as a certified interval: Arb/flint, or mpmath with outward rounding.
3. Report:
   - ê_N;
   - the optimal e_N from ba5654b4;
   - the ratio ê_N / e_N;
   - ê_N·log N;
   - a certified YES/NO for ê_N·log N ≤ 1/2.

## PART 2 — Core H_N on S

1. Compute b_N for every N ≤ 10^7 and list the set S ∩ [3, 10^7].
2. Head part of H_N, every N ≤ 10^7, cheap: (1/ℓ²) Σ_{k≤N} |ψ(k) − k·ℓ·s_N|² / [k(k+1)], with ℓ = log N and s_N as in §5–§7 of the source.
3. Full H_N, including the shoulder N < k < K_N with the full divisor formula R_N(k) from (24):
   - for every N ∈ S with N ≤ 10^4;
   - on a log grid of about 100 points with N ≤ 10^4.

   Use floor-block grouping, O(√k) per k, in C++.
4. Report:
   - |S| per decade;
   - max and min of H_N over S, per decade;
   - the head and shoulder parts of H_N, separately;
   - plots of H_N and H_N·log N against N, with S marked.

## JUDGES (build first)

- **J1.** At N ≤ 200, ê_N ≥ e_N exactly; at larger N, the intervals show ê_N ≥ e_N. This is the domination G_∞ ≤ G_up.
- **J2.** At small N (≤ 50), the tail bound (11) holds: ê_N − e_N ≤ the right side of (11) evaluated at the optimum. If the source's inequality does not literally apply to the optimal coefficients, say so and report both numbers.
- **J3.** H_N from (24) equals the direct norm of the taper residual minus the paid tail, to 1e−10, at N ≤ 200.
- **J4 (planted control, compute analytically BEFORE the run).** Replace ψ(k) in the head part by ψ(k) − 2Re(k^ρ/ρ), with ρ = 1/2 + 1/3 + 7i.
  - Expected head-part slope of log H_N against log N on [10^5, 10^7]: ≈ 2/3, minus log factors.
  - First derive the planted prefix analytically and confirm that it has no constant offset. This is the lesson from the last run: its J5 failed on exactly such an offset.
  - If the analytic exponent differs from 2/3, report the correct exponent and use it as the gate. Do not void the unaffected parts.

A judge failure voids only the part it guards, not the whole run.

## PRE-REGISTERED PREDICTIONS (Mythos, before any run; scored after)

| ID | Prediction | p |
|---|---|---|
| P1 | ê_N / e_N ≤ 1.5 for every N ≤ 1000 | 0.6 |
| P2 | ê_N·log N ≤ 1/2 certified for every N ≤ 2000 on the grid | 0.85 |
| P3 | S has at least 10 elements in [3, 10^4], and S is non-empty in every decade up to 10^7 | 0.7 |
| P4 | max H_N over S ∩ [10^3, 10^4] ≤ 1 | 0.75 |
| P5 | The head part of H_N on S decays like c/log N with c ∈ [0.02, 0.3] for N ≥ 10^4 | 0.45 |
| P6 | J4 shows the planted growth with the analytically confirmed exponent | 0.9 |

## OUTPUT

Folder `docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06/`, containing:
- the scripts, run with uv, with an ASCII progress bar with ETA;
- the CSVs;
- the plots;
- PREREGISTRATION.json, committed before any numbers;
- REPORT.md with:
  - the tables;
  - J1–J4;
  - HIT/MISS for P1–P6;
  - every truncation and rounding statement.

Give the commit, the paths and the blobs in the final message.
