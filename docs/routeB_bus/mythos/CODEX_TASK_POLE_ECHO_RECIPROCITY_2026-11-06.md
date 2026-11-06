# CODEX TASK (addendum) — pole echo inside E_N: the quantum-modular / “mock” side — 2026-11-06

Repo: https://github.com/Malaeu/chen_q3 · branch `rh_clean`

This addendum runs alongside the task at commit `d665cb6951be32061201366640578d6560cb0420`,
`docs/routeB_bus/mythos/CODEX_TASK_ZERO_SENSITIVE_FAKES_2026-11-06.md` (T0–T2, F1–F3). It does not repeat those systems.
Output dir: `docs/routeB_bus/diag/POLE_ECHO_RECIPROCITY_2026-11-06/`

## Inputs
- Reciprocity verdict (definitions of a_n, q_n, b_N, u_N, E_N, T_N, V, c0 and formulas (1)–(8)): branch `proshka_inbox_2026-10-31`, commit `2cb305016f3f935fa5d9332ba8f9b3c1b0a25d95`, `docs/routeB_bus/proshka/PROSHKA_VERDICT_MOBIUS_RECIPROCITY_2026-11-06_B.md`, blob `f568cd803251872ae9f7a5c7f1058abf03d62170`.
- Bettin–Conrey, *Period functions and cotangent sums*, arXiv:1111.0931v2 / ANT 7 (2013) 215–242: Theorem 1 (reciprocity for c_a) and formulas (13)–(14).
- R8 / thermometer code for E_N on S (S starts at 43297), as already in the repo.

## Why
Bettin–Conrey state that the c0 reciprocity is only *nearly* quantum modular (Zagier). The reason they give: the Eisenstein L-function ζ(s)ζ(s − a) has a pole. Maass analogues have entire L-functions and are strictly quantum modular. E_N = 1 + 2b_N u_N − πT_N is built from exactly this c0. The measurement below asks how much of E_N on S is carried by the pole correction, and how much by the analytic period function ψ0.

## Steps
1. Take Theorem 1 at a = 0 from the source, with every sign as printed. Iterate it along the continued-fraction chain of h/k. This writes c0(h/k) as:
   - (i) the sum of the pole/correction terms, i.e. the limit a → 0 of k^a·aζ(1 − a)/(πh) along the chain;
   - (ii) the sum of the period-function terms ψ0;
   - (iii) the terminal value.
2. Judge J1: the chain formula equals the direct cotangent sum to 1e−12 for all coprime h < k ≤ 2000. If it fails, STOP and report.
3. Through formula (8) of the verdict, split T_N = T_N^pole + T_N^ψ + T_N^term. For each N report all three parts, E_N, 1 − πT_N, and the J_N layer as defined in `PROSHKA_VERDICT_SMOOTH_PROFILE_HARDY_RETURN_2026-11-06_B.md` (commit b227cf63).
4. Values of N: the first 6 elements of S, and 6 non-S values of N of the same size.
   - The work is O(N²) pairs per N; do it in C++ with the chain.
   - If the runtime is too long, reduce to 3+3 values and record that reduction.
5. Control: run the same split for the Dedekind sum s(h, k) (c_{−1}, Zagier's strict "Example 0"). Report the share of the correction term in the whole.
6. Judge J2: E_N from the split equals E_N from the direct R8 formula (1) to 1e−9 for every N reported.

## Preregistration
Commit and push PREREGISTRATION.json with C1–C3 verbatim **before any production run**. Mythos stakes:
- C1: on S, |T_N^pole| ≥ 0.5·|T_N^ψ| for at least 4 of 6 values of N — 0.35
- C2: the sign of T_N^pole is the same for all 6 S-values — 0.55
- C3: on S, the pole part differs from the non-S mean by more than 3 standard deviations of the non-S values — 0.30

## Deliverables
REPORT.md (C1–C3 HIT/MISS by the preregistered criteria; a table of the parts per N), CSV, scripts, ANALYSIS.json, ARTIFACT_BLOBS.json, independent REVIEW.md. Commit and push to `rh_clean`; update docs/Codex/NEXT.md.
