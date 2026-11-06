# CODEX TASK (addendum 2) — balanced Green form Z_N: real-μ values on S, non-vacuity against fakes — 2026-11-06

Repo: https://github.com/Malaeu/chen_q3 · branch `rh_clean`
Runs alongside:
- `docs/routeB_bus/mythos/CODEX_TASK_ZERO_SENSITIVE_FAKES_2026-11-06.md` (commit `d665cb6951be32061201366640578d6560cb0420`)
- `docs/routeB_bus/mythos/CODEX_TASK_POLE_ECHO_RECIPROCITY_2026-11-06.md` (commit `3a872ae77ddc02462d698422a6342d34ea9daab1`)

Output dir: `docs/routeB_bus/diag/BALANCED_Z_NONVACUITY_2026-11-06/`

## Source object
Branch `proshka_inbox_2026-10-31`, commit `a337b335777c3912694fb058a68a019c47061ffe`,
`docs/routeB_bus/proshka/PROSHKA_VERDICT_BLOCK_B_MULTISCALE_2026-11-06_C.md`, blob `692b10822320c76a8d2c9a82168bb5c35f124d4b`.
Use exactly:
- definition (16) of Z_N = Z_(N,T) with the tent kernel κ;
- the window formula (11), which needs O(T) operations after A_N is built;
- the finite transfer (17): E_N ≤ 14 Z_N + 9/L², Z_N ≤ 30 E_N + 135/L²;
- the cutoff cost 4Q²/T;
- the initial-square expression (18).

The receiver is (20): Z_N ≤ C for an unbounded part of S. S is as in R8 (S = {N : b_N b_(N+1) ≤ 0}, first element 43297).

## Why
AutoIP lesson (Clason–Helin–Nursultanov–Oksanen, as reported): a formally correct hypothesis can be satisfiable only trivially. Before (20) goes back to Proshka as the target, check two things:
- (a) it holds numerically where it should, on the real μ on S;
- (b) the same object visibly fails on sources where RH is false or the head identity is broken.

## Steps
1. **Judge J1.** Reproduce the table in §9 of the verdict: N = 3, 8, 16, 32, 64, T = N², Z_N and E_N to ≥ 12 digits.
2. **Real μ (T0).**
   - N values: the first 8 elements of S, plus 8 non-S values of N of the same size, plus N = 10³, 3·10³, 10⁴, 2·10⁴.
   - Primary cutoff T = N², using a segmented divisor sieve for A_N(ℓ) and prefix sums per window.
   - If T = N² is infeasible for the largest values, use T = N²/L² and record the paid cost 4Q²/T beside every value.
   - Report Z_N, E_N, Z_N·L, and the split of Z_N into:
     - the initial square ℓ, k ≤ N, i.e. (18);
     - the cross band (ℓ ≤ N < k ≤ 2N or symmetric);
     - the outer part ℓ, k > N.
3. **Fakes, same code, same N grid (non-S N only, since S is defined by the real μ).**
   - F1: μ_DH = the Dirichlet inverse of the Davenport–Heilbronn coefficients from d665cb69, placed on ordinary integers.
   - F3: μ of the integer-rounded planted-zero system from d665cb69, amplitude 0.2.
   - S4: random multiplicative signs, seeds 4401–4405 from the ablation.
   - R9 bad array from `PROSHKA_VERDICT_ROUND9_2026-11-06_B.md` (commit b5fc098b).
   - Proshka §8 states that for DH and DMV the ordinary r_n / floor is not their own Mellin-null dictionary. These runs therefore measure what the real-μ certificate does with a wrong source; they are not a test of the fakes' own NB criterion. Say this in the REPORT.
4. **Growth.** For every source, fit the OLS slope of log Z_N on log N over the grid. Plot all sources on one log–log plot.
5. **Judge J2.** For N ≤ 64, the window formula (11) equals the direct double sum (16) to 1e−9 (relative).

## Preregistration
Commit and push PREREGISTRATION.json with D1–D4 verbatim **before any production run**. Mythos stakes:
- D1: T0, Z_N ≤ 0.3 for every computed N ∈ S — 0.80
- D2: F1, the slope of log Z_N on log N is ≥ 0.2 — 0.60
- D3: T0 on S, the initial square (18) is < 50% of Z_N for at least 6 of 8 values — 0.55
- D4: T0 on S, Z_N·L has coefficient of variation < 30% — 0.50

## Deliverables
REPORT.md (D1–D4 HIT/MISS by the preregistered criteria; tables per source; split table; growth plot), CSV, scripts, ANALYSIS.json, ARTIFACT_BLOBS.json, independent REVIEW.md. Commit and push to `rh_clean`; update docs/Codex/NEXT.md.
