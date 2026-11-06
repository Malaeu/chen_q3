# CODEX TASK — PRIME-PROPERTY ABLATION: WHICH PROPERTY CARRIES √-CANCELLATION? (2026-11-06)

Repository: https://github.com/Malaeu/chen_q3 (public)

Branch `rh_clean` holds:
- this task;
- the dictionary `docs/routeB_bus/mythos/PRIME_PROPERTIES_VS_ZEROS_DICTIONARY_2026-11-06.md` (same commit), §3;
- the sieve and Kahan infrastructure in `docs/routeB_bus/corner_thermometer_2026-11-04/` (commit a33870cb).

Result: push to `rh_clean` per AGENTS.md.

## Systems

All prime-like sequences are increasing real numbers > 1. The generalised integers are their multiplicative semigroup, enumerated up to X_max with multiplicities.

| System | Definition |
|---|---|
| S0 | True primes |
| S1 | Cramér–Beurling. Each integer m ≥ 3 is a "prime" independently with probability 1/log m. Use 5 seeds. |
| S2 | Hybrid: true primes ≤ y, Cramér primes above y, for y ∈ {10², 10³, 10⁴}. Use 3 seeds. |
| S3 | Perturbed primes q_p = p·(1 + ε_p), with ε_p uniform in [−1/(10 log p), +1/(10 log p)]. Use 3 seeds. |
| S4 | True integers with a random completely multiplicative-on-squarefree sign: f(p) = ±1 independently, f(n) = Π f(p) for squarefree n, f(n) = 0 otherwise. Use 5 seeds. |
| S5 | Liouville λ(n) on the true integers. |

For S0–S3 the Möbius function of the system is μ_P. For S4 and S5 use f and λ directly.

## Measurements

X_max = 10^7 for every system; additionally 10^8 for S0, S4 and S5. Report:

1. M(x) = Σ_{n≤x} μ_P(n), or the corresponding f / λ sum.
2. W(X) = (1/log X) ∫_1^X (M(x)/x)² dx on a log grid of X.
3. Quantiles of M(x)/√x on log-uniform samples.
4. Sign changes of M per decade.
5. The log-scale variance of M(x)/√x per decade.
6. For S1–S3: the counting error N_P(x) − ρx of the generalised integers, so we know whether the "integers" of the fake are RH-quality.

## Judges (build first)

- **J1.** S0 reproduces published M(10^k) (OEIS A084237) for k ≤ 7, or k ≤ 8 where run.
- **J2.** S5 reproduces published L(x) values, including the first positive L(x) at x = 906150258 if X reaches it. Otherwise check L(10^k) against OEIS A090410.
- **J3.** For S1, the generalised-integer counting function N_P(x)/x converges, i.e. the semigroup enumeration is correct. Check this on small X against brute force.
- **J4, planted control.** Add the term 0.05·x^{0.8}·cos(7 log x), recentred so that its prefix integral has no constant offset, to the S0 M(x). W(X) of the planted series must grow visibly: log-slope ≥ 0.4 on [10^5, 10^7]. Derive the expected slope analytically BEFORE the run.

## Pre-registered predictions (Mythos, before any run)

| ID | Prediction | p |
|---|---|---|
| A1 | S0 W(X) stays in [0.01, 1] on [10^3, 10^8] with no upward log-trend | 0.8 |
| A2 | S4 (random signs) W(X) is bounded on the grid and **smaller** than S0 on average, in line with Harper's "better than √" | 0.55 |
| A3 | S1 (Cramér–Beurling) W(X) is bounded on the grid. Random fakes look RH-like. | 0.6 |
| A4 | S5 (Liouville) W(X) is dominated by the Pólya bias: mean of L(x)/√x ≈ 1/ζ(½) ≈ −0.68 on log samples, within ±0.15 | 0.7 |
| A5 | Some system differs from S0 in the W-trend at log-slope level > 0.1. Ablation discriminates numerically. | 0.35 |

## Output

Folder `docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/`, containing:
- PREREGISTRATION.json, committed first;
- scripts (uv, ASCII progress with ETA);
- CSVs per system and seed;
- plots of W(X) for all systems on one log axis, and M/√x histograms;
- REPORT.md with J1–J4, HIT/MISS for A1–A5, and every truncation stated.

Give the commit, the paths and the blobs in the final message.
