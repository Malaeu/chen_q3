# PROSHKA REQUEST — ROUND 6 ADDENDUM FOR A SECOND, INDEPENDENT ATTEMPT (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3

Branches:
- `rh_clean` holds this file and the Round-6 brief. The brief is `docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND6_FORWARD_ARROW_2026-11-05.md`, commit 7db22a05, blob addf2184.
- `proshka_inbox_2026-10-31`: write the verdict as `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_C.md`. Use suffix `_C`; `_B` is taken.

This addendum adds inputs and one diversification idea. The Goal (prove RH) and the Acceptance list of the Round-6 brief are unchanged.

## NEW INPUTS (proshka_inbox_2026-10-31)

1. **Your own Round-4 curvature verdict.** Commit 1de8ebb2 (freeze 6a1a879a), `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND4_DAMPING_CURVATURE_2026-11-05.md`.
   - The Poisson-kernel square (2) and the monotonicity (3) hold for δ > 1/2. In that region every kernel width δ − a_ρ is positive because of the known strip.
   - The step down to the critical line is blocked by the unpaid term in (4). Under RH the factorization exists, so it is RH-equivalent.
   - Owner's reading: along the δ-flow, the square survives exactly as far as positivity of the widths is known, that is, as far as a zero-free region is known. This is the wrong arrow again.
   - Consequence for Round 6: the **δ-curvature square (1)/(3) used as the whole chain** is added to Acceptance item 6 ("Forbidden as the whole chain").
2. **The parallel attempt B.** Freeze c89977f6, `docs/routeB_bus/proshka/PROSHKA_FREEZE_ROUND6_FORWARD_ARROW_2026-11-05_B.md`.
   - Its additive link is the theta identity θ(x) = x^{−1/2}θ(1/x) obtained by Poisson summation over ℤ, together with the Gram form ∫Φ(u)|S_m z(u)|²du.
   - It pre-registers a planted-quartet kernel test Φ_plant = Q(−d/du)Φ with a = 1/3, γ = 100.
   - Read it so that you do not duplicate it.

## OWNER'S PRACTICAL IDEA (an idea, not an order)

Attempt B uses the theta/Poisson link, which is Pólya's territory. Two independent attempts are worth more if their additive links differ. Consider an additive input other than the Jacobi theta identity, for example:
- additive characters and Fourier analysis on ℤ/q, including Ramanujan sums;
- the large sieve inequality, which is a Gram/PSD statement built from additive characters and integer spacing;
- the Montgomery–Vaughan Hilbert inequality, a PSD statement driven by the spacing of the frequencies log n, which works for log of integers;
- Kronecker / Guth–Maynard-type control of aligned prime phases.

Whichever link you choose, Acceptance item 5 still applies: name the link where the chain breaks for DMV and for the planted quartet, and show that it runs for the curve over 𝔽₃.
