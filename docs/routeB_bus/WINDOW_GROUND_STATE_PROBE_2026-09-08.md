# Window ground-state probe: is the lowest mode of A_a even and simple at a = 0.8? (2026-09-08, owner's «Го»)

Status: DIAGNOSTIC_NEVER_A_PROOF, floating point (sc_build.py, single centre, half-width a, Legendre degrees < K, full Weil
form incl. the pole term, no constraints; overlap() now Gauss–Legendre, regression three-lobe floor 0.9663482407 unchanged).
Raw: docs/routeB_bus/phase5_codex/six_centre/out/window_ground_state.json.

## Numbers (λ_even, λ_odd = lowest eigenvalue in each parity sector; K = 36 unless noted)
| a | active atoms | λ_even | λ_odd | ground parity | Rayleigh of Φ·1_{(−a,a)} | Φ mass outside (−a,a), rel. |
|---:|---|---:|---:|---|---:|---:|
| 0.3 | none | +7.57e−3 | +2.23e−1 | EVEN, simple, gap 0.215 | — | — |
| 0.5 | 2 | +1e−6 | +2e−4 | EVEN | 7.0e−4 | 8.5e−4 |
| 0.8 | 2,3,4 | ≈ 0 (2.7e−14 at K=24) | ≈ 0 | degenerate cluster | 8.8e−9 | 5.9e−9 |
| 1.0 | 2,3,4,5,7 | ≈ 0 (±1e−16) | ≈ 0 | degenerate cluster | 2.3e−11 | 6e−15 |
| 1.3 | …13 | ≈ 0 (±3e−15) | ≈ 0 | degenerate cluster | 7.2e−8 (K-limited) | 3e−16 |
Overlap of the numerical ground vector with the cut-off theta test Φ·1_{(−a,a)}: 0.991 (a = 0.5), 0.999 (0.8), 0.998 (1.0).

## Readings
1. **ЕСЛИ_B.** Beyond a ≈ 0.5 the window ground state is not an isolated even mode: it is the cut-off theta null test Φ
   (overlap 0.999 at a = 0.8), and the next eigenvalues are equally ≈ 0 (cut-offs of ∂Φ, ∂²Φ, …). Parity of «the» lowest
   mode is meaningless there; the first-touch lemma cannot lean on Suzuki's small-a «even and simple» (Thm 1.4 holds at
   a = 0.3: even, simple, gap 0.215 — reproduced).
2. **An explicit unconditional upper bound on the window floor:** λ_a ≤ Q[Φ·1_{(−a,a)}]/‖Φ·1_{(−a,a)}‖², and Q of the cut
   test is of the order of the mass of Φ outside the window, i.e. doubly exponentially small: ≈ e^{−πe^{2a}} up to
   polynomial factors (Φ(x) ~ e^{9x/2}e^{−πe^{2x}}). Numerically 7e−4 (a = 0.5), 9e−9 (0.8), 2e−11 (1.0). Under RH
   0 < λ_a ≤ this; the window floors are ≈ 0 from a ≈ 0.6 on. This sharpens ALIGN (A30)/SCREW (S22) for windows with an
   explicit rate, and explains the certification wall: Zhu's floor 8.9e−18 at a = 0.8 (Thm 1.2) sits below a true floor of
   order 1e−9…1e−14, and a = 1.19 would need ~1e−15…1e−30 resolution — the withdrawn L = 1.19 claim was fighting a doubly
   exponential. (Observer's reading, PAPER-level for the bound, numerics for the scale.)
3. Numerical sign resolution at a ≥ 1 is impossible in double precision (λ_min = −1.7e−16, −3.2e−15 are roundoff, not
   witnesses — rule: a straddling value is not a verdict). Any first-touch statement is purely analytic.

## Consequence for the candidate (rule 19)
The candidate «first-touch rigidity with an even ground mode» loses its crutch: p drops from 0.15 to 0.05. What survives
and sharpens: the window floor is governed by the theta null family's cut-off mass; a first touch, if it exists, happens
at a doubly-exponentially small level invisible to numerics, and the lemma must be proved from the zero-mode equation
A_a v = 0 with v ≈ a cut-off of the null family. Cheapest next probe (hours): the a-derivative of λ_a on the Legendre space
compared with the derivative of the cut-off mass — does λ_a track the null family's tail exactly (ЕСЛИ_A: λ_a = tail mass
× (1 + o(1)), the window problem is «how much of Φ sticks out»; ЕСЛИ_B: λ_a decays faster — the window finds better null
combinations, and the relevant object is the whole cut-off span of {g_k}).
