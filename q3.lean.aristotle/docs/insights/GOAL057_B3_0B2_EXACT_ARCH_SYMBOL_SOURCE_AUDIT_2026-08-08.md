# Goal 057 B3.0B2 exact arch-symbol source audit (in progress)

Source lock: `c3885e03b67c9cf8c6361d3d451c1404ca565709`.

1. The exact source multiplier is
   `hPlus(t) = -log pi + Re (digamma (1/4 + i*t/2))`.
2. A temporary Lean audit compiled the exact scaling crosswalk
   `hPlus(t) = -Q3.a_star (t/(2*pi)) / (2*pi)`.
3. `Q3.re_digamma_remainder_bound_stieltjes` already gives a global
   sorry-free complex-digamma remainder bound on `Re z > 0`; the source line
   `z = 1/4 + i*t/2` satisfies that hypothesis for every real `t`.
4. `a_star_abs_le_stieltjesLogEnvelope` already proves the corresponding
   global `a_star` bound, but it lives inside the 9,107-line Step33
   `PSD_CenteredCoeffAnalyticABoundsBackend` and is not an acceptable Route B
   dependency.
5. The 507-row `capability` table returns zero hits for `digamma`, `a_star`,
   `stieltjes`, and `log envelope`; semantic search did find the hidden
   supplier through the Step33 monitor.  The earlier B3.0B audit was therefore
   factually stale, not mathematically blocked.
6. Dependency decision: allowlist the live foundational supplier
   `Q3.DigammaRemainder`; exclude the generated PSD/Step33 backend.
7. Minimal candidate: one bounded Route B file defining the exact source
   multiplier, proving the scaling identity, and deriving one global
   `exists C > 0` absolute domination by `vModeLogGrowthEnvelope` directly
   from the Stieltjes theorem.
8. Keep separate: exact-symbol domination is not yet a source Weil form,
   associated operator graph, operator-domain theorem, compression,
   checkpoint closure, H4a1b, promotion, PX, or RH.

Status: `IN_PROGRESS_AWAITING_SAME_CHAT_PROSHKA_RELEASE`.
