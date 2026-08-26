# STATUS: EDGE_TOP_PREFLIGHT — TOP FUNCTIONAL IS EXPONENTIALLY NEGLIGIBLE (probe law T ~ e^{-pi lam^2/4}); READING A CONFIRMED BEYOND THE CLAIM; SUPPLIER SHAPE FOR LEAN NEEDS ADJUDICATION

```yaml
ARTIFACT_CLASS: LINUX_EDGE_TOP_PREFLIGHT
GOAL: GOAL_058
GAP: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE (verdict c47b75a8)
DISCRIMINATOR: TOP_BUDGET_SQUARED_OVER_PHYSICAL_BANDWIDTH
DISCRIMINATOR_OUTCOME: PASS_NUMERICALLY_WITH_EXPONENTIAL_MARGIN — Lean supplier shape open
PROBE: scripts/edge_slope_probe.py (DIAGNOSTIC_NEVER_A_PROOF)
AUTHOR_BODY: LINUX_CLAUDE (LINUX_STANDING_GRANT_2026-08-25)
RH_CLAIM: false
```

## 1. The probe (committed objects, not a model)

`scripts/edge_slope_probe.py` builds the committed even prolate Ferrers
mode from the EXACT committed three-term recurrence
(`D0Mode4PSWFLegendreRecurrenceCrosswalk`), including the committed
`(-1)^q` of `mode4FerrersTerm` (one probe iteration was burned on omitting
it — the sign conjugation preserves the spectrum and destroys the
function; recorded as a warning for any future numeric consumer of the
recurrence).  Certification: ODE residual 1e-8..1e-6 in the bulk;
eigenvalue ladder `chi_n/m -> (4n+1)*2pi` exact to 4 digits; the anchored
mode matches the cylinder target with sup-error `0.021/lam^2` at BOTH
m = 64 and m = 256 — **the F72.6 C0 input family is numerically TRUE with
constant C ~ 0.021.**

## 2. Findings

1. **My registered polynomial amplification (delta'(edge) ~ C*lam) is DEAD.**
   The uniform-C0 flux argument was sound but not sharp: the defect
   derivative is not uniformly C0-sized near the edge — it is
   Gaussian-dead there.  Measured: |delta'(y)| falls like the Gaussian
   envelope from 1e-4 at y ~ 1 to the float floor (1e-14..1e-16) for all
   y >= 0.45*lam; at the window edge it is invisible at float64 (true
   value ~ e^{-c*lam^2}).
2. **The top functional obeys the law `T_k ~ e^{-pi*lam^2/4}`.**  Both
   pre-floor points match it: m=16: T = 2.75e-6 vs e^{-pi*16/4} = 3.4e-6;
   m=32: T = 1.67e-11 vs e^{-pi*32/4} = 1.2e-11.  Beyond m=32 the float
   floor (~1e-13) is reached.
3. **Mechanism, two elementary halves:**
   (a) ARITHMETIC: the top lattice point always satisfies
       `y_top > lam/2` — for u > lam/2 it is y_top = u > lam/2; for
       u <= lam/2 it is y_top > lam - u >= lam/2.  No analysis involved.
   (b) ANALYTIC: on y >= lam/2 the defect derivative carries the
       forbidden-region/Gaussian envelope of the mode (turning scale of
       the committed mode is y ~ O(1), like the cylinder target).
4. P_WC_TOP_1 (0.72): CONFIRMED in strengthened form — not merely
   bandwidth-negligible but exponentially so.

## 3. The honest Lean gap

The committed UNIFORM C0 rate `|delta| <= C/lam^2` does NOT prove (3b):
through the flux representation it yields only `|delta'(y_top)| <= C*lam`
and `T_k = O(lam^{2.5})` — insufficient for `T_k = o(lam^{1/2})`.  The
exponential regime needs a GAUSSIAN-ENVELOPE supplier on the outer
half-window.  Candidate minimal shapes (adjudication requested):

  (E1) OUTER-GAUSSIAN C0: eventually, for y in [lam/2, lam]:
       |c*S_phys(y) - W(y)| <= C * exp(-y^2/4).
       Then the flux route (F(lam)=0, F' = -r, both r-terms
       Gaussian-enveloped on the outer half) gives
       |delta'(y_top)| <= C' * lam^3 * e^{-lam^2/16}-type bounds and
       T_k^2/bandwidth -> 0 with exponential margin.  This is a
       C0-CLASS statement (no derivative), same object family as F72.6,
       plausibly sourceable from the same Satz-9/CCM analysis on the
       outer region — or numerically it even holds with C ~ C_{F72.6}.
  (E2) OUTER-GAUSSIAN mode bound only: |S_phys(y)| <= C*e^{-y^2/4} on
       [lam/2, lam] (the cylinder part is explicit; the defect inherits).
       Slightly weaker to state, same consumer.
  (E3) Direct coefficient route: edge smallness of the alternating sums
       sum (-1)^q a_q (2q)(2q+1)-type rows via the committed tail
       contraction — TRUE but exponential-cancellation-shaped; judged
       expensive in Lean; NOT preferred.

Consumer once (E1) or (E2) lands: y_top > lam/2 (arithmetic lemma) +
envelope at y_top + explicit x-integral of sqrt(u)*lam*C*e^{-lam^2/16}
=> T_k <= C''*lam^{3/2}*e^{-lam^2/16}, and T_k^2 * bandwidth^{-1} -> 0
trivially.  Zero further inputs.

CLOSES: EDGE_TOP_DISCRIMINATOR_NUMERIC (PASS, exponential),
        MY_POLYNOMIAL_EDGE_AMPLIFICATION_FORK (retracted)
OPENS:  W5_DEFECT_OUTER_GAUSSIAN_ENVELOPE (single named supplier, shape E1/E2 pending adjudication)
CARRIES_OPEN: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE (until the envelope lands)
