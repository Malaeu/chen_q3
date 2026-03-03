/-!
# PrimeCert margin — Path B (analytic) template (v2, factor-4 fixed)

Goal
----
A *data-free* proof of the prime-cap / margin gate that avoids importing any of the
heavy auto-generated PrimeCert chunks (`PrimePowAutoGT10000`, `PrimeGrid`, ...).

Key analytic object
-------------------
We cap the prime operator norm by an RKHS quantity `ρ(t)` defined by the Gaussian-type integral

    ρ(t) := 2 ∫₀^∞ y · exp(y/2) · exp(-4π² t y²) dy.

Closed-form and safe bound
-------------------------
The exact closed-form has an `erf` term. Bounding `erf ≤ 1` yields the clean inequality

    ρ(t) ≤ 1/(4π² t) + √π / (2 (4π² t)^(3/2)) · exp( 1/(64π² t) ).

**Factor-4 sanity check.** Completing the square for `y/2 - a y²` gives the constant
`1/(16a)`. With `a = 4π² t` this is `1/(64π² t)`. (Older drafts sometimes used `1/(16π² t)`.)

Numeric cap we want
-------------------
At `t = 1` the RHS is `< 1/25`, hence `ρ(1) < 1/25`.
This is massively below `c_*/4 = 11/40`, so we have plenty of slack.
-!/

import Q3.Proofs.PrimeCert.PrimeCert_Margin_Spec
import Q3.Proofs.RKHS_PrimeCap_Analytic

-- Optional helpers (use only if you need them)
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Interval

namespace Q3.Proofs.PrimeCert

open Real

/-- Alias the rho from your analytic layer.
Rename this if your file exports it as `ρ` or under a namespace. -/
abbrev rho := Q3.Proofs.RKHS_PrimeCap_Analytic.rho

/-- Closed-form upper bound for `rho t`.

If you already have it in `RKHS_PrimeCap_Analytic`, just `exact` it.
Otherwise prove it from the integral definition by completing the square and bounding
`erf` by `1` (or bounding the Gaussian tail by `√π`).
-/
lemma rho_le_closed_form (t : ℝ) (ht : 0 < t) :
    rho t ≤
      (1 / (4 * Real.pi^2 * t))
      + (Real.sqrt Real.pi) / (2 * (4 * Real.pi^2 * t)^(3/2)) * Real.exp (1 / (64 * Real.pi^2 * t)) := by
  -- TODO: replace with your proven lemma.
  -- Suggested proof sketch:
  --   1) unfold `rho` to an integral of `y * exp(y/2 - 4π² t y²)`.
  --   2) set `a := 4π² t`, complete the square.
  --   3) use the exact primitive (gives `erf`) and bound `erf` by `1`.
  sorry

/-- Numeric cap: `rho 1 < 1/25`.

Clean route:
1) apply `rho_le_closed_form` at `t=1`,
2) close the remaining numeric inequality with `interval`.
-/
theorem rho_one_lt_one_over_twentyfive : rho 1 < (1/25 : ℝ) := by
  have ht : (0 : ℝ) < 1 := by norm_num
  have hbound := rho_le_closed_form (t := (1 : ℝ)) ht
  have :
      (1 / (4 * Real.pi^2 * (1:ℝ)))
      + (Real.sqrt Real.pi) / (2 * (4 * Real.pi^2 * (1:ℝ))^(3/2)) * Real.exp (1 / (64 * Real.pi^2 * (1:ℝ)))
        < (1/25 : ℝ) := by
    interval
  exact lt_of_le_of_lt hbound this

/-- Final bridge: produce the gate proposition from the analytic cap.

Adapt this to your exact `PrimeCertMarginOnBrange` definition.
The only **hard** input you should need in this file is `rho_one_lt_one_over_twentyfive`.
-/
theorem prime_cert_margin_from_pathB : PrimeCertMarginOnBrange := by
  -- Typical pattern:
  --   refine PrimeCertMarginOnBrange.mk ?fields
  --   · show ‖T_P‖ ≤ rho 1      from RKHS layer
  --   · show rho 1 < 1/25       from `rho_one_lt_one_over_twentyfive`
  --   · show 1/25 < c_*/4       from arithmetic (c_* = 11/10)
  --
  -- Keep this proof *data-free*: no imports of prime tables.
  sorry

end Q3.Proofs.PrimeCert
