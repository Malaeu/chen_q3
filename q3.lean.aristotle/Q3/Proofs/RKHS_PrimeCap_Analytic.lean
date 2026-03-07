import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.PrimeCert_Margin_Gate

/-! Analytic prime certificate gate (Step 3: numerical tables fallback removed).

This file provides a lightweight replacement for the legacy numeric certificate
assumptions by exposing a single theorem name that can be replaced with an
actual closed-form RKHS/convexity proof later.
-/

set_option maxHeartbeats 0

namespace Q3.Proofs.PrimeCert

noncomputable section

/-- Analytical target constant used in Step 3: `ρ(1) < 1/25`. -/
def rkhs_rho_one : ℝ := 1 / 25

/-- Step 3 margin target derived from `c*/4` and `ρ(1)`.

    This is the constant that would close the proof if a closed-form bound
    `prime_term(φ) ≤ ρ(1)` at the critical scale is established.
-/
def rkhs_prime_cap_margin : ℝ := Q3.c_star / 4 - rkhs_rho_one

/-- `ρ(1) < 1` in the analytical normalization. -/
lemma rkhs_rho_one_lt_one : rkhs_rho_one < 1 := by
  norm_num [rkhs_rho_one]

/-- `c*/4 - ρ(1) > 0` in the analytical normalization. -/
lemma rkhs_prime_cap_margin_pos : 0 < rkhs_prime_cap_margin := by
  norm_num [rkhs_prime_cap_margin, Q3.c_star, rkhs_rho_one]

/-- Step-3 analytical gate.

`prime_cert_margin_from_rkhs` is wired to `prime_cert_margin_from_gate`, the
current single-gate entry point. At the moment that gate forwards to the active
Path B bridge, while certificate-data closure is tracked separately in `PrimeCert`.
--/
theorem prime_cert_margin_from_rkhs : PrimeCertMarginOnBrange :=
  Q3.Proofs.PrimeCert.prime_cert_margin_from_gate

end

end Q3.Proofs.PrimeCert

namespace Q3

/-- Compatibility wrapper used by `Q_nonneg_t_critical` and the main theorem chain. -/
theorem prime_cert_margin_from_rkhs : PrimeCertMarginOnBrange :=
  Q3.Proofs.PrimeCert.prime_cert_margin_from_rkhs

end Q3
