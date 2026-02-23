/-
Off-diagonal exponential sum bridge (compatibility wrapper)
=========================================================

This module exposes `Q3.off_diag_exp_sum_closed` for active bridge imports.
-/

import Q3.Axioms

namespace Q3

/-- Compatibility theorem with the exact signature used by bridge modules. -/
theorem off_diag_exp_sum_closed (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    [Fintype (Nodes K)]
    (i : Nodes K) :
    ∑ j : Nodes K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0) ≤ S_K K t :=
  off_diag_exp_sum_axiom K t hK ht i

end Q3
