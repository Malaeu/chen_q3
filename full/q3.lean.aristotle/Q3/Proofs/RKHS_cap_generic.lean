/-
Generic RKHS-cap lemma from a weight-sum bound.

This isolates the “Schur/weight_sum” route (Option 2) into a reusable lemma:
if you can bound the weight-sum at a given `t`, you immediately get a Rayleigh
quotient cap for `T_P_comp_real` at the *same* `t`.
-/

import Q3.Proofs.RKHS_cap_rayleigh  -- for `T_P_comp_real_opNorm_le_weight_sum`
import Q3.Proofs.Rayleigh_utils     -- for `RayleighQuotient_le_opNorm`

set_option linter.mathlibStandardSet false

open scoped BigOperators

noncomputable section

namespace Q3.Proofs

open Q3

/-- Generic cap: a weight-sum bound implies a Rayleigh-quotient bound at the same `t`. -/
lemma rkhs_cap_rayleigh_of_weight_sum (K B t rho : ℝ) [Fintype (Q3.Nodes K)]
    (h_weight_sum :
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ ≤ rho) :
    ∀ (M : ℕ) (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t M) v ≤ rho := by
  intro M v hv
  have hnorm :
      ‖Q3.T_P_comp_real K B t M‖ ≤
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ :=
    T_P_comp_real_opNorm_le_weight_sum (K := K) (B := B) (t := t) (M := M)
  have hRayleigh :
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t M) v ≤
        ‖Q3.T_P_comp_real K B t M‖ :=
    RayleighQuotient_le_opNorm (A := Q3.T_P_comp_real K B t M) (v := v) hv
  exact le_trans hRayleigh (le_trans hnorm h_weight_sum)

end Q3.Proofs
