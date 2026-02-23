/-
One-scale Fourier A3 bridge (scaffolding)
========================================

This module is the “железобетон” antidote to the legacy two-scale mismatch:
it states/proves the bridge at a *single* heat parameter `t`.

What remains (outside this file) is to actually provide:
  (1) a floor bound `P_A(B_min,t,θ) ≥ c_star` on θ ∈ [-1/2,1/2], and
  (2) a weight-sum cap for the *same* `t`.
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.Rayleigh_utils
import Q3.Proofs.A3_Floor_Bounds  -- for `B_min`
import Q3.Proofs.A3_Floor_Main    -- for definition `P_A`
import Q3.Proofs.P_A_Properties   -- for `P_A_continuous_of_t`

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.P_A_Bridge.OneScale

open Q3

/-- Rayleigh lower bound for Fourier Toeplitz, given a pointwise floor on the symbol. -/
lemma P_A_rayleigh_lower_bound_of_floor
    (t : ℝ)
    (hP_cont : Continuous (P_A B_min t))
    (hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), c_star ≤ P_A B_min t θ)
    (M : ℕ) (hM : M > 0)
    (v : Fin M → ℝ) (hv : v ≠ 0) :
    Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real M (P_A B_min t)) v ≥ c_star := by
  exact RayleighFourier.rayleigh_lower_bound_real
    (M := M) (hM := hM)
    (P := P_A B_min t) (hP_cont := hP_cont)
    (m := c_star) (hP_ge := hP_ge)
    (v := v) (hv := hv)

/-- One-scale A3 bridge datum: the same `t` is used in `P_A` and `T_P_comp_real`. -/
def A3_bridge_data_rayleigh_Fourier_at (K t : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Q3.Nodes K)], ∀ M : ℕ,
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t) -
           Q3.T_P_comp_real K K t M) v
        ≥ Q3.c_star / 4

/-- Assemble the one-scale bridge from:

* an A3 floor bound for `P_A(B_min,t,θ)` (arch side), and
* a weight-sum cap for `T_P_comp_real(K,K,t)` (prime side).
-/
axiom A3_bridge_rayleigh_at_from_weight_sum_P_A (K t rho : ℝ)
    (h_floor : c_star / 4 ≤ c_star - rho)
    (hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), c_star ≤ P_A B_min t θ)
    (h_weight_sum :
      ∀ [Fintype (Q3.Nodes K)],
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t (Q3.xi_n n)) : ℂ)‖ ≤ rho) :
    A3_bridge_data_rayleigh_Fourier_at K t

end Q3.Proofs.P_A_Bridge.OneScale
