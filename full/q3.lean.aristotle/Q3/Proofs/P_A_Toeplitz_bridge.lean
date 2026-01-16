/-
P_A Toeplitz Bridge: Connect A3_FLOOR (P_A ≥ c*) with Rayleigh_Fourier

This module bridges:
- A3_FLOOR_v22_stage4_floor.P_A_ge_c_star : P_A(B_min, t_sym, θ) ≥ 11/10 for θ ∈ [-1/2, 1/2]
- Rayleigh_Fourier.rayleigh_lower_bound_real : RQ(ToeplitzFourier P) ≥ inf(P)

Result: RQ(ToeplitzFourier P_A) ≥ c_star

Integration: change-durch: claude-code 2026-01-16 P_A_Toeplitz_bridge
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.A3_bridge_rayleigh_first  -- t_rkhs_cap, one_le_t_rkhs_cap, c_star_div_four_le_sub_rho_one
import Q3.Proofs.RKHS_cap_rayleigh         -- rkhs_cap_rayleigh_tcap
import Q3.Proofs.Rayleigh_utils            -- RayleighQuotient_sub_ge
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.P_A_Bridge

open Q3.Proofs  -- access t_rkhs_cap, rkhs_cap_rayleigh_tcap, RayleighQuotient_sub_ge, etc.

/- P_A is the periodized windowed archimedean symbol.
   P_A(B,t,θ) = 2π Σ_{m∈ℤ} g(B,t,θ+m) where g = a · w (Fejér×heat window).

   Continuity is currently assumed in `A3_FLOOR_v22_stage4_floor` as
   `P_A_continuous`. -/

/-- Bridge lemma: Apply Rayleigh lower bound to P_A.
    Uses P_A_ge_c_star from A3_FLOOR and rayleigh_lower_bound_real from Rayleigh_Fourier. -/
lemma P_A_rayleigh_lower_bound
    (M : ℕ) (hM : M > 0)
    (v : Fin M → ℝ) (hv : v ≠ 0) :
    Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real M (P_A B_min t_sym)) v ≥ c_star := by
  have hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), c_star ≤ P_A B_min t_sym θ := by
    intro θ hθ
    exact P_A_ge_c_star hθ
  exact RayleighFourier.rayleigh_lower_bound_real
    (M := M) (hM := hM)
    (P := P_A B_min t_sym) (hP_cont := P_A_continuous)
    (m := c_star) (hP_ge := hP_ge)
    (v := v) (hv := hv)

/-- Specialized version for M = 2*M' + 1 (symmetric frequency window). -/
lemma P_A_rayleigh_lower_bound_odd
    (M' : ℕ)
    (v : Fin (2 * M' + 1) → ℝ) (hv : v ≠ 0) :
    Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M' + 1) (P_A B_min t_sym)) v ≥ c_star := by
  have hM : 2 * M' + 1 > 0 := by omega
  exact P_A_rayleigh_lower_bound (2 * M' + 1) hM v hv

/-- A3 bridge data using Fourier Toeplitz with P_A symbol.
    This is the CORRECT formulation (Fourier coefficients, not sampling). -/
def A3_bridge_data_rayleigh_Fourier (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Q3.Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        Q3.RayleighQuotient
            (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
             Q3.T_P_comp_real K K t M) v
          ≥ Q3.c_star / 4

/-- Bridge from weight_sum bound to A3_bridge_data_rayleigh_Fourier.
    Uses P_A_rayleigh_lower_bound and RKHS cap. -/
lemma A3_bridge_rayleigh_from_weight_sum_P_A (K : ℝ)
    (h_weight_sum :
      ∀ [Fintype (Q3.Nodes K)],
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one) :
    A3_bridge_data_rayleigh_Fourier K := by
  intro hK _inst
  refine ⟨t_rkhs_cap, by linarith [one_le_t_rkhs_cap], ?_⟩
  intro M v hv
  -- Rayleigh lower bound for Fourier Toeplitz with P_A
  have hT :
      Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym)) v
        ≥ c_star := by
    have hM : 2 * M + 1 > 0 := by omega
    exact P_A_rayleigh_lower_bound (2 * M + 1) hM v hv
  -- RKHS cap
  have hP :
      Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one := by
    have h_weight_sum' :
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one := h_weight_sum
    exact rkhs_cap_rayleigh_tcap (K:=K) (B:=K) (h_weight_sum:=h_weight_sum') M v hv
  -- Combine via subtraction
  have hsub :
      Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
           Q3.T_P_comp_real K K t_rkhs_cap M) v
        ≥ c_star - rho_one := by
    exact RayleighQuotient_sub_ge
      (A:=RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym))
      (B:=Q3.T_P_comp_real K K t_rkhs_cap M) (v:=v)
      (a:=c_star) (b:=rho_one) hT hP
  exact le_trans c_star_div_four_le_sub_rho_one hsub

end Q3.Proofs.P_A_Bridge
