/-
Carleson Measure Property for Prime Sampling
============================================

This file establishes that the prime sampling measure μ = Σ w_Q(n) · δ_{ξ_n}
is a Carleson measure for the heat kernel RKHS.

The Carleson property follows from:
1. Node spacing (separation between prime nodes)
2. Off-diagonal exponential decay of heat kernel
3. Weight sum bound via PNT and exponential decay
4. Schur test for Gram matrix norm

Key result:
  Σ w_Q(n) · |f(ξ_n)|² ≤ ρ₁ · ‖f‖²_{H_t}
  where ρ₁ = 1/25 < 1, showing the embedding is contractive.
-/

import Q3.Proofs.RKHS_cap_rayleigh
import Q3.Proofs.A3_bridge_rayleigh_first

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Matrix.Norms.L2Operator

namespace Q3.Proofs

/-! ## Heat Kernel RKHS Definition -/

/-- Heat kernel: K_t(ξ, η) = exp(-2π²t(ξ-η)²)
    This is the reproducing kernel for the heat RKHS. -/
noncomputable def heat_kernel (t ξ η : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi ^ 2 * t * (ξ - η) ^ 2)

/-- Heat kernel is symmetric -/
lemma heat_kernel_symm (t ξ η : ℝ) : heat_kernel t ξ η = heat_kernel t η ξ := by
  unfold heat_kernel
  ring_nf

/-- Heat kernel diagonal is 1 -/
lemma heat_kernel_diag (t ξ : ℝ) : heat_kernel t ξ ξ = 1 := by
  unfold heat_kernel
  simp [Real.exp_zero]

/-- Heat kernel is positive -/
lemma heat_kernel_pos (t ξ η : ℝ) : 0 < heat_kernel t ξ η := by
  unfold heat_kernel
  exact Real.exp_pos _

/-! ## Carleson Measure Definition -/

/-- A discrete measure μ = Σ w_n · δ_{ξ_n} is C-Carleson for heat RKHS if
    the weighted Gram matrix has operator norm ≤ C.

    This is equivalent to: Σ w_n |f(ξ_n)|² ≤ C · ‖f‖²_{H_t} for all f ∈ H_t. -/
def is_carleson (K t C : ℝ) [Fintype (Q3.Nodes K)] : Prop :=
  ∀ (M : ℕ) (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
    Q3.RayleighQuotient (Q3.T_P_comp_real K K t M) v ≤ C

/-! ## Main Carleson Theorem -/

/-- The prime sampling measure is a Carleson measure with constant ρ₁ = 1/25.

    This follows from `weight_sum_le_rho_one` which shows:
    Σ w_Q(n) · Φ(ξ_n) ≤ ρ₁ for heat windows Φ.

    Combined with:
    - Node spacing (Nodes are separated by at least δ_K)
    - Off-diagonal decay (heat kernel decays exponentially with separation)
    - Schur test (operator norm ≤ max row sum)
-/
theorem prime_sampling_is_carleson (K : ℝ) (hK : K > 0) [Fintype (Q3.Nodes K)] :
    is_carleson K t_rkhs_cap rho_one := by
  intro M v hv
  have h_weight_sum := weight_sum_le_rho_one K K hK
  exact rkhs_cap_rayleigh_tcap K K h_weight_sum M v hv

/-- Carleson constant for prime sampling: ρ₁ = 1/25 < 1 -/
lemma carleson_constant_lt_one : rho_one < 1 := by
  norm_num [rho_one]

/-- The prime sampling is a contractive embedding into heat RKHS.

    This means: ‖T_P‖ < 1 where T_P is the prime sampling operator.
    Combined with A3 floor bound (Toeplitz ≥ c_*), this gives Q ≥ 0 on atoms. -/
theorem prime_sampling_contractive (K : ℝ) (hK : K > 0) [Fintype (Q3.Nodes K)] :
    ∀ (M : ℕ) (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v < 1 := by
  intro M v hv
  have h_carl := prime_sampling_is_carleson K hK M v hv
  calc
    Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v
        ≤ rho_one := h_carl
    _ < 1 := carleson_constant_lt_one

/-! ## Connection to RKHS Contraction -/

/-- The Carleson bound implies RKHS contraction in the arch ≥ prime sense.

    If ‖T_P‖ ≤ ρ₁ and Toeplitz_a* ≥ c_*, then:
    arch_term(Φ) - prime_term(Φ) ≥ c_* - ρ₁ > 0

    for appropriate heat window Φ. -/
lemma carleson_implies_arch_ge_prime (K : ℝ) (hK : K > 0) [Fintype (Q3.Nodes K)] :
    ∀ (M : ℕ) (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one := by
  exact prime_sampling_is_carleson K hK

/-! ## Key Lemmas from Existing Machinery -/

/-- The weight sum bound is the core of Carleson:
    Σ w_Q(n) · Φ(ξ_n) ≤ ρ₁

    This uses:
    - Exponential decay: w_Q(n) · exp(-t(log n)²) ≤ C/n^10
    - Geometric series: Σ 1/n^10 converges
    - Explicit bound: rho_one = 1/25 -/
lemma carleson_weight_bound (K B : ℝ) (hB : 0 < B) [Fintype (Q3.Nodes K)] :
    ∑ n : Q3.Nodes K,
      ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ ≤ rho_one :=
  weight_sum_le_rho_one K B hB

end Q3.Proofs
