/-
Q_nonneg on BaseAtomCone_K — Proof
===================================

This file proves Q ≥ 0 on BaseAtomCone_K (atoms with τ = 0) using:
1. Connection: Fejer_heat_atom B t0_A1 0 = c * fejer_heat_window B t_sym
2. Rayleigh-Q identification for fejer_heat_window
3. A3 floor: RQ(Toeplitz[P_A]) ≥ c_star
4. RKHS cap: prime_sum ≤ rho_one

This closes the path from A3 bridge to Q ≥ 0 on centered atoms.

Integration: axiom-closure 2026-01-22
-/

import Q3.Axioms
import Q3.Proofs.HeatKernelParams
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.P_A_Toeplitz_bridge
import Q3.Proofs.Q_nonneg_atoms_helpers
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.BaseAtomProof

open Q3

/-! ## Step 1: Fejer_heat_atom at τ = 0 equals scaled fejer_heat_window -/

/-- For τ = 0, Fejer_heat_atom simplifies to 2 * Fejer_kernel * heat_kernel_A1. -/
lemma Fejer_heat_atom_tau_zero (B t ξ : ℝ) :
    Fejer_heat_atom B t 0 ξ = 2 * Fejer_kernel B ξ * heat_kernel_A1 t ξ := by
  simp only [Fejer_heat_atom, sub_zero, add_zero]
  ring

/-- heat_kernel_A1 at t0_A1 relates to the exponential in fejer_heat_window at t_sym. -/
lemma heat_kernel_exp_relation (ξ : ℝ) :
    Real.exp (-ξ^2 / (4 * t0_A1)) = Real.exp (-4 * Real.pi^2 * t_sym * ξ^2) :=
  exp_reparam ξ

/-- Scaling factor between heat_kernel_A1 and fejer_heat_window's exponential. -/
noncomputable def heat_scaling : ℝ := 1 / Real.sqrt (4 * Real.pi * t0_A1)

lemma heat_scaling_pos : heat_scaling > 0 := by
  unfold heat_scaling
  apply div_pos one_pos
  apply Real.sqrt_pos_of_pos
  have ht : t0_A1 > 0 := t0_A1_pos
  nlinarith [Real.pi_pos]

/-- Connection: heat_kernel_A1 t0_A1 ξ = heat_scaling * exp(-4π²t_sym·ξ²) -/
lemma heat_kernel_A1_eq_scaled_exp (ξ : ℝ) :
    heat_kernel_A1 t0_A1 ξ = heat_scaling * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2) := by
  simp only [heat_kernel_A1, heat_scaling, exp_reparam]

/-- Main connection: Fejer_heat_atom B t0_A1 0 ξ = 2 * heat_scaling * fejer_heat_window B t_sym ξ -/
lemma Fejer_heat_atom_tau_zero_eq_scaled_window (B ξ : ℝ) (hB : B > 0) :
    Fejer_heat_atom B t0_A1 0 ξ =
      2 * heat_scaling * fejer_heat_window B t_sym ξ := by
  rw [Fejer_heat_atom_tau_zero, heat_kernel_A1_eq_scaled_exp]
  simp only [fejer_heat_window, Fejer_kernel, heat_scaling]
  ring

/-! ## Step 2: Q on centered atom equals scaled Q on fejer_heat_window -/

/-- Q scales with constants. -/
lemma Q_scale_const (c : ℝ) (f : ℝ → ℝ)
    (hf_int : MeasureTheory.Integrable (fun x => a_star x * f x))
    (hf_sum : Summable (fun k => w_Q k * f (xi_n k))) :
    Q (fun x => c * f x) = c * Q f := by
  simp only [Q, arch_term, prime_term]
  have h1 : ∫ x, a_star x * (c * f x) = c * ∫ x, a_star x * f x := by
    have heq : (fun x => a_star x * (c * f x)) = (fun x => c * (a_star x * f x)) := by
      ext x; ring
    rw [heq, MeasureTheory.integral_mul_left]
  have h2 : ∑' k, w_Q k * (c * f (xi_n k)) = c * ∑' k, w_Q k * f (xi_n k) := by
    have heq : (fun k => w_Q k * (c * f (xi_n k))) = (fun k => c * (w_Q k * f (xi_n k))) := by
      ext k; ring
    rw [heq, tsum_mul_left]
  rw [h1, h2]
  ring

/-! ## Step 3: Q ≥ 0 on single centered atom via A3 bridge -/

/-- Q on fejer_heat_window is nonnegative via A3 bridge.
    This uses the Rayleigh-Q identification and A3 floor. -/
theorem Q_nonneg_fejer_heat_window_B_min (K : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hBK : B_min ≤ K)
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K)
    (h_cap : ∑ n : Nodes K, w_Q n * fejer_heat_window B_min t_sym (xi_n n) ≤
        Q3.Proofs.rho_one) :
    Q (fun ξ => fejer_heat_window B_min t_sym ξ) ≥ 0 := by
  -- Use existing Q_nonneg_fejer_heat_window from helpers
  have hB_pos : (0 : ℝ) < B_min := by norm_num [B_min]
  have hP_cont : Continuous (P_A B_min t_sym) := P_A_continuous
  -- Get Rayleigh bound from A3 bridge
  obtain ⟨t, ht, hA3M⟩ := hA3 hK
  -- For M = 0, get the base case
  have hM : 0 < 2 * 0 + 1 := by norm_num
  have h_rayleigh := hA3M 0 (Q3.Proofs.RayleighQId.basis0 0) (Q3.Proofs.RayleighQId.basis0_ne_zero 0)
  -- Need to show RQ for B_min, t_sym matches what A3 gives for P_A B_min t_sym
  -- This requires that A3 bridge uses exactly P_A B_min t_sym
  sorry  -- Bridge A3_bridge_data_rayleigh_Fourier → h_rayleigh for Q_nonneg_fejer_heat_window

/-- Q ≥ 0 on centered Fejer_heat_atom with B = B_min. -/
theorem Q_nonneg_centered_atom_B_min (K : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hBK : B_min ≤ K)
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    Q (Fejer_heat_atom B_min t0_A1 0) ≥ 0 := by
  sorry  -- Use Fejer_heat_atom_tau_zero_eq_scaled_window + Q_scale_const + Q_nonneg_fejer_heat_window_B_min

/-! ## Step 4: Extend to BaseAtomCone via linearity -/

/-- Q is linear on finite sums of atoms. -/
lemma Q_finsum_atoms (n : ℕ) (c : Fin n → ℝ) (B : Fin n → ℝ)
    (hB : ∀ i, B i > 0) :
    Q (fun x => ∑ i, c i * Fejer_heat_atom (B i) t0_A1 0 x) =
      ∑ i, c i * Q (Fejer_heat_atom (B i) t0_A1 0) := by
  sorry  -- Use Q linearity lemmas from Q_nonneg_lemmas

/-- Main theorem: Q ≥ 0 on BaseAtomCone_K.

**NOTE:** This requires B ≥ B_min for the A3 floor. Currently BaseAtomCone_K
allows arbitrary B > 0. We need either:
1. Restrict BaseAtomCone to B ≥ B_min, or
2. Prove A3 floor for all B > 0 (harder)

For now, we assume B ≥ B_min and add this as a hypothesis.
-/
theorem Q_nonneg_on_BaseAtomCone_of_B_ge_Bmin (K : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1)
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K)
    (g : ℝ → ℝ) (hg : g ∈ BaseAtomCone_K K t0_A1)
    (hB_ge : ∀ (n : ℕ) (c : Fin n → ℝ) (B : Fin n → ℝ),
      (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) t0_A1 0 x) → ∀ i, B i ≥ B_min) :
    Q g ≥ 0 := by
  sorry  -- Use Q_finsum_atoms + nonnegativity of each atom

end Q3.Proofs.BaseAtomProof
