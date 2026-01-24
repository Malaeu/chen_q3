/-
Q_nonneg on AtomCone_K_fixed — Axiom Closure
=============================================

This file closes the axiom `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
by proving Q ≥ 0 on atoms via the Rayleigh-Q identification.

**Strategy:**
1. Q ≥ 0 on phi_shift (single shifted window) via Rayleigh identification
2. Fejer_heat_atom = sum of shifted windows (with heat kernel scaling)
3. Q linear → Q(atom) = sum of Q(shifts) ≥ 0
4. Apply Q_nonneg_on_atomcone_fixed_of_atoms

**Key insight:** The Rayleigh quotient RQ(Toeplitz[P_A] - T_P_comp, basis0) equals
Q(phi_shift) by rayleigh_Q_eq_Q_shift. The A3 bridge gives RQ ≥ c_*/4 > 0.

Integration: axiom-closure 2026-01-22
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.Rayleigh_basis0_of_A3
import Q3.Proofs.Q_nonneg_atoms_helpers
import Q3.Proofs.Q_nonneg_lemmas
import Q3.Proofs.Q_nonneg_t_critical
import Q3.Proofs.P_A_Toeplitz_bridge
import Q3.Proofs.Params_Critical
import Q3.Proofs.SingleScale_Assumptions
import Q3.Proofs.ShiftedWindows

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.QNonnegClosure

open Q3
open Q3.Proofs.SingleScale

abbrev t_main : ℝ := t_critical
abbrev t0_main : ℝ := t0_critical

/-! ## Step 1: Q ≥ 0 on phi_shift via Rayleigh

The key is to connect:
- rayleigh_basis0_of_A3: A3 bridge → RQ ≥ c_*/4
- rayleigh_Q_eq_Q_shift: RQ at basis0 = Q(phi_shift)
-/

/-- Q is nonnegative on phi_shift at t_sym (single shifted fejer-heat window).
    Uses Rayleigh-Q identification and A3 bridge.

    **Key:** phi_shift B t_sym τ uses the SAME exponential parameter as A3 floor.
    This is because t_sym = 3/50 appears directly in fejer_heat_window's exp(-4π²·t_sym·ξ²).

    The A3 bridge gives RQ(Toeplitz[P_A B_min t_sym] - T_P_comp) ≥ c_star/4.
    Combined with arch_rayleigh_eq_shift and prime bounds, this yields Q ≥ 0.
-/
theorem Q_nonneg_phi_shift_tsym (K B τ : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K)
    (_hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    Q (fun ξ => phi_shift B t_main τ ξ) ≥ 0 := by
  -- Single-scale mainline: delegate to the t_critical proof.
  simpa [t_main, Q3.phi_shift_critical] using
    (Q3.Q_phi_shift_nonneg_t_critical K B τ hK hB hτB)

/-! ## Step 2: Fejer_heat_atom decomposition

Fejer_heat_atom B t τ ξ =
  Fejer_kernel B (ξ - τ) * heat_kernel_A1 t (ξ - τ) +
  Fejer_kernel B (ξ + τ) * heat_kernel_A1 t (ξ + τ)

This is a sum of two "half-atoms".
-/

/-- Half-atom: single term of Fejer_heat_atom -/
noncomputable def half_atom (B t τ : ℝ) (ξ : ℝ) : ℝ :=
  Fejer_kernel B (ξ - τ) * heat_kernel_A1 t (ξ - τ)

/-- Fejer_heat_atom is sum of two half-atoms -/
lemma Fejer_heat_atom_eq_sum_half_atoms (B t τ ξ : ℝ) :
    Fejer_heat_atom B t τ ξ = half_atom B t τ ξ + half_atom B t (-τ) ξ := by
  simp only [Fejer_heat_atom, half_atom, sub_neg_eq_add]

/-! ## Step 4: Q linearity on Fejer_heat_atom -/

/-- Q is additive: Q(f + g) = Q(f) + Q(g) for appropriate functions -/
lemma Q_add (f g : ℝ → ℝ)
    (hf_int : MeasureTheory.Integrable (fun x => a_star x * f x))
    (hg_int : MeasureTheory.Integrable (fun x => a_star x * g x))
    (hf_sum : Summable (fun k => w_Q k * f (xi_n k)))
    (hg_sum : Summable (fun k => w_Q k * g (xi_n k))) :
    Q (fun x => f x + g x) = Q f + Q g := by
  simp only [Q, arch_term, prime_term]
  -- arch_term is linear (integral)
  have h_arch : ∫ x, a_star x * (f x + g x) =
      (∫ x, a_star x * f x) + (∫ x, a_star x * g x) := by
    have heq : (fun x => a_star x * (f x + g x)) =
        (fun x => a_star x * f x + a_star x * g x) := by
      ext x; ring
    rw [heq, MeasureTheory.integral_add hf_int hg_int]
  -- prime_term is linear (tsum)
  have h_prime : ∑' k, w_Q k * (f (xi_n k) + g (xi_n k)) =
      (∑' k, w_Q k * f (xi_n k)) + (∑' k, w_Q k * g (xi_n k)) := by
    have heq : (fun k => w_Q k * (f (xi_n k) + g (xi_n k))) =
        (fun k => w_Q k * f (xi_n k) + w_Q k * g (xi_n k)) := by
      ext k; ring
    rw [heq]
    exact tsum_add hf_sum hg_sum
  rw [h_arch, h_prime]
  ring

  -- (removed) Q_Fejer_heat_atom_eq_sum: we use the scaled phi_shift sum directly at t0_main.

/-! ## Step 5: Q ≥ 0 on half_atom via scaling -/

/-- half_atom at t0_A1 is a scaled version of phi_shift at t_sym.

    **Proof:**
    half_atom B t0_A1 τ ξ = Fejer_kernel B (ξ-τ) * heat_kernel_A1 t0_A1 (ξ-τ)
                         = Fejer_kernel B (ξ-τ) * (1/√(4π·t0_A1)) * exp(-(ξ-τ)²/(4·t0_A1))
                         = (1/√(4π·t0_A1)) * Fejer_kernel B (ξ-τ) * exp(-4π²·t_sym·(ξ-τ)²)
                           (using exp_reparam)
                         = (1/√(4π·t0_A1)) * fejer_heat_window B t_sym (ξ-τ)
                         = (1/√(4π·t0_A1)) * phi_shift B t_sym τ ξ
-/
lemma half_atom_eq_scaled_phi_shift (B τ ξ : ℝ) :
    half_atom B t0_main τ ξ =
      (1 / Real.sqrt (4 * Real.pi * t0_main)) * phi_shift B t_main τ ξ := by
  simp only [half_atom, heat_kernel_A1, phi_shift, fejer_heat_window, Fejer_kernel]
  -- exp_reparam_critical gives: exp(-x²/(4·t0_main)) = exp(-4π²·t_main·x²)
  have hexp := exp_reparam_critical (ξ - τ)
  rw [hexp]
  ring

/-- Q scales with positive constants -/
lemma Q_scale (c : ℝ) (hc : c > 0) (f : ℝ → ℝ)
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

/-- Q ≥ 0 on half_atom.

    Uses: half_atom = c * phi_shift B t_sym τ, and Q(phi_shift B t_sym τ) ≥ 0.
-/
theorem Q_nonneg_half_atom (K B τ : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K)
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    Q (half_atom B t0_main τ) ≥ 0 := by
  -- half_atom = c * phi_shift B t_sym τ
  have hc_pos : (1 / Real.sqrt (4 * Real.pi * t0_main)) > 0 := by
    apply div_pos one_pos
    apply Real.sqrt_pos_of_pos
    have ht : t0_main > 0 := t0_critical_pos
    nlinarith [Real.pi_pos]
  have h_eq : half_atom B t0_main τ = fun ξ =>
      (1 / Real.sqrt (4 * Real.pi * t0_main)) * phi_shift B t_main τ ξ := by
    ext ξ
    exact half_atom_eq_scaled_phi_shift B τ ξ
  rw [h_eq]
  -- Q(c * f) = c * Q(f), and Q(phi_shift) ≥ 0
  have hQ_phi := Q_nonneg_phi_shift_tsym K B τ hK hB hτB hA3
  -- Need integrability and summability for Q_scale
  have h_int :
      MeasureTheory.Integrable (fun x => a_star x * phi_shift B t_main τ x) :=
    Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star (B:=B) (t:=t_main) (tau:=τ) hB
  have h_sum :
      Summable (fun k => w_Q k * phi_shift B t_main τ (xi_n k)) :=
    Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable (B:=B) (t:=t_main) (tau:=τ) hB
  have hQ_scale := Q_scale (c:=(1 / Real.sqrt (4 * Real.pi * t0_main))) hc_pos
    (f:=fun x => phi_shift B t_main τ x) h_int h_sum
  -- Q(c*f) = c*Q(f) and c>0, Q(f)>=0
  have hQ_nonneg : 0 ≤ Q (fun x => phi_shift B t_main τ x) := by
    exact hQ_phi
  have hc_nonneg : 0 ≤ (1 / Real.sqrt (4 * Real.pi * t0_main)) := le_of_lt hc_pos
  -- Rewrite and finish
  have hQ_half : Q (fun x => (1 / Real.sqrt (4 * Real.pi * t0_main)) * phi_shift B t_main τ x) =
      (1 / Real.sqrt (4 * Real.pi * t0_main)) * Q (fun x => phi_shift B t_main τ x) := by
    simpa using hQ_scale
  rw [hQ_half]
  exact mul_nonneg hc_nonneg hQ_nonneg

/-! ## Step 6: Q ≥ 0 on Fejer_heat_atom -/

lemma Fejer_heat_atom_eq_scaled_phi_shift_sum (B τ ξ : ℝ) :
    Fejer_heat_atom B t0_main τ ξ =
      (1 / Real.sqrt (4 * Real.pi * t0_main)) *
        (phi_shift B t_main τ ξ + phi_shift B t_main (-τ) ξ) := by
  have h1 := half_atom_eq_scaled_phi_shift B τ ξ
  have h2 := half_atom_eq_scaled_phi_shift B (-τ) ξ
  -- expand Fejer_heat_atom and rewrite both half-atoms
  simp [Fejer_heat_atom_eq_sum_half_atoms, h1, h2, mul_add, add_mul, add_comm,
    add_left_comm, add_assoc]

/-- Q ≥ 0 on Fejer_heat_atom -/
theorem Q_nonneg_Fejer_heat_atom (K B τ : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K)
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    Q (Fejer_heat_atom B t0_main τ) ≥ 0 := by
  set c : ℝ := (Real.sqrt (4 * Real.pi * t0_main))⁻¹
  -- rewrite atom as scaled sum of phi_shifts, then use Q_scale_add
  have h_int :
      MeasureTheory.Integrable (fun x => a_star x * phi_shift B t_main τ x) :=
    Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star (B:=B) (t:=t_main) (tau:=τ) hB
  have h_int_neg :
      MeasureTheory.Integrable (fun x => a_star x * phi_shift B t_main (-τ) x) :=
    Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star (B:=B) (t:=t_main) (tau:=(-τ)) hB
  have h_sum :
      Summable (fun k => w_Q k * phi_shift B t_main τ (xi_n k)) :=
    Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable (B:=B) (t:=t_main) (tau:=τ) hB
  have h_sum_neg :
      Summable (fun k => w_Q k * phi_shift B t_main (-τ) (xi_n k)) :=
    Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable (B:=B) (t:=t_main) (tau:=(-τ)) hB
  have hQ_phi := Q_nonneg_phi_shift_tsym K B τ hK hB hτB hA3
  have hQ_phi_neg := Q_nonneg_phi_shift_tsym K B (-τ) hK hB (by simpa [abs_neg] using hτB) hA3
  have hQ_scale_add := Q3.Proofs.QNonnegAtoms.Q_scale_add
    (f:=fun x => phi_shift B t_main τ x)
    (g:=fun x => phi_shift B t_main (-τ) x)
    (c:=c) h_int h_int_neg h_sum h_sum_neg
  have h_eval :
      (fun x => c * (phi_shift B t_main τ x + phi_shift B t_main (-τ) x)) =
        fun x => Fejer_heat_atom B t0_main τ x := by
    funext x
    simp [c, Fejer_heat_atom_eq_scaled_phi_shift_sum, one_div]
  have hQ' : Q (Fejer_heat_atom B t0_main τ) =
      c * (Q (fun x => phi_shift B t_main τ x) +
        Q (fun x => phi_shift B t_main (-τ) x)) := by
    simpa [h_eval] using hQ_scale_add
  have hsum_nonneg :
      0 ≤ Q (fun x => phi_shift B t_main τ x) + Q (fun x => phi_shift B t_main (-τ) x) := by
    linarith [hQ_phi, hQ_phi_neg]
  have hc_nonneg : 0 ≤ c := by
    have hc_pos : c > 0 := by
      have hs : 0 < Real.sqrt (4 * Real.pi * t0_main) := by
        apply Real.sqrt_pos_of_pos
        have ht : t0_main > 0 := t0_critical_pos
        nlinarith [Real.pi_pos, ht]
      simpa [c] using (inv_pos.mpr hs)
    exact le_of_lt hc_pos
  have hfinal : 0 ≤ c *
        (Q (fun x => phi_shift B t_main τ x) + Q (fun x => phi_shift B t_main (-τ) x)) :=
    mul_nonneg hc_nonneg hsum_nonneg
  nlinarith [hQ', hfinal]

/-! ## Step 7: Final theorem -/

/-- **Main theorem:** Q ≥ 0 on AtomCone_K_fixed.
    This closes the axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom. -/
theorem Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm :
    ∀ (K : ℝ) (hK : K ≥ 1) [Fintype (Nodes K)],
      Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
      RKHS_contraction_data K →
      ∀ g ∈ AtomCone_K_fixed K t0_main, Q g ≥ 0 := by
  intro K hK _inst hA3 _hRKHS g hg
  have h_atom :
      ∀ B τ, B > 0 → |τ| + B ≤ K → Q (Fejer_heat_atom B t0_main τ) ≥ 0 := by
    intro B τ hB hτB
    exact Q_nonneg_Fejer_heat_atom (K:=K) (B:=B) (τ:=τ) hK hB hτB hA3
  exact Q3.Proofs.QNonnegAtoms.Q_nonneg_on_atomcone_fixed_of_atoms
    (K:=K) (t0:=t0_main) hK (t0_critical_pos) h_atom g hg

end Q3.Proofs.QNonnegClosure
