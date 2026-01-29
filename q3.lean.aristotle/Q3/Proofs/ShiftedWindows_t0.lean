/-
Shifted windows: fixed-t0 Fejer-heat atom rewrite.
-/

import Q3.Proofs.ShiftedWindows
import Q3.Proofs.HeatKernelParams

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3.Proofs.ShiftedWindows

open Q3

lemma Fejer_heat_atom_eq_const_mul_phi_shift_sum (B τ : ℝ) :
    Q3.Fejer_heat_atom B Q3.t0_A1 τ =
      fun x => (1 / Real.sqrt (4 * Real.pi * Q3.t0_A1)) *
        (Q3.phi_shift B t_sym τ x + Q3.phi_shift B t_sym (-τ) x) := by
  funext x
  have h1 :
      rexp (-(x - τ) ^ 2 / (t0_A1 * 4)) =
        rexp (-(t_sym * (Real.pi ^ 2 * ((x - τ) ^ 2 * 4)))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (Q3.exp_reparam (x - τ))
  have h2 :
      rexp (-(x + τ) ^ 2 / (t0_A1 * 4)) =
        rexp (-(t_sym * (Real.pi ^ 2 * ((x + τ) ^ 2 * 4)))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (Q3.exp_reparam (x + τ))
  unfold Q3.Fejer_heat_atom Q3.phi_shift
  simp [Q3.fejer_heat_window, Q3.Fejer_kernel, Q3.heat_kernel_A1, h1, h2,
    add_mul, mul_assoc, mul_left_comm, mul_comm]

end Q3.Proofs.ShiftedWindows
