import Mathlib
import Q3.Basic.Defs
import Q3.Axioms

set_option linter.mathlibStandardSet false

open scoped Real Classical
open MeasureTheory
open Q3

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Heat-weighted factor used in the Lipschitz bound. -/
def heat_weight (t : ℝ) (xi : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) * |xi|

/-- Integrability of the heat-weighted arch integrand, using linear growth of `a_star`. -/
lemma integrable_abs_a_star_mul_heat_weight (t : ℝ) (ht : 0 < t) :
    Integrable (fun ξ => |a_star ξ| * heat_weight t ξ) := by
  obtain ⟨C0, C1, hC0, hC1, h_growth⟩ := Q3.a_star_linear_growth
  set c : ℝ := 4 * Real.pi ^ 2 * t
  have hc : 0 < c := by
    have hpi : 0 < (4 * Real.pi ^ 2) := by positivity
    simpa [c] using mul_pos hpi ht

  -- |x| * exp(-c*x^2) is integrable (use Gaussian lemma + norm).
  have h_int_abs :
      Integrable (fun x => |x| * Real.exp (-c * x ^ 2)) := by
    have h := (integrable_mul_exp_neg_mul_sq (b := c) hc)
    have h' := h.norm
    -- ‖x * exp(-c*x^2)‖ = |x| * exp(-c*x^2)
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, c] using h'

  -- x^2 * exp(-c*x^2) is integrable (Gaussian with polynomial weight).
  have h_int_sq :
      Integrable (fun x => x ^ 2 * Real.exp (-c * x ^ 2)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := c) hc (s := (2 : ℝ)) (by linarith))
    -- rewrite x^(2:ℝ) as x^2
    simpa [Real.rpow_natCast, c] using h

  -- Integrability of heat_weight and |x| * heat_weight.
  have h_int_hw :
      Integrable (fun x => heat_weight t x) := by
    simpa [heat_weight, mul_comm, mul_left_comm, mul_assoc, c] using h_int_abs

  have h_int_hw_abs :
      Integrable (fun x => |x| * heat_weight t x) := by
    -- |x| * heat_weight = x^2 * exp(-c*x^2)
    have h_eq :
        (fun x => |x| * heat_weight t x) =
          fun x => x ^ 2 * Real.exp (-4 * Real.pi ^ 2 * t * x ^ 2) := by
      funext x
      unfold heat_weight
      set E : ℝ := Real.exp (-4 * Real.pi ^ 2 * t * x ^ 2)
      have h_abs_mul : |x| * |x| = x * x := by
        calc
          |x| * |x| = |x * x| := (abs_mul x x).symm
          _ = x * x := abs_mul_self x
      have h_mul : (|x| * |x|) * E = (x * x) * E := by
        simpa using congrArg (fun y => y * E) h_abs_mul
      have h1 : |x| * (|x| * E) = x * (x * E) := by
        calc
          |x| * (|x| * E) = (|x| * |x|) * E := by
            exact (mul_assoc _ _ _).symm
          _ = x * x * E := by
            simpa [mul_assoc] using h_mul
          _ = x * (x * E) := by
            exact (mul_assoc _ _ _)
      have h2 : |x| * (E * |x|) = x * (x * E) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h1
      simpa [pow_two, mul_assoc] using h2
    simpa [c, h_eq] using h_int_sq

  -- Majorant integrable.
  have h_int_majorant :
      Integrable (fun x => (C0 + C1 * |x|) * heat_weight t x) := by
    have h1 : Integrable (fun x => C0 * heat_weight t x) :=
      h_int_hw.const_mul C0
    have h2 : Integrable (fun x => C1 * (|x| * heat_weight t x)) :=
      h_int_hw_abs.const_mul C1
    have hsum :
        Integrable (fun x =>
          C0 * heat_weight t x +
          C1 * (|x| * heat_weight t x)) := h1.add h2
    simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hsum

  -- Measurability of the target function.
  have h_meas :
      AEStronglyMeasurable (fun ξ => |a_star ξ| * heat_weight t ξ) := by
    have h_cont_hw : Continuous (heat_weight t) := by
      unfold heat_weight
      fun_prop
    exact (Q3.a_star_continuous.abs.mul h_cont_hw).aestronglyMeasurable

  -- Comparison with majorant.
  refine Integrable.mono h_int_majorant h_meas ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hw_nonneg : 0 ≤ heat_weight t x := by
    unfold heat_weight
    positivity
  have hsum_nonneg : 0 ≤ C0 + C1 * |x| := by
    nlinarith [abs_nonneg x]
  have hmaj_nonneg :
      0 ≤ (C0 + C1 * |x|) * heat_weight t x := by
    have hprod : 0 ≤ heat_weight t x := hw_nonneg
    exact mul_nonneg hsum_nonneg hprod
  have h_bound :
      |a_star x| * heat_weight t x ≤ (C0 + C1 * |x|) * heat_weight t x := by
    have hx := h_growth x
    exact mul_le_mul_of_nonneg_right hx hw_nonneg
  -- convert to norms
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nonneg,
    abs_of_nonneg hsum_nonneg, abs_of_nonneg hmaj_nonneg] using h_bound

end Q3.Proofs.PrimeCert
