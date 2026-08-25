import Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# The explicit H derivative comb budget (W5_EXPLICIT_H_QCOMB_BOUNDED)

Ratified by verdict dee1ec4d.  The target derivative comb
`g_H(y) = 4 * y * H'(y)` for the explicit limit profile
`H(y) = (π/2) y² (2πy² − 3) e^{−πy²}` admits a uniform absolute budget:
an explicit majorant `hMaj` dominates the comb pointwise on every window,
and its weighted window integral is bounded by an absolute constant.

The load-bearing algebraic fact: `g_H` has the EXACT elementary
antiderivative `V(y) = (4π²y⁵ − 4πy³) e^{−πy²}`, so every cell integral of
the comb is closed-form and the Euler–Maclaurin leading term needs no
zero-mass or Poisson input at all.
-/

/-- The real profile of `explicitCCMLimitH`. -/
def hbHRe (y : ℝ) : ℝ :=
  (Real.pi / 2) * y ^ 2 * (2 * Real.pi * y ^ 2 - 3) * Real.exp (-Real.pi * y ^ 2)

/-- The derivative comb kernel `g_H(y) = 4 y H'(y)`, in closed polynomial form. -/
def hbG (y : ℝ) : ℝ :=
  (-(8 * Real.pi ^ 3) * y ^ 6 + 28 * Real.pi ^ 2 * y ^ 4 - 12 * Real.pi * y ^ 2) *
    Real.exp (-Real.pi * y ^ 2)

/-- First derivative of `hbG`. -/
def hbG1 (y : ℝ) : ℝ :=
  (16 * Real.pi ^ 4 * y ^ 7 - 104 * Real.pi ^ 3 * y ^ 5 +
      136 * Real.pi ^ 2 * y ^ 3 - 24 * Real.pi * y) *
    Real.exp (-Real.pi * y ^ 2)

/-- Second derivative of `hbG`. -/
def hbG2 (y : ℝ) : ℝ :=
  (-(32 * Real.pi ^ 5) * y ^ 8 + 320 * Real.pi ^ 4 * y ^ 6 -
      792 * Real.pi ^ 3 * y ^ 4 + 456 * Real.pi ^ 2 * y ^ 2 - 24 * Real.pi) *
    Real.exp (-Real.pi * y ^ 2)

/-- The exact elementary antiderivative of `hbG`. -/
def hbV (y : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * y ^ 5 - 4 * Real.pi * y ^ 3) * Real.exp (-Real.pi * y ^ 2)

private theorem hb_exp_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))
      (-2 * Real.pi * y * Real.exp (-Real.pi * y ^ 2)) y := by
  have h1 : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2) (-2 * Real.pi * y) y := by
    have := (hasDerivAt_pow 2 y).const_mul (-Real.pi)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have := h1.exp
  simpa [mul_comm] using this

private theorem hb_polyexp_hasDerivAt {P : ℝ → ℝ} {p : ℝ} (y : ℝ)
    (hP : HasDerivAt P p y) :
    HasDerivAt (fun t : ℝ => P t * Real.exp (-Real.pi * t ^ 2))
      ((p - 2 * Real.pi * y * P y) * Real.exp (-Real.pi * y ^ 2)) y := by
  have h := hP.mul (hb_exp_hasDerivAt y)
  exact h.congr_deriv (by ring)

private theorem hbV_hasDerivAt (y : ℝ) :
    HasDerivAt hbV (hbG y) y := by
  have hP : HasDerivAt (fun t : ℝ => 4 * Real.pi ^ 2 * t ^ 5 - 4 * Real.pi * t ^ 3)
      (4 * Real.pi ^ 2 * (5 * y ^ 4) - 4 * Real.pi * (3 * y ^ 2)) y := by
    have h5 := (hasDerivAt_pow 5 y).const_mul (4 * Real.pi ^ 2)
    have h3 := (hasDerivAt_pow 3 y).const_mul (4 * Real.pi)
    exact (HasDerivAt.sub h5 h3).congr_deriv (by push_cast; ring)
  have h := hb_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    (4 * Real.pi ^ 2 * t ^ 5 - 4 * Real.pi * t ^ 3) *
      Real.exp (-Real.pi * t ^ 2)) (hbG y) y
  exact h.congr_deriv (by unfold hbG; ring)

private theorem hbG_hasDerivAt (y : ℝ) :
    HasDerivAt hbG (hbG1 y) y := by
  have hP : HasDerivAt
      (fun t : ℝ => -(8 * Real.pi ^ 3) * t ^ 6 + 28 * Real.pi ^ 2 * t ^ 4 -
        12 * Real.pi * t ^ 2)
      (-(8 * Real.pi ^ 3) * (6 * y ^ 5) + 28 * Real.pi ^ 2 * (4 * y ^ 3) -
        12 * Real.pi * (2 * y)) y := by
    have h6 := (hasDerivAt_pow 6 y).const_mul (-(8 * Real.pi ^ 3))
    have h4 := (hasDerivAt_pow 4 y).const_mul (28 * Real.pi ^ 2)
    have h2 := (hasDerivAt_pow 2 y).const_mul (12 * Real.pi)
    exact (HasDerivAt.sub (HasDerivAt.add h6 h4) h2).congr_deriv
      (by push_cast; ring)
  have h := hb_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    (-(8 * Real.pi ^ 3) * t ^ 6 + 28 * Real.pi ^ 2 * t ^ 4 -
      12 * Real.pi * t ^ 2) * Real.exp (-Real.pi * t ^ 2)) (hbG1 y) y
  exact h.congr_deriv (by unfold hbG1; ring)

private theorem hbG1_hasDerivAt (y : ℝ) :
    HasDerivAt hbG1 (hbG2 y) y := by
  have hP : HasDerivAt
      (fun t : ℝ => 16 * Real.pi ^ 4 * t ^ 7 - 104 * Real.pi ^ 3 * t ^ 5 +
        136 * Real.pi ^ 2 * t ^ 3 - 24 * Real.pi * t)
      (16 * Real.pi ^ 4 * (7 * y ^ 6) - 104 * Real.pi ^ 3 * (5 * y ^ 4) +
        136 * Real.pi ^ 2 * (3 * y ^ 2) - 24 * Real.pi * 1) y := by
    have h7 := (hasDerivAt_pow 7 y).const_mul (16 * Real.pi ^ 4)
    have h5 := (hasDerivAt_pow 5 y).const_mul (104 * Real.pi ^ 3)
    have h3 := (hasDerivAt_pow 3 y).const_mul (136 * Real.pi ^ 2)
    have h1 := (hasDerivAt_id y).const_mul (24 * Real.pi)
    exact (HasDerivAt.sub (HasDerivAt.add (HasDerivAt.sub h7 h5) h3) h1).congr_deriv
      (by push_cast; ring)
  have h := hb_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    (16 * Real.pi ^ 4 * t ^ 7 - 104 * Real.pi ^ 3 * t ^ 5 +
      136 * Real.pi ^ 2 * t ^ 3 - 24 * Real.pi * t) *
      Real.exp (-Real.pi * t ^ 2)) (hbG2 y) y
  exact h.congr_deriv (by unfold hbG2; ring)

private theorem hbG_continuous : Continuous hbG := by
  unfold hbG
  fun_prop

private theorem hbG1_continuous : Continuous hbG1 := by
  unfold hbG1
  fun_prop

private theorem hbG2_continuous : Continuous hbG2 := by
  unfold hbG2
  fun_prop

/-- The link to the complex target derivative: `hbG y = 4y * Re(H'(y))` in the
sense that `deriv explicitCCMLimitH y = ((hbG y / (4*y) ...))`.  Recorded as the
profile identity `explicitCCMLimitH y = hbHRe y` and the derivative identity for
downstream consumers. -/
theorem explicitCCMLimitH_eq_hbHRe (y : ℝ) :
    explicitCCMLimitH y = ((hbHRe y : ℝ) : ℂ) := by
  unfold explicitCCMLimitH hbHRe
  rw [show (-Real.pi * (y : ℂ) ^ 2) = (((-Real.pi * y ^ 2 : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

private theorem hbHRe_hasDerivAt (y : ℝ) :
    HasDerivAt hbHRe
      ((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 - 3 * Real.pi * y) *
        Real.exp (-Real.pi * y ^ 2)) y := by
  have hRe_eq : hbHRe = fun t : ℝ =>
      (Real.pi ^ 2 * t ^ 4 - 3 * Real.pi / 2 * t ^ 2) *
        Real.exp (-Real.pi * t ^ 2) := by
    funext t
    unfold hbHRe
    ring
  have hP : HasDerivAt (fun t : ℝ => Real.pi ^ 2 * t ^ 4 - 3 * Real.pi / 2 * t ^ 2)
      (Real.pi ^ 2 * (4 * y ^ 3) - 3 * Real.pi / 2 * (2 * y)) y := by
    have h4 := (hasDerivAt_pow 4 y).const_mul (Real.pi ^ 2)
    have h2 := (hasDerivAt_pow 2 y).const_mul (3 * Real.pi / 2)
    exact (HasDerivAt.sub h4 h2).congr_deriv (by push_cast; ring)
  have h := hb_polyexp_hasDerivAt y hP
  rw [hRe_eq]
  exact h.congr_deriv (by ring)

/-- `hbG` is exactly `4 y * (d/dy) hbHRe`. -/
theorem hbG_eq_four_mul_deriv (y : ℝ) :
    hbG y = 4 * y * deriv hbHRe y := by
  rw [(hbHRe_hasDerivAt y).deriv]
  unfold hbG
  ring

/-! ## Absolute bounds -/

/-- Polynomial coefficient mass of `hbG`. -/
def hbCg1 : ℝ := 8 * Real.pi ^ 3 + 28 * Real.pi ^ 2 + 12 * Real.pi

/-- Tail constant for `hbG`. -/
def hbCgC : ℝ := 24 * hbCg1 / Real.pi ^ 4

/-- Head constant for `hbV`. -/
def hbCv1 : ℝ := 4 * Real.pi ^ 2 + 4 * Real.pi

/-- Tail constant for `hbV`. -/
def hbCvC : ℝ := 24 / Real.pi ^ 4 * (8 * Real.pi ^ 2 + 32 * Real.pi)

/-- Second-derivative mass on the half line. -/
def hbKG : ℝ := ∫ y in Ioi (0 : ℝ), |hbG2 y|

private theorem hbCg1_pos : 0 < hbCg1 := by unfold hbCg1; positivity
private theorem hbCgC_pos : 0 < hbCgC := by
  have := hbCg1_pos
  unfold hbCgC
  positivity
private theorem hbCv1_pos : 0 < hbCv1 := by unfold hbCv1; positivity
private theorem hbCvC_pos : 0 < hbCvC := by unfold hbCvC; positivity
private theorem hbKG_nonneg : 0 ≤ hbKG := by
  unfold hbKG
  positivity

private theorem hb_exp_le_one (y : ℝ) :
    Real.exp (-Real.pi * y ^ 2) ≤ 1 := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
  apply Real.exp_le_exp.mpr
  have := Real.pi_pos
  nlinarith [sq_nonneg y]

private theorem hb_exp_tail (y : ℝ) (hy : 0 < y) :
    Real.exp (-Real.pi * y ^ 2) ≤ 24 / (Real.pi ^ 4 * y ^ 8) := by
  have hx : (0 : ℝ) ≤ Real.pi * y ^ 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (x := Real.pi * y ^ 2) hx 4
  have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfact] at h
  have hpow : (Real.pi * y ^ 2) ^ 4 = Real.pi ^ 4 * y ^ 8 := by ring
  rw [hpow] at h
  have hpos : (0 : ℝ) < Real.pi ^ 4 * y ^ 8 := by positivity
  have hexp_pos : (0 : ℝ) < Real.exp (Real.pi * y ^ 2) := Real.exp_pos _
  rw [show -Real.pi * y ^ 2 = -(Real.pi * y ^ 2) by ring, Real.exp_neg,
    inv_le_iff_one_le_mul₀ hexp_pos, div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [h]

private theorem hbG_head (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    |hbG y| ≤ hbCg1 * y ^ 2 := by
  unfold hbG hbCg1
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := hb_exp_le_one y
  have h6 : y ^ 6 ≤ y ^ 2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h4 : y ^ 4 ≤ y ^ 2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h6s : 8 * Real.pi ^ 3 * y ^ 6 ≤ 8 * Real.pi ^ 3 * y ^ 2 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have h4s : 28 * Real.pi ^ 2 * y ^ 4 ≤ 28 * Real.pi ^ 2 * y ^ 2 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6n : (0:ℝ) ≤ 8 * Real.pi ^ 3 * y ^ 6 := by positivity
  have h4n : (0:ℝ) ≤ 28 * Real.pi ^ 2 * y ^ 4 := by positivity
  have h2n : (0:ℝ) ≤ 12 * Real.pi * y ^ 2 := by positivity
  have hpoly : |(-(8 * Real.pi ^ 3) * y ^ 6 + 28 * Real.pi ^ 2 * y ^ 4 -
      12 * Real.pi * y ^ 2)| ≤
      (8 * Real.pi ^ 3 + 28 * Real.pi ^ 2 + 12 * Real.pi) * y ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [h6s, h4s, h6n, h4n, h2n]
  calc
    |(-(8 * Real.pi ^ 3) * y ^ 6 + 28 * Real.pi ^ 2 * y ^ 4 -
        12 * Real.pi * y ^ 2)| * Real.exp (-Real.pi * y ^ 2)
        ≤ ((8 * Real.pi ^ 3 + 28 * Real.pi ^ 2 + 12 * Real.pi) * y ^ 2) * 1 := by
          apply mul_le_mul hpoly hexp (Real.exp_pos _).le
          positivity
    _ = (8 * Real.pi ^ 3 + 28 * Real.pi ^ 2 + 12 * Real.pi) * y ^ 2 := by ring

private theorem hbG_tail (y : ℝ) (hy : 1 ≤ y) :
    |hbG y| ≤ hbCgC / y ^ 2 := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  unfold hbG
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := hb_exp_tail y hy0
  have hpi := Real.pi_pos
  have hpoly : |(-(8 * Real.pi ^ 3) * y ^ 6 + 28 * Real.pi ^ 2 * y ^ 4 -
      12 * Real.pi * y ^ 2)| ≤ hbCg1 * y ^ 6 := by
    unfold hbCg1
    have h4 : y ^ 4 ≤ y ^ 6 := pow_le_pow_right₀ hy (by norm_num)
    have h2 : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ hy (by norm_num)
    have h4s : 28 * Real.pi ^ 2 * y ^ 4 ≤ 28 * Real.pi ^ 2 * y ^ 6 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h2s : 12 * Real.pi * y ^ 2 ≤ 12 * Real.pi * y ^ 6 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6n : (0:ℝ) ≤ 8 * Real.pi ^ 3 * y ^ 6 := by positivity
    have h4n : (0:ℝ) ≤ 28 * Real.pi ^ 2 * y ^ 4 := by positivity
    have h2n : (0:ℝ) ≤ 12 * Real.pi * y ^ 2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith [h4s, h2s, h6n, h4n, h2n]
  have hstep : |(-(8 * Real.pi ^ 3) * y ^ 6 + 28 * Real.pi ^ 2 * y ^ 4 -
      12 * Real.pi * y ^ 2)| * Real.exp (-Real.pi * y ^ 2) ≤
      hbCg1 * y ^ 6 * (24 / (Real.pi ^ 4 * y ^ 8)) := by
    apply mul_le_mul hpoly hexp (Real.exp_pos _).le
    have := hbCg1_pos
    positivity
  refine hstep.trans (le_of_eq ?_)
  unfold hbCgC
  field_simp

private theorem hbV_head (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    |hbV y| ≤ hbCv1 * y ^ 3 := by
  unfold hbV hbCv1
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := hb_exp_le_one y
  have hpi := Real.pi_pos
  have h5 : y ^ 5 ≤ y ^ 3 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h5s : 4 * Real.pi ^ 2 * y ^ 5 ≤ 4 * Real.pi ^ 2 * y ^ 3 :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h5n : (0:ℝ) ≤ 4 * Real.pi ^ 2 * y ^ 5 := by positivity
  have h3n : (0:ℝ) ≤ 4 * Real.pi * y ^ 3 := by positivity
  have hpoly : |4 * Real.pi ^ 2 * y ^ 5 - 4 * Real.pi * y ^ 3| ≤
      (4 * Real.pi ^ 2 + 4 * Real.pi) * y ^ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [h5s, h5n, h3n]
  calc
    |4 * Real.pi ^ 2 * y ^ 5 - 4 * Real.pi * y ^ 3| *
        Real.exp (-Real.pi * y ^ 2)
        ≤ ((4 * Real.pi ^ 2 + 4 * Real.pi) * y ^ 3) * 1 := by
          apply mul_le_mul hpoly hexp (Real.exp_pos _).le
          positivity
    _ = (4 * Real.pi ^ 2 + 4 * Real.pi) * y ^ 3 := by ring

private theorem hbV_tail (y : ℝ) (hy : 1 / 2 ≤ y) :
    |hbV y| ≤ hbCvC / y ^ 2 := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  unfold hbV
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := hb_exp_tail y hy0
  have hpi := Real.pi_pos
  have hpoly : |4 * Real.pi ^ 2 * y ^ 5 - 4 * Real.pi * y ^ 3| ≤
      4 * Real.pi ^ 2 * y ^ 5 + 4 * Real.pi * y ^ 3 := by
    have h5n : (0:ℝ) ≤ 4 * Real.pi ^ 2 * y ^ 5 := by positivity
    have h3n : (0:ℝ) ≤ 4 * Real.pi * y ^ 3 := by positivity
    rw [abs_le]
    constructor <;> nlinarith [h5n, h3n]
  have hstep : |4 * Real.pi ^ 2 * y ^ 5 - 4 * Real.pi * y ^ 3| *
      Real.exp (-Real.pi * y ^ 2) ≤
      (4 * Real.pi ^ 2 * y ^ 5 + 4 * Real.pi * y ^ 3) *
        (24 / (Real.pi ^ 4 * y ^ 8)) := by
    apply mul_le_mul hpoly hexp (Real.exp_pos _).le
    positivity
  refine hstep.trans ?_
  unfold hbCvC
  rw [le_div_iff₀ (by positivity : (0:ℝ) < y ^ 2)]
  have hkey : (4 * Real.pi ^ 2 * y ^ 5 + 4 * Real.pi * y ^ 3) *
      (24 / (Real.pi ^ 4 * y ^ 8)) * y ^ 2 =
      24 / Real.pi ^ 4 * (4 * Real.pi ^ 2 / y + 4 * Real.pi / y ^ 3) := by
    field_simp
  rw [hkey]
  have hy1 : 4 * Real.pi ^ 2 / y ≤ 8 * Real.pi ^ 2 := by
    rw [div_le_iff₀ hy0]
    nlinarith [Real.pi_pos]
  have hy3 : 4 * Real.pi / y ^ 3 ≤ 32 * Real.pi := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < y ^ 3)]
    have h8 : (1:ℝ) / 8 ≤ y ^ 3 := by nlinarith
    nlinarith [Real.pi_pos]
  have h24 : (0:ℝ) ≤ 24 / Real.pi ^ 4 := by positivity
  apply mul_le_mul_of_nonneg_left _ h24
  linarith

/-! ## Exact FTC and the cell/comb estimates -/

private theorem hb_ftc (a b : ℝ) :
    ∫ y in a..b, hbG y = hbV b - hbV a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hbV_hasDerivAt y)
    (hbG_continuous.intervalIntegrable a b)

private theorem hbG2_abs_integrable :
    IntegrableOn (fun y : ℝ => |hbG2 y|) (Ioi (0 : ℝ)) volume := by
  have hmono : ∀ k : ℕ, Integrable
      (fun y : ℝ => y ^ (2 * k) * Real.exp (-Real.pi * y ^ 2)) volume := by
    intro k
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
      (s := ((2 * k : ℕ) : ℝ))
      (lt_of_lt_of_le neg_one_lt_zero (by positivity))
    refine h.congr ?_
    filter_upwards [] with y
    rw [Real.rpow_natCast]
  have hQ : Integrable (fun y : ℝ =>
      32 * Real.pi ^ 5 * (y ^ (2 * 4) * Real.exp (-Real.pi * y ^ 2)) +
      320 * Real.pi ^ 4 * (y ^ (2 * 3) * Real.exp (-Real.pi * y ^ 2)) +
      792 * Real.pi ^ 3 * (y ^ (2 * 2) * Real.exp (-Real.pi * y ^ 2)) +
      456 * Real.pi ^ 2 * (y ^ (2 * 1) * Real.exp (-Real.pi * y ^ 2)) +
      24 * Real.pi * (y ^ (2 * 0) * Real.exp (-Real.pi * y ^ 2))) volume := by
    exact (((((hmono 4).const_mul (32 * Real.pi ^ 5)).add
      ((hmono 3).const_mul (320 * Real.pi ^ 4))).add
      ((hmono 2).const_mul (792 * Real.pi ^ 3))).add
      ((hmono 1).const_mul (456 * Real.pi ^ 2))).add
      ((hmono 0).const_mul (24 * Real.pi))
  have hbound : ∀ y : ℝ, ‖|hbG2 y|‖ ≤
      32 * Real.pi ^ 5 * (y ^ (2 * 4) * Real.exp (-Real.pi * y ^ 2)) +
      320 * Real.pi ^ 4 * (y ^ (2 * 3) * Real.exp (-Real.pi * y ^ 2)) +
      792 * Real.pi ^ 3 * (y ^ (2 * 2) * Real.exp (-Real.pi * y ^ 2)) +
      456 * Real.pi ^ 2 * (y ^ (2 * 1) * Real.exp (-Real.pi * y ^ 2)) +
      24 * Real.pi * (y ^ (2 * 0) * Real.exp (-Real.pi * y ^ 2)) := by
    intro y
    rw [Real.norm_eq_abs, abs_abs]
    unfold hbG2
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hpi := Real.pi_pos
    have h8 : (0:ℝ) ≤ y ^ 8 := by positivity
    have h6 : (0:ℝ) ≤ y ^ 6 := by positivity
    have h4 : (0:ℝ) ≤ y ^ 4 := by positivity
    have h2 : (0:ℝ) ≤ y ^ 2 := by positivity
    have hexp : (0:ℝ) < Real.exp (-Real.pi * y ^ 2) := Real.exp_pos _
    have habs : |(-(32 * Real.pi ^ 5) * y ^ 8 + 320 * Real.pi ^ 4 * y ^ 6 -
        792 * Real.pi ^ 3 * y ^ 4 + 456 * Real.pi ^ 2 * y ^ 2 - 24 * Real.pi)| ≤
        32 * Real.pi ^ 5 * y ^ 8 + 320 * Real.pi ^ 4 * y ^ 6 +
        792 * Real.pi ^ 3 * y ^ 4 + 456 * Real.pi ^ 2 * y ^ 2 + 24 * Real.pi := by
      have hA : (0:ℝ) ≤ 32 * Real.pi ^ 5 * y ^ 8 := by positivity
      have hB : (0:ℝ) ≤ 320 * Real.pi ^ 4 * y ^ 6 := by positivity
      have hC : (0:ℝ) ≤ 792 * Real.pi ^ 3 * y ^ 4 := by positivity
      have hD : (0:ℝ) ≤ 456 * Real.pi ^ 2 * y ^ 2 := by positivity
      have hEc : (0:ℝ) ≤ 24 * Real.pi := by positivity
      rw [abs_le]
      constructor <;> nlinarith [hA, hB, hC, hD, hEc]
    calc
      |(-(32 * Real.pi ^ 5) * y ^ 8 + 320 * Real.pi ^ 4 * y ^ 6 -
          792 * Real.pi ^ 3 * y ^ 4 + 456 * Real.pi ^ 2 * y ^ 2 - 24 * Real.pi)| *
          Real.exp (-Real.pi * y ^ 2)
          ≤ (32 * Real.pi ^ 5 * y ^ 8 + 320 * Real.pi ^ 4 * y ^ 6 +
              792 * Real.pi ^ 3 * y ^ 4 + 456 * Real.pi ^ 2 * y ^ 2 +
              24 * Real.pi) * Real.exp (-Real.pi * y ^ 2) := by
            apply mul_le_mul_of_nonneg_right habs hexp.le
      _ = _ := by norm_num; ring
  exact (Integrable.mono' hQ
    hbG2_continuous.abs.aestronglyMeasurable
    (Eventually.of_forall hbound)).integrableOn

private theorem hb_cell (u m : ℝ) (hu : 0 < u) :
    |u * hbG m - ∫ y in (m - u / 2)..(m + u / 2), hbG y| ≤
      u ^ 2 / 2 * ∫ y in (m - u / 2)..(m + u / 2), |hbG2 y| := by
  set a := m - u / 2 with ha
  set b := m + u / 2 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  set E := ∫ y in a..b, |hbG2 y| with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    apply intervalIntegral.integral_nonneg hab
    intro y _
    positivity
  have hmemm : m ∈ Set.Icc a b := by
    constructor
    · rw [ha]; linarith
    · rw [hb]; linarith
  have hgdiff : ∀ t ∈ Set.Icc a b, |hbG1 t - hbG1 m| ≤ E := by
    intro t ht
    have hftc : hbG1 t - hbG1 m = ∫ s in m..t, hbG2 s :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hbG1_hasDerivAt s)
        (hbG2_continuous.intervalIntegrable m t)).symm
    rw [hftc, ← Real.norm_eq_abs]
    calc
      ‖∫ s in m..t, hbG2 s‖ ≤ |∫ s in m..t, ‖hbG2 s‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ ≤ |∫ s in a..b, ‖hbG2 s‖| := by
        apply intervalIntegral.abs_integral_mono_interval
        · rw [Set.uIoc, Set.uIoc]
          apply Set.Ioc_subset_Ioc
          · exact le_inf (inf_le_left.trans hmemm.1) (inf_le_left.trans ht.1)
          · exact sup_le (hmemm.2.trans le_sup_right) (ht.2.trans le_sup_right)
        · filter_upwards [] with s
          positivity
        · exact hbG2_continuous.norm.intervalIntegrable a b
      _ = E := by
        rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab
          (fun s _ => norm_nonneg _))]
        rw [hE]
        apply intervalIntegral.integral_congr
        intro s _
        simp [Real.norm_eq_abs]
  have hphi : ∀ y ∈ Set.uIoc a b,
      ‖hbG y - hbG m - hbG1 m * (y - m)‖ ≤ E * (u / 2) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc a b := by
      have h1 := Set.uIoc_subset_uIcc hy
      rwa [Set.uIcc_of_le hab] at h1
    have hftcG : hbG y - hbG m = ∫ t in m..y, hbG1 t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hbG_hasDerivAt t)
        (hbG1_continuous.intervalIntegrable m y)).symm
    have hconst : hbG1 m * (y - m) = ∫ t in m..y, hbG1 m := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hftcG, hconst, ← intervalIntegral.integral_sub
      (hbG1_continuous.intervalIntegrable m y) intervalIntegral.intervalIntegrable_const]
    have hboundt : ∀ t ∈ Set.uIoc m y, ‖hbG1 t - hbG1 m‖ ≤ E := by
      intro t ht
      have htIcc : t ∈ Set.Icc a b := by
        have h1 := Set.uIoc_subset_uIcc ht
        have h2 : Set.uIcc m y ⊆ Set.Icc a b := Set.uIcc_subset_Icc hmemm hyIcc
        exact h2 h1
      rw [Real.norm_eq_abs]
      exact hgdiff t htIcc
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hboundt
    refine h.trans ?_
    have hym : |y - m| ≤ u / 2 := by
      rw [abs_le]
      constructor
      · have h1 := hyIcc.1; rw [ha] at h1; linarith
      · have h2 := hyIcc.2; rw [hb] at h2; linarith
    exact mul_le_mul_of_nonneg_left hym hE0
  have hlin : (∫ y in a..b, (y - m)) = 0 := by
    rw [intervalIntegral.integral_sub (continuous_id'.intervalIntegrable _ _)
      intervalIntegral.intervalIntegrable_const]
    rw [integral_id, intervalIntegral.integral_const, smul_eq_mul]
    rw [ha, hb]
    ring
  have hsplit : u * hbG m - ∫ y in a..b, hbG y =
      -∫ y in a..b, (hbG y - hbG m - hbG1 m * (y - m)) := by
    rw [intervalIntegral.integral_sub
      ((hbG_continuous.intervalIntegrable a b).sub intervalIntegral.intervalIntegrable_const)
      (((continuous_id'.intervalIntegrable _ _).sub intervalIntegral.intervalIntegrable_const).const_mul _)]
    rw [intervalIntegral.integral_sub
      (hbG_continuous.intervalIntegrable a b) intervalIntegral.intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul, hlin,
      intervalIntegral.integral_const, smul_eq_mul]
    have hba : b - a = u := by rw [ha, hb]; ring
    rw [hba]
    ring
  rw [hsplit, abs_neg, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hphi
  refine h.trans (le_of_eq ?_)
  have hba : |b - a| = u := by
    rw [ha, hb, abs_of_pos (by linarith)]
    ring
  rw [hba, hE]
  ring

private theorem hb_comb (u : ℝ) (hu : 0 < u) (M : ℕ) :
    |(∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)) -
        (hbV (((M : ℝ) + 1 / 2) * u) - hbV (u / 2)) / u| ≤
      u / 2 * hbKG := by
  set aa : ℕ → ℝ := fun j => ((j : ℝ) + 1 / 2) * u with haa
  have hcell : ∀ j : ℕ,
      |hbG (((j : ℝ) + 1) * u) * u - ∫ y in (aa j)..(aa (j + 1)), hbG y| ≤
        u ^ 2 / 2 * ∫ y in (aa j)..(aa (j + 1)), |hbG2 y| := by
    intro j
    have h := hb_cell u (((j : ℝ) + 1) * u) hu
    have ha' : ((j : ℝ) + 1) * u - u / 2 = aa j := by
      rw [haa]; push_cast; ring
    have hb' : ((j : ℝ) + 1) * u + u / 2 = aa (j + 1) := by
      rw [haa]; push_cast; ring
    rw [ha', hb'] at h
    rwa [show hbG (((j : ℝ) + 1) * u) * u = u * hbG (((j : ℝ) + 1) * u) by ring]
  have hsum_int : (∑ j ∈ Finset.range M, ∫ y in (aa j)..(aa (j + 1)), hbG y) =
      ∫ y in (aa 0)..(aa M), hbG y := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro k _
    exact hbG_continuous.intervalIntegrable _ _
  have hsum_abs : (∑ j ∈ Finset.range M,
      ∫ y in (aa j)..(aa (j + 1)), |hbG2 y|) =
      ∫ y in (aa 0)..(aa M), |hbG2 y| := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro k _
    exact hbG2_continuous.abs.intervalIntegrable _ _
  have hreindex : (∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)) =
      ∑ j ∈ Finset.range M, hbG (((j : ℝ) + 1) * u) := by
    rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by norm_num)
    intro j _
    congr 1
    push_cast
    ring
  have hmain : |(∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)) * u -
      (hbV (aa M) - hbV (aa 0))| ≤
      u ^ 2 / 2 * ∫ y in (aa 0)..(aa M), |hbG2 y| := by
    rw [hreindex, ← hb_ftc (aa 0) (aa M), ← hsum_int, ← hsum_abs,
      Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    calc
      |∑ j ∈ Finset.range M,
          (hbG (((j : ℝ) + 1) * u) * u - ∫ y in (aa j)..(aa (j + 1)), hbG y)|
          ≤ ∑ j ∈ Finset.range M,
            |hbG (((j : ℝ) + 1) * u) * u - ∫ y in (aa j)..(aa (j + 1)), hbG y| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range M,
            u ^ 2 / 2 * ∫ y in (aa j)..(aa (j + 1)), |hbG2 y| :=
            Finset.sum_le_sum fun j _ => hcell j
  have hKGbound : (∫ y in (aa 0)..(aa M), |hbG2 y|) ≤ hbKG := by
    have h0 : (0 : ℝ) < aa 0 := by
      rw [haa]
      push_cast
      nlinarith
    have hle : aa 0 ≤ aa M := by
      rw [haa]
      push_cast
      have hM : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
      nlinarith
    rw [intervalIntegral.integral_of_le hle]
    unfold hbKG
    apply setIntegral_mono_set hbG2_abs_integrable
      (Eventually.of_forall fun y => abs_nonneg _)
    apply HasSubset.Subset.eventuallyLE
    intro y hy
    exact lt_trans h0 hy.1
  have haa0 : aa 0 = u / 2 := by rw [haa]; push_cast; ring
  have haaM : aa M = ((M : ℝ) + 1 / 2) * u := by rw [haa]
  have hrw : (∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)) -
      (hbV (((M : ℝ) + 1 / 2) * u) - hbV (u / 2)) / u =
      ((∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)) * u -
        (hbV (aa M) - hbV (aa 0))) / u := by
    rw [haa0, haaM]
    field_simp
    ring
  rw [hrw, abs_div, abs_of_pos hu, div_le_iff₀ hu]
  calc
    |(∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)) * u -
        (hbV (aa M) - hbV (aa 0))|
        ≤ u ^ 2 / 2 * ∫ y in (aa 0)..(aa M), |hbG2 y| := hmain
    _ ≤ u ^ 2 / 2 * hbKG := by
        apply mul_le_mul_of_nonneg_left hKGbound
        positivity
    _ = u / 2 * hbKG * u := by ring

/-! ## The window majorant and the uniform budget -/

/-- Explicit pointwise majorant for the H derivative comb on the window. -/
noncomputable def hbMaj (lam u : ℝ) : ℝ :=
  if u ≤ 1 then
    hbCv1 / 8 * u ^ 2 + hbKG / 2 * u + 4 * hbCvC / (lam ^ 2 * u)
  else
    2 * hbCgC / u ^ 2

/-- The absolute budget constant. -/
noncomputable def hbBudget : ℝ :=
  hbCv1 / 8 + hbKG / 2 + 4 * hbCvC + 2 * hbCgC

theorem hbBudget_nonneg : 0 ≤ hbBudget := by
  have h1 := hbCv1_pos
  have h2 := hbKG_nonneg
  have h3 := hbCvC_pos
  have h4 := hbCgC_pos
  unfold hbBudget
  linarith

private theorem hb_sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **Pointwise majorant bound for the explicit H derivative comb.** -/
theorem hbComb_le_hbMaj (lam u : ℝ)
    (hlam : Real.sqrt 2 ≤ lam)
    (hu1 : lam⁻¹ ≤ u) (hu2 : u ≤ lam) :
    |∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)), hbG ((n : ℝ) * u)| ≤
      hbMaj lam u := by
  have hlam1 : (1 : ℝ) < lam := lt_of_lt_of_le hb_sqrt2_gt_one hlam
  have hlam0 : (0 : ℝ) < lam := lt_trans one_pos hlam1
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (inv_pos.mpr hlam0) hu1
  set M := Nat.floor (lam / u) with hM
  have hMfloor : (M : ℝ) ≤ lam / u := Nat.floor_le (by positivity)
  have hMone : lam / u < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMu_up : (M : ℝ) * u ≤ lam := by
    rw [← le_div_iff₀ hu0]
    exact hMfloor
  have hMu_low : lam - u < (M : ℝ) * u := by
    have h := hMone
    rw [div_lt_iff₀ hu0] at h
    nlinarith
  by_cases hcase : u ≤ 1
  · set S := ∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u) with hS
    set D := (hbV (((M : ℝ) + 1 / 2) * u) - hbV (u / 2)) / u with hD
    have hcomb : |S - D| ≤ u / 2 * hbKG := hb_comb u hu0 M
    have hVhead : |hbV (u / 2)| ≤ hbCv1 * (u / 2) ^ 3 :=
      hbV_head (u / 2) (by linarith) (by linarith)
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := hb_sqrt2_gt_one.le
    have hyplus : (1 : ℝ) / 2 ≤ ((M : ℝ) + 1 / 2) * u := by
      nlinarith [hMu_low, hlam, hs2, hcase]
    have hyplus2 : lam / 2 ≤ ((M : ℝ) + 1 / 2) * u := by
      nlinarith [hMu_low, hu2]
    have hVtail : |hbV (((M : ℝ) + 1 / 2) * u)| ≤
        hbCvC / (((M : ℝ) + 1 / 2) * u) ^ 2 := hbV_tail _ hyplus
    have hcv := hbCvC_pos
    have hyppos : (0 : ℝ) < ((M : ℝ) + 1 / 2) * u := by nlinarith [hyplus2]
    have hVtail2 : |hbV (((M : ℝ) + 1 / 2) * u)| ≤ 4 * hbCvC / lam ^ 2 := by
      refine hVtail.trans ?_
      have hsq : lam ^ 2 / 4 ≤ (((M : ℝ) + 1 / 2) * u) ^ 2 := by
        nlinarith [hyplus2, hlam0]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsq, hcv]
    have hDbound : |D| ≤ (4 * hbCvC / lam ^ 2 + hbCv1 * (u / 2) ^ 3) / u := by
      rw [hD, abs_div, abs_of_pos hu0]
      apply div_le_div_of_nonneg_right _ hu0.le
      calc
        |hbV (((M : ℝ) + 1 / 2) * u) - hbV (u / 2)| =
            |hbV (((M : ℝ) + 1 / 2) * u) + -hbV (u / 2)| := by
          rw [sub_eq_add_neg]
        _ ≤ |hbV (((M : ℝ) + 1 / 2) * u)| + |-hbV (u / 2)| := abs_add_le _ _
        _ = |hbV (((M : ℝ) + 1 / 2) * u)| + |hbV (u / 2)| := by rw [abs_neg]
        _ ≤ 4 * hbCvC / lam ^ 2 + hbCv1 * (u / 2) ^ 3 := by
          linarith [hVtail2, hVhead]
    have htri : |S| ≤ |S - D| + |D| := by
      calc
        |S| = |(S - D) + D| := by rw [sub_add_cancel]
        _ ≤ |S - D| + |D| := abs_add_le _ _
    simp only [hbMaj]; rw [if_pos hcase]
    refine htri.trans ?_
    have hcombine : |S - D| + |D| ≤ u / 2 * hbKG +
        (4 * hbCvC / lam ^ 2 + hbCv1 * (u / 2) ^ 3) / u := by
      linarith [hcomb, hDbound]
    refine hcombine.trans (le_of_eq ?_)
    field_simp
    ring
  · push_neg at hcase
    simp only [hbMaj]; rw [if_neg (not_le.mpr hcase)]
    have hterm : ∀ n ∈ Finset.Icc 1 M,
        |hbG ((n : ℝ) * u)| ≤ hbCgC / u ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnu : (1 : ℝ) ≤ (n : ℝ) * u := by nlinarith
      have h := hbG_tail ((n : ℝ) * u) hnu
      refine h.trans (le_of_eq ?_)
      have hne : ((n : ℝ)) ≠ 0 := by positivity
      field_simp
    have hsum2 : (∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
      have hins : Finset.Icc 1 M ⊆ insert 1 (Finset.Ioo 1 (M + 1)) := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_insert, Finset.mem_Ioo]
        omega
      calc
        (∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ 2)⁻¹)
            ≤ ∑ n ∈ insert 1 (Finset.Ioo 1 (M + 1)), ((n : ℝ) ^ 2)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hins
                (fun n _ _ => by positivity)
        _ = ((1 : ℝ) ^ 2)⁻¹ + ∑ n ∈ Finset.Ioo 1 (M + 1), ((n : ℝ) ^ 2)⁻¹ := by
              rw [Finset.sum_insert (by simp)]
              norm_num
        _ ≤ 1 + 1 := by
              have hIoo := sum_Ioo_inv_sq_le (α := ℝ) 1 (M + 1)
              have : (∑ n ∈ Finset.Ioo 1 (M + 1), ((n : ℝ) ^ 2)⁻¹) ≤ 1 := by
                refine le_trans ?_ (by norm_num : (2 : ℝ) / (1 + 1) ≤ 1)
                convert hIoo using 2
                norm_num
              norm_num
              linarith
        _ = 2 := by norm_num
    calc
      |∑ n ∈ Finset.Icc 1 M, hbG ((n : ℝ) * u)|
          ≤ ∑ n ∈ Finset.Icc 1 M, |hbG ((n : ℝ) * u)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 M, hbCgC / u ^ 2 * ((n : ℝ) ^ 2)⁻¹ :=
            Finset.sum_le_sum hterm
      _ = hbCgC / u ^ 2 * ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]
      _ ≤ hbCgC / u ^ 2 * 2 := by
            apply mul_le_mul_of_nonneg_left hsum2
            have := hbCgC_pos
            positivity
      _ = 2 * hbCgC / u ^ 2 := by ring

/-- **The uniform weighted window integral of the majorant.** -/
theorem hbMaj_integral_le (lam : ℝ) (hlam : Real.sqrt 2 ≤ lam) :
    (∫ u in Icc lam⁻¹ lam, (Real.sqrt u)⁻¹ * hbMaj lam u) ≤ hbBudget := by
  have hlam1 : (1 : ℝ) < lam := lt_of_lt_of_le hb_sqrt2_gt_one hlam
  have hlam0 : (0 : ℝ) < lam := lt_trans one_pos hlam1
  have hinv1 : lam⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hlam1.le
  have hinv0 : (0 : ℝ) < lam⁻¹ := inv_pos.mpr hlam0
  have hsplit : Icc lam⁻¹ lam = Icc lam⁻¹ 1 ∪ Ioc 1 lam :=
    (Set.Icc_union_Ioc_eq_Icc hinv1 hlam1.le).symm
  have hsmall_point : ∀ u ∈ Icc lam⁻¹ (1 : ℝ),
      (Real.sqrt u)⁻¹ * hbMaj lam u ≤ hbCv1 / 8 + hbKG / 2 + 4 * hbCvC := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hinv0 hu.1
    have hu1 : u ≤ 1 := hu.2
    have hsq0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
    simp only [hbMaj]; rw [if_pos hu1]
    have huq : u ≤ Real.sqrt u :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    have hterm1 : (Real.sqrt u)⁻¹ * (hbCv1 / 8 * u ^ 2) ≤ hbCv1 / 8 := by
      have hu2sq : u ^ 2 ≤ Real.sqrt u := by nlinarith [huq]
      rw [mul_comm, mul_inv_le_iff₀ hsq0]
      exact mul_le_mul_of_nonneg_left hu2sq
        (div_nonneg hbCv1_pos.le (by norm_num))
    have hterm2 : (Real.sqrt u)⁻¹ * (hbKG / 2 * u) ≤ hbKG / 2 := by
      rw [mul_comm, mul_inv_le_iff₀ hsq0]
      exact mul_le_mul_of_nonneg_left huq
        (div_nonneg hbKG_nonneg (by norm_num))
    have hterm3 : (Real.sqrt u)⁻¹ * (4 * hbCvC / (lam ^ 2 * u)) ≤ 4 * hbCvC := by
      have hcv := hbCvC_pos
      have hlow : lam⁻¹ ≤ u := hu.1
      have hsqrt_low : lam⁻¹ ≤ Real.sqrt u := by
        have h1 : Real.sqrt lam⁻¹ ≤ Real.sqrt u := Real.sqrt_le_sqrt hlow
        have h2 : lam⁻¹ ≤ Real.sqrt lam⁻¹ :=
          Real.le_sqrt_of_sq_le (by nlinarith [hinv0, hinv1])
        linarith
      have hprod : lam⁻¹ * lam⁻¹ ≤ u * Real.sqrt u :=
        mul_le_mul hlow hsqrt_low hinv0.le hu0.le
      have hsq0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
      have hpos : (0:ℝ) < lam ^ 2 * u * Real.sqrt u :=
        mul_pos (mul_pos (pow_pos hlam0 2) hu0) hsq0
      rw [inv_mul_eq_div, div_div, div_le_iff₀ hpos]
      have hla : (0:ℝ) < lam ^ 2 := pow_pos hlam0 2
      have h2 : lam ^ 2 * (lam⁻¹ * lam⁻¹) ≤ lam ^ 2 * (u * Real.sqrt u) :=
        mul_le_mul_of_nonneg_left hprod hla.le
      have hcancel : lam ^ 2 * (lam⁻¹ * lam⁻¹) = 1 := by
        field_simp
      have hge1 : (1:ℝ) ≤ lam ^ 2 * u * Real.sqrt u := by
        calc (1:ℝ) = lam ^ 2 * (lam⁻¹ * lam⁻¹) := hcancel.symm
          _ ≤ lam ^ 2 * (u * Real.sqrt u) := h2
          _ = lam ^ 2 * u * Real.sqrt u := by ring
      nlinarith [hge1, hcv]
    calc
      (Real.sqrt u)⁻¹ * (hbCv1 / 8 * u ^ 2 + hbKG / 2 * u +
          4 * hbCvC / (lam ^ 2 * u))
          = (Real.sqrt u)⁻¹ * (hbCv1 / 8 * u ^ 2) +
            (Real.sqrt u)⁻¹ * (hbKG / 2 * u) +
            (Real.sqrt u)⁻¹ * (4 * hbCvC / (lam ^ 2 * u)) := by ring
      _ ≤ hbCv1 / 8 + hbKG / 2 + 4 * hbCvC := by
            linarith [hterm1, hterm2, hterm3]
  have hcont_w : ContinuousOn (fun u : ℝ => (Real.sqrt u)⁻¹)
      {u : ℝ | 0 < u} := by
    apply ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn
    intro u hu
    exact (Real.sqrt_pos.mpr hu).ne'
  have hint_small : IntegrableOn
      (fun u : ℝ => (Real.sqrt u)⁻¹ * hbMaj lam u) (Icc lam⁻¹ 1) volume := by
    apply MeasureTheory.IntegrableOn.congr_fun
      (f := fun u : ℝ => (Real.sqrt u)⁻¹ *
        (hbCv1 / 8 * u ^ 2 + hbKG / 2 * u + 4 * hbCvC / (lam ^ 2 * u)))
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.mul
      · apply hcont_w.mono
        intro u hu
        exact lt_of_lt_of_le hinv0 hu.1
      · apply ContinuousOn.add
        · apply ContinuousOn.add
          · fun_prop
          · fun_prop
        · apply ContinuousOn.div continuousOn_const
          · fun_prop
          · intro u hu
            have : (0:ℝ) < u := lt_of_lt_of_le hinv0 hu.1
            positivity
    · intro u hu
      simp only [hbMaj]; rw [if_pos hu.2]
    · exact measurableSet_Icc
  have hint_large_maj : IntegrableOn
      (fun u : ℝ => 2 * hbCgC / u ^ 2) (Ioc 1 lam) volume := by
    apply MeasureTheory.IntegrableOn.mono_set (t := Icc (1:ℝ) lam)
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro u hu
        have : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1
        positivity
    · exact Set.Ioc_subset_Icc_self
  have hint_large : IntegrableOn
      (fun u : ℝ => (Real.sqrt u)⁻¹ * hbMaj lam u) (Ioc 1 lam) volume := by
    apply MeasureTheory.IntegrableOn.congr_fun
      (f := fun u : ℝ => (Real.sqrt u)⁻¹ * (2 * hbCgC / u ^ 2))
    · apply MeasureTheory.IntegrableOn.mono_set (t := Icc (1:ℝ) lam)
      · apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.mul
        · apply hcont_w.mono
          intro u hu
          exact lt_of_lt_of_le one_pos hu.1
        · apply ContinuousOn.div continuousOn_const
          · fun_prop
          · intro u hu
            have : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1
            positivity
      · exact Set.Ioc_subset_Icc_self
    · intro u hu
      simp only [hbMaj]; rw [if_neg (not_le.mpr hu.1)]
    · exact measurableSet_Ioc
  have hsmall_bound :
      (∫ u in Icc lam⁻¹ 1, (Real.sqrt u)⁻¹ * hbMaj lam u) ≤
        hbCv1 / 8 + hbKG / 2 + 4 * hbCvC := by
    have hconstInt : IntegrableOn
        (fun _ : ℝ => hbCv1 / 8 + hbKG / 2 + 4 * hbCvC)
        (Icc lam⁻¹ 1) volume :=
      MeasureTheory.integrableOn_const
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have h := MeasureTheory.setIntegral_mono_on hint_small hconstInt
      measurableSet_Icc hsmall_point
    refine h.trans ?_
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Icc]
    have hcv := hbCv1_pos
    have hkg := hbKG_nonneg
    have hcc := hbCvC_pos
    have hvol : max (1 - lam⁻¹) 0 ≤ 1 := by
      apply max_le _ zero_le_one
      linarith [hinv0]
    nlinarith [hvol]
  have hlarge_bound :
      (∫ u in Ioc 1 lam, (Real.sqrt u)⁻¹ * hbMaj lam u) ≤ 2 * hbCgC := by
    have hpoint : ∀ u ∈ Ioc (1:ℝ) lam,
        (Real.sqrt u)⁻¹ * hbMaj lam u ≤ 2 * hbCgC / u ^ 2 := by
      intro u hu
      have hu1 : (1:ℝ) < u := hu.1
      have hu0 : (0:ℝ) < u := lt_trans one_pos hu1
      simp only [hbMaj]; rw [if_neg (not_le.mpr hu1)]
      have hsq1 : (1:ℝ) ≤ Real.sqrt u := by
        rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt hu1.le
      have hinv : (Real.sqrt u)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact hsq1
      have hnn : (0:ℝ) ≤ 2 * hbCgC / u ^ 2 := by
        have := hbCgC_pos
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hinv hnn]
    have h := MeasureTheory.setIntegral_mono_on hint_large hint_large_maj
      measurableSet_Ioc hpoint
    refine h.trans ?_
    have hIoc_eq : (∫ u in Ioc (1:ℝ) lam, 2 * hbCgC / u ^ 2) =
        ∫ u in (1:ℝ)..lam, 2 * hbCgC / u ^ 2 := by
      rw [intervalIntegral.integral_of_le hlam1.le]
    rw [hIoc_eq]
    have hftc : (∫ u in (1:ℝ)..lam, 2 * hbCgC / u ^ 2) =
        -(2 * hbCgC) / lam - -(2 * hbCgC) / 1 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => -(2 * hbCgC) / y)
      · intro u hu
        rw [Set.uIcc_of_le hlam1.le] at hu
        have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1
        have h0 := (hasDerivAt_inv hu0.ne').const_mul (2 * hbCgC)
        have h1 : HasDerivAt (fun y : ℝ => -(2 * hbCgC * y⁻¹))
            (-(2 * hbCgC * -(u ^ 2)⁻¹)) u := h0.neg
        have heq : (fun y : ℝ => -(2 * hbCgC * y⁻¹)) =
            fun y : ℝ => -(2 * hbCgC) / y := by
          funext y
          rw [neg_div]
          ring
        rw [heq] at h1
        exact h1.congr_deriv (by field_simp)
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const
        · fun_prop
        · intro u hu
          rw [Set.uIcc_of_le hlam1.le] at hu
          have : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1
          positivity
    rw [hftc]
    have hcg := hbCgC_pos
    have hpos : (0:ℝ) ≤ 2 * hbCgC / lam := by positivity
    have hval2 : -(2 * hbCgC) / lam - -(2 * hbCgC) / 1 =
        2 * hbCgC - 2 * hbCgC / lam := by
      rw [div_one, neg_div]
      ring
    rw [hval2]
    linarith
  have hdisj : Disjoint (Icc lam⁻¹ (1:ℝ)) (Ioc (1:ℝ) lam) := by
    apply Set.disjoint_left.mpr
    intro x hx1 hx2
    exact absurd hx1.2 (not_le.mpr hx2.1)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
    hint_small hint_large]
  unfold hbBudget
  linarith [hsmall_bound, hlarge_bound]

/--
**W5_EXPLICIT_H_QCOMB_BOUNDED** (verdict dee1ec4d): the explicit target
derivative comb admits a pointwise explicit majorant whose weighted window
integral is bounded by one absolute constant, uniformly over every window
`[lam⁻¹, lam]` with `lam ≥ √2` — in particular over the whole selected
family `lam = selectedFerrersPaperLambda k`.  No source hypotheses.
-/
theorem explicitH_derivative_comb_budget :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ lam : ℝ, Real.sqrt 2 ≤ lam →
        (∀ u ∈ Icc lam⁻¹ lam,
          |∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)), hbG ((n : ℝ) * u)| ≤
            hbMaj lam u) ∧
        (∫ u in Icc lam⁻¹ lam, (Real.sqrt u)⁻¹ * hbMaj lam u) ≤ D :=
  ⟨hbBudget, hbBudget_nonneg, fun lam hlam =>
    ⟨fun u hu => hbComb_le_hbMaj lam u hlam hu.1 hu.2,
      hbMaj_integral_le lam hlam⟩⟩

#print axioms hb_cell
#print axioms hb_comb
#print axioms explicitH_derivative_comb_budget

end Q3.RouteB.D0Pstar
