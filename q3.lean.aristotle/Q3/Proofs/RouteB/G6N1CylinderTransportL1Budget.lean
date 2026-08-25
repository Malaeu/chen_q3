import Q3.Proofs.RouteB.G6N1ExplicitHDerivativeCombBudget
import Q3.Proofs.RouteB.G6N1ParabolicCylinderD0D4Exact

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# W_TRANSPORT_L1_NODE (verdict 4c0e13ba, node 2)

Absolute `L¹` bounds for the explicit cylinder transport derivatives
`d/dx (x² W'(x))` of the two fixed target profiles
`W_n(x) = parabolicCylinderD n (projectCylinderArgument x)`, `n ∈ {0, 4}`.
Both are polynomial-times-Gaussian; the profiles do not depend on `k`, so
the constants are absolute.  Inputs: none.
-/

/-- The mode-0 physical cylinder profile `W₀(x) = e^{-π x²}`. -/
def ctW0 (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

/-- The mode-4 physical cylinder profile
`W₄(x) = (16π²x⁴ - 24πx² + 3) e^{-π x²}`. -/
def ctW4 (x : ℝ) : ℝ :=
  (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) *
    Real.exp (-Real.pi * x ^ 2)

/-- The transport derivative of the mode-0 profile:
`(x² W₀')' = (4π²x⁴ - 6πx²) e^{-π x²}`. -/
def ctT0 (x : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * x ^ 4 - 6 * Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2)

/-- The transport derivative of the mode-4 profile:
`(x² W₄')' = (64π⁴x⁸ - 448π³x⁶ + 668π²x⁴ - 162πx²) e^{-π x²}`. -/
def ctT4 (x : ℝ) : ℝ :=
  (64 * Real.pi ^ 4 * x ^ 8 - 448 * Real.pi ^ 3 * x ^ 6 +
      668 * Real.pi ^ 2 * x ^ 4 - 162 * Real.pi * x ^ 2) *
    Real.exp (-Real.pi * x ^ 2)

/-- Link to the committed cylinder target: `ctW0 = D₀ ∘ proj`. -/
theorem ctW0_eq_cylinder (x : ℝ) :
    ctW0 x = parabolicCylinderD 0 (projectCylinderArgument x) := by
  rw [parabolicCylinderD, Polynomial.hermite_zero, projectCylinderArgument]
  unfold ctW0
  have hsq : (Real.sqrt (4 * Real.pi) * x) ^ 2 = 4 * Real.pi * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq]
  simp
  ring_nf

private theorem ct_exp_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))
      (-2 * Real.pi * y * Real.exp (-Real.pi * y ^ 2)) y := by
  have h1 : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2) (-2 * Real.pi * y) y := by
    have := (hasDerivAt_pow 2 y).const_mul (-Real.pi)
    exact this.congr_deriv (by push_cast; ring)
  have := h1.exp
  simpa [mul_comm] using this

private theorem ct_polyexp_hasDerivAt {P : ℝ → ℝ} {p : ℝ} (y : ℝ)
    (hP : HasDerivAt P p y) :
    HasDerivAt (fun t : ℝ => P t * Real.exp (-Real.pi * t ^ 2))
      ((p - 2 * Real.pi * y * P y) * Real.exp (-Real.pi * y ^ 2)) y := by
  have h := hP.mul (ct_exp_hasDerivAt y)
  exact h.congr_deriv (by ring)

/-- `x² W₀'` has derivative `ctT0`. -/
private theorem ctW0_transport_hasDerivAt (y : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 *
        (-2 * Real.pi * x * Real.exp (-Real.pi * x ^ 2)))
      (ctT0 y) y := by
  have hP : HasDerivAt (fun t : ℝ => -2 * Real.pi * t ^ 3)
      (-2 * Real.pi * (3 * y ^ 2)) y := by
    have h3 := (hasDerivAt_pow 3 y).const_mul (-2 * Real.pi)
    exact h3.congr_deriv (by push_cast; ring)
  have h := ct_polyexp_hasDerivAt y hP
  have hfun : (fun t : ℝ => -2 * Real.pi * t ^ 3 * Real.exp (-Real.pi * t ^ 2)) =
      fun x : ℝ => x ^ 2 * (-2 * Real.pi * x * Real.exp (-Real.pi * x ^ 2)) := by
    funext t
    ring
  rw [hfun] at h
  exact h.congr_deriv (by unfold ctT0; ring)

/-- `x² W₄'` has derivative `ctT4`. -/
private theorem ctW4_transport_hasDerivAt (y : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 *
        ((-32 * Real.pi ^ 3 * x ^ 5 + 112 * Real.pi ^ 2 * x ^ 3 -
            54 * Real.pi * x) * Real.exp (-Real.pi * x ^ 2)))
      (ctT4 y) y := by
  have hP : HasDerivAt
      (fun t : ℝ => -32 * Real.pi ^ 3 * t ^ 7 + 112 * Real.pi ^ 2 * t ^ 5 -
        54 * Real.pi * t ^ 3)
      (-32 * Real.pi ^ 3 * (7 * y ^ 6) + 112 * Real.pi ^ 2 * (5 * y ^ 4) -
        54 * Real.pi * (3 * y ^ 2)) y := by
    have h7 := (hasDerivAt_pow 7 y).const_mul (-32 * Real.pi ^ 3)
    have h5 := (hasDerivAt_pow 5 y).const_mul (112 * Real.pi ^ 2)
    have h3 := (hasDerivAt_pow 3 y).const_mul (54 * Real.pi)
    exact ((HasDerivAt.add h7 h5).sub h3).congr_deriv (by push_cast; ring)
  have h := ct_polyexp_hasDerivAt y hP
  have hfun : (fun t : ℝ =>
      (-32 * Real.pi ^ 3 * t ^ 7 + 112 * Real.pi ^ 2 * t ^ 5 -
        54 * Real.pi * t ^ 3) * Real.exp (-Real.pi * t ^ 2)) =
      fun x : ℝ => x ^ 2 *
        ((-32 * Real.pi ^ 3 * x ^ 5 + 112 * Real.pi ^ 2 * x ^ 3 -
            54 * Real.pi * x) * Real.exp (-Real.pi * x ^ 2)) := by
    funext t
    ring
  rw [hfun] at h
  exact h.congr_deriv (by unfold ctT4; ring)

/-- The mode-4 derivative used above is the true `W₄'`. -/
private theorem ctW4_hasDerivAt (y : ℝ) :
    HasDerivAt ctW4
      ((-32 * Real.pi ^ 3 * y ^ 5 + 112 * Real.pi ^ 2 * y ^ 3 -
          54 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2)) y := by
  have hP : HasDerivAt
      (fun t : ℝ => 16 * Real.pi ^ 2 * t ^ 4 - 24 * Real.pi * t ^ 2 + 3)
      (16 * Real.pi ^ 2 * (4 * y ^ 3) - 24 * Real.pi * (2 * y) + 0) y := by
    have h4 := (hasDerivAt_pow 4 y).const_mul (16 * Real.pi ^ 2)
    have h2 := (hasDerivAt_pow 2 y).const_mul (24 * Real.pi)
    have hc := hasDerivAt_const y (3 : ℝ)
    exact ((HasDerivAt.sub h4 h2).add hc).congr_deriv (by push_cast; ring)
  have h := ct_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    (16 * Real.pi ^ 2 * t ^ 4 - 24 * Real.pi * t ^ 2 + 3) *
      Real.exp (-Real.pi * t ^ 2)) _ y
  exact h.congr_deriv (by ring)

/-- The mode-0 derivative shape. -/
private theorem ctW0_hasDerivAt (y : ℝ) :
    HasDerivAt ctW0 (-2 * Real.pi * y * Real.exp (-Real.pi * y ^ 2)) y :=
  ct_exp_hasDerivAt y

private theorem ct_gauss_poly_integrable (c : ℝ) (k : ℕ) :
    Integrable (fun y : ℝ => c * (y ^ (2 * k) * Real.exp (-Real.pi * y ^ 2)))
      volume := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
    (s := ((2 * k : ℕ) : ℝ))
    (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine (h.const_mul c).congr ?_
  filter_upwards [] with y
  rw [Real.rpow_natCast]

private theorem ctT0_abs_integrable :
    Integrable (fun y : ℝ => |ctT0 y|) volume := by
  have hQ := (ct_gauss_poly_integrable (4 * Real.pi ^ 2) 2).add
    (ct_gauss_poly_integrable (6 * Real.pi) 1)
  refine Integrable.mono' hQ ?_ ?_
  · unfold ctT0
    fun_prop
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_abs]
    unfold ctT0
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hpi := Real.pi_pos
    have h4 : (0:ℝ) ≤ y ^ 4 := by positivity
    have h2 : (0:ℝ) ≤ y ^ 2 := by positivity
    have hexp : (0:ℝ) < Real.exp (-Real.pi * y ^ 2) := Real.exp_pos _
    have habs : |4 * Real.pi ^ 2 * y ^ 4 - 6 * Real.pi * y ^ 2| ≤
        4 * Real.pi ^ 2 * y ^ 4 + 6 * Real.pi * y ^ 2 := by
      have hA : (0:ℝ) ≤ 4 * Real.pi ^ 2 * y ^ 4 := by positivity
      have hB : (0:ℝ) ≤ 6 * Real.pi * y ^ 2 := by positivity
      rw [abs_le]
      constructor <;> nlinarith [hA, hB]
    calc
      |4 * Real.pi ^ 2 * y ^ 4 - 6 * Real.pi * y ^ 2| *
          Real.exp (-Real.pi * y ^ 2)
          ≤ (4 * Real.pi ^ 2 * y ^ 4 + 6 * Real.pi * y ^ 2) *
            Real.exp (-Real.pi * y ^ 2) :=
            mul_le_mul_of_nonneg_right habs hexp.le
      _ = 4 * Real.pi ^ 2 * (y ^ (2 * 2) * Real.exp (-Real.pi * y ^ 2)) +
            6 * Real.pi * (y ^ (2 * 1) * Real.exp (-Real.pi * y ^ 2)) := by
            norm_num
            ring

private theorem ctT4_abs_integrable :
    Integrable (fun y : ℝ => |ctT4 y|) volume := by
  have hQ := (((ct_gauss_poly_integrable (64 * Real.pi ^ 4) 4).add
    (ct_gauss_poly_integrable (448 * Real.pi ^ 3) 3)).add
    (ct_gauss_poly_integrable (668 * Real.pi ^ 2) 2)).add
    (ct_gauss_poly_integrable (162 * Real.pi) 1)
  refine Integrable.mono' hQ ?_ ?_
  · unfold ctT4
    fun_prop
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_abs]
    unfold ctT4
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hpi := Real.pi_pos
    have hexp : (0:ℝ) < Real.exp (-Real.pi * y ^ 2) := Real.exp_pos _
    have hA : (0:ℝ) ≤ 64 * Real.pi ^ 4 * y ^ 8 := by positivity
    have hB : (0:ℝ) ≤ 448 * Real.pi ^ 3 * y ^ 6 := by positivity
    have hC : (0:ℝ) ≤ 668 * Real.pi ^ 2 * y ^ 4 := by positivity
    have hD : (0:ℝ) ≤ 162 * Real.pi * y ^ 2 := by positivity
    have habs : |64 * Real.pi ^ 4 * y ^ 8 - 448 * Real.pi ^ 3 * y ^ 6 +
        668 * Real.pi ^ 2 * y ^ 4 - 162 * Real.pi * y ^ 2| ≤
        64 * Real.pi ^ 4 * y ^ 8 + 448 * Real.pi ^ 3 * y ^ 6 +
        668 * Real.pi ^ 2 * y ^ 4 + 162 * Real.pi * y ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [hA, hB, hC, hD]
    calc
      |64 * Real.pi ^ 4 * y ^ 8 - 448 * Real.pi ^ 3 * y ^ 6 +
          668 * Real.pi ^ 2 * y ^ 4 - 162 * Real.pi * y ^ 2| *
          Real.exp (-Real.pi * y ^ 2)
          ≤ (64 * Real.pi ^ 4 * y ^ 8 + 448 * Real.pi ^ 3 * y ^ 6 +
              668 * Real.pi ^ 2 * y ^ 4 + 162 * Real.pi * y ^ 2) *
            Real.exp (-Real.pi * y ^ 2) :=
            mul_le_mul_of_nonneg_right habs hexp.le
      _ = 64 * Real.pi ^ 4 * (y ^ (2 * 4) * Real.exp (-Real.pi * y ^ 2)) +
            448 * Real.pi ^ 3 * (y ^ (2 * 3) * Real.exp (-Real.pi * y ^ 2)) +
            668 * Real.pi ^ 2 * (y ^ (2 * 2) * Real.exp (-Real.pi * y ^ 2)) +
            162 * Real.pi * (y ^ (2 * 1) * Real.exp (-Real.pi * y ^ 2)) := by
            norm_num
            ring

/--
**W_TRANSPORT_L1_NODE.**  The transport derivatives of both fixed cylinder
profiles have absolute `L¹` mass: one constant, independent of the selected
index, bounds `∫ |(x² W_n')'|` for `n ∈ {0, 4}`.  Inputs: none.
-/
theorem cylinderTransport_L1_bounded :
    ∃ D : ℝ, 0 ≤ D ∧
      (∫ y : ℝ, |ctT0 y|) ≤ D ∧ (∫ y : ℝ, |ctT4 y|) ≤ D ∧
      Integrable (fun y : ℝ => |ctT0 y|) volume ∧
      Integrable (fun y : ℝ => |ctT4 y|) volume := by
  refine ⟨(∫ y : ℝ, |ctT0 y|) + (∫ y : ℝ, |ctT4 y|), ?_, ?_, ?_,
    ctT0_abs_integrable, ctT4_abs_integrable⟩
  · have h0 : (0:ℝ) ≤ ∫ y : ℝ, |ctT0 y| := by positivity
    have h4 : (0:ℝ) ≤ ∫ y : ℝ, |ctT4 y| := by positivity
    linarith
  · have h4 : (0:ℝ) ≤ ∫ y : ℝ, |ctT4 y| := by positivity
    linarith
  · have h0 : (0:ℝ) ≤ ∫ y : ℝ, |ctT0 y| := by positivity
    linarith

#print axioms ctW0_eq_cylinder
#print axioms cylinderTransport_L1_bounded

end Q3.RouteB.D0Pstar
