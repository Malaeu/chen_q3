import Q3.Basic.Defs

set_option linter.mathlibStandardSet false

open Complex

noncomputable section

namespace Q3.RouteB

/-- Riemann's entire `xi`, expressed through Mathlib's pole-removed entire
completion.  This formula has the correct removable values at `0` and `1`. -/
def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

/-- The centered entire function used by Route B. -/
def centeredXi (z : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + Complex.I * z)

/-- The open centered strip corresponding to the critical strip. -/
def centeredCriticalStrip : Set ℂ :=
  {z | |z.im| < 1 / 2}

/-- All centered zeros in the open strip are real. -/
def CenteredXiZerosReal : Prop :=
  ∀ z : ℂ, centeredXi z = 0 → z ∈ centeredCriticalStrip → z.im = 0

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  have hcomp : Differentiable ℂ completedRiemannZeta₀ :=
    differentiable_completedZeta₀
  unfold riemannXi
  fun_prop

theorem differentiable_centeredXi : Differentiable ℂ centeredXi := by
  have hxi : Differentiable ℂ riemannXi := differentiable_riemannXi
  unfold centeredXi
  fun_prop

@[simp] theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

@[simp] theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- Away from the removable points, the entire definition agrees with the
usual `s(s-1)Λ(s)/2` formula. -/
theorem riemannXi_eq_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp [hs0, h1s]
  ring

theorem completedRiemannZeta_eq_Gamma_mul_riemannZeta
    {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hdiv := riemannZeta_def_of_ne_zero hs0
  have hmul : riemannZeta s * Gammaℝ s = completedRiemannZeta s :=
    (eq_div_iff hGamma).mp hdiv
  simpa [mul_comm] using hmul.symm

/-- In the open critical strip, `riemannXi` and Mathlib's `riemannZeta` have
exactly the same zeros. -/
theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs_ne_zero : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs0
  have hs_ne_one : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs1
  rw [riemannXi_eq_completedRiemannZeta hs_ne_zero hs_ne_one,
    completedRiemannZeta_eq_Gamma_mul_riemannZeta hs0]
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne_one
  simp [hs_ne_zero, hsm1, hGamma]

@[simp] theorem centered_argument_re (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z).re = 1 / 2 - z.im := by
  simp
  ring

/-- Inverse affine coordinate from the critical strip to the centered strip. -/
def centeredCoordinate (s : ℂ) : ℂ :=
  -Complex.I * (s - (1 / 2 : ℂ))

@[simp] theorem centeredCoordinate_im (s : ℂ) :
    (centeredCoordinate s).im = 1 / 2 - s.re := by
  simp [centeredCoordinate]

@[simp] theorem centered_argument_centeredCoordinate (s : ℂ) :
    (1 / 2 : ℂ) + Complex.I * centeredCoordinate s = s := by
  simp [centeredCoordinate]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- Exact Lean pin of the classical Route-B interface: the project definition
of RH is equivalent to reality of all centered `Xi` zeros in the open strip. -/
theorem rh_iff_centeredXi_zeros_real :
    Q3.RH ↔ CenteredXiZerosReal := by
  constructor
  · intro hRH z hz hstrip
    have him : |z.im| < 1 / 2 := hstrip
    have him_bounds := abs_lt.mp him
    have hs0 : 0 < ((1 / 2 : ℂ) + Complex.I * z).re := by
      rw [centered_argument_re]
      linarith
    have hs1 : ((1 / 2 : ℂ) + Complex.I * z).re < 1 := by
      rw [centered_argument_re]
      linarith
    have hzeta : riemannZeta ((1 / 2 : ℂ) + Complex.I * z) = 0 :=
      (riemannXi_eq_zero_iff_riemannZeta_eq_zero hs0 hs1).mp hz
    have hline := hRH ((1 / 2 : ℂ) + Complex.I * z) hzeta hs0 hs1
    rw [centered_argument_re] at hline
    linarith
  · intro hcenter s hzeta hs0 hs1
    let z := centeredCoordinate s
    have hzXi : centeredXi z = 0 := by
      unfold centeredXi
      rw [centered_argument_centeredCoordinate]
      exact (riemannXi_eq_zero_iff_riemannZeta_eq_zero hs0 hs1).mpr hzeta
    have hzstrip : z ∈ centeredCriticalStrip := by
      change |z.im| < 1 / 2
      rw [show z.im = 1 / 2 - s.re by simp [z]]
      rw [abs_lt]
      constructor <;> linarith
    have hzreal := hcenter z hzXi hzstrip
    rw [show z.im = 1 / 2 - s.re by simp [z]] at hzreal
    linarith

#print axioms rh_iff_centeredXi_zeros_real

end Q3.RouteB
