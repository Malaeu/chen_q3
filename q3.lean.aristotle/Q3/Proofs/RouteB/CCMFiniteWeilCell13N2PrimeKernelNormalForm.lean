import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2W02NormalForm

/-!
# Exact prime-kernel normal form for the CCM cell `(13, 2)`

This file normalizes the seven literal prime-component representatives while
keeping all remaining trigonometric values symbolic.
-/

namespace Q3.RouteB

open ArithmeticFunction

/- P-PRIME-1 preflight: the `k = 8` prime-power weight. -/
private theorem ccmPrime_plant_eight_weight :
    vonMangoldt 8 * (Real.sqrt (8 : ℝ))⁻¹ =
      Real.log 2 * (2 * Real.sqrt 2)⁻¹ := by
  have hsqrt8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [show 8 = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num),
    vonMangoldt_apply_prime (by norm_num), hsqrt8]
  norm_num

/- P-PRIME-2 preflight: the asymmetric off-diagonal orientation. -/
private theorem ccmPrime_plant_offdiag_orientation
    (L x : ℝ) :
    ccmQKernel L (-2) 1 x =
      -(Real.sin (2 * Real.pi * x / L) +
          Real.sin (4 * Real.pi * x / L)) / (3 * Real.pi) := by
  unfold ccmQKernel
  norm_num
  rw [show -(2 * Real.pi * 2 * x) / L =
    -(4 * Real.pi * x / L) by ring, Real.sin_neg]
  ring

/- P-PRIME-3 preflight: the diagonal mode-two frequency. -/
private theorem ccmPrime_plant_diagonal_frequency
    (L x : ℝ) :
    ccmQKernel L (-2) (-2) x =
      2 * (L - x) / L * Real.cos (4 * Real.pi * x / L) := by
  unfold ccmQKernel
  norm_num
  rw [show -(2 * Real.pi * 2 * x) / L =
    -(4 * Real.pi * x / L) by ring, Real.cos_neg]
  exact Or.inl rfl

/- P-PRIME-4 preflight: diagonal and asymmetric `p = 13` boundary values. -/
private theorem ccmPrime_plant_boundary_thirteen :
    let L := ccmL 13
    ccmQKernel L 0 0 L = 0 ∧
      ccmQKernel L (-2) 1 L = 0 := by
  dsimp only
  have hL : ccmL 13 ≠ 0 := ne_of_gt (ccmL_pos 13 (by norm_num))
  constructor
  · simp [ccmQKernel]
  · rw [ccmPrime_plant_offdiag_orientation]
    field_simp [hL]
    rw [Real.sin_two_pi]
    norm_num
    simpa [mul_comm] using Real.sin_int_mul_pi 4

private theorem ccmPrime_log_four :
    Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

private theorem ccmPrime_log_eight :
    Real.log (8 : ℝ) = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num

private theorem ccmPrime_log_nine :
    Real.log (9 : ℝ) = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  norm_num

private theorem ccmPrime_sqrt_four :
    Real.sqrt (4 : ℝ) = 2 := by norm_num

private theorem ccmPrime_sqrt_eight :
    Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 4 * 2 by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

private theorem ccmPrime_sqrt_nine :
    Real.sqrt (9 : ℝ) = 3 := by norm_num

private theorem ccmPrime_kernel_two_minus_one
    (L x : ℝ) :
    ccmQKernel L (-2) (-1) x =
      (Real.sin (2 * Real.pi * x / L) -
        Real.sin (4 * Real.pi * x / L)) / Real.pi := by
  unfold ccmQKernel
  norm_num
  rw [show -(2 * Real.pi * x) / L =
      -(2 * Real.pi * x / L) by ring,
    show -(2 * Real.pi * 2 * x) / L =
      -(4 * Real.pi * x / L) by ring,
    Real.sin_neg, Real.sin_neg]
  ring

private theorem ccmPrime_kernel_two_zero
    (L x : ℝ) :
    ccmQKernel L (-2) 0 x =
      -Real.sin (4 * Real.pi * x / L) / (2 * Real.pi) := by
  unfold ccmQKernel
  norm_num
  rw [show -(2 * Real.pi * 2 * x) / L =
      -(4 * Real.pi * x / L) by ring,
    Real.sin_neg]
  ring

private theorem ccmPrime_kernel_one_one
    (L x : ℝ) :
    ccmQKernel L (-1) (-1) x =
      2 * (L - x) / L * Real.cos (2 * Real.pi * x / L) := by
  unfold ccmQKernel
  norm_num
  rw [show -(2 * Real.pi * x) / L =
      -(2 * Real.pi * x / L) by ring,
    Real.cos_neg]
  exact Or.inl rfl

private theorem ccmPrime_kernel_one_zero
    (L x : ℝ) :
    ccmQKernel L (-1) 0 x =
      -Real.sin (2 * Real.pi * x / L) / Real.pi := by
  unfold ccmQKernel
  norm_num
  rw [show -(2 * Real.pi * x) / L =
      -(2 * Real.pi * x / L) by ring,
    Real.sin_neg]

private theorem ccmPrime_kernel_zero_zero
    (L x : ℝ) :
    ccmQKernel L 0 0 x = 2 * (L - x) / L := by
  simp [ccmQKernel]

private theorem ccmPrime_all_boundary_thirteen :
    let L := ccmL 13
    ccmQKernel L (-2) (-2) L = 0 ∧
      ccmQKernel L (-2) (-1) L = 0 ∧
      ccmQKernel L (-2) 0 L = 0 ∧
      ccmQKernel L (-2) 1 L = 0 ∧
      ccmQKernel L (-1) (-1) L = 0 ∧
      ccmQKernel L (-1) 0 L = 0 ∧
      ccmQKernel L 0 0 L = 0 := by
  dsimp only
  have hL : ccmL 13 ≠ 0 := ne_of_gt (ccmL_pos 13 (by norm_num))
  have hsin4 : Real.sin (Real.pi * 4) = 0 := by
    simpa [mul_comm] using Real.sin_int_mul_pi 4
  constructor
  · rw [ccmPrime_plant_diagonal_frequency]
    simp
  constructor
  · rw [ccmPrime_kernel_two_minus_one]
    field_simp [hL]
    rw [Real.sin_two_pi]
    norm_num
    exact hsin4
  constructor
  · rw [ccmPrime_kernel_two_zero]
    field_simp [hL]
    rw [show 4 * Real.pi = Real.pi * 4 by ring, hsin4]
    norm_num
  constructor
  · exact ccmPrime_plant_boundary_thirteen.2
  constructor
  · rw [ccmPrime_kernel_one_one]
    simp
  constructor
  · rw [ccmPrime_kernel_one_zero]
    field_simp [hL]
    rw [Real.sin_two_pi]
    norm_num
  · rw [ccmPrime_kernel_zero_zero]
    simp

private theorem ccmPrimeEntryN1_thirteen_of_kernel
    (n m : ℤ) (K : ℝ → ℝ)
    (hK : ∀ x, ccmQKernel (ccmL 13) n m x = K x)
    (hKL : K (ccmL 13) = 0) :
    ccmPrimeEntryN1 13 n m =
      Real.log 2 *
          ((Real.sqrt 2)⁻¹ * K (Real.log 2) +
            (2 : ℝ)⁻¹ * K (2 * Real.log 2) +
            (2 * Real.sqrt 2)⁻¹ * K (3 * Real.log 2)) +
        Real.log 3 *
          ((Real.sqrt 3)⁻¹ * K (Real.log 3) +
            (3 : ℝ)⁻¹ * K (2 * Real.log 3)) +
        Real.log 5 * (Real.sqrt 5)⁻¹ * K (Real.log 5) +
        Real.log 7 * (Real.sqrt 7)⁻¹ * K (Real.log 7) +
        Real.log 11 * (Real.sqrt 11)⁻¹ * K (Real.log 11) := by
  unfold ccmPrimeEntryN1
  simp_rw [mul_assoc]
  rw [ccmVonMangoldt_sum_Icc_2_13]
  norm_num
  rw [ccmPrime_log_four, ccmPrime_log_eight, ccmPrime_log_nine,
    ccmPrime_sqrt_eight]
  simp_rw [hK]
  rw [show Real.log (13 : ℝ) = ccmL 13 by rfl, hKL]
  norm_num

/--
Exact seven-representative symbolic normal form of the literal CCM prime
component for the cell `(13,2)`. Prime-power logarithms and reciprocal
square-root weights are normalized; the seven fixed `ccmQKernel` branches are
unfolded; the `k = 13` boundary term is proved zero. No trigonometric value is
numerically enclosed.
-/
theorem ccmPrimeEntryN1_13_seven_class_exact_normal_form :
    let L := ccmL 13
    let primeFunctional : (ℝ → ℝ) → ℝ := fun K =>
      Real.log 2 *
          ((Real.sqrt 2)⁻¹ * K (Real.log 2) +
            (2 : ℝ)⁻¹ * K (2 * Real.log 2) +
            (2 * Real.sqrt 2)⁻¹ * K (3 * Real.log 2)) +
        Real.log 3 *
          ((Real.sqrt 3)⁻¹ * K (Real.log 3) +
            (3 : ℝ)⁻¹ * K (2 * Real.log 3)) +
        Real.log 5 * (Real.sqrt 5)⁻¹ * K (Real.log 5) +
        Real.log 7 * (Real.sqrt 7)⁻¹ * K (Real.log 7) +
        Real.log 11 * (Real.sqrt 11)⁻¹ * K (Real.log 11)
    let K22 : ℝ → ℝ := fun x =>
      2 * (L - x) / L * Real.cos (4 * Real.pi * x / L)
    let K2m1 : ℝ → ℝ := fun x =>
      (Real.sin (2 * Real.pi * x / L) -
          Real.sin (4 * Real.pi * x / L)) / Real.pi
    let K20 : ℝ → ℝ := fun x =>
      -Real.sin (4 * Real.pi * x / L) / (2 * Real.pi)
    let K21 : ℝ → ℝ := fun x =>
      -(Real.sin (2 * Real.pi * x / L) +
          Real.sin (4 * Real.pi * x / L)) / (3 * Real.pi)
    let K11 : ℝ → ℝ := fun x =>
      2 * (L - x) / L * Real.cos (2 * Real.pi * x / L)
    let K10 : ℝ → ℝ := fun x =>
      -Real.sin (2 * Real.pi * x / L) / Real.pi
    let K00 : ℝ → ℝ := fun x =>
      2 * (L - x) / L
    ccmPrimeEntryN1 13 (-2) (-2) = primeFunctional K22 ∧
    ccmPrimeEntryN1 13 (-2) (-1) = primeFunctional K2m1 ∧
    ccmPrimeEntryN1 13 (-2) 0 = primeFunctional K20 ∧
    ccmPrimeEntryN1 13 (-2) 1 = primeFunctional K21 ∧
    ccmPrimeEntryN1 13 (-1) (-1) = primeFunctional K11 ∧
    ccmPrimeEntryN1 13 (-1) 0 = primeFunctional K10 ∧
    ccmPrimeEntryN1 13 0 0 = primeFunctional K00 := by
  dsimp only
  rcases ccmPrime_all_boundary_thirteen with
    ⟨hb22, hb2m1, hb20, hb21, hb11, hb10, hb00⟩
  constructor
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      (-2) (-2) (fun x =>
        2 * (ccmL 13 - x) / ccmL 13 *
          Real.cos (4 * Real.pi * x / ccmL 13))
    · exact ccmPrime_plant_diagonal_frequency (ccmL 13)
    · rw [← ccmPrime_plant_diagonal_frequency]
      exact hb22
  constructor
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      (-2) (-1) (fun x =>
        (Real.sin (2 * Real.pi * x / ccmL 13) -
          Real.sin (4 * Real.pi * x / ccmL 13)) / Real.pi)
    · exact ccmPrime_kernel_two_minus_one (ccmL 13)
    · rw [← ccmPrime_kernel_two_minus_one]
      exact hb2m1
  constructor
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      (-2) 0 (fun x =>
        -Real.sin (4 * Real.pi * x / ccmL 13) /
          (2 * Real.pi))
    · exact ccmPrime_kernel_two_zero (ccmL 13)
    · rw [← ccmPrime_kernel_two_zero]
      exact hb20
  constructor
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      (-2) 1 (fun x =>
        -(Real.sin (2 * Real.pi * x / ccmL 13) +
          Real.sin (4 * Real.pi * x / ccmL 13)) /
            (3 * Real.pi))
    · exact ccmPrime_plant_offdiag_orientation (ccmL 13)
    · rw [← ccmPrime_plant_offdiag_orientation]
      exact hb21
  constructor
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      (-1) (-1) (fun x =>
        2 * (ccmL 13 - x) / ccmL 13 *
          Real.cos (2 * Real.pi * x / ccmL 13))
    · exact ccmPrime_kernel_one_one (ccmL 13)
    · rw [← ccmPrime_kernel_one_one]
      exact hb11
  constructor
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      (-1) 0 (fun x =>
        -Real.sin (2 * Real.pi * x / ccmL 13) / Real.pi)
    · exact ccmPrime_kernel_one_zero (ccmL 13)
    · rw [← ccmPrime_kernel_one_zero]
      exact hb10
  · apply ccmPrimeEntryN1_thirteen_of_kernel
      0 0 (fun x => 2 * (ccmL 13 - x) / ccmL 13)
    · exact ccmPrime_kernel_zero_zero (ccmL 13)
    · rw [← ccmPrime_kernel_zero_zero]
      exact hb00

#print axioms ccmPrimeEntryN1_13_seven_class_exact_normal_form

end Q3.RouteB
