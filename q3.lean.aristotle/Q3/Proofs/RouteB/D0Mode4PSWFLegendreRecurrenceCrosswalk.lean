import Q3.Proofs.RouteB.D0Mode4HermitianSchurTailEnvelopes

/-!
# Exact even-Legendre recurrence crosswalk for the mode-four Jacobi coefficients

DLMF 30.8.3--30.8.4 gives the Ferrers/Legendre coefficient recurrence for the
spheroidal differential equation.  Specializing its order and base degree to
`m = n = 0`, and writing the even Legendre degree as `N = 2q`, gives the three
coefficients recorded below.

This file proves only their exact algebraic agreement with the committed
`mode4JacobiLower`, `mode4JacobiCenter`, and `mode4JacobiUpper`.  In particular,
the differential spectral energy is `E = Λ + G`.  It does not construct a
Sturm--Liouville operator, an ordered PSWF spectrum, a Weyl tail, a Schur
complement, an endpoint, or a determinant sign.
-/

noncomputable section

/-- DLMF 30.8.3 coefficient `A_q` after the even-sector specialization
`m = n = 0`, `N = 2q`, and `gamma^2 = G`. -/
noncomputable def mode4PSWFLegendreSubdiagonal
    (G : ℝ) (q : ℕ) : ℝ :=
  let N := mode4JacobiIndex q;
  -G * (N - 1) * N / ((2 * N - 3) * (2 * N - 1))

/-- Diagonal coefficient of the positive prolate Sturm--Liouville operator
`-((1-x^2)f')' + G*x^2*f` in the even Legendre sector.  This equals the
DLMF 30.8.3 coefficient `B_q` plus `G`. -/
noncomputable def mode4PSWFLegendreDiagonal
    (G : ℝ) (q : ℕ) : ℝ :=
  let N := mode4JacobiIndex q;
  N * (N + 1) +
    G * (2 * N * (N + 1) - 1) /
      ((2 * N - 1) * (2 * N + 3))

/-- DLMF 30.8.3 coefficient `C_q` after the even-sector specialization
`m = n = 0`, `N = 2q`, and `gamma^2 = G`. -/
noncomputable def mode4PSWFLegendreSuperdiagonal
    (G : ℝ) (q : ℕ) : ℝ :=
  let N := mode4JacobiIndex q;
  -G * (N + 1) * (N + 2) / ((2 * N + 3) * (2 * N + 5))

/-- The committed positive lower Jacobi coefficient is exactly the negative
of the source recurrence coefficient `A_q`. -/
theorem mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal
    (G : ℝ) (q : ℕ) :
    mode4JacobiLower G q = -mode4PSWFLegendreSubdiagonal G q := by
  unfold mode4JacobiLower mode4PSWFLegendreSubdiagonal
  ring

/-- Exact shifted-diagonal identity.  The project variable `Λ` is the DLMF
spheroidal eigenvalue, while the positive Sturm--Liouville spectral energy is
`Λ + G`. -/
theorem mode4JacobiCenter_eq_pswfLegendreDiagonal_shift
    (G Λ : ℝ) (q : ℕ) :
    mode4JacobiCenter G Λ q =
      mode4PSWFLegendreDiagonal G q - (Λ + G) := by
  have hleft : 2 * mode4JacobiIndex q - 1 ≠ 0 := by
    unfold mode4JacobiIndex
    intro h
    have hreal : (4 : ℝ) * (q : ℝ) = 1 := by linarith
    have hnat : 4 * q = 1 := by exact_mod_cast hreal
    omega
  have hright : 2 * mode4JacobiIndex q + 3 ≠ 0 := by
    unfold mode4JacobiIndex
    positivity
  have hden :
      (2 * mode4JacobiIndex q - 1) *
          (2 * mode4JacobiIndex q + 3) ≠ 0 :=
    mul_ne_zero hleft hright
  have hden' :
      -3 + mode4JacobiIndex q * 4 +
          mode4JacobiIndex q ^ 2 * 4 ≠ 0 := by
    rw [show
      -3 + mode4JacobiIndex q * 4 + mode4JacobiIndex q ^ 2 * 4 =
        (2 * mode4JacobiIndex q - 1) *
          (2 * mode4JacobiIndex q + 3) by ring]
    exact hden
  have hcancel :
      (-3 + mode4JacobiIndex q * 4 +
          mode4JacobiIndex q ^ 2 * 4)⁻¹ *
        (-3 + mode4JacobiIndex q * 4 +
          mode4JacobiIndex q ^ 2 * 4) = 1 :=
    inv_mul_cancel₀ hden'
  unfold mode4JacobiCenter mode4PSWFLegendreDiagonal
  dsimp
  ring_nf at hcancel ⊢
  linear_combination -G * hcancel

/-- The committed positive upper Jacobi coefficient is exactly the negative
of the source recurrence coefficient `C_q`. -/
theorem mode4JacobiUpper_eq_neg_pswfLegendreSuperdiagonal
    (G : ℝ) (q : ℕ) :
    mode4JacobiUpper G q = -mode4PSWFLegendreSuperdiagonal G q := by
  unfold mode4JacobiUpper mode4PSWFLegendreSuperdiagonal
  ring

/-- Consumer-sized statement of the complete three-coefficient algebraic
crosswalk.  The signs match DLMF 30.8.4:
`A_q f_(q-1) + (B_q-Λ) f_q + C_q f_(q+1) = 0`. -/
theorem mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk
    (G Λ : ℝ) (q : ℕ) :
    mode4JacobiLower G q = -mode4PSWFLegendreSubdiagonal G q ∧
      mode4JacobiCenter G Λ q =
        mode4PSWFLegendreDiagonal G q - (Λ + G) ∧
      mode4JacobiUpper G q = -mode4PSWFLegendreSuperdiagonal G q := by
  exact ⟨mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal G q,
    mode4JacobiCenter_eq_pswfLegendreDiagonal_shift G Λ q,
    mode4JacobiUpper_eq_neg_pswfLegendreSuperdiagonal G q⟩

#print axioms mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal
#print axioms mode4JacobiCenter_eq_pswfLegendreDiagonal_shift
#print axioms mode4JacobiUpper_eq_neg_pswfLegendreSuperdiagonal
#print axioms mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk
