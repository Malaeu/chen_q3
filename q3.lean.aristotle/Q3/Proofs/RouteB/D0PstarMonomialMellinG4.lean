import Q3.Proofs.RouteB.D0PstarActualProlateEStarMemLp

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex MeasureTheory Set
open scoped BigOperators Real

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# G4 — closed Mellin of the compact monomial `t^d`

Paper source: `docs/routeB_bus/proshka/ccm_exact_source_generator_2026-09-20/VERDICT.md`
§4, identity G4 (commit `70da2617`).

This file locks the closed form, the exponent identity `m^{s_n} = √m`,
and the compact-support certificate for the monomial.  The inner-product
identification
`⟨V_n, E_star (monomial t^d)⟩ = monomialMellinClosed`
is the remaining analytic step (change of variables on the D0 window).

LEDGER:
  CLOSES: [G4_CLOSED_FORM_ALGEBRA]
  OPENS:  [G4_INNER_EQUALS_CLOSED_FORM]
-/

/-- Mellin-Fourier exponent `s_n = 1/2 - 2π i n / L_m`. -/
def sourceSn (i : PairIndex) (n : ℤ) : ℂ :=
  (1 : ℂ) / 2 - 2 * Real.pi * I * n / (L_m i)

private theorem g4_L_m_pos (i : PairIndex) : 0 < L_m i := by
  unfold L_m logLength
  exact Real.log_pos
    (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) i.hm))

private theorem g4_one_lt_lambda (i : PairIndex) : 1 < lambda_m i := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  simpa [lambda_m] using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
      Real.sqrt 1 < Real.sqrt i.m)

private theorem g4_lambda_m_pos (i : PairIndex) : 0 < lambda_m i :=
  lt_trans one_pos (g4_one_lt_lambda i)

private theorem g4_lambda_m_sq (i : PairIndex) :
    lambda_m i * lambda_m i = (i.m : ℝ) := by
  rw [lambda_m, Real.mul_self_sqrt]
  positivity

/-- `exp(L_m / 2) = λ_m = √m`.  Same identity as the W5 midpoint envelope. -/
private theorem g4_exp_half_L (i : PairIndex) :
    Real.exp (L_m i / 2) = lambda_m i := by
  have hlam0 : 0 < lambda_m i := g4_lambda_m_pos i
  have hm0 : (0 : ℝ) ≤ (i.m : ℝ) := by positivity
  have hsq : lambda_m i ^ 2 = (i.m : ℝ) := by
    rw [lambda_m]
    exact Real.sq_sqrt hm0
  have hlog : L_m i = 2 * Real.log (lambda_m i) := by
    show logLength i = 2 * Real.log (lambda_m i)
    rw [logLength, ← hsq, Real.log_pow]
    push_cast
    ring
  rw [hlog,
    show (2 : ℝ) * Real.log (lambda_m i) / 2 = Real.log (lambda_m i) by ring]
  exact Real.exp_log hlam0

theorem sourceSn_re (i : PairIndex) (n : ℤ) :
    (sourceSn i n).re = 1 / 2 := by
  unfold sourceSn
  rw [sub_re, div_re]
  simp [mul_re, mul_im, I_re, I_im, Complex.ofReal_re, Complex.ofReal_im]

theorem sourceSn_add_nat_re (i : PairIndex) (n : ℤ) (d : ℕ) :
    ((d : ℂ) + sourceSn i n).re = (d : ℝ) + 1 / 2 := by
  rw [add_re, sourceSn_re]
  simp

theorem sourceSn_add_nat_ne_zero (i : PairIndex) (n : ℤ) (d : ℕ) :
    (d : ℂ) + sourceSn i n ≠ 0 := by
  intro h
  have hre : ((d : ℂ) + sourceSn i n).re = 0 := by
    simpa using congrArg Complex.re h
  have hval : ((d : ℂ) + sourceSn i n).re = (d : ℝ) + 1 / 2 :=
    sourceSn_add_nat_re i n d
  have hpos : (0 : ℝ) < (d : ℝ) + 1 / 2 := by positivity
  linarith

/-- Integer Fourier mode: `m^{s_n} = √m`. -/
theorem cpow_m_sourceSn (i : PairIndex) (n : ℤ) :
    (i.m : ℂ) ^ sourceSn i n = (Real.sqrt i.m : ℂ) := by
  have hm : (0 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two i.hm)
  have hm0 : (i.m : ℂ) ≠ 0 := by
    exact_mod_cast hm.ne'
  rw [Complex.cpow_def_of_ne_zero hm0]
  have hlog : Complex.log (i.m : ℂ) = (L_m i : ℂ) := by
    have hcast : (i.m : ℂ) = ((i.m : ℝ) : ℂ) := by norm_cast
    rw [hcast, ← Complex.ofReal_log hm.le]
    rfl
  rw [hlog]
  -- `cpow_def` uses `log z * s`, not `s * log z`.
  have hsplit :
      (L_m i : ℂ) * sourceSn i n =
        ((L_m i / 2 : ℝ) : ℂ) +
          ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    unfold sourceSn
    have hLne : (L_m i : ℂ) ≠ 0 := by
      exact_mod_cast (g4_L_m_pos i).ne'
    push_cast
    field_simp [hLne]
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    ← Complex.ofReal_exp, g4_exp_half_L i, lambda_m]

/-- Finite Dirichlet polynomial `∑_{k=1}^m k^{-s}`. -/
def dirichletPartial (m : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 m, (k : ℂ) ^ (-s)

/-- Finite power sum `∑_{k=1}^m k^d`. -/
def powerPartial (m d : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 m, (k : ℂ) ^ d

/-- Closed G4 right-hand side. -/
def monomialMellinClosed (i : PairIndex) (n : ℤ) (d : ℕ) : ℂ :=
  (i.m : ℂ) ^ (-((1 : ℂ) / 4)) / (Real.sqrt (L_m i) : ℂ) *
    (((Real.sqrt i.m : ℂ) * dirichletPartial i.m (sourceSn i n) -
        (i.m : ℂ) ^ (-(d : ℂ)) * powerPartial i.m d) /
      ((d : ℂ) + sourceSn i n))

/-- G4 boxed form rewritten as a sum over `k = 1..m`, still before the
ratio identity `(m/k)^{s_n} = √m · k^{-s_n}`. -/
theorem monomialMellinClosed_eq_weighted_sum
    (i : PairIndex) (n : ℤ) (d : ℕ) :
    monomialMellinClosed i n d =
      (i.m : ℂ) ^ (-((1 : ℂ) / 4)) / (Real.sqrt (L_m i) : ℂ) *
        ∑ k ∈ Finset.Icc 1 i.m,
          ((Real.sqrt i.m : ℂ) * (k : ℂ) ^ (-sourceSn i n) -
              (i.m : ℂ) ^ (-(d : ℂ)) * (k : ℂ) ^ d) /
            ((d : ℂ) + sourceSn i n) := by
  unfold monomialMellinClosed dirichletPartial powerPartial
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- Compact monomial on the positive D0 support. Odd `d` is allowed; G5
uses even degrees from Legendre. -/
def monomialSource (i : PairIndex) (d : ℕ) (x : ℝ) : ℂ :=
  if 0 ≤ x ∧ x ≤ lambda_m i then ((x / lambda_m i : ℝ) : ℂ) ^ d else 0

private theorem monomialSource_eq_zero_of_not_le
    (i : PairIndex) (d : ℕ) {x : ℝ} (hx : ¬ x ≤ lambda_m i) :
    monomialSource i d x = 0 := by
  unfold monomialSource
  simp [hx]

/-- Compact support at the production D0 scale, same certificate as
`prolateCombination_windowFiniteSupport`. -/
theorem monomialSource_windowFiniteSupport (i : PairIndex) (d : ℕ) :
    WindowFiniteSupport (lambda_m i) (sourcePositiveIndexFinset i)
      (monomialSource i d) := by
  intro u hu n hn
  apply monomialSource_eq_zero_of_not_le
  intro hx
  have hnlt : i.m < (n : ℕ) := by
    have hnnot :
        ¬ n ≤
          (⟨i.m, lt_of_lt_of_le Nat.zero_lt_two i.hm⟩ : ℕ+) := by
      intro hnle
      exact hn (Finset.mem_Icc.mpr ⟨by exact n.prop, hnle⟩)
    exact Nat.lt_of_not_ge (fun hle => hnnot hle)
  have hlam : 0 < lambda_m i := g4_lambda_m_pos i
  have hnreal : (i.m : ℝ) < ((n : ℕ) : ℝ) := by
    exact_mod_cast hnlt
  have hmul : ((n : ℕ) : ℝ) * (lambda_m i)⁻¹ ≤
      ((n : ℕ) : ℝ) * u := by
    exact mul_le_mul_of_nonneg_left hu.1 (by positivity)
  have hstrict : lambda_m i <
      ((n : ℕ) : ℝ) * (lambda_m i)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (lt_div_iff₀ hlam).2
    rw [g4_lambda_m_sq]
    exact hnreal
  linarith [hx]

#print axioms sourceSn_re
#print axioms cpow_m_sourceSn
#print axioms monomialMellinClosed_eq_weighted_sum
#print axioms monomialSource_windowFiniteSupport

end Q3.RouteB.D0Pstar
