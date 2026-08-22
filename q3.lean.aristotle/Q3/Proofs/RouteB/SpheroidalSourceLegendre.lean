import Mathlib

/-!
# Legendre polynomials

Mathlib does not contain the Legendre polynomials, so we develop here exactly the amount of
theory needed for the spheroidal spectrum: the three-term recursion, the classical derivative
identities, the Legendre differential equation, parity, the value at `1`, and crude exponential
bounds for the polynomial and its first two derivatives on `[-1, 1]`.
-/

noncomputable section

open Polynomial

/-- The Legendre polynomials, defined by the standard three-term recursion
`(n+1) P_{n+1} = (2n+1) X P_n - n P_{n-1}`. -/
noncomputable def legendreP : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => X
  | (n + 2) =>
      C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) * X * legendreP (n + 1) -
        C (((n : ℝ) + 1) / ((n : ℝ) + 2)) * legendreP n

@[simp] theorem legendreP_zero : legendreP 0 = 1 := rfl

@[simp] theorem legendreP_one : legendreP 1 = X := rfl

theorem legendreP_add_two (n : ℕ) :
    legendreP (n + 2) =
      C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) * X * legendreP (n + 1) -
        C (((n : ℝ) + 1) / ((n : ℝ) + 2)) * legendreP n := rfl

/-- The three-term recursion with denominators cleared. -/
theorem legendreP_rec (n : ℕ) :
    C ((n : ℝ) + 2) * legendreP (n + 2) =
      C (2 * (n : ℝ) + 3) * (X * legendreP (n + 1)) - C ((n : ℝ) + 1) * legendreP n := by
  have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
  have e1 : ((n : ℝ) + 2) * ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) = 2 * (n : ℝ) + 3 := by
    field_simp
  have e2 : ((n : ℝ) + 2) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) = (n : ℝ) + 1 := by
    field_simp
  calc C ((n : ℝ) + 2) * legendreP (n + 2)
      = C (((n : ℝ) + 2) * ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2))) * (X * legendreP (n + 1))
        - C (((n : ℝ) + 2) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) * legendreP n := by
        rw [legendreP_add_two, C_mul, C_mul]; ring
    _ = _ := by rw [e1, e2]

/-- Value of the `n`-th Legendre polynomial at `x`. -/
noncomputable def lpv (n : ℕ) (x : ℝ) : ℝ := (legendreP n).eval x

/-- Value of the derivative of the `n`-th Legendre polynomial at `x`. -/
noncomputable def lpd (n : ℕ) (x : ℝ) : ℝ := (derivative (legendreP n)).eval x

/-- Value of the second derivative of the `n`-th Legendre polynomial at `x`. -/
noncomputable def lpdd (n : ℕ) (x : ℝ) : ℝ := (derivative (derivative (legendreP n))).eval x

theorem hasDerivAt_lpv (n : ℕ) (x : ℝ) : HasDerivAt (lpv n) (lpd n x) x :=
  (legendreP n).hasDerivAt x

theorem hasDerivAt_lpd (n : ℕ) (x : ℝ) : HasDerivAt (lpd n) (lpdd n x) x :=
  (derivative (legendreP n)).hasDerivAt x

theorem continuous_lpv (n : ℕ) : Continuous (lpv n) := (legendreP n).continuous

theorem continuous_lpd (n : ℕ) : Continuous (lpd n) := (derivative (legendreP n)).continuous

@[simp] theorem lpv_zero (x : ℝ) : lpv 0 x = 1 := by simp [lpv]

@[simp] theorem lpv_one (x : ℝ) : lpv 1 x = x := by simp [lpv]

@[simp] theorem lpd_zero (x : ℝ) : lpd 0 x = 0 := by simp [lpd]

@[simp] theorem lpd_one (x : ℝ) : lpd 1 x = 1 := by simp [lpd]

@[simp] theorem lpdd_zero (x : ℝ) : lpdd 0 x = 0 := by simp [lpdd]

@[simp] theorem lpdd_one (x : ℝ) : lpdd 1 x = 0 := by simp [lpdd]

theorem lpv_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * lpv (n + 2) x
      = (2 * (n : ℝ) + 3) * (x * lpv (n + 1) x) - ((n : ℝ) + 1) * lpv n x := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x) (legendreP_rec n)
  simpa [lpv] using h

theorem lpd_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * lpd (n + 2) x
      = (2 * (n : ℝ) + 3) * (lpv (n + 1) x + x * lpd (n + 1) x) - ((n : ℝ) + 1) * lpd n x := by
  have h := congrArg (fun p : Polynomial ℝ => (derivative p).eval x) (legendreP_rec n)
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, one_mul, zero_mul,
    zero_add, mul_zero, add_zero, eval_sub, eval_mul, eval_C, eval_add, eval_X, eval_zero] at h
  simp only [lpd, lpv]
  linarith [h]

theorem lpdd_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * lpdd (n + 2) x
      = (2 * (n : ℝ) + 3) * (2 * lpd (n + 1) x + x * lpdd (n + 1) x)
        - ((n : ℝ) + 1) * lpdd n x := by
  have h := congrArg (fun p : Polynomial ℝ => (derivative (derivative p)).eval x) (legendreP_rec n)
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, derivative_add, one_mul,
    zero_mul, zero_add, mul_zero, add_zero, eval_sub, eval_mul, eval_C, eval_add, eval_X,
    eval_zero] at h
  simp only [lpdd, lpd]
  linarith [h]

/-- The two classical derivative recursions, proved simultaneously by induction. -/
theorem lp_deriv_pair (n : ℕ) (x : ℝ) :
    lpd (n + 1) x = x * lpd n x + ((n : ℝ) + 1) * lpv n x ∧
      x * lpd (n + 1) x = lpd n x + ((n : ℝ) + 1) * lpv (n + 1) x := by
  induction n with
  | zero => constructor <;> simp
  | succ n ih =>
    obtain ⟨hA, hB⟩ := ih
    have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hA1 : lpd (n + 2) x = x * lpd (n + 1) x + ((n : ℝ) + 2) * lpv (n + 1) x := by
      refine mul_left_cancel₀ hne ?_
      linear_combination lpd_rec n x + ((n : ℝ) + 1) * hB
    refine ⟨?_, ?_⟩
    · push_cast
      linear_combination hA1
    · push_cast
      linear_combination x * hA1 - hA + x * hB - lpv_rec n x

theorem lpd_eq (n : ℕ) (x : ℝ) :
    lpd (n + 1) x = x * lpd n x + ((n : ℝ) + 1) * lpv n x := (lp_deriv_pair n x).1

theorem lpd_eq' (n : ℕ) (x : ℝ) :
    x * lpd (n + 1) x = lpd n x + ((n : ℝ) + 1) * lpv (n + 1) x := (lp_deriv_pair n x).2

/-- `(1 - x²) P_{n+1}'(x) = (n+1) (P_n(x) - x P_{n+1}(x))`. -/
theorem lpd_one_sub_sq (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * lpd (n + 1) x = ((n : ℝ) + 1) * (lpv n x - x * lpv (n + 1) x) := by
  linear_combination lpd_eq n x - x * lpd_eq' n x

/-- **The Legendre differential equation.** -/
theorem legendre_ode (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * lpdd n x - 2 * x * lpd n x + (n : ℝ) * ((n : ℝ) + 1) * lpv n x = 0 := by
  match n with
  | 0 => simp
  | (m + 1) =>
    have hfun : (fun y : ℝ => (1 - y ^ 2) * lpd (m + 1) y)
        = fun y : ℝ => ((m : ℝ) + 1) * (lpv m y - y * lpv (m + 1) y) :=
      funext (fun y => lpd_one_sub_sq m y)
    have hsq : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have d1 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * lpd (m + 1) y)
        (-(2 * x) * lpd (m + 1) x + (1 - x ^ 2) * lpdd (m + 1) x) x :=
      hsq.mul (hasDerivAt_lpd (m + 1) x)
    have d2 : HasDerivAt (fun y : ℝ => ((m : ℝ) + 1) * (lpv m y - y * lpv (m + 1) y))
        (((m : ℝ) + 1) * (lpd m x - (1 * lpv (m + 1) x + x * lpd (m + 1) x))) x :=
      ((hasDerivAt_lpv m x).sub ((hasDerivAt_id x).mul (hasDerivAt_lpv (m + 1) x))).const_mul _
    rw [hfun] at d1
    have hkey := d1.unique d2
    have hB := lpd_eq' m x
    push_cast
    linear_combination hkey - ((m : ℝ) + 1) * hB

/-- The second derivative recursion `P''_{n+1}(x) = (n+2) P'_n(x) + x P''_n(x)`. -/
theorem lpdd_eq (n : ℕ) (x : ℝ) :
    lpdd (n + 1) x = ((n : ℝ) + 2) * lpd n x + x * lpdd n x := by
  have hfun : (fun y : ℝ => lpd (n + 1) y)
      = fun y : ℝ => y * lpd n y + ((n : ℝ) + 1) * lpv n y :=
    funext (fun y => lpd_eq n y)
  have d1 : HasDerivAt (fun y : ℝ => lpd (n + 1) y) (lpdd (n + 1) x) x := hasDerivAt_lpd (n + 1) x
  have d2 : HasDerivAt (fun y : ℝ => y * lpd n y + ((n : ℝ) + 1) * lpv n y)
      (1 * lpd n x + x * lpdd n x + ((n : ℝ) + 1) * lpd n x) x :=
    ((hasDerivAt_id x).mul (hasDerivAt_lpd n x)).add ((hasDerivAt_lpv n x).const_mul _)
  rw [hfun] at d1
  have h := d1.unique d2
  linarith [h]

/-- Parity of the Legendre polynomials. -/
theorem lpv_neg (n : ℕ) (x : ℝ) : lpv n (-x) = (-1 : ℝ) ^ n * lpv n x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
      have h1 := ih (m + 1) (by omega) 
      have h0 := ih m (by omega)
      have hne : ((m : ℝ) + 2) ≠ 0 := by positivity
      refine mul_left_cancel₀ hne ?_
      have hr := lpv_rec m (-x)
      have hr' := lpv_rec m x
      have hp1 : (-1 : ℝ) ^ (m + 1) = -(-1) ^ m := by ring
      have hp2 : (-1 : ℝ) ^ (m + 2) = (-1) ^ m := by ring
      rw [hr, h1, h0, hp1, hp2]
      linear_combination (-((-1 : ℝ) ^ m)) * hr'

/-- Every Legendre polynomial takes the value `1` at `x = 1`. -/
theorem lpv_at_one (n : ℕ) : lpv n 1 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hne : ((m : ℝ) + 2) ≠ 0 := by positivity
      refine mul_left_cancel₀ hne ?_
      rw [lpv_rec m 1, h1, h0]
      ring

/-- An elementary exponential comparison used for the crude Legendre bounds. -/
theorem real_nat_add_two_le (n : ℕ) : ((n : ℝ) + 2) ≤ 2 * 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hk : (0 : ℝ) < 3 ^ k := by positivity
    have : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
    push_cast
    rw [this]
    linarith

/-- A crude exponential bound for the Legendre polynomials on `[-1, 1]`. -/
theorem lpv_abs_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |lpv n x| ≤ 3 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp only [lpv_one, pow_one]; linarith
    | (m + 2) =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hne : (0 : ℝ) < (m : ℝ) + 2 := by positivity
      have hr := lpv_rec m x
      have hkey : ((m : ℝ) + 2) * |lpv (m + 2) x| ≤ ((m : ℝ) + 2) * 3 ^ (m + 2) := by
        have habs : ((m : ℝ) + 2) * |lpv (m + 2) x|
            = |(2 * (m : ℝ) + 3) * (x * lpv (m + 1) x) - ((m : ℝ) + 1) * lpv m x| := by
          rw [← hr, abs_mul, abs_of_pos hne]
        rw [habs]
        have hb : |(2 * (m : ℝ) + 3) * (x * lpv (m + 1) x) - ((m : ℝ) + 1) * lpv m x|
            ≤ (2 * (m : ℝ) + 3) * (1 * 3 ^ (m + 1)) + ((m : ℝ) + 1) * 3 ^ m := by
          refine le_trans (abs_sub _ _) ?_
          gcongr
          · rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 3)]
            gcongr
          · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
            gcongr
        refine le_trans hb ?_
        have h3 : (3 : ℝ) ^ (m + 2) = 9 * 3 ^ m := by ring
        have h3' : (3 : ℝ) ^ (m + 1) = 3 * 3 ^ m := by ring
        have hpos : (0 : ℝ) < 3 ^ m := by positivity
        rw [h3, h3']
        nlinarith [hpos]
      exact le_of_mul_le_mul_left hkey hne

/-- A crude exponential bound for the derivative of the Legendre polynomials on `[-1, 1]`. -/
theorem lpd_abs_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |lpd n x| ≤ 9 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := lpd_eq n x
    have hv := lpv_abs_le n hx
    have hpow : ((n : ℝ) + 1) * 3 ^ n ≤ 8 * 9 ^ n := by
      have h1 : ((n : ℝ) + 1) ≤ 8 * 3 ^ n := by
        have := real_nat_add_two_le (n := n)
        have h3 : (0 : ℝ) < 3 ^ n := by positivity
        linarith
      have h3 : (0 : ℝ) < 3 ^ n := by positivity
      calc ((n : ℝ) + 1) * 3 ^ n ≤ (8 * 3 ^ n) * 3 ^ n := by gcongr
        _ = 8 * (3 ^ n * 3 ^ n) := by ring
        _ = 8 * 9 ^ n := by rw [← mul_pow]; norm_num
    calc |lpd (n + 1) x| = |x * lpd n x + ((n : ℝ) + 1) * lpv n x| := by rw [hr]
      _ ≤ |x * lpd n x| + |((n : ℝ) + 1) * lpv n x| := abs_add_le _ _
      _ ≤ 1 * 9 ^ n + ((n : ℝ) + 1) * 3 ^ n := by
          gcongr
          · rw [abs_mul]; gcongr
          · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]; gcongr
      _ ≤ 9 ^ (n + 1) := by
          have : (9 : ℝ) ^ (n + 1) = 9 * 9 ^ n := by ring
          rw [this]; linarith

/-- A crude exponential bound for the second derivative of the Legendre polynomials
on `[-1, 1]`. -/
theorem lpdd_abs_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |lpdd n x| ≤ 27 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := lpdd_eq n x
    have hd := lpd_abs_le n hx
    have hpow : ((n : ℝ) + 2) * 9 ^ n ≤ 26 * 27 ^ n := by
      have h1 : ((n : ℝ) + 2) ≤ 26 * 3 ^ n := by
        have := real_nat_add_two_le (n := n)
        have h3 : (0 : ℝ) < 3 ^ n := by positivity
        linarith
      have h3 : (0 : ℝ) < 9 ^ n := by positivity
      calc ((n : ℝ) + 2) * 9 ^ n ≤ (26 * 3 ^ n) * 9 ^ n := by gcongr
        _ = 26 * (3 ^ n * 9 ^ n) := by ring
        _ = 26 * 27 ^ n := by rw [← mul_pow]; norm_num
    calc |lpdd (n + 1) x| = |((n : ℝ) + 2) * lpd n x + x * lpdd n x| := by rw [hr]
      _ ≤ |((n : ℝ) + 2) * lpd n x| + |x * lpdd n x| := abs_add_le _ _
      _ ≤ ((n : ℝ) + 2) * 9 ^ n + 1 * 27 ^ n := by
          gcongr
          · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)]; gcongr
          · rw [abs_mul]; gcongr
      _ ≤ 27 ^ (n + 1) := by
          have : (27 : ℝ) ^ (n + 1) = 27 * 27 ^ n := by ring
          rw [this]; linarith

/-! ## The three-term expansion of `(1 - x²) P_{2k}` in the even Legendre basis -/

/-- Coefficient of `P_{2k+1}` in `x P_{2k}`. -/
noncomputable def lcU (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) / (4 * (k : ℝ) + 1)

/-- Coefficient of `P_{2k-1}` in `x P_{2k}`. -/
noncomputable def lcV (k : ℕ) : ℝ := (2 * (k : ℝ)) / (4 * (k : ℝ) + 1)

/-- Coefficient of `P_{2k+2}` in `x P_{2k+1}`. -/
noncomputable def lcS (k : ℕ) : ℝ := (2 * (k : ℝ) + 2) / (4 * (k : ℝ) + 3)

/-- Coefficient of `P_{2k}` in `x P_{2k+1}`. -/
noncomputable def lcT (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) / (4 * (k : ℝ) + 3)

theorem lcU_nonneg (k : ℕ) : 0 ≤ lcU k := by unfold lcU; positivity

theorem lcV_nonneg (k : ℕ) : 0 ≤ lcV k := by unfold lcV; positivity

theorem lcS_nonneg (k : ℕ) : 0 ≤ lcS k := by unfold lcS; positivity

theorem lcT_nonneg (k : ℕ) : 0 ≤ lcT k := by unfold lcT; positivity

theorem lcU_add_lcV (k : ℕ) : lcU k + lcV k = 1 := by
  unfold lcU lcV
  have h : (4 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem lcS_add_lcT (k : ℕ) : lcS k + lcT k = 1 := by
  unfold lcS lcT
  have h : (4 * (k : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

theorem lcU_le_one (k : ℕ) : lcU k ≤ 1 := by
  have := lcU_add_lcV k; have := lcV_nonneg k; linarith

theorem lcV_le_one (k : ℕ) : lcV k ≤ 1 := by
  have := lcU_add_lcV k; have := lcU_nonneg k; linarith

theorem lcS_le_one (k : ℕ) : lcS k ≤ 1 := by
  have := lcS_add_lcT k; have := lcT_nonneg k; linarith

theorem lcT_le_one (k : ℕ) : lcT k ≤ 1 := by
  have := lcS_add_lcT k; have := lcS_nonneg k; linarith

@[simp] theorem lcV_zero : lcV 0 = 0 := by unfold lcV; norm_num

@[simp] theorem lcU_zero : lcU 0 = 1 := by unfold lcU; norm_num

/-- `x P_{2j+2}(x) = u_{j+1} P_{2j+3}(x) + v_{j+1} P_{2j+1}(x)`. -/
theorem lpv_x_even_succ (j : ℕ) (x : ℝ) :
    x * lpv (2 * j + 2) x = lcU (j + 1) * lpv (2 * j + 3) x + lcV (j + 1) * lpv (2 * j + 1) x := by
  have hr := lpv_rec (2 * j + 1) x
  simp only [show 2 * j + 1 + 2 = 2 * j + 3 from by omega,
    show 2 * j + 1 + 1 = 2 * j + 2 from by omega] at hr
  unfold lcU lcV
  have hne : (4 * ((j : ℝ) + 1) + 1) ≠ 0 := by positivity
  push_cast at hr ⊢
  field_simp
  linarith [hr]

/-- `x P_{2k+1}(x) = s_k P_{2k+2}(x) + t_k P_{2k}(x)`. -/
theorem lpv_x_odd (k : ℕ) (x : ℝ) :
    x * lpv (2 * k + 1) x = lcS k * lpv (2 * k + 2) x + lcT k * lpv (2 * k) x := by
  have hr := lpv_rec (2 * k) x
  unfold lcS lcT
  have hne : (4 * (k : ℝ) + 3) ≠ 0 := by positivity
  push_cast at hr ⊢
  field_simp
  linarith [hr]

/-- `x P_{2j+3}(x) = s_{j+1} P_{2j+4}(x) + t_{j+1} P_{2j+2}(x)`. -/
theorem lpv_x_odd_succ (j : ℕ) (x : ℝ) :
    x * lpv (2 * j + 3) x = lcS (j + 1) * lpv (2 * j + 4) x + lcT (j + 1) * lpv (2 * j + 2) x := by
  have h := lpv_x_odd (j + 1) x
  simp only [show 2 * (j + 1) + 1 = 2 * j + 3 from by omega,
    show 2 * (j + 1) + 2 = 2 * j + 4 from by omega,
    show 2 * (j + 1) = 2 * j + 2 from by omega] at h
  exact h

/-- Coefficient of `P_{2k+2}` in `(1 - x²) P_{2k}`. -/
noncomputable def jacA (k : ℕ) : ℝ := -(lcU k * lcS k)

/-- Coefficient of `P_{2k}` in `(1 - x²) P_{2k}`. -/
noncomputable def jacB (k : ℕ) : ℝ := 1 - (lcU k * lcT k + lcV k * lcS (k - 1))

/-- Coefficient of `P_{2k-2}` in `(1 - x²) P_{2k}`. -/
noncomputable def jacC (k : ℕ) : ℝ := -(lcV k * lcT (k - 1))

@[simp] theorem jacC_zero : jacC 0 = 0 := by simp [jacC]

/-- **The three-term expansion.** `(1 - x²) P_{2k}` is a combination of `P_{2k+2}`, `P_{2k}`
and `P_{2k-2}` (the last term is absent for `k = 0`). -/
theorem legendre_even_expansion (k : ℕ) (x : ℝ) :
    (1 - x ^ 2) * lpv (2 * k) x
      = jacA k * lpv (2 * k + 2) x + jacB k * lpv (2 * k) x + jacC k * lpv (2 * k - 2) x := by
  match k with
  | 0 =>
    have hodd0 := lpv_x_odd 0 x
    norm_num at hodd0 ⊢
    simp only [jacA, jacB, jacC, lcU_zero, lcV_zero, one_mul, zero_mul, add_zero, mul_zero]
    linear_combination -hodd0
  | (j + 1) =>
    have hx' := lpv_x_even_succ j x
    have hodd' := lpv_x_odd_succ j x
    have hoddm := lpv_x_odd j x
    simp only [show 2 * (j + 1) + 2 = 2 * j + 4 from by omega,
      show 2 * (j + 1) - 2 = 2 * j from by omega,
      show 2 * (j + 1) = 2 * j + 2 from by omega,
      show 2 * j + 2 - 2 = 2 * j from by omega]
    simp only [jacA, jacB, jacC, show (j + 1) - 1 = j from rfl]
    linear_combination (-x) * hx' - lcU (j + 1) * hodd' - lcV (j + 1) * hoddm

theorem jacA_abs_le_one (k : ℕ) : |jacA k| ≤ 1 := by
  have h1 := lcU_nonneg k; have h2 := lcS_nonneg k
  have h3 := lcU_le_one k; have h4 := lcS_le_one k
  rw [jacA, abs_le]
  constructor <;> nlinarith

theorem jacC_abs_le_one (k : ℕ) : |jacC k| ≤ 1 := by
  have h1 := lcV_nonneg k; have h2 := lcT_nonneg (k - 1)
  have h3 := lcV_le_one k; have h4 := lcT_le_one (k - 1)
  rw [jacC, abs_le]
  constructor <;> nlinarith

theorem jacB_abs_le_one (k : ℕ) : |jacB k| ≤ 1 := by
  have h1 := lcU_nonneg k; have h2 := lcT_nonneg k
  have h3 := lcV_nonneg k; have h4 := lcS_nonneg (k - 1)
  have h5 := lcT_le_one k; have h6 := lcS_le_one (k - 1)
  have h7 := lcU_add_lcV k
  rw [jacB, abs_le]
  constructor <;> nlinarith

end
