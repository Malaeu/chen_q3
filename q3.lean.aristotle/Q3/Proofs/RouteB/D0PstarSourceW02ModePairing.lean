import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Q3.RouteB.D0Pstar

noncomputable def sourceW02ModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) *
      ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)

private theorem integral_Icc_const_mul_exp_mul
    {a b : ℝ} {C A : ℂ} (hab : a ≤ b) (hA : A ≠ 0) :
    (∫ x : ℝ in Set.Icc a b, C * Complex.exp (A * x)) =
      C * ((Complex.exp (A * b) - Complex.exp (A * a)) / A) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_exp_mul_complex hA]

private noncomputable def sourceW02LogEndpointPlus
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (x / 2) : ℂ)

private noncomputable def sourceW02LogEndpointMinus
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (-x / 2) : ℂ)

private theorem sourceW02LogEndpointPlus_eq
    (i : PairIndex) (n : ℤ) :
    sourceW02LogEndpointPlus i n =
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        ((Complex.exp
            (((1 / 2 : ℂ) +
              2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ)) *
              (L_m i : ℂ)) - 1) /
          ((1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ))) := by
  let A : ℂ :=
    (1 / 2 : ℂ) +
      2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ)
  have hA : A ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [A] at hre
  unfold sourceW02LogEndpointPlus
  calc
    (∫ x in Set.Icc 0 (L_m i),
        logWindowZeroExtendedMode i n x * (Real.exp (x / 2) : ℂ)) =
      ∫ x in Set.Icc 0 (L_m i),
        ((Real.sqrt (L_m i))⁻¹ : ℂ) * Complex.exp (A * x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          rw [logWindowZeroExtendedMode, Set.indicator_of_mem hx]
          rw [Complex.ofReal_exp]
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          dsimp [A]
          push_cast
          field_simp [(logLength_pos i).ne']
          ring
    _ = ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        ((Complex.exp (A * (L_m i : ℂ)) - Complex.exp (A * 0)) / A) := by
          exact integral_Icc_const_mul_exp_mul
            (le_of_lt (logLength_pos i)) hA
    _ = ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        ((Complex.exp
            (((1 / 2 : ℂ) +
              2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ)) *
              (L_m i : ℂ)) - 1) /
          ((1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ))) := by
          simp [A]

private theorem sourceW02LogEndpointMinus_eq
    (i : PairIndex) (n : ℤ) :
    sourceW02LogEndpointMinus i n =
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        ((Complex.exp
            (((-1 / 2 : ℂ) +
              2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ)) *
              (L_m i : ℂ)) - 1) /
          ((-1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ))) := by
  let A : ℂ :=
    (-1 / 2 : ℂ) +
      2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ)
  have hA : A ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [A] at hre
  unfold sourceW02LogEndpointMinus
  calc
    (∫ x in Set.Icc 0 (L_m i),
        logWindowZeroExtendedMode i n x * (Real.exp (-x / 2) : ℂ)) =
      ∫ x in Set.Icc 0 (L_m i),
        ((Real.sqrt (L_m i))⁻¹ : ℂ) * Complex.exp (A * x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          rw [logWindowZeroExtendedMode, Set.indicator_of_mem hx]
          rw [Complex.ofReal_exp]
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          dsimp [A]
          push_cast
          field_simp [(logLength_pos i).ne']
          ring
    _ = ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        ((Complex.exp (A * (L_m i : ℂ)) - Complex.exp (A * 0)) / A) := by
          exact integral_Icc_const_mul_exp_mul
            (le_of_lt (logLength_pos i)) hA
    _ = ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        ((Complex.exp
            (((-1 / 2 : ℂ) +
              2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ)) *
              (L_m i : ℂ)) - 1) /
          ((-1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (n : ℂ) / (L_m i : ℂ))) := by
          simp [A]

private theorem integral_Icc_exp_mul_sin
    {L a b : ℝ} (hL : 0 ≤ L) (hden : a ^ 2 + b ^ 2 ≠ 0) :
    (∫ x : ℝ in Set.Icc 0 L,
        Real.exp (a * x) * Real.sin (b * x)) =
      (Real.exp (a * L) *
          (a * Real.sin (b * L) - b * Real.cos (b * L)) + b) /
        (a ^ 2 + b ^ 2) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hL]
  let F : ℝ → ℝ := fun x =>
    Real.exp (a * x) *
        (a * Real.sin (b * x) - b * Real.cos (b * x)) /
      (a ^ 2 + b ^ 2)
  have hF : ∀ x : ℝ,
      HasDerivAt F (Real.exp (a * x) * Real.sin (b * x)) x := by
    intro x
    have hexp :
        HasDerivAt (fun y : ℝ => Real.exp (a * y))
          (a * Real.exp (a * x)) x := by
      convert (Real.hasDerivAt_exp (a * x)).comp x
        ((hasDerivAt_id x).const_mul a) using 1 <;> ring
    have hsin :
        HasDerivAt (fun y : ℝ => Real.sin (b * y))
          (b * Real.cos (b * x)) x := by
      convert (Real.hasDerivAt_sin (b * x)).comp x
        ((hasDerivAt_id x).const_mul b) using 1 <;> ring
    have hcos :
        HasDerivAt (fun y : ℝ => Real.cos (b * y))
          (-b * Real.sin (b * x)) x := by
      convert (Real.hasDerivAt_cos (b * x)).comp x
        ((hasDerivAt_id x).const_mul b) using 1 <;> ring
    dsimp [F]
    convert
      (hexp.mul ((hsin.const_mul a).sub (hcos.const_mul b))).div_const
        (a ^ 2 + b ^ 2) using 1 <;>
      simp only [Pi.sub_apply] <;>
      field_simp [hden] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x)
    (by
      have hcont : Continuous
          (fun x : ℝ => Real.exp (a * x) * Real.sin (b * x)) := by
        fun_prop
      exact hcont.intervalIntegrable 0 L)]
  dsimp [F]
  simp
  ring

private theorem sourceW02WeightedSinIntegral
    (i : PairIndex) (k : ℤ) :
    (∫ x : ℝ in Set.Icc 0 (L_m i),
        Real.sin (2 * Real.pi * (k : ℝ) * x / L_m i) *
          (Real.exp (x / 2) + Real.exp (-x / 2))) =
      -32 * Real.pi * (k : ℝ) * L_m i * Real.sinh (L_m i / 4) ^ 2 /
        (L_m i ^ 2 + 16 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
  let b : ℝ := 2 * Real.pi * (k : ℝ) / L_m i
  have hL : 0 ≤ L_m i := (logLength_pos i).le
  have hdenPlus : (1 / 2 : ℝ) ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hdenMinus : (-1 / 2 : ℝ) ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hplus := integral_Icc_exp_mul_sin
    (L := L_m i) (a := (1 / 2 : ℝ)) (b := b) hL hdenPlus
  have hminus := integral_Icc_exp_mul_sin
    (L := L_m i) (a := (-1 / 2 : ℝ)) (b := b) hL hdenMinus
  have hbL : b * L_m i = (k : ℝ) * (2 * Real.pi) := by
    dsimp [b]
    field_simp [(logLength_pos i).ne']
  have hsin : Real.sin (b * L_m i) = 0 := by
    rw [hbL]
    simpa using Real.sin_add_int_mul_two_pi 0 k
  have hcos : Real.cos (b * L_m i) = 1 := by
    rw [hbL]
    exact Real.cos_int_mul_two_pi k
  have hintAdd :
      IntegrableOn
        (fun x : ℝ => Real.exp (x / 2) * Real.sin (b * x))
        (Set.Icc 0 (L_m i)) := by
    apply Continuous.integrableOn_Icc
    fun_prop
  have hintSub :
      IntegrableOn
        (fun x : ℝ => Real.exp (-x / 2) * Real.sin (b * x))
        (Set.Icc 0 (L_m i)) := by
    apply Continuous.integrableOn_Icc
    fun_prop
  have hexpSplit :
      Real.exp (L_m i / 2) + Real.exp (-L_m i / 2) - 2 =
        4 * Real.sinh (L_m i / 4) ^ 2 := by
    rw [Real.sinh_eq]
    rw [show -(L_m i / 4) = -L_m i / 4 by ring]
    have hp : Real.exp (L_m i / 2) = Real.exp (L_m i / 4) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hm : Real.exp (-L_m i / 2) = Real.exp (-L_m i / 4) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hpm : Real.exp (L_m i / 4) * Real.exp (-L_m i / 4) = 1 := by
      rw [← Real.exp_add]
      rw [show L_m i / 4 + -L_m i / 4 = 0 by ring]
      simp
    rw [hp, hm]
    calc
      Real.exp (L_m i / 4) ^ 2 + Real.exp (-L_m i / 4) ^ 2 - 2 =
          Real.exp (L_m i / 4) ^ 2 + Real.exp (-L_m i / 4) ^ 2 -
            2 * (Real.exp (L_m i / 4) * Real.exp (-L_m i / 4)) := by
              rw [hpm]
              ring
      _ = (Real.exp (L_m i / 4) - Real.exp (-L_m i / 4)) ^ 2 := by
            ring
      _ = 4 *
          ((Real.exp (L_m i / 4) - Real.exp (-L_m i / 4)) / 2) ^ 2 := by
            ring
  have hplus' :
      (∫ x : ℝ in Set.Icc 0 (L_m i),
          Real.exp (x / 2) * Real.sin (b * x)) =
        (Real.exp ((1 / 2 : ℝ) * L_m i) *
          ((1 / 2 : ℝ) * Real.sin (b * L_m i) -
            b * Real.cos (b * L_m i)) + b) /
          ((1 / 2 : ℝ) ^ 2 + b ^ 2) := by
    simpa [div_eq_mul_inv, mul_comm] using hplus
  have hminus' :
      (∫ x : ℝ in Set.Icc 0 (L_m i),
          Real.exp (-x / 2) * Real.sin (b * x)) =
        (Real.exp ((-1 / 2 : ℝ) * L_m i) *
          ((-1 / 2 : ℝ) * Real.sin (b * L_m i) -
            b * Real.cos (b * L_m i)) + b) /
          ((-1 / 2 : ℝ) ^ 2 + b ^ 2) := by
    simpa [div_eq_mul_inv, mul_comm] using hminus
  calc
    (∫ x : ℝ in Set.Icc 0 (L_m i),
        Real.sin (2 * Real.pi * (k : ℝ) * x / L_m i) *
          (Real.exp (x / 2) + Real.exp (-x / 2))) =
      (∫ x : ℝ in Set.Icc 0 (L_m i),
          Real.exp (x / 2) * Real.sin (b * x)) +
        ∫ x : ℝ in Set.Icc 0 (L_m i),
          Real.exp (-x / 2) * Real.sin (b * x) := by
            rw [← integral_add hintAdd hintSub]
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [b]
            ring
    _ =
      (Real.exp ((1 / 2 : ℝ) * L_m i) *
          ((1 / 2 : ℝ) * Real.sin (b * L_m i) -
            b * Real.cos (b * L_m i)) + b) /
          ((1 / 2 : ℝ) ^ 2 + b ^ 2) +
        (Real.exp ((-1 / 2 : ℝ) * L_m i) *
          ((-1 / 2 : ℝ) * Real.sin (b * L_m i) -
            b * Real.cos (b * L_m i)) + b) /
          ((-1 / 2 : ℝ) ^ 2 + b ^ 2) := by
            rw [hplus', hminus']
    _ = -32 * Real.pi * (k : ℝ) * L_m i *
          Real.sinh (L_m i / 4) ^ 2 /
        (L_m i ^ 2 + 16 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
            rw [hsin, hcos]
            simp only [mul_zero, zero_sub, mul_one]
            dsimp [b]
            rw [show (1 / 2 : ℝ) * L_m i = L_m i / 2 by ring]
            rw [show (-1 / 2 : ℝ) * L_m i = -L_m i / 2 by ring]
            have hsinh :
                Real.sinh (L_m i / 4) ^ 2 =
                  (Real.exp (L_m i / 2) + Real.exp (-L_m i / 2) - 2) / 4 := by
              linarith [hexpSplit]
            rw [hsinh]
            field_simp [(logLength_pos i).ne']
            ring

private theorem integral_Icc_sub_mul_complex_exp
    {L : ℝ} {c : ℂ} (hL : 0 ≤ L) (hc : c ≠ 0) :
    (∫ x : ℝ in Set.Icc 0 L,
        ((L - x : ℝ) : ℂ) * Complex.exp (c * x)) =
      (Complex.exp (c * (L : ℂ)) - 1 - c * (L : ℂ)) / c ^ 2 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hL]
  let F : ℝ → ℂ := fun x =>
    Complex.exp (c * x) *
      ((((L - x : ℝ) : ℂ) / c) + 1 / c ^ 2)
  have hF : ∀ x : ℝ,
      HasDerivAt F (((L - x : ℝ) : ℂ) * Complex.exp (c * x)) x := by
    intro x
    have hlin :
        HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa using
        ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
    have hexp :
        HasDerivAt (fun y : ℝ => Complex.exp (c * y))
          (c * Complex.exp (c * x)) x := by
      convert (Complex.hasDerivAt_exp (c * x)).comp x hlin using 1 <;> ring
    have hsub :
        HasDerivAt (fun y : ℝ => ((L - y : ℝ) : ℂ)) (-1 : ℂ) x := by
      simpa using
        (((hasDerivAt_const (x : ℂ) (L : ℂ)).sub
          (hasDerivAt_id (x : ℂ))).comp_ofReal)
    have hbracket :
        HasDerivAt
          (fun y : ℝ => (((L - y : ℝ) : ℂ) / c) + 1 / c ^ 2)
          ((-1 : ℂ) / c) x := by
      simpa using (hsub.div_const c).add_const (1 / c ^ 2)
    dsimp [F]
    convert hexp.mul hbracket using 1 <;>
      field_simp [hc] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x)
    (by
      have hcont : Continuous
          (fun x : ℝ => ((L - x : ℝ) : ℂ) * Complex.exp (c * x)) := by
        fun_prop
      exact hcont.intervalIntegrable 0 L)]
  dsimp [F]
  simp
  field_simp [hc]
  ring

private theorem sourceW02ModePairing_eq_sourceModeCosineIntegral
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      ∫ x in Set.Icc 0 (L_m i),
        (2 * ∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (Real.cos (2 * Real.pi * t * x) : ℂ) *
            𝓕 (logWindowZeroExtendedMode i r) t) *
          ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ) := by
  unfold sourceW02ModePairing
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    i n r x hx.1]
  rw [if_pos hx.2]

private theorem sourceW02ModePairing_eq_ccmW02Entry_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceW02ModePairing i n r =
      (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ) := by
  have hnrR : (n : ℝ) - (r : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hnr)
  have hden : Real.pi * ((n : ℝ) - (r : ℝ)) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero hnrR
  have hir : IntegrableOn
      (fun x : ℝ =>
        Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) *
          (Real.exp (x / 2) + Real.exp (-x / 2)))
      (Set.Icc 0 (L_m i)) := by
    apply Continuous.integrableOn_Icc
    fun_prop
  have hin : IntegrableOn
      (fun x : ℝ =>
        Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i) *
          (Real.exp (x / 2) + Real.exp (-x / 2)))
      (Set.Icc 0 (L_m i)) := by
    apply Continuous.integrableOn_Icc
    fun_prop
  have hr := sourceW02WeightedSinIntegral i r
  have hn := sourceW02WeightedSinIntegral i n
  have hDr :
      L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 ≠ 0 := by
    have hL2 : 0 < L_m i ^ 2 := sq_pos_of_pos (logLength_pos i)
    have hrest : 0 ≤ 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 := by positivity
    nlinarith
  have hDn :
      L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by
    have hL2 : 0 < L_m i ^ 2 := sq_pos_of_pos (logLength_pos i)
    have hrest : 0 ≤ 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hfrac :
      (((n : ℝ) /
          (L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2) -
        (r : ℝ) /
          (L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2)) /
        ((n : ℝ) - (r : ℝ))) =
      (L_m i ^ 2 - 16 * Real.pi ^ 2 * (r : ℝ) * (n : ℝ)) /
        ((L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2) *
          (L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)) := by
    let Dr : ℝ := L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2
    let Dn : ℝ := L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2
    have hDr' : Dr ≠ 0 := by simpa [Dr] using hDr
    have hDn' : Dn ≠ 0 := by simpa [Dn] using hDn
    change (((n : ℝ) / Dn - (r : ℝ) / Dr) /
      ((n : ℝ) - (r : ℝ))) =
        (L_m i ^ 2 - 16 * Real.pi ^ 2 * (r : ℝ) * (n : ℝ)) /
          (Dr * Dn)
    field_simp [hnrR, hDr', hDn']
    ring
  have hreal :
      (∫ x : ℝ in Set.Icc 0 (L_m i),
        ((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
            Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
          (Real.pi * ((n : ℝ) - (r : ℝ)))) *
          (Real.exp (x / 2) + Real.exp (-x / 2))) =
        Q3.RouteB.ccmW02Entry (L_m i) n r := by
    calc
      (∫ x : ℝ in Set.Icc 0 (L_m i),
        ((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
            Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
          (Real.pi * ((n : ℝ) - (r : ℝ)))) *
          (Real.exp (x / 2) + Real.exp (-x / 2))) =
          (Real.pi * ((n : ℝ) - (r : ℝ)))⁻¹ *
          ((∫ x : ℝ in Set.Icc 0 (L_m i),
            Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) *
              (Real.exp (x / 2) + Real.exp (-x / 2))) -
            ∫ x : ℝ in Set.Icc 0 (L_m i),
              Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i) *
                (Real.exp (x / 2) + Real.exp (-x / 2))) := by
          calc
            (∫ x : ℝ in Set.Icc 0 (L_m i),
              ((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
                  Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
                (Real.pi * ((n : ℝ) - (r : ℝ)))) *
                (Real.exp (x / 2) + Real.exp (-x / 2))) =
              ∫ x : ℝ in Set.Icc 0 (L_m i),
                (Real.pi * ((n : ℝ) - (r : ℝ)))⁻¹ *
                  ((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) *
                      (Real.exp (x / 2) + Real.exp (-x / 2))) -
                    Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i) *
                      (Real.exp (x / 2) + Real.exp (-x / 2))) := by
                        apply integral_congr_ae
                        filter_upwards [] with x
                        field_simp [hden]
            _ = (Real.pi * ((n : ℝ) - (r : ℝ)))⁻¹ *
                ∫ x : ℝ in Set.Icc 0 (L_m i),
                  ((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) *
                      (Real.exp (x / 2) + Real.exp (-x / 2))) -
                    Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i) *
                      (Real.exp (x / 2) + Real.exp (-x / 2))) := by
                      rw [integral_const_mul]
            _ = (Real.pi * ((n : ℝ) - (r : ℝ)))⁻¹ *
                ((∫ x : ℝ in Set.Icc 0 (L_m i),
                  Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) *
                    (Real.exp (x / 2) + Real.exp (-x / 2))) -
                  ∫ x : ℝ in Set.Icc 0 (L_m i),
                    Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i) *
                      (Real.exp (x / 2) + Real.exp (-x / 2))) := by
                        rw [integral_sub hir hin]
      _ = Q3.RouteB.ccmW02Entry (L_m i) n r := by
          rw [hr, hn]
          unfold Q3.RouteB.ccmW02Entry
          calc
            (Real.pi * ((n : ℝ) - (r : ℝ)))⁻¹ *
                (-32 * Real.pi * (r : ℝ) * L_m i *
                    Real.sinh (L_m i / 4) ^ 2 /
                      (L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2) -
                  -32 * Real.pi * (n : ℝ) * L_m i *
                    Real.sinh (L_m i / 4) ^ 2 /
                      (L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)) =
              32 * L_m i * Real.sinh (L_m i / 4) ^ 2 *
                (((n : ℝ) /
                    (L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2) -
                  (r : ℝ) /
                    (L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2)) /
                  ((n : ℝ) - (r : ℝ))) := by
                    let Dr : ℝ :=
                      L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2
                    let Dn : ℝ :=
                      L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2
                    have hDr' : Dr ≠ 0 := by simpa [Dr] using hDr
                    have hDn' : Dn ≠ 0 := by simpa [Dn] using hDn
                    change (Real.pi * ((n : ℝ) - (r : ℝ)))⁻¹ *
                        (-32 * Real.pi * (r : ℝ) * L_m i *
                            Real.sinh (L_m i / 4) ^ 2 / Dr -
                          -32 * Real.pi * (n : ℝ) * L_m i *
                            Real.sinh (L_m i / 4) ^ 2 / Dn) =
                      32 * L_m i * Real.sinh (L_m i / 4) ^ 2 *
                        (((n : ℝ) / Dn - (r : ℝ) / Dr) /
                          ((n : ℝ) - (r : ℝ)))
                    field_simp [Real.pi_ne_zero, hnrR, hDr', hDn']
                    ring
            _ = 32 * L_m i * Real.sinh (L_m i / 4) ^ 2 *
                (L_m i ^ 2 - 16 * Real.pi ^ 2 * (r : ℝ) * (n : ℝ)) /
                ((L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2) *
                  (L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)) := by
                    rw [hfrac]
                    ring
  unfold sourceW02ModePairing
  simp only [Q3.RouteB.ccmQKernel, if_neg hnr]
  have hcast :
      (∫ x : ℝ in Set.Icc 0 (L_m i),
      (((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
          Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
        (Real.pi * ((n : ℝ) - (r : ℝ))) : ℝ) : ℂ) *
        ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)) =
      ∫ x : ℝ in Set.Icc 0 (L_m i),
        (((((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
            Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
          (Real.pi * ((n : ℝ) - (r : ℝ)))) *
          (Real.exp (x / 2) + Real.exp (-x / 2))) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [] with x
    push_cast
    ring
  rw [hcast, integral_complex_ofReal]
  exact_mod_cast hreal

private theorem sourceW02DiagPointwise
    (i : PairIndex) (n : ℤ) (x : ℝ) :
    (((2 * (L_m i - x) / L_m i *
          Real.cos (2 * Real.pi * (n : ℝ) * x / L_m i) : ℝ) : ℂ) *
        ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)) =
      ((L_m i : ℂ)⁻¹) *
        ((((L_m i - x : ℝ) : ℂ) *
            Complex.exp
              (((1 / 2 : ℂ) +
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) +
          ((L_m i - x : ℝ) : ℂ) *
            Complex.exp
              (((1 / 2 : ℂ) -
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x)) +
          (((L_m i - x : ℝ) : ℂ) *
            Complex.exp
              (((-1 / 2 : ℂ) +
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) +
          ((L_m i - x : ℝ) : ℂ) *
            Complex.exp
              (((-1 / 2 : ℂ) -
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x))) := by
  push_cast
  unfold Complex.cos
  have hLne : (L_m i : ℂ) ≠ 0 := by
    exact_mod_cast (logLength_pos i).ne'
  let p : ℂ :=
    2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (L_m i : ℂ)
  have hphase :
      (2 * (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) / (L_m i : ℂ)) *
          Complex.I = p := by
    dsimp [p]
    field_simp [hLne]
  have hphaseNeg :
      (-(2 * (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) / (L_m i : ℂ))) *
          Complex.I = -p := by
    dsimp [p]
    field_simp [hLne]
  rw [hphase, hphaseNeg]
  have hpp :
      Complex.exp p * Complex.exp ((x : ℂ) * (1 / 2)) =
        Complex.exp
          (((1 / 2 : ℂ) +
            Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [p]
    push_cast
    field_simp [hLne]
    ring
  have hpm :
      Complex.exp (-p) * Complex.exp ((x : ℂ) * (1 / 2)) =
        Complex.exp
          (((1 / 2 : ℂ) -
            Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [p]
    push_cast
    field_simp [hLne]
    ring
  have hmp :
      Complex.exp p * Complex.exp ((x : ℂ) * (-1 / 2)) =
        Complex.exp
          (((-1 / 2 : ℂ) +
            Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [p]
    push_cast
    field_simp [hLne]
    ring
  have hmm :
      Complex.exp (-p) * Complex.exp ((x : ℂ) * (-1 / 2)) =
        Complex.exp
          (((-1 / 2 : ℂ) -
            Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [p]
    push_cast
    field_simp [hLne]
    ring
  calc
    2 * ((L_m i : ℂ) - (x : ℂ)) / (L_m i : ℂ) *
          ((Complex.exp p + Complex.exp (-p)) / 2) *
          (Complex.exp ((x : ℂ) / 2) +
            Complex.exp (-(x : ℂ) / 2)) =
      ((L_m i : ℂ)⁻¹) *
        ((((L_m i : ℂ) - (x : ℂ)) *
              (Complex.exp p * Complex.exp ((x : ℂ) * (1 / 2))) +
            ((L_m i : ℂ) - (x : ℂ)) *
              (Complex.exp (-p) * Complex.exp ((x : ℂ) * (1 / 2)))) +
          (((L_m i : ℂ) - (x : ℂ)) *
              (Complex.exp p * Complex.exp ((x : ℂ) * (-1 / 2))) +
            ((L_m i : ℂ) - (x : ℂ)) *
              (Complex.exp (-p) * Complex.exp ((x : ℂ) * (-1 / 2))))) := by
                field_simp [hLne]
    _ = ((L_m i : ℂ)⁻¹) *
        ((((L_m i : ℂ) - (x : ℂ)) *
            Complex.exp
              (((1 / 2 : ℂ) +
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) +
          ((L_m i : ℂ) - (x : ℂ)) *
            Complex.exp
              (((1 / 2 : ℂ) -
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x)) +
          (((L_m i : ℂ) - (x : ℂ)) *
            Complex.exp
              (((-1 / 2 : ℂ) +
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x) +
          ((L_m i : ℂ) - (x : ℂ)) *
            Complex.exp
              (((-1 / 2 : ℂ) -
                Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)) * x))) := by
              rw [hpp, hpm, hmp, hmm]

theorem sourceW02ModePairing_eq_ccmW02Entry
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ) := by
  by_cases hnr : n = r
  · subst r
    let cpp : ℂ :=
      (1 / 2 : ℂ) +
        Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)
    let cpm : ℂ :=
      (1 / 2 : ℂ) -
        Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)
    let cmp : ℂ :=
      (-1 / 2 : ℂ) +
        Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)
    let cmm : ℂ :=
      (-1 / 2 : ℂ) -
        Complex.I * (2 * Real.pi * (n : ℝ) / L_m i)
    have hcpp : cpp ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [cpp] at hre
    have hcpm : cpm ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [cpm] at hre
    have hcmp : cmp ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [cmp] at hre
    have hcmm : cmm ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [cmm] at hre
    have hphase (a : ℝ) (k : ℤ) :
        Complex.exp
            ((((a : ℂ) +
              Complex.I * (2 * Real.pi * (k : ℝ) / L_m i))) *
              (L_m i : ℂ)) =
          ((Real.exp (a * L_m i) : ℝ) : ℂ) := by
      have hLne : (L_m i : ℂ) ≠ 0 := by
        exact_mod_cast (logLength_pos i).ne'
      calc
        Complex.exp
            ((((a : ℂ) +
              Complex.I * (2 * Real.pi * (k : ℝ) / L_m i))) *
              (L_m i : ℂ)) =
          Complex.exp
            (((a * L_m i : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * (k : ℂ)) := by
                congr 1
                push_cast
                field_simp [hLne]
        _ = Complex.exp (((a * L_m i : ℝ) : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) := by
              rw [Complex.exp_add]
        _ = ((Real.exp (a * L_m i) : ℝ) : ℂ) := by
              have hk :
                  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) = 1 := by
                convert Complex.exp_int_mul_two_pi_mul_I k using 2 <;> ring
              rw [hk, mul_one]
              exact (Complex.ofReal_exp (a * L_m i)).symm
    have hphaseCpp :
        Complex.exp (cpp * (L_m i : ℂ)) =
          ((Real.exp (L_m i / 2) : ℝ) : ℂ) := by
      convert hphase (1 / 2) n using 1 <;>
        simp [cpp] <;> ring
    have hphaseCpm :
        Complex.exp (cpm * (L_m i : ℂ)) =
          ((Real.exp (L_m i / 2) : ℝ) : ℂ) := by
      convert hphase (1 / 2) (-n) using 1 <;>
        simp [cpm] <;> ring
    have hphaseCmp :
        Complex.exp (cmp * (L_m i : ℂ)) =
          ((Real.exp (-L_m i / 2) : ℝ) : ℂ) := by
      convert hphase (-1 / 2) n using 1 <;>
        simp [cmp] <;> ring
    have hphaseCmm :
        Complex.exp (cmm * (L_m i : ℂ)) =
          ((Real.exp (-L_m i / 2) : ℝ) : ℂ) := by
      convert hphase (-1 / 2) (-n) using 1 <;>
        simp [cmm] <;> ring
    have hjpp := integral_Icc_sub_mul_complex_exp
      (L := L_m i) (c := cpp) (logLength_pos i).le hcpp
    have hjpm := integral_Icc_sub_mul_complex_exp
      (L := L_m i) (c := cpm) (logLength_pos i).le hcpm
    have hjmp := integral_Icc_sub_mul_complex_exp
      (L := L_m i) (c := cmp) (logLength_pos i).le hcmp
    have hjmm := integral_Icc_sub_mul_complex_exp
      (L := L_m i) (c := cmm) (logLength_pos i).le hcmm
    have hint (c : ℂ) : IntegrableOn
        (fun x : ℝ => ((L_m i - x : ℝ) : ℂ) * Complex.exp (c * x))
        (Set.Icc 0 (L_m i)) := by
      apply Continuous.integrableOn_Icc
      fun_prop
    have hsource :
        sourceW02ModePairing i n n =
          ((L_m i : ℂ)⁻¹) *
            (((Complex.exp (cpp * (L_m i : ℂ)) - 1 -
                  cpp * (L_m i : ℂ)) / cpp ^ 2 +
              (Complex.exp (cpm * (L_m i : ℂ)) - 1 -
                  cpm * (L_m i : ℂ)) / cpm ^ 2) +
              ((Complex.exp (cmp * (L_m i : ℂ)) - 1 -
                  cmp * (L_m i : ℂ)) / cmp ^ 2 +
              (Complex.exp (cmm * (L_m i : ℂ)) - 1 -
                  cmm * (L_m i : ℂ)) / cmm ^ 2)) := by
      unfold sourceW02ModePairing
      simp only [Q3.RouteB.ccmQKernel, if_pos rfl]
      calc
        (∫ x : ℝ in Set.Icc 0 (L_m i),
          (((2 * (L_m i - x) / L_m i *
              Real.cos (2 * Real.pi * (n : ℝ) * x / L_m i) : ℝ) : ℂ) *
            ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ))) =
          ∫ x : ℝ in Set.Icc 0 (L_m i),
            ((L_m i : ℂ)⁻¹) *
              (((((L_m i - x : ℝ) : ℂ) * Complex.exp (cpp * x) +
                  ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpm * x)) +
                (((L_m i - x : ℝ) : ℂ) * Complex.exp (cmp * x) +
                  ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmm * x)))) := by
                    apply integral_congr_ae
                    filter_upwards [] with x
                    simpa [cpp, cpm, cmp, cmm] using
                      sourceW02DiagPointwise i n x
        _ = ((L_m i : ℂ)⁻¹) *
            (((∫ x : ℝ in Set.Icc 0 (L_m i),
                  ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpp * x)) +
                ∫ x : ℝ in Set.Icc 0 (L_m i),
                  ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpm * x)) +
              ((∫ x : ℝ in Set.Icc 0 (L_m i),
                  ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmp * x)) +
                ∫ x : ℝ in Set.Icc 0 (L_m i),
                  ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmm * x))) := by
                      rw [integral_const_mul]
                      rw [show
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          (((L_m i - x : ℝ) : ℂ) * Complex.exp (cpp * x) +
                            ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpm * x)) +
                          (((L_m i - x : ℝ) : ℂ) * Complex.exp (cmp * x) +
                            ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmm * x))) =
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpp * x) +
                            ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpm * x)) +
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmp * x) +
                            ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmm * x)) by
                          simpa only [Pi.add_apply] using
                            integral_add ((hint cpp).add (hint cpm))
                              ((hint cmp).add (hint cmm))]
                      rw [show
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpp * x) +
                            ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpm * x)) =
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpp * x)) +
                        ∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cpm * x) by
                          simpa only [Pi.add_apply] using
                            integral_add (hint cpp) (hint cpm)]
                      rw [show
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmp * x) +
                            ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmm * x)) =
                        (∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmp * x)) +
                        ∫ x : ℝ in Set.Icc 0 (L_m i),
                          ((L_m i - x : ℝ) : ℂ) * Complex.exp (cmm * x) by
                          simpa only [Pi.add_apply] using
                            integral_add (hint cmp) (hint cmm)]
        _ = ((L_m i : ℂ)⁻¹) *
            (((Complex.exp (cpp * (L_m i : ℂ)) - 1 -
                  cpp * (L_m i : ℂ)) / cpp ^ 2 +
              (Complex.exp (cpm * (L_m i : ℂ)) - 1 -
                  cpm * (L_m i : ℂ)) / cpm ^ 2) +
              ((Complex.exp (cmp * (L_m i : ℂ)) - 1 -
                  cmp * (L_m i : ℂ)) / cmp ^ 2 +
              (Complex.exp (cmm * (L_m i : ℂ)) - 1 -
                  cmm * (L_m i : ℂ)) / cmm ^ 2)) := by
                    rw [hjpp, hjpm, hjmp, hjmm]
    rw [hsource, hphaseCpp, hphaseCpm, hphaseCmp, hphaseCmm]
    unfold Q3.RouteB.ccmW02Entry
    have hexpSplit :
        Real.exp (L_m i / 2) + Real.exp (-L_m i / 2) - 2 =
          4 * Real.sinh (L_m i / 4) ^ 2 := by
      rw [Real.sinh_eq]
      have hpmul :
          Real.exp (L_m i / 4) * Real.exp (-L_m i / 4) = 1 := by
        rw [← Real.exp_add]
        rw [show L_m i / 4 + -L_m i / 4 = 0 by ring]
        simp
      rw [show Real.exp (L_m i / 2) = Real.exp (L_m i / 4) ^ 2 by
        rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
      rw [show Real.exp (-L_m i / 2) = Real.exp (-L_m i / 4) ^ 2 by
        rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
      rw [show -(L_m i / 4) = -L_m i / 4 by ring]
      calc
        Real.exp (L_m i / 4) ^ 2 + Real.exp (-L_m i / 4) ^ 2 - 2 =
            Real.exp (L_m i / 4) ^ 2 + Real.exp (-L_m i / 4) ^ 2 -
              2 * (Real.exp (L_m i / 4) * Real.exp (-L_m i / 4)) := by
                rw [hpmul]
                ring
        _ = (Real.exp (L_m i / 4) - Real.exp (-L_m i / 4)) ^ 2 := by ring
        _ = 4 *
            ((Real.exp (L_m i / 4) - Real.exp (-L_m i / 4)) / 2) ^ 2 := by ring
    have hLne : (L_m i : ℂ) ≠ 0 := by
      exact_mod_cast (logLength_pos i).ne'
    have hD :
        (L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (n : ℂ) ^ 2 ≠ 0 := by
      have hDreal :
          L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by
        have hL2 : 0 < L_m i ^ 2 := sq_pos_of_pos (logLength_pos i)
        have hrest : 0 ≤ 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
        nlinarith
      exact_mod_cast hDreal
    have hsinh :
        Real.sinh (L_m i / 4) ^ 2 =
          (Real.exp (L_m i / 2) + Real.exp (-L_m i / 2) - 2) / 4 := by
      linarith [hexpSplit]
    rw [hsinh]
    push_cast
    field_simp [hcpp, hcpm, hcmp, hcmm, hLne, hD]
    dsimp [cpp, cpm, cmp, cmm]
    field_simp [hLne]
    have hI6 : Complex.I ^ 6 = -1 := by
      rw [show 6 = 4 + 2 by norm_num, pow_add, Complex.I_pow_four, Complex.I_sq]
      norm_num
    have hI8 : Complex.I ^ 8 = 1 := by
      rw [show 8 = 4 + 4 by norm_num, pow_add, Complex.I_pow_four]
      norm_num
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four, hI6, hI8]
    ring
  · exact sourceW02ModePairing_eq_ccmW02Entry_of_ne i hnr

private theorem sourceW02ModePairing_eq_rankTwoLogEndpointMoments
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      conj (sourceW02LogEndpointMinus i n) *
          sourceW02LogEndpointPlus i r +
        conj (sourceW02LogEndpointPlus i n) *
          sourceW02LogEndpointMinus i r := by
  rw [sourceW02ModePairing_eq_ccmW02Entry]
  rw [sourceW02LogEndpointMinus_eq,
    sourceW02LogEndpointPlus_eq,
    sourceW02LogEndpointPlus_eq,
    sourceW02LogEndpointMinus_eq]
  have hLnePhase : (L_m i : ℂ) ≠ 0 := by
    exact_mod_cast (logLength_pos i).ne'
  have hPhasePlus (k : ℤ) :
      Complex.exp
          (((1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ)) *
            (L_m i : ℂ)) =
        ((Real.exp (L_m i / 2) : ℝ) : ℂ) := by
    calc
      Complex.exp
          (((1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ)) *
            (L_m i : ℂ)) =
        Complex.exp
          (((L_m i / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * (k : ℂ)) := by
              congr 1
              field_simp [hLnePhase]
              norm_num
              push_cast
              ring
      _ = Complex.exp (((L_m i / 2 : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) := by
            rw [Complex.exp_add]
      _ = ((Real.exp (L_m i / 2) : ℝ) : ℂ) := by
            have hk :
                Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) = 1 := by
              convert Complex.exp_int_mul_two_pi_mul_I k using 2 <;> ring
            rw [hk, mul_one]
            exact (Complex.ofReal_exp (L_m i / 2)).symm
  have hPhaseMinus (k : ℤ) :
      Complex.exp
          (((-1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ)) *
            (L_m i : ℂ)) =
        ((Real.exp (-L_m i / 2) : ℝ) : ℂ) := by
    calc
      Complex.exp
          (((-1 / 2 : ℂ) +
            2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ)) *
            (L_m i : ℂ)) =
        Complex.exp
          (((-L_m i / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * (k : ℂ)) := by
              congr 1
              field_simp [hLnePhase]
              norm_num
              push_cast
              ring
      _ = Complex.exp (((-L_m i / 2 : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) := by
            rw [Complex.exp_add]
      _ = ((Real.exp (-L_m i / 2) : ℝ) : ℂ) := by
            have hk :
                Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) = 1 := by
              convert Complex.exp_int_mul_two_pi_mul_I k using 2 <;> ring
            rw [hk, mul_one]
            exact (Complex.ofReal_exp (-L_m i / 2)).symm
  rw [hPhaseMinus n, hPhasePlus r, hPhasePlus n, hPhaseMinus r]
  unfold Q3.RouteB.ccmW02Entry
  simp only [map_mul, map_inv₀, map_div₀, map_sub, map_add,
    Complex.conj_ofReal, Complex.conj_I, Int.cast_negSucc,
    Int.cast_ofNat]
  simp only [map_one, map_neg, map_ofNat, map_intCast]
  have hLne : (L_m i : ℂ) ≠ 0 := by
    exact_mod_cast (logLength_pos i).ne'
  have hsqrtPos : 0 < Real.sqrt (L_m i) :=
    Real.sqrt_pos.2 (logLength_pos i)
  have hsqrtNe : ((Real.sqrt (L_m i) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hPlus (k : ℤ) :
      (1 / 2 : ℂ) +
          2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hPlusConj (k : ℤ) :
      (1 / 2 : ℂ) +
          2 * Real.pi * (-Complex.I) * (k : ℂ) / (L_m i : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hMinus (k : ℤ) :
      (-1 / 2 : ℂ) +
          2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hMinusConj (k : ℤ) :
      (-1 / 2 : ℂ) +
          2 * Real.pi * (-Complex.I) * (k : ℂ) / (L_m i : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hsqrtSq :
      (((Real.sqrt (L_m i) : ℝ) : ℂ)) ^ 2 = (L_m i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt (logLength_pos i))
  have hExpMulReal :
      Real.exp (L_m i / 2) * Real.exp (-L_m i / 2) = 1 := by
    rw [← Real.exp_add]
    congr 1
    ring
    simp
  have hExpMul :
      ((Real.exp (L_m i / 2) : ℝ) : ℂ) *
          ((Real.exp (-L_m i / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hExpMulReal
  have hExpSplitReal :
      Real.exp (L_m i / 2) + Real.exp (-L_m i / 2) - 2 =
        4 * Real.sinh (L_m i / 4) ^ 2 := by
    rw [Real.sinh_eq]
    have hpmul :
        Real.exp (L_m i / 4) * Real.exp (-L_m i / 4) = 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
      simp
    rw [show Real.exp (L_m i / 2) = Real.exp (L_m i / 4) ^ 2 by
      rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
    rw [show Real.exp (-L_m i / 2) = Real.exp (-L_m i / 4) ^ 2 by
      rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
    rw [show -(L_m i / 4) = -L_m i / 4 by ring]
    calc
      Real.exp (L_m i / 4) ^ 2 + Real.exp (-L_m i / 4) ^ 2 - 2 =
          Real.exp (L_m i / 4) ^ 2 + Real.exp (-L_m i / 4) ^ 2 -
            2 * (Real.exp (L_m i / 4) * Real.exp (-L_m i / 4)) := by
              rw [hpmul]
              ring
      _ = (Real.exp (L_m i / 4) - Real.exp (-L_m i / 4)) ^ 2 := by ring
      _ = 4 *
          ((Real.exp (L_m i / 4) - Real.exp (-L_m i / 4)) / 2) ^ 2 := by ring
  have hExpSplit :
      ((Real.exp (L_m i / 2) : ℝ) : ℂ) +
          ((Real.exp (-L_m i / 2) : ℝ) : ℂ) - 2 =
        4 * ((Real.sinh (L_m i / 4) : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hExpSplitReal
  have hDnReal :
      L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by
    have hL2 : 0 < L_m i ^ 2 := sq_pos_of_pos (logLength_pos i)
    have hrest : 0 ≤ 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hDrReal :
      L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 ≠ 0 := by
    have hL2 : 0 < L_m i ^ 2 := sq_pos_of_pos (logLength_pos i)
    have hrest : 0 ≤ 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 := by positivity
    nlinarith
  have hDn :
      (L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (n : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hDnReal
  have hDr :
      (L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hDrReal
  have hCast :
      ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 *
          (L_m i ^ 2 - 16 * Real.pi ^ 2 * (r : ℝ) * (n : ℝ)) /
          ((L_m i ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2) *
            (L_m i ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)) : ℝ) : ℂ) =
        32 * (L_m i : ℂ) * ((Real.sinh (L_m i / 4) : ℝ) : ℂ) ^ 2 *
          ((L_m i : ℂ) ^ 2 - 16 * Real.pi ^ 2 * (r : ℂ) * (n : ℂ)) /
          (((L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (r : ℂ) ^ 2) *
            ((L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (n : ℂ) ^ 2)) := by
    push_cast
    rfl
  rw [hCast]
  have hPosPlus (k : ℤ) :
      (L_m i : ℂ) + 4 * Real.pi * Complex.I * (k : ℂ) ≠ 0 := by
    have hscale :
        (2 * (L_m i : ℂ)) *
            ((1 / 2 : ℂ) +
              2 * Real.pi * Complex.I * (k : ℂ) / (L_m i : ℂ)) =
          (L_m i : ℂ) + 4 * Real.pi * Complex.I * (k : ℂ) := by
      field_simp [hLne]
      ring
    rw [← hscale]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hLne) (hPlus k)
  have hPosMinus (k : ℤ) :
      (L_m i : ℂ) - 4 * Real.pi * Complex.I * (k : ℂ) ≠ 0 := by
    have hscale :
        (2 * (L_m i : ℂ)) *
            ((1 / 2 : ℂ) +
              2 * Real.pi * (-Complex.I) * (k : ℂ) / (L_m i : ℂ)) =
          (L_m i : ℂ) - 4 * Real.pi * Complex.I * (k : ℂ) := by
      field_simp [hLne]
      ring
    rw [← hscale]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hLne) (hPlusConj k)
  have hD1 :
      (-(L_m i : ℂ) - 4 * Real.pi * Complex.I * (n : ℂ)) *
          ((L_m i : ℂ) + 4 * Real.pi * Complex.I * (r : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · convert neg_ne_zero.mpr (hPosPlus n) using 1 <;> ring
    · exact hPosPlus r
  have hD2 :
      ((L_m i : ℂ) - 4 * Real.pi * Complex.I * (n : ℂ)) *
          (-(L_m i : ℂ) + 4 * Real.pi * Complex.I * (r : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact hPosMinus n
    · convert neg_ne_zero.mpr (hPosMinus r) using 1 <;> ring
  have hD1' :
      (-(L_m i : ℂ) +
          -((Real.pi : ℂ) * (n : ℂ) * 2 ^ 2 * Complex.I)) *
        ((L_m i : ℂ) +
          (Real.pi : ℂ) * (r : ℂ) * 2 ^ 2 * Complex.I) ≠ 0 := by
    convert hD1 using 1 <;> norm_num <;> ring
  have hD2' :
      ((L_m i : ℂ) +
          -((Real.pi : ℂ) * (n : ℂ) * 2 ^ 2 * Complex.I)) *
        (-(L_m i : ℂ) +
          (Real.pi : ℂ) * (r : ℂ) * 2 ^ 2 * Complex.I) ≠ 0 := by
    convert hD2 using 1 <;> norm_num <;> ring
  have hRecip :
      1 / ((-(L_m i : ℂ) +
            -((Real.pi : ℂ) * (n : ℂ) * 2 ^ 2 * Complex.I)) *
          ((L_m i : ℂ) +
            (Real.pi : ℂ) * (r : ℂ) * 2 ^ 2 * Complex.I)) +
        1 / (((L_m i : ℂ) +
            -((Real.pi : ℂ) * (n : ℂ) * 2 ^ 2 * Complex.I)) *
          (-(L_m i : ℂ) +
            (Real.pi : ℂ) * (r : ℂ) * 2 ^ 2 * Complex.I)) =
        -2 * ((L_m i : ℂ) ^ 2 -
            16 * Real.pi ^ 2 * (r : ℂ) * (n : ℂ)) /
          (((L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (r : ℂ) ^ 2) *
            ((L_m i : ℂ) ^ 2 + 16 * Real.pi ^ 2 * (n : ℂ) ^ 2)) := by
    rw [one_div_add_one_div hD1' hD2']
    field_simp [hD1', hD2', hDn, hDr]
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  have hExpProduct :
      (((Real.exp (-(L_m i / 2)) : ℝ) : ℂ) - 1) *
          (((Real.exp (L_m i / 2) : ℝ) : ℂ) - 1) =
        -4 * ((Real.sinh (L_m i / 4) : ℝ) : ℂ) ^ 2 := by
    calc
      (((Real.exp (-(L_m i / 2)) : ℝ) : ℂ) - 1) *
          (((Real.exp (L_m i / 2) : ℝ) : ℂ) - 1) =
        ((Real.exp (L_m i / 2) : ℝ) : ℂ) *
            ((Real.exp (-L_m i / 2) : ℝ) : ℂ) -
          (((Real.exp (L_m i / 2) : ℝ) : ℂ) +
            ((Real.exp (-L_m i / 2) : ℝ) : ℂ)) + 1 := by ring
      _ = -4 * ((Real.sinh (L_m i / 4) : ℝ) : ℂ) ^ 2 := by
        rw [hExpMul]
        linear_combination -hExpSplit
  have hExpProduct4 :
      (((Real.exp (-(L_m i / 2)) : ℝ) : ℂ) - 1) * 2 ^ 2 *
          (((Real.exp (L_m i / 2) : ℝ) : ℂ) - 1) =
        -16 * ((Real.sinh (L_m i / 4) : ℝ) : ℂ) ^ 2 := by
    rw [show
      (((Real.exp (-(L_m i / 2)) : ℝ) : ℂ) - 1) * 2 ^ 2 *
          (((Real.exp (L_m i / 2) : ℝ) : ℂ) - 1) =
        4 * ((((Real.exp (-(L_m i / 2)) : ℝ) : ℂ) - 1) *
          (((Real.exp (L_m i / 2) : ℝ) : ℂ) - 1)) by norm_num; ring]
    rw [hExpProduct]
    ring
  field_simp [hLne, hsqrtNe, hPlus n, hPlus r, hPlusConj n,
    hMinus n, hMinus r, hMinusConj n, hDn, hDr, hD1, hD2,
    hD1', hD2']
  rw [hRecip, hsqrtSq]
  field_simp [hDn, hDr]
  ring_nf at hExpProduct4 ⊢
  linear_combination
    (2 * ((L_m i : ℂ) ^ 2 -
      16 * Real.pi ^ 2 * (r : ℂ) * (n : ℂ))) * hExpProduct4

/-- Public source seam for the ambient rank-two W02 construction.  The
endpoint values remain literal compact-interval moments, while the long
closed-form calculation stays private in this module. -/
theorem sourceW02ModePairing_eq_rankTwoEndpointIntegrals
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      star
          (∫ x in Set.Icc 0 (L_m i),
            logWindowZeroExtendedMode i n x *
              (Real.exp (-x / 2) : ℂ)) *
          (∫ x in Set.Icc 0 (L_m i),
            logWindowZeroExtendedMode i r x *
              (Real.exp (x / 2) : ℂ)) +
        star
          (∫ x in Set.Icc 0 (L_m i),
            logWindowZeroExtendedMode i n x *
              (Real.exp (x / 2) : ℂ)) *
          (∫ x in Set.Icc 0 (L_m i),
            logWindowZeroExtendedMode i r x *
              (Real.exp (-x / 2) : ℂ)) := by
  simpa only [sourceW02LogEndpointMinus, sourceW02LogEndpointPlus,
    starRingEnd_apply] using
    sourceW02ModePairing_eq_rankTwoLogEndpointMoments i n r

#print axioms sourceW02ModePairing_eq_rankTwoEndpointIntegrals



end Q3.RouteB.D0Pstar
