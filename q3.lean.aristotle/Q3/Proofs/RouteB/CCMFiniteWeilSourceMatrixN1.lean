import Mathlib

set_option linter.mathlibStandardSet false

/-
Source lock:
- Connes–Consani–Moscovici, Zeta Spectral Triples
- arXiv:2511.22755v1
- e-print SHA-256:
  96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
- equations: (2.9), (2.10), (3.13)–(3.16), (4.1)–(4.4),
  Lemma 5.1, Lemma 5.2
- scope: literal N = 1 pilot only
-/

namespace Q3.RouteB

open Matrix MeasureTheory
open scoped BigOperators

/-- The three source modes `{-1,0,1}` for the literal `N = 1` pilot. -/
abbrev CCMModeN1 := Fin 3

/-- Integer label of a literal `N = 1` source mode. -/
def ccmModeN1 (i : CCMModeN1) : ℤ := (i.1 : ℤ) - 1

/-- The central mode, whose integer label is zero. -/
def ccmCenterN1 : CCMModeN1 := ⟨1, by decide⟩

/-- Reflection of the three source modes. -/
def ccmNegN1 (i : CCMModeN1) : CCMModeN1 := ⟨2 - i.1, by omega⟩

noncomputable def ccmLambda (mProject : ℕ) : ℝ :=
  Real.sqrt (mProject : ℝ)

noncomputable def ccmL (mProject : ℕ) : ℝ :=
  Real.log (mProject : ℝ)

/-- CCM equations (2.9)--(2.10), with the diagonal branch kept literal. -/
noncomputable def ccmQKernel (L : ℝ) (n m : ℤ) (x : ℝ) : ℝ :=
  if n = m then
    2 * (L - x) / L * Real.cos (2 * Real.pi * (n : ℝ) * x / L)
  else
    (Real.sin (2 * Real.pi * (m : ℝ) * x / L) -
        Real.sin (2 * Real.pi * (n : ℝ) * x / L)) /
      (Real.pi * ((n : ℝ) - (m : ℝ)))

/-- The closed `W_{0,2}` entry from CCM equation (4.2). -/
noncomputable def ccmW02Entry (L : ℝ) (n m : ℤ) : ℝ :=
  32 * L * Real.sinh (L / 4) ^ 2 *
      (L ^ 2 - 16 * Real.pi ^ 2 * (m : ℝ) * (n : ℝ)) /
    ((L ^ 2 + 16 * Real.pi ^ 2 * (m : ℝ) ^ 2) *
      (L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2))

/-- The literal finite von-Mangoldt entry from CCM equation (4.3). -/
noncomputable def ccmPrimeEntryN1 (mProject : ℕ) (n m : ℤ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 mProject,
    ArithmeticFunction.vonMangoldt k *
      (Real.sqrt (k : ℝ))⁻¹ *
      ccmQKernel (ccmL mProject) n m (Real.log (k : ℝ))

/-- The raw archimedean integrand in CCM equation (4.4). -/
noncomputable def ccmWRIntegrand (L : ℝ) (n m : ℤ) (x : ℝ) : ℝ :=
  (Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0) /
    (Real.exp x - Real.exp (-x))

private noncomputable def ccmWRNumerator (L : ℝ) (n m : ℤ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0

private noncomputable def ccmWRDenominator (x : ℝ) : ℝ :=
  Real.exp x - Real.exp (-x)

/-- Continuous numerator slope used to expose the removable endpoint singularity. -/
private noncomputable def ccmWRNumeratorSlope (L : ℝ) (n m : ℤ) : ℝ → ℝ :=
  Function.update
    (fun x => (ccmWRNumerator L n m x - ccmWRNumerator L n m 0) / (x - 0))
    0 (deriv (ccmWRNumerator L n m) 0)

/-- Continuous denominator slope, whose value at zero is the exact derivative `2`. -/
private noncomputable def ccmWRDenominatorSlope : ℝ → ℝ :=
  Function.update
    (fun x => (ccmWRDenominator x - ccmWRDenominator 0) / (x - 0))
    0 2

/-- A continuous extension of the raw CCM integrand across the omitted endpoint. -/
private noncomputable def ccmWRExtendedIntegrand (L : ℝ) (n m : ℤ) (x : ℝ) : ℝ :=
  ccmWRNumeratorSlope L n m x / ccmWRDenominatorSlope x

/-- The complete archimedean entry from CCM equation (4.4). -/
noncomputable def ccmWREntry (L : ℝ) (n m : ℤ) : ℝ :=
  ccmQKernel L n m 0 / 2 *
      (Real.eulerMascheroniConstant +
        Real.log (4 * Real.pi * ((Real.exp L - 1) / (Real.exp L + 1)))) +
    ∫ x in Set.Ioc 0 L, ccmWRIntegrand L n m x

/-- The full literal finite Weil entry `W_{0,2} - W_ℝ - Prime`. -/
noncomputable def ccmWeilTauN1 (mProject : ℕ) (n m : ℤ) : ℝ :=
  ccmW02Entry (ccmL mProject) n m -
    ccmWREntry (ccmL mProject) n m -
    ccmPrimeEntryN1 mProject n m

/-- The literal `3 × 3` CCM source matrix for `N = 1`. -/
noncomputable def ccmWeilMatN1 (mProject : ℕ) : Matrix CCMModeN1 CCMModeN1 ℝ :=
  fun i j => ccmWeilTauN1 mProject (ccmModeN1 i) (ccmModeN1 j)

/-- The diagonal scaling generator on the three source modes. -/
noncomputable def ccmModeDiagN1 : Matrix CCMModeN1 CCMModeN1 ℝ :=
  Matrix.diagonal (fun i => (ccmModeN1 i : ℝ))

/-- The all-ones vector used in CCM Lemmas 5.1--5.2. -/
def ccmEtaN1 : CCMModeN1 → ℝ := fun _ => 1

/-- The source beta vector, normalized by its zero central component. -/
noncomputable def ccmBetaN1 (mProject : ℕ) : CCMModeN1 → ℝ :=
  fun i => (ccmModeN1 i : ℝ) * ccmWeilMatN1 mProject i ccmCenterN1

/-- The normalized constant vector `L^(-1/2) η`. -/
noncomputable def ccmDeltaN1 (mProject : ℕ) : CCMModeN1 → ℝ :=
  (Real.sqrt (ccmL mProject))⁻¹ • ccmEtaN1

/-- The literal finite Weil operator associated with the source matrix. -/
noncomputable def ccmWeilOpN1 (mProject : ℕ) :
    (CCMModeN1 → ℝ) →ₗ[ℝ] (CCMModeN1 → ℝ) :=
  (ccmWeilMatN1 mProject).mulVecLin

theorem ccmModeN1_values :
    ccmModeN1 (0 : CCMModeN1) = -1 ∧
      ccmModeN1 (1 : CCMModeN1) = 0 ∧
      ccmModeN1 (2 : CCMModeN1) = 1 := by
  norm_num [ccmModeN1, ccmCenterN1]

theorem ccmModeN1_neg (i : CCMModeN1) :
    ccmModeN1 (ccmNegN1 i) = -ccmModeN1 i := by
  fin_cases i <;> norm_num [ccmModeN1, ccmNegN1]

theorem ccmL_pos (mProject : ℕ) (hm : 2 ≤ mProject) :
    0 < ccmL mProject := by
  exact Real.log_pos (by exact_mod_cast hm)

theorem ccm_exp_L (mProject : ℕ) (hm : 2 ≤ mProject) :
    Real.exp (ccmL mProject) = (mProject : ℝ) := by
  rw [ccmL, Real.exp_log]
  exact_mod_cast (show 0 < mProject by omega)

theorem ccmL_eq_two_log_lambda (mProject : ℕ) (hm : 2 ≤ mProject) :
    ccmL mProject = 2 * Real.log (ccmLambda mProject) := by
  rw [ccmL, ccmLambda, Real.log_sqrt]
  · ring
  · exact_mod_cast (show 0 ≤ mProject by omega)

theorem ccmQKernel_symm (L : ℝ) (n m : ℤ) (x : ℝ) :
    ccmQKernel L n m x = ccmQKernel L m n x := by
  by_cases hnm : n = m
  · simp [hnm]
  · have hmn : m ≠ n := Ne.symm hnm
    rw [ccmQKernel, ccmQKernel, if_neg hnm, if_neg hmn]
    rw [show ((m : ℝ) - (n : ℝ)) = -((n : ℝ) - (m : ℝ)) by ring]
    rw [mul_neg, div_neg]
    ring

private theorem ccmQKernel_differentiable (L : ℝ) (n m : ℤ) :
    Differentiable ℝ (ccmQKernel L n m) := by
  unfold ccmQKernel
  split_ifs <;> fun_prop

private theorem ccmWRNumerator_differentiable (L : ℝ) (n m : ℤ) :
    Differentiable ℝ (ccmWRNumerator L n m) := by
  unfold ccmWRNumerator
  exact (Real.differentiable_exp.comp (differentiable_id.div_const 2)).mul
    (ccmQKernel_differentiable L n m) |>.sub
      (differentiable_const (c := ccmQKernel L n m 0))

private theorem ccmWRDenominator_hasDerivAt_zero :
    HasDerivAt ccmWRDenominator 2 0 := by
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1) 0 := hasDerivAt_neg 0
  have h := (Real.hasDerivAt_exp 0).sub
    ((Real.hasDerivAt_exp (-0)).comp 0 hneg)
  change HasDerivAt (fun x : ℝ => Real.exp x - Real.exp (-x)) 2 0
  convert h using 1
  all_goals norm_num [Function.comp_def]

private theorem ccmWRNumeratorSlope_continuous (L : ℝ) (n m : ℤ) :
    Continuous (ccmWRNumeratorSlope L n m) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact (ccmWRNumerator_differentiable L n m 0).hasDerivAt.continuousAt_div
  · rw [ccmWRNumeratorSlope, continuousAt_update_of_ne hx]
    apply ContinuousAt.div
    · exact (ccmWRNumerator_differentiable L n m x).continuousAt.sub
        continuousAt_const
    · exact continuousAt_id.sub continuousAt_const
    · simpa using hx

private theorem ccmWRDenominatorSlope_continuous :
    Continuous ccmWRDenominatorSlope := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact ccmWRDenominator_hasDerivAt_zero.continuousAt_div
  · rw [ccmWRDenominatorSlope, continuousAt_update_of_ne hx]
    apply ContinuousAt.div
    · unfold ccmWRDenominator
      fun_prop
    · fun_prop
    · simpa using hx

private theorem ccmWRDenominatorSlope_ne_zero (x : ℝ) :
    ccmWRDenominatorSlope x ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    simp [ccmWRDenominatorSlope]
  · rw [ccmWRDenominatorSlope, Function.update_of_ne hx]
    apply div_ne_zero
    · simp only [ccmWRDenominator]
      norm_num
      intro heq
      have harg : x = -x := Real.exp_injective (sub_eq_zero.mp heq)
      exact hx (by linarith)
    · simpa using hx

private theorem ccmWRExtendedIntegrand_continuous (L : ℝ) (n m : ℤ) :
    Continuous (ccmWRExtendedIntegrand L n m) := by
  exact (ccmWRNumeratorSlope_continuous L n m).div
    ccmWRDenominatorSlope_continuous ccmWRDenominatorSlope_ne_zero

private theorem ccmWRExtendedIntegrand_eq_raw
    (L : ℝ) (n m : ℤ) {x : ℝ} (hx : x ≠ 0) :
    ccmWRExtendedIntegrand L n m x = ccmWRIntegrand L n m x := by
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    have harg : x = -x := Real.exp_injective (sub_eq_zero.mp h)
    exact hx (by linarith)
  simp only [ccmWRExtendedIntegrand, ccmWRNumeratorSlope,
    ccmWRDenominatorSlope, Function.update_of_ne hx]
  simp only [ccmWRNumerator, ccmWRDenominator, ccmWRIntegrand]
  simp only [Real.exp_zero, zero_div, sub_self, neg_zero, sub_zero]
  field_simp [hx, hden]
  ring

/-- Generic removable-singularity lemma behind the literal `N = 1` entry gate. -/
private theorem ccmWRIntegrand_integrableOn (L : ℝ) (n m : ℤ) :
    IntegrableOn (ccmWRIntegrand L n m) (Set.Ioc 0 L) := by
  apply (ccmWRExtendedIntegrand_continuous L n m).integrableOn_Ioc.congr_fun
  · intro x hx
    exact ccmWRExtendedIntegrand_eq_raw L n m (ne_of_gt hx.1)
  · exact measurableSet_Ioc

/-- The CCM archimedean entry is genuinely integrable on its literal `Ioc` domain. -/
theorem ccmWRIntegrandN1_integrableOn
    (mProject : ℕ) (hm : 2 ≤ mProject) (i j : CCMModeN1) :
    IntegrableOn
      (ccmWRIntegrand (ccmL mProject) (ccmModeN1 i) (ccmModeN1 j))
      (Set.Ioc 0 (ccmL mProject)) := by
  have _hL := ccmL_pos mProject hm
  exact ccmWRIntegrand_integrableOn
    (ccmL mProject) (ccmModeN1 i) (ccmModeN1 j)

theorem ccmQKernel_neg_neg (L : ℝ) (n m : ℤ) (x : ℝ) :
    ccmQKernel L (-n) (-m) x = ccmQKernel L n m x := by
  by_cases hnm : n = m
  · subst m
    rw [ccmQKernel, ccmQKernel, if_pos rfl, if_pos rfl]
    simp only [Int.cast_neg]
    rw [show 2 * Real.pi * (-(n : ℝ)) * x / L =
      -(2 * Real.pi * (n : ℝ) * x / L) by ring, Real.cos_neg]
  · have hneg : -n ≠ -m := by simpa using hnm
    rw [ccmQKernel, ccmQKernel, if_neg hneg, if_neg hnm]
    simp only [Int.cast_neg]
    rw [show 2 * Real.pi * (-(m : ℝ)) * x / L =
      -(2 * Real.pi * (m : ℝ) * x / L) by ring]
    rw [show 2 * Real.pi * (-(n : ℝ)) * x / L =
      -(2 * Real.pi * (n : ℝ) * x / L) by ring]
    rw [Real.sin_neg, Real.sin_neg]
    rw [show (-(n : ℝ) - -(m : ℝ)) =
      -((n : ℝ) - (m : ℝ)) by ring]
    rw [mul_neg, div_neg]
    ring

theorem ccmQKernel_neg_one_one_eq_neg_one_zero (L x : ℝ) :
    ccmQKernel L (-1) 1 x = ccmQKernel L (-1) 0 x := by
  rw [ccmQKernel, ccmQKernel]
  norm_num
  rw [show -(2 * Real.pi * x) / L =
    -(2 * Real.pi * x / L) by ring, Real.sin_neg]
  field_simp [Real.pi_ne_zero]
  ring

theorem ccmW02Entry_symm (L : ℝ) (n m : ℤ) :
    ccmW02Entry L n m = ccmW02Entry L m n := by
  unfold ccmW02Entry
  ring

theorem ccmW02Entry_neg_neg (L : ℝ) (n m : ℤ) :
    ccmW02Entry L (-n) (-m) = ccmW02Entry L n m := by
  unfold ccmW02Entry
  simp only [Int.cast_neg]
  ring

theorem ccmW02Entry_neg_one_one_eq_neg_one_zero (L : ℝ) :
    ccmW02Entry L (-1) 1 = ccmW02Entry L (-1) 0 := by
  by_cases hL : L = 0
  · simp [ccmW02Entry, hL]
  · unfold ccmW02Entry
    norm_num
    field_simp [hL, Real.pi_ne_zero]

theorem ccmPrimeEntryN1_symm (mProject : ℕ) (n m : ℤ) :
    ccmPrimeEntryN1 mProject n m = ccmPrimeEntryN1 mProject m n := by
  unfold ccmPrimeEntryN1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ccmQKernel_symm]

theorem ccmPrimeEntryN1_neg_neg (mProject : ℕ) (n m : ℤ) :
    ccmPrimeEntryN1 mProject (-n) (-m) = ccmPrimeEntryN1 mProject n m := by
  unfold ccmPrimeEntryN1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ccmQKernel_neg_neg]

theorem ccmPrimeEntryN1_neg_one_one_eq_neg_one_zero (mProject : ℕ) :
    ccmPrimeEntryN1 mProject (-1) 1 = ccmPrimeEntryN1 mProject (-1) 0 := by
  unfold ccmPrimeEntryN1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ccmQKernel_neg_one_one_eq_neg_one_zero]

theorem ccmWRIntegrand_symm (L : ℝ) (n m : ℤ) (x : ℝ) :
    ccmWRIntegrand L n m x = ccmWRIntegrand L m n x := by
  simp only [ccmWRIntegrand, ccmQKernel_symm]

theorem ccmWRIntegrand_neg_neg (L : ℝ) (n m : ℤ) (x : ℝ) :
    ccmWRIntegrand L (-n) (-m) x = ccmWRIntegrand L n m x := by
  simp only [ccmWRIntegrand, ccmQKernel_neg_neg]

theorem ccmWRIntegrand_neg_one_one_eq_neg_one_zero (L x : ℝ) :
    ccmWRIntegrand L (-1) 1 x = ccmWRIntegrand L (-1) 0 x := by
  simp only [ccmWRIntegrand, ccmQKernel_neg_one_one_eq_neg_one_zero]

theorem ccmWREntry_symm (L : ℝ) (n m : ℤ) :
    ccmWREntry L n m = ccmWREntry L m n := by
  unfold ccmWREntry
  rw [ccmQKernel_symm]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc fun x _ => ccmWRIntegrand_symm L n m x

theorem ccmWREntry_neg_neg (L : ℝ) (n m : ℤ) :
    ccmWREntry L (-n) (-m) = ccmWREntry L n m := by
  unfold ccmWREntry
  rw [ccmQKernel_neg_neg]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc fun x _ => ccmWRIntegrand_neg_neg L n m x

theorem ccmWREntry_neg_one_one_eq_neg_one_zero (L : ℝ) :
    ccmWREntry L (-1) 1 = ccmWREntry L (-1) 0 := by
  unfold ccmWREntry
  rw [ccmQKernel_neg_one_one_eq_neg_one_zero]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc fun x _ =>
    ccmWRIntegrand_neg_one_one_eq_neg_one_zero L x

private theorem ccmWeilTauN1_symm_raw (mProject : ℕ) (n m : ℤ) :
    ccmWeilTauN1 mProject n m = ccmWeilTauN1 mProject m n := by
  simp only [ccmWeilTauN1, ccmW02Entry_symm, ccmWREntry_symm,
    ccmPrimeEntryN1_symm]

private theorem ccmWeilTauN1_neg_neg_raw (mProject : ℕ) (n m : ℤ) :
    ccmWeilTauN1 mProject (-n) (-m) = ccmWeilTauN1 mProject n m := by
  simp only [ccmWeilTauN1, ccmW02Entry_neg_neg, ccmWREntry_neg_neg,
    ccmPrimeEntryN1_neg_neg]

theorem ccmWeilTauN1_neg_one_one_eq_neg_one_zero (mProject : ℕ) :
    ccmWeilTauN1 mProject (-1) 1 = ccmWeilTauN1 mProject (-1) 0 := by
  simp only [ccmWeilTauN1, ccmW02Entry_neg_one_one_eq_neg_one_zero,
    ccmWREntry_neg_one_one_eq_neg_one_zero,
    ccmPrimeEntryN1_neg_one_one_eq_neg_one_zero]

theorem ccmWeilTauN1_symm
    (mProject : ℕ) (hm : 2 ≤ mProject) (n m : ℤ) :
    ccmWeilTauN1 mProject n m = ccmWeilTauN1 mProject m n := by
  have _hL := ccmL_pos mProject hm
  exact ccmWeilTauN1_symm_raw mProject n m

theorem ccmWeilTauN1_neg_neg
    (mProject : ℕ) (hm : 2 ≤ mProject) (n m : ℤ) :
    ccmWeilTauN1 mProject (-n) (-m) = ccmWeilTauN1 mProject n m := by
  have _hL := ccmL_pos mProject hm
  exact ccmWeilTauN1_neg_neg_raw mProject n m

@[simp] theorem ccmWeilMatN1_apply (mProject : ℕ) (i j : CCMModeN1) :
    ccmWeilMatN1 mProject i j =
      ccmW02Entry (ccmL mProject) (ccmModeN1 i) (ccmModeN1 j) -
        ccmWREntry (ccmL mProject) (ccmModeN1 i) (ccmModeN1 j) -
        ccmPrimeEntryN1 mProject (ccmModeN1 i) (ccmModeN1 j) := rfl

theorem ccmWeilMatN1_transpose_eq (mProject : ℕ) (hm : 2 ≤ mProject) :
    (ccmWeilMatN1 mProject).transpose = ccmWeilMatN1 mProject := by
  ext i j
  exact ccmWeilTauN1_symm mProject hm (ccmModeN1 j) (ccmModeN1 i)

theorem ccmWeilMatN1_centrosymmetric
    (mProject : ℕ) (hm : 2 ≤ mProject) (i j : CCMModeN1) :
    ccmWeilMatN1 mProject (ccmNegN1 i) (ccmNegN1 j) =
      ccmWeilMatN1 mProject i j := by
  change ccmWeilTauN1 mProject
      (ccmModeN1 (ccmNegN1 i)) (ccmModeN1 (ccmNegN1 j)) =
    ccmWeilTauN1 mProject (ccmModeN1 i) (ccmModeN1 j)
  simp only [ccmModeN1_neg, ccmWeilTauN1_neg_neg mProject hm]

private theorem ccmWeilMatN1_structured_raw
    (mProject : ℕ) (i j : CCMModeN1) :
    ((ccmModeN1 j : ℝ) - (ccmModeN1 i : ℝ)) *
        ccmWeilMatN1 mProject i j =
      -ccmBetaN1 mProject i + ccmBetaN1 mProject j := by
  unfold ccmBetaN1 ccmWeilMatN1
  have h10 : ccmWeilTauN1 mProject 1 0 =
      ccmWeilTauN1 mProject (-1) 0 := by
    simpa using ccmWeilTauN1_neg_neg_raw mProject (-1) 0
  have h0m : ccmWeilTauN1 mProject 0 (-1) =
      ccmWeilTauN1 mProject (-1) 0 :=
    ccmWeilTauN1_symm_raw mProject 0 (-1)
  have h01 : ccmWeilTauN1 mProject 0 1 =
      ccmWeilTauN1 mProject (-1) 0 := by
    rw [ccmWeilTauN1_symm_raw, h10]
  have hm1 : ccmWeilTauN1 mProject (-1) 1 =
      ccmWeilTauN1 mProject (-1) 0 :=
    ccmWeilTauN1_neg_one_one_eq_neg_one_zero mProject
  have h1m : ccmWeilTauN1 mProject 1 (-1) =
      ccmWeilTauN1 mProject (-1) 0 := by
    rw [ccmWeilTauN1_symm_raw, hm1]
  fin_cases i <;> fin_cases j <;>
    norm_num [ccmModeN1, ccmCenterN1] <;>
    simp only [h10, h0m, h01, hm1, h1m] <;> ring

private theorem ccmModeN1_cast_sub_ne
    {i j : CCMModeN1} (hij : i ≠ j) :
    (ccmModeN1 i : ℝ) - (ccmModeN1 j : ℝ) ≠ 0 := by
  fin_cases i <;> fin_cases j
  all_goals simp_all [ccmModeN1]
  all_goals norm_num

/-- Literal source-oriented quotient form of the CCM Lemma-5.1 off-diagonal law. -/
theorem ccmWeilMatN1_structured_offdiag
    (mProject : ℕ) (hm : 2 ≤ mProject) {i j : CCMModeN1} (hij : i ≠ j) :
    ccmWeilMatN1 mProject i j =
      (ccmBetaN1 mProject i - ccmBetaN1 mProject j) /
        ((ccmModeN1 i : ℝ) - (ccmModeN1 j : ℝ)) := by
  have _hL := ccmL_pos mProject hm
  have hden := ccmModeN1_cast_sub_ne hij
  apply (eq_div_iff hden).2
  have h := ccmWeilMatN1_structured_raw mProject i j
  nlinarith

/-- With central value fixed to zero, the Lemma-5.1 beta vector is unique. -/
private theorem ccmBetaN1_unique_raw
    (mProject : ℕ) (beta : CCMModeN1 → ℝ)
    (hcenter : beta ccmCenterN1 = 0)
    (hstructured : ∀ i j,
      ((ccmModeN1 j : ℝ) - (ccmModeN1 i : ℝ)) *
          ccmWeilMatN1 mProject i j = -beta i + beta j) :
    beta = ccmBetaN1 mProject := by
  funext i
  have hi := hstructured i ccmCenterN1
  have hz : ccmModeN1 ccmCenterN1 = 0 := by
    norm_num [ccmModeN1, ccmCenterN1]
  rw [hz, Int.cast_zero] at hi
  rw [hcenter, add_zero] at hi
  change beta i = (ccmModeN1 i : ℝ) *
    ccmWeilMatN1 mProject i ccmCenterN1
  linarith

theorem ccmBetaN1_unique
    (mProject : ℕ) (hm : 2 ≤ mProject) (beta : CCMModeN1 → ℝ)
    (hbeta0 : beta ccmCenterN1 = 0)
    (hstructured : ∀ i j, i ≠ j →
      ccmWeilMatN1 mProject i j =
        (beta i - beta j) /
          ((ccmModeN1 i : ℝ) - (ccmModeN1 j : ℝ))) :
    beta = ccmBetaN1 mProject := by
  have _hL := ccmL_pos mProject hm
  apply ccmBetaN1_unique_raw mProject beta hbeta0
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · have hden := ccmModeN1_cast_sub_ne hij
    have h := (eq_div_iff hden).mp (hstructured i j hij)
    nlinarith

/-- Literal `N = 1` specialization of the CCM Lemma-5.2 commutator. -/
theorem ccmWeilMatN1_commutator (mProject : ℕ) (hm : 2 ≤ mProject) :
    ccmModeDiagN1 * ccmWeilMatN1 mProject -
        ccmWeilMatN1 mProject * ccmModeDiagN1 =
      Matrix.vecMulVec (ccmBetaN1 mProject) ccmEtaN1 -
        Matrix.vecMulVec ccmEtaN1 (ccmBetaN1 mProject) := by
  have _hL := ccmL_pos mProject hm
  ext i j
  simp only [Matrix.sub_apply,
    Matrix.vecMulVec_apply, ccmEtaN1, mul_one, one_mul]
  simp only [ccmModeDiagN1, Matrix.mul_apply, Matrix.diagonal]
  simp
  have h := ccmWeilMatN1_structured_raw mProject i j
  rw [ccmWeilMatN1_apply] at h
  nlinarith

@[simp] theorem ccmDeltaN1_apply (mProject : ℕ) (i : CCMModeN1) :
    ccmDeltaN1 mProject i = (Real.sqrt (ccmL mProject))⁻¹ := by
  simp [ccmDeltaN1, ccmEtaN1]

theorem ccmDeltaN1_eq_invSqrtL_smul_eta (mProject : ℕ) :
    ccmDeltaN1 mProject =
      (Real.sqrt (ccmL mProject))⁻¹ • ccmEtaN1 := rfl

#print axioms ccmWRIntegrandN1_integrableOn
#print axioms ccmWeilMatN1_structured_offdiag
#print axioms ccmBetaN1_unique
#print axioms ccmWeilMatN1_commutator

end Q3.RouteB
