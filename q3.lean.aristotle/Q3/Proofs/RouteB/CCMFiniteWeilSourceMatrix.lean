import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrixN1

set_option linter.mathlibStandardSet false

/-
Source lock:
- Connes–Consani–Moscovici, Zeta Spectral Triples
- arXiv:2511.22755v1
- e-print SHA-256:
  96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
- scope: general finite mode wrapper around the literal CCM entry constructor
- no positivity, spectral, H2a, or H2b claim is made here
-/

namespace Q3.RouteB

open Matrix MeasureTheory

/-- The source modes `{-N, ..., N}`. -/
abbrev CCMModeFinite (N : ℕ) := Fin (2 * N + 1)

/-- Integer label of a finite source mode. -/
def ccmModeFinite (N : ℕ) (i : CCMModeFinite N) : ℤ :=
  (i.1 : ℤ) - N

/-- The central mode, whose integer label is zero. -/
def ccmCenterFinite (N : ℕ) : CCMModeFinite N :=
  ⟨N, by omega⟩

/-- Reflection of the finite source modes across the central mode. -/
def ccmNegFinite (N : ℕ) (i : CCMModeFinite N) : CCMModeFinite N :=
  ⟨2 * N - i.1, by omega⟩

/-- The literal full-source CCM matrix on modes `{-N, ..., N}`. -/
noncomputable def ccmWeilMatFinite
    (mProject N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  fun i j =>
    ccmWeilTauN1 mProject
      (ccmModeFinite N i)
      (ccmModeFinite N j)

/-- The diagonal source-mode generator. -/
noncomputable def ccmModeDiagFinite
    (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  Matrix.diagonal
    (fun i => (ccmModeFinite N i : ℝ))

/-- The all-ones vector on the finite source modes. -/
def ccmEtaFinite
    (N : ℕ) : CCMModeFinite N → ℝ :=
  fun _ => 1

/-- The normalized constant source vector `L^(-1/2) eta`. -/
noncomputable def ccmDeltaFinite
    (mProject N : ℕ) :
    CCMModeFinite N → ℝ :=
  (Real.sqrt (ccmL mProject))⁻¹ •
    ccmEtaFinite N

/-- The finite Weil operator associated with the literal source matrix. -/
noncomputable def ccmWeilOpFinite
    (mProject N : ℕ) :
    Module.End ℝ (CCMModeFinite N → ℝ) :=
  (ccmWeilMatFinite mProject N).mulVecLin

theorem ccmModeFinite_range
    (N : ℕ) (i : CCMModeFinite N) :
    -(N : ℤ) ≤ ccmModeFinite N i ∧
      ccmModeFinite N i ≤ N := by
  unfold ccmModeFinite
  omega

theorem ccmModeFinite_neg
    (N : ℕ) (i : CCMModeFinite N) :
    ccmModeFinite N (ccmNegFinite N i) =
      -ccmModeFinite N i := by
  have hi : i.1 ≤ 2 * N := by omega
  simp only [ccmModeFinite, ccmNegFinite]
  rw [Nat.cast_sub hi]
  push_cast
  ring

/-- The `N = 2` mode order is literally `-2,-1,0,1,2`. -/
theorem ccmModeFinite_two_values :
    ccmModeFinite 2 (0 : CCMModeFinite 2) = -2 ∧
      ccmModeFinite 2 (1 : CCMModeFinite 2) = -1 ∧
      ccmModeFinite 2 (2 : CCMModeFinite 2) = 0 ∧
      ccmModeFinite 2 (3 : CCMModeFinite 2) = 1 ∧
      ccmModeFinite 2 (4 : CCMModeFinite 2) = 2 := by
  norm_num [ccmModeFinite]

/- The imported `N = 1` file keeps its generic endpoint lemma private so that
the public surface stays source-shaped.  The following local construction
repeats that removable-singularity argument for arbitrary integer modes. -/

private noncomputable def ccmWRFiniteNumerator
    (L : ℝ) (n m : ℤ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0

private noncomputable def ccmWRFiniteDenominator (x : ℝ) : ℝ :=
  Real.exp x - Real.exp (-x)

private noncomputable def ccmWRFiniteNumeratorSlope
    (L : ℝ) (n m : ℤ) : ℝ → ℝ :=
  Function.update
    (fun x =>
      (ccmWRFiniteNumerator L n m x - ccmWRFiniteNumerator L n m 0) /
        (x - 0))
    0 (deriv (ccmWRFiniteNumerator L n m) 0)

private noncomputable def ccmWRFiniteDenominatorSlope : ℝ → ℝ :=
  Function.update
    (fun x =>
      (ccmWRFiniteDenominator x - ccmWRFiniteDenominator 0) / (x - 0))
    0 2

private noncomputable def ccmWRFiniteExtendedIntegrand
    (L : ℝ) (n m : ℤ) (x : ℝ) : ℝ :=
  ccmWRFiniteNumeratorSlope L n m x / ccmWRFiniteDenominatorSlope x

private theorem ccmQKernelFinite_differentiable (L : ℝ) (n m : ℤ) :
    Differentiable ℝ (ccmQKernel L n m) := by
  unfold ccmQKernel
  split_ifs <;> fun_prop

private theorem ccmWRFiniteNumerator_differentiable (L : ℝ) (n m : ℤ) :
    Differentiable ℝ (ccmWRFiniteNumerator L n m) := by
  unfold ccmWRFiniteNumerator
  exact (Real.differentiable_exp.comp (differentiable_id.div_const 2)).mul
    (ccmQKernelFinite_differentiable L n m) |>.sub
      (differentiable_const (c := ccmQKernel L n m 0))

private theorem ccmWRFiniteDenominator_hasDerivAt_zero :
    HasDerivAt ccmWRFiniteDenominator 2 0 := by
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1) 0 := hasDerivAt_neg 0
  have h := (Real.hasDerivAt_exp 0).sub
    ((Real.hasDerivAt_exp (-0)).comp 0 hneg)
  change HasDerivAt (fun x : ℝ => Real.exp x - Real.exp (-x)) 2 0
  convert h using 1
  all_goals norm_num [Function.comp_def]

private theorem ccmWRFiniteNumeratorSlope_continuous (L : ℝ) (n m : ℤ) :
    Continuous (ccmWRFiniteNumeratorSlope L n m) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact (ccmWRFiniteNumerator_differentiable L n m 0).hasDerivAt.continuousAt_div
  · rw [ccmWRFiniteNumeratorSlope, continuousAt_update_of_ne hx]
    apply ContinuousAt.div
    · exact (ccmWRFiniteNumerator_differentiable L n m x).continuousAt.sub
        continuousAt_const
    · exact continuousAt_id.sub continuousAt_const
    · simpa using hx

private theorem ccmWRFiniteDenominatorSlope_continuous :
    Continuous ccmWRFiniteDenominatorSlope := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact ccmWRFiniteDenominator_hasDerivAt_zero.continuousAt_div
  · rw [ccmWRFiniteDenominatorSlope, continuousAt_update_of_ne hx]
    apply ContinuousAt.div
    · unfold ccmWRFiniteDenominator
      fun_prop
    · fun_prop
    · simpa using hx

private theorem ccmWRFiniteDenominatorSlope_ne_zero (x : ℝ) :
    ccmWRFiniteDenominatorSlope x ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    simp [ccmWRFiniteDenominatorSlope]
  · rw [ccmWRFiniteDenominatorSlope, Function.update_of_ne hx]
    apply div_ne_zero
    · simp only [ccmWRFiniteDenominator]
      norm_num
      intro heq
      have harg : x = -x := Real.exp_injective (sub_eq_zero.mp heq)
      exact hx (by linarith)
    · simpa using hx

private theorem ccmWRFiniteExtendedIntegrand_continuous (L : ℝ) (n m : ℤ) :
    Continuous (ccmWRFiniteExtendedIntegrand L n m) := by
  exact (ccmWRFiniteNumeratorSlope_continuous L n m).div
    ccmWRFiniteDenominatorSlope_continuous
    ccmWRFiniteDenominatorSlope_ne_zero

private theorem ccmWRFiniteExtendedIntegrand_eq_raw
    (L : ℝ) (n m : ℤ) {x : ℝ} (hx : x ≠ 0) :
    ccmWRFiniteExtendedIntegrand L n m x = ccmWRIntegrand L n m x := by
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    have harg : x = -x := Real.exp_injective (sub_eq_zero.mp h)
    exact hx (by linarith)
  simp only [ccmWRFiniteExtendedIntegrand, ccmWRFiniteNumeratorSlope,
    ccmWRFiniteDenominatorSlope, Function.update_of_ne hx]
  simp only [ccmWRFiniteNumerator, ccmWRFiniteDenominator, ccmWRIntegrand]
  simp only [Real.exp_zero, zero_div, sub_self, neg_zero, sub_zero]
  field_simp [hx, hden]
  ring

private theorem ccmWRIntegrandFinite_generic_integrableOn
    (L : ℝ) (n m : ℤ) :
    IntegrableOn (ccmWRIntegrand L n m) (Set.Ioc 0 L) := by
  apply (ccmWRFiniteExtendedIntegrand_continuous L n m).integrableOn_Ioc.congr_fun
  · intro x hx
    exact ccmWRFiniteExtendedIntegrand_eq_raw L n m (ne_of_gt hx.1)
  · exact measurableSet_Ioc

theorem ccmWRIntegrandFinite_integrableOn
    (mProject N : ℕ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (i j : CCMModeFinite N) :
    IntegrableOn
      (ccmWRIntegrand
        (ccmL mProject)
        (ccmModeFinite N i)
        (ccmModeFinite N j))
      (Set.Ioc 0 (ccmL mProject)) := by
  have _hL := ccmL_pos mProject hm
  have _hN := hN
  exact ccmWRIntegrandFinite_generic_integrableOn
    (ccmL mProject) (ccmModeFinite N i) (ccmModeFinite N j)

@[simp] theorem ccmWeilMatFinite_apply
    (mProject N : ℕ)
    (i j : CCMModeFinite N) :
    ccmWeilMatFinite mProject N i j =
      ccmWeilTauN1 mProject
        (ccmModeFinite N i)
        (ccmModeFinite N j) :=
  rfl

theorem ccmWeilMatFinite_transpose_eq
    (mProject N : ℕ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N) :
    (ccmWeilMatFinite mProject N).transpose =
      ccmWeilMatFinite mProject N := by
  have _hN := hN
  ext i j
  exact ccmWeilTauN1_symm mProject hm
    (ccmModeFinite N j) (ccmModeFinite N i)

theorem ccmWeilMatFinite_centrosymmetric
    (mProject N : ℕ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (i j : CCMModeFinite N) :
    ccmWeilMatFinite mProject N
        (ccmNegFinite N i) (ccmNegFinite N j) =
      ccmWeilMatFinite mProject N i j := by
  have _hN := hN
  change ccmWeilTauN1 mProject
      (ccmModeFinite N (ccmNegFinite N i))
      (ccmModeFinite N (ccmNegFinite N j)) =
    ccmWeilTauN1 mProject (ccmModeFinite N i) (ccmModeFinite N j)
  simp only [ccmModeFinite_neg, ccmWeilTauN1_neg_neg mProject hm]

theorem ccmWeilMatFinite_one_eq
    (mProject : ℕ) :
    ccmWeilMatFinite mProject 1 =
      ccmWeilMatN1 mProject := by
  rfl

theorem ccmDeltaFinite_eq_invSqrtL_smul_eta
    (mProject N : ℕ) :
    ccmDeltaFinite mProject N =
      (Real.sqrt (ccmL mProject))⁻¹ •
        ccmEtaFinite N :=
  rfl

#print axioms ccmWRIntegrandFinite_integrableOn
#print axioms ccmWeilMatFinite_transpose_eq
#print axioms ccmWeilMatFinite_centrosymmetric
#print axioms ccmWeilMatFinite_one_eq

end Q3.RouteB
