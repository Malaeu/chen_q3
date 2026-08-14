import Q3.Proofs.RouteB.D0Mode4FerrersCoefficientExtraction
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Connected.Clopen

/-!
# Goal 058 G3: simplicity of interior mode-four Ferrers zeros

The accepted regular-solution object now identifies its formal derivative
series with actual derivatives.  This file rewrites the scalar prolate ODE as
a first-order linear system and applies local ODE uniqueness.  Zero Cauchy
data therefore propagate across the connected source interval, contradicting
the already proved positive zeroth-coefficient extraction.

This is still a dimensionless mode-four source theorem.  It does not count
zeros, identify the ordered degree-four PSWF, select a matching root, or supply
the physical scaling or finite-Fourier eigenrelation.
-/

namespace Q3.RouteB

private noncomputable def mode4ProlateFirstOrderCLM
    (mProject : ℕ) (Λ x : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  let A :=
    (mode4JacobiG mProject * x ^ 2 -
      (Λ + mode4JacobiG mProject)) / (1 - x ^ 2)
  let B := (2 * x) / (1 - x ^ 2)
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (A • ContinuousLinearMap.fst ℝ ℝ ℝ +
      B • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp]
private theorem mode4ProlateFirstOrderCLM_apply
    (mProject : ℕ) (Λ x : ℝ) (p : ℝ × ℝ) :
    mode4ProlateFirstOrderCLM mProject Λ x p =
      (p.2,
        ((mode4JacobiG mProject * x ^ 2 -
              (Λ + mode4JacobiG mProject)) * p.1 +
            2 * x * p.2) / (1 - x ^ 2)) := by
  simp [mode4ProlateFirstOrderCLM]
  ring

private theorem mode4ProlateFirstOrderCLM_continuousAt
    (mProject : ℕ) (Λ x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousAt (mode4ProlateFirstOrderCLM mProject Λ) x := by
  have hdenPos : 0 < 1 - x ^ 2 := by
    have hxLeft : 0 < x + 1 := by linarith [hx.1]
    have hxRight : 0 < 1 - x := by linarith [hx.2]
    nlinarith [mul_pos hxLeft hxRight]
  have hden : 1 - x ^ 2 ≠ 0 := hdenPos.ne'
  have hSecond :
      ContinuousAt
        (fun y : ℝ =>
          (((mode4JacobiG mProject * y ^ 2 -
                  (Λ + mode4JacobiG mProject)) / (1 - y ^ 2)) •
              ContinuousLinearMap.fst ℝ ℝ ℝ +
            ((2 * y) / (1 - y ^ 2)) •
              ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
    have hNumA :
        ContinuousAt
          (fun y : ℝ =>
            mode4JacobiG mProject * y ^ 2 -
              (Λ + mode4JacobiG mProject)) x := by
      fun_prop
    have hDen :
        ContinuousAt (fun y : ℝ => 1 - y ^ 2) x := by
      fun_prop
    have hA :
        ContinuousAt
          (fun y : ℝ =>
            (mode4JacobiG mProject * y ^ 2 -
              (Λ + mode4JacobiG mProject)) / (1 - y ^ 2)) x :=
      hNumA.div hDen hden
    have hNumB : ContinuousAt (fun y : ℝ => 2 * y) x := by
      fun_prop
    have hB :
        ContinuousAt (fun y : ℝ => (2 * y) / (1 - y ^ 2)) x :=
      hNumB.div hDen hden
    exact
      (hA.smul continuousAt_const).add
        (hB.smul continuousAt_const)
  have hPair :
      ContinuousAt
        (fun y : ℝ =>
          (ContinuousLinearMap.snd ℝ ℝ ℝ,
            (((mode4JacobiG mProject * y ^ 2 -
                    (Λ + mode4JacobiG mProject)) / (1 - y ^ 2)) •
                ContinuousLinearMap.fst ℝ ℝ ℝ +
              ((2 * y) / (1 - y ^ 2)) •
                ContinuousLinearMap.snd ℝ ℝ ℝ))) x :=
    continuousAt_const.prodMk hSecond
  simpa [mode4ProlateFirstOrderCLM] using
    ((ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp hPair)

/-- Every interior zero of the accepted regular even mode-four Ferrers
solution is simple.  The theorem uses only the semantic derivative interface,
the stored prolate ODE, and the positive zeroth-coefficient extraction; source
tail guards do not leak into this consumer. -/
theorem Mode4FerrersRegularEvenProlateSolution.interior_zero_simple
    {mProject K : ℕ} {Λ x : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hz : mode4FerrersSeries S.coefficients x = 0) :
    deriv (mode4FerrersSeries S.coefficients) x ≠ 0 := by
  intro hDerivZero
  let state : ℝ → ℝ × ℝ := fun t =>
    (mode4FerrersSeries S.coefficients t,
      mode4FerrersFirstDerivativeSeries S.coefficients t)
  let vectorField : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    mode4ProlateFirstOrderCLM mProject Λ
  have hStateDeriv :
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt state (vectorField t (state t)) t := by
    intro t ht
    have hFirst :=
      S.ferrersSeries_hasDerivAt_firstDerivativeSeries t ht
    have hSecond :=
      S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries t ht
    have hODE := S.prolateDifferentialEquation t ht
    have hdenPos : 0 < 1 - t ^ 2 := by
      have htLeft : 0 < t + 1 := by linarith [ht.1]
      have htRight : 0 < 1 - t := by linarith [ht.2]
      nlinarith [mul_pos htLeft htRight]
    have hSecondEq :
        mode4FerrersSecondDerivativeSeries S.coefficients t =
          ((mode4JacobiG mProject * t ^ 2 -
                (Λ + mode4JacobiG mProject)) *
              mode4FerrersSeries S.coefficients t +
            2 * t *
              mode4FerrersFirstDerivativeSeries S.coefficients t) /
            (1 - t ^ 2) := by
      apply (eq_div_iff hdenPos.ne').2
      nlinarith
    convert hFirst.prodMk hSecond using 1
    simp only [state, vectorField, mode4ProlateFirstOrderCLM_apply]
    rw [hSecondEq]
  have hStateContinuous : ContinuousOn state (Set.Ioo (-1 : ℝ) 1) :=
    fun t ht => (hStateDeriv t ht).continuousAt.continuousWithinAt
  have hLocalZero :
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        state t = (0, 0) →
          state =ᶠ[nhds t] (fun _ : ℝ => (0, 0)) := by
    intro t ht hzt
    have hFieldContinuous : ContinuousAt vectorField t :=
      mode4ProlateFirstOrderCLM_continuousAt mProject Λ t ht
    have hNormEventually :
        ∀ᶠ y in nhds t,
          ‖vectorField y‖₊ < ‖vectorField t‖₊ + 1 :=
      hFieldContinuous.nnnorm.tendsto
        (Iio_mem_nhds (lt_add_one _))
    apply ODE_solution_unique_of_eventually
      (K := ‖vectorField t‖₊ + 1)
      (v := fun y => vectorField y)
      (s := fun _ => Set.univ)
    · filter_upwards [hNormEventually] with y hy
      exact ((vectorField y).lipschitz.weaken hy.le).lipschitzOnWith
    · filter_upwards [isOpen_Ioo.eventually_mem ht] with y hy
      exact ⟨hStateDeriv y hy, Set.mem_univ _⟩
    · exact Filter.Eventually.of_forall fun y => by
        constructor
        · convert (hasDerivAt_const y (0 : ℝ × ℝ)) using 1;
            simp [vectorField]
        · exact Set.mem_univ _
    · exact hzt
  have hFirstZero :
      mode4FerrersFirstDerivativeSeries S.coefficients x = 0 := by
    rw [← (S.ferrersSeries_hasDerivAt_firstDerivativeSeries x hx).deriv]
    exact hDerivZero
  have hxState : state x = (0, 0) := by
    simp [state, hz, hFirstZero]
  let I : Set ℝ := Set.Ioo (-1 : ℝ) 1
  let Z : Set I := {t | state t.1 = (0, 0)}
  letI : PreconnectedSpace I :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hStateRestrictContinuous :
      Continuous (fun t : I => state t.1) := by
    exact continuousOn_iff_continuous_restrict.mp hStateContinuous
  have hZClosed : IsClosed Z := by
    exact isClosed_singleton.preimage hStateRestrictContinuous
  have hZOpen : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hEqEventually := hLocalZero t.1 t.2 ht
    exact (continuous_subtype_val.tendsto t) hEqEventually
  have hZNonempty : Z.Nonempty :=
    ⟨⟨x, hx⟩, hxState⟩
  have hZUniv : Z = Set.univ :=
    (show IsClopen Z from ⟨hZClosed, hZOpen⟩).eq_univ hZNonempty
  have hEqOpen :
      Set.EqOn (mode4FerrersSeries S.coefficients) 0
        (Set.Ioo (-1 : ℝ) 1) := by
    intro t ht
    have htZ : (⟨t, ht⟩ : I) ∈ Z := by
      rw [hZUniv]
      exact Set.mem_univ _
    exact congrArg Prod.fst htZ
  have hEqClosed :
      Set.EqOn (mode4FerrersSeries S.coefficients) 0
        (Set.Icc (-1 : ℝ) 1) := by
    apply hEqOpen.of_subset_closure
      S.continuousOn_closed continuousOn_const
      Set.Ioo_subset_Icc_self
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  have hIntegralZero :
      ∫ t in (-1 : ℝ)..1,
        mode4FerrersSeries S.coefficients t = 0 := by
    calc
      ∫ t in (-1 : ℝ)..1,
          mode4FerrersSeries S.coefficients t =
          ∫ _t in (-1 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hEqClosed (by simpa using ht)
      _ = 0 := by simp
  have hIntegral :=
    mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
      S.coefficients S.coefficients_abs_summable
  rw [hIntegral] at hIntegralZero
  nlinarith [S.coefficient_zero_pos]

#print axioms Mode4FerrersRegularEvenProlateSolution.interior_zero_simple

end Q3.RouteB
