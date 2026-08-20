import Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
import Q3.Proofs.RouteB.D0ModeZeroFourFerrersProductionProlatePair
import Q3.Proofs.RouteB.D0PstarActualProlateEStarMemLp

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# The selected Ferrers inhabitant of `SelectedProlatePreAnchorData`

Knowledge preflight: `./ask.sh "SelectedProlatePreAnchorData inhabitant"`
returned no existing constructor; the structure had no inhabitant.

Precommitted schedule (C09, fixed before any proof attempt):
`k ↦ (mProject, N, K) = (k + 2, k + 2, 5 * (k + 2))`.
The schedule is strictly monotone in `k`, hence both cofinality fields are
arithmetic.  The pair at every `k` is the exact witness returned by
`exists_modeZero_modeFour_selectedFerrersProductionProlatePair`; no other
`ProlatePair` value enters.  `pair_spec` re-exports the full witness
conjunction, so the Ferrers provenance stays visible to later floors.

The only analytic field is `eStar_memLp`.  It is supplied by a new window
lemma that needs one global bound and almost-everywhere strong measurability
instead of `IsActualProlateModePair`; both follow from continuity of the
Ferrers series on its closed window.

This file does not touch `CCMLemma73PreAnchorPort`, does not assume the CCM
Lemma 7.2 rate, and defines no source scale.

LEDGER:
  CLOSES: [SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT]
  OPENS:  []
-/

/-- Precommitted index schedule: `m = N = k + 2`. -/
def selectedFerrersPreAnchorIndex (k : ℕ) : PairIndex :=
  ⟨k + 2, k + 2, by omega⟩

/-- The precommitted truncation `K = 5 * (k + 2)` satisfies the Ferrers
separation inequality: for `q ≥ K` the Jacobi diagonal dominates the
`31/24`-scaled bandwidth.  Pure arithmetic from `π ≤ 4`. -/
theorem selectedFerrersPreAnchorSeparation (k : ℕ) :
    ∀ q ≥ 5 * (k + 2),
      (31 / 24 : ℝ) * mode4JacobiG (k + 2) ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
  intro q hq
  rw [mode4JacobiG, mode4JacobiIndex]
  have hqr : 5 * ((k : ℝ) + 2) ≤ (q : ℝ) := by exact_mod_cast hq
  have hm2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpisq : Real.pi * Real.pi ≤ 16 := by nlinarith
  have hmsq : (2 : ℝ) * 2 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2) := by nlinarith
  have hqsq : (5 * ((k : ℝ) + 2)) * (5 * ((k : ℝ) + 2)) ≤ (q : ℝ) * (q : ℝ) := by
    have h0 : (0 : ℝ) ≤ 5 * ((k : ℝ) + 2) := by linarith
    exact mul_le_mul hqr hqr h0 ((Nat.cast_nonneg q))
  have hkey : Real.pi * Real.pi * (((k : ℝ) + 2) * ((k : ℝ) + 2)) ≤
      16 * (((k : ℝ) + 2) * ((k : ℝ) + 2)) := by
    have hnn : (0 : ℝ) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2) := by positivity
    exact mul_le_mul_of_nonneg_right hpisq hnn
  push_cast
  nlinarith [hkey, hqsq, hmsq, hqr, hm2]

/-- The witness package at every precommitted index.  This is the single
source of the pair; nothing else constructs a `ProlatePair` in this file. -/
private theorem selectedFerrersPreAnchorWitness (k : ℕ) :
    ∃ (S0 : Mode4FerrersRegularEvenProlateSolution (k + 2) (5 * (k + 2))
          (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0))
      (S4 : Mode4FerrersRegularEvenProlateSolution (k + 2) (5 * (k + 2))
          (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2))
      (P : ProlatePair),
      P.pw.lambda = Real.sqrt ((k + 2 : ℕ) : ℝ) ∧
      P.h0 = S0.normalizedPhysicalMode ∧
      P.h4 = S4.normalizedPhysicalMode ∧
      0 < P.I0 ∧ 0 < P.I4 ∧
      P.chi0 ≠ 0 ∧ P.chi2 ≠ 0 ∧
      (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
        finiteFourierAction P.pw.lambda P.h0 x =
          (P.chi0 : ℂ) * P.h0 x) ∧
      (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
        finiteFourierAction P.pw.lambda P.h4 x =
          (P.chi2 : ℂ) * P.h4 x) ∧
      mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 <
        mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 :=
  exists_modeZero_modeFour_selectedFerrersProductionProlatePair
    (k + 2) (5 * (k + 2)) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k)

/-- The selected mode-zero Ferrers solution on the precommitted schedule. -/
def selectedFerrersPreAnchorSolution0 (k : ℕ) :
    Mode4FerrersRegularEvenProlateSolution (k + 2) (5 * (k + 2))
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0) :=
  (selectedFerrersPreAnchorWitness k).choose

/-- The selected mode-four Ferrers solution on the precommitted schedule. -/
def selectedFerrersPreAnchorSolution4 (k : ℕ) :
    Mode4FerrersRegularEvenProlateSolution (k + 2) (5 * (k + 2))
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2) :=
  (selectedFerrersPreAnchorWitness k).choose_spec.choose

/-- The selected Ferrers production pair on the precommitted schedule. -/
def selectedFerrersPreAnchorPair (k : ℕ) : ProlatePair :=
  (selectedFerrersPreAnchorWitness k).choose_spec.choose_spec.choose

/-- Full provenance record: the pair at every index carries the exact witness
conjunction of the Ferrers production theorem.  This is the `pair_spec`
export required downstream: the modes are the selected normalized
zero-extended Ferrers modes, both integrals are positive, both Fourier
scalars are nonzero eigenvalue witnesses on the window, and the two
classical eigenvalues are strictly ordered. -/
theorem selectedFerrersPreAnchorPair_spec (k : ℕ) :
    (selectedFerrersPreAnchorPair k).pw.lambda = Real.sqrt ((k + 2 : ℕ) : ℝ) ∧
    (selectedFerrersPreAnchorPair k).h0 =
      (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode ∧
    (selectedFerrersPreAnchorPair k).h4 =
      (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode ∧
    0 < (selectedFerrersPreAnchorPair k).I0 ∧
    0 < (selectedFerrersPreAnchorPair k).I4 ∧
    (selectedFerrersPreAnchorPair k).chi0 ≠ 0 ∧
    (selectedFerrersPreAnchorPair k).chi2 ≠ 0 ∧
    (∀ x ∈ Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda,
      finiteFourierAction (selectedFerrersPreAnchorPair k).pw.lambda
          (selectedFerrersPreAnchorPair k).h0 x =
        ((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (selectedFerrersPreAnchorPair k).h0 x) ∧
    (∀ x ∈ Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda,
      finiteFourierAction (selectedFerrersPreAnchorPair k).pw.lambda
          (selectedFerrersPreAnchorPair k).h4 x =
        ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (selectedFerrersPreAnchorPair k).h4 x) ∧
    mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 <
      mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 :=
  (selectedFerrersPreAnchorWitness k).choose_spec.choose_spec.choose_spec

/-- The pair lives at the exact D0 scale of the precommitted index. -/
theorem selectedFerrersPreAnchorPair_lambda_eq (k : ℕ) :
    (selectedFerrersPreAnchorPair k).pw.lambda =
      lambda_m (selectedFerrersPreAnchorIndex k) := by
  have h := (selectedFerrersPreAnchorPair_spec k).1
  rw [h, lambda_m, selectedFerrersPreAnchorIndex]

/-- A normalized zero-extended Ferrers mode is almost everywhere strongly
measurable: it is the indicator of its closed window applied to a function
continuous on that window, divided by a constant. -/
theorem normalizedPhysicalMode_aestronglyMeasurable
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    AEStronglyMeasurable S.normalizedPhysicalMode volume := by
  have hzero : AEStronglyMeasurable S.physicalZeroExtension volume := by
    have hrepr : S.physicalZeroExtension =
        (Icc (-Real.sqrt mProject) (Real.sqrt mProject)).indicator
          (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) := rfl
    rw [hrepr, aestronglyMeasurable_indicator_iff measurableSet_Icc]
    exact (S.physicalComplex_continuousOn_closed hm).aestronglyMeasurable
      measurableSet_Icc
  simpa only [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    div_eq_mul_inv] using
      hzero.mul_const ((S.physicalL2Normalization : ℂ)⁻¹)

/-- A normalized zero-extended Ferrers mode is globally bounded: continuous
on its compact window, zero outside. -/
theorem normalizedPhysicalMode_norm_bound
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖S.normalizedPhysicalMode x‖ ≤ C := by
  obtain ⟨C0, hC0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      (S.physicalComplex_continuousOn_closed hm)
  have hzeroMem : (0 : ℝ) ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) :=
    ⟨neg_nonpos.mpr (Real.sqrt_nonneg _), Real.sqrt_nonneg _⟩
  have hC0nn : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 0 hzeroMem)
  have hnorm : 0 < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  refine ⟨C0 / S.physicalL2Normalization, by positivity, ?_⟩
  intro x
  rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnorm]
  have hnum : ‖S.physicalZeroExtension x‖ ≤ C0 := by
    rw [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension]
    by_cases hx : x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject)
    · rw [indicator_of_mem hx]
      exact hC0 x hx
    · rw [indicator_of_notMem hx, norm_zero]
      exact hC0nn
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hnorm.le)

/-- Window `MemLp` certificate from a global bound and measurability alone.
This weakens `prolateCombination_E_star_memLp_of_actualModes`: no
`IsActualProlateModePair` is consumed, only compact support at the D0 scale
(from the `ProlatePair` fields), one global norm bound, and almost
everywhere strong measurability. -/
theorem prolateCombination_E_star_memLp_of_windowBound
    (i : PairIndex) (P : ProlatePair)
    (hlambda : P.pw.lambda = lambda_m i)
    (hmeas : AEStronglyMeasurable (prolateCombination P) volume)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, ‖prolateCombination P x‖ ≤ C) :
    MemLp (E_star (prolateCombination P)) 2
      (dStar.restrict (I_m i)) := by
  let h := prolateCombination P
  let S := sourcePositiveIndexFinset i
  have hlam : 0 < lambda_m i := by
    rw [lambda_m]
    exact Real.sqrt_pos.2
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two i.hm))
  have hfinite : WindowFiniteSupport (lambda_m i) S h := by
    simpa only [h, S] using
      prolateCombination_windowFiniteSupport i P hlambda
  have hterm : ∀ n : ℕ+,
      AEStronglyMeasurable
        (fun u : ℝ => h (((n : ℕ) : ℝ) * u)) volume := by
    intro n
    have hn : (((n : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast n.pos.ne'
    have hqmp : Measure.QuasiMeasurePreserving
        (fun u : ℝ => ((n : ℕ) : ℝ) * u) volume volume := by
      refine ⟨measurable_const_mul _, ?_⟩
      rw [Real.map_volume_mul_left hn]
      exact Measure.smul_absolutelyContinuous
    simpa [Function.comp] using
      hmeas.comp_quasiMeasurePreserving hqmp
  have hcore : AEStronglyMeasurable (finiteEStarCore S h) volume := by
    have hfun : finiteEStarCore S h =
        ∑ n ∈ S, fun u : ℝ => h (((n : ℕ) : ℝ) * u) := by
      funext u
      simp [finiteEStarCore, Finset.sum_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ fun n _ => hterm n
  have hsqrtm : AEStronglyMeasurable
      (fun u : ℝ => ((Real.sqrt u : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp Real.continuous_sqrt).aestronglyMeasurable
  have hfiniteAESM : AEStronglyMeasurable (finiteEStar S h) volume := by
    unfold finiteEStar
    exact hsqrtm.mul hcore
  have hAC : dStar.restrict (I_m i) ≪ volume := by
    have h1 : dStar ≪ volume := withDensity_absolutelyContinuous _ _
    exact (h1.restrict _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  let B : ℝ := Real.sqrt (lambda_m i) * (S.card : ℝ) * C
  have hfiniteBound : ∀ u ∈ I_m i, ‖finiteEStar S h u‖ ≤ B := by
    intro u hu
    have hsqrt : Real.sqrt u ≤ Real.sqrt (lambda_m i) :=
      Real.sqrt_le_sqrt hu.2
    have hsum : ‖finiteEStarCore S h u‖ ≤ (S.card : ℝ) * C := by
      calc
        ‖finiteEStarCore S h u‖ ≤
            ∑ n ∈ S, ‖h (((n : ℕ) : ℝ) * u)‖ := by
          unfold finiteEStarCore
          exact norm_sum_le _ _
        _ ≤ ∑ n ∈ S, C := by
          gcongr with n hn
          exact hbound _
        _ = (S.card : ℝ) * C := by simp
    rw [finiteEStar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg u)]
    dsimp [B]
    calc
      Real.sqrt u * ‖finiteEStarCore S h u‖ ≤
          Real.sqrt (lambda_m i) * ((S.card : ℝ) * C) :=
        mul_le_mul hsqrt hsum (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (lambda_m i) * (S.card : ℝ) * C := by ring
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      have hinv : IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
        apply ContinuousOn.integrableOn_Icc
        apply continuousOn_id.inv₀
        intro u hu
        exact ne_of_gt ((inv_pos.mpr hlam).trans_le hu.1)
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hfiniteLp : MemLp (finiteEStar S h) 2
      (dStar.restrict (I_m i)) := by
    apply MemLp.of_bound (hfiniteAESM.mono_ac hAC) B
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hfiniteBound u hu
  have heq :
      finiteEStar S h =ᵐ[dStar.restrict (I_m i)] E_star h := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact
      (E_star_eq_finiteEStar_of_windowFiniteSupport hfinite hu).symm
  simpa only [h] using MemLp.ae_eq heq hfiniteLp

/-- The selected Ferrers packet is almost everywhere strongly measurable. -/
theorem selectedFerrersPreAnchorPair_combination_aestronglyMeasurable
    (k : ℕ) :
    AEStronglyMeasurable
      (prolateCombination (selectedFerrersPreAnchorPair k)) volume := by
  obtain ⟨_, hh0, hh4, _, _, _, _, _, _, _⟩ :=
    selectedFerrersPreAnchorPair_spec k
  have h0m := normalizedPhysicalMode_aestronglyMeasurable
    (selectedFerrersPreAnchorSolution0 k) (by omega)
  have h4m := normalizedPhysicalMode_aestronglyMeasurable
    (selectedFerrersPreAnchorSolution4 k) (by omega)
  unfold prolateCombination
  rw [hh0, hh4]
  simp only [div_eq_mul_inv]
  exact ((h0m.const_mul _).sub (h4m.const_mul _)).mul_const _

/-- The selected Ferrers packet is globally bounded. -/
theorem selectedFerrersPreAnchorPair_combination_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖prolateCombination (selectedFerrersPreAnchorPair k) x‖ ≤ C := by
  obtain ⟨_, hh0, hh4, hI0, _, _, _, _, _, _⟩ :=
    selectedFerrersPreAnchorPair_spec k
  obtain ⟨C0, hC0nn, hC0⟩ := normalizedPhysicalMode_norm_bound
    (selectedFerrersPreAnchorSolution0 k) (by omega)
  obtain ⟨C4, hC4nn, hC4⟩ := normalizedPhysicalMode_norm_bound
    (selectedFerrersPreAnchorSolution4 k) (by omega)
  set P := selectedFerrersPreAnchorPair k with hP
  have hden : 0 < P.normalizingDenominator := by
    rw [ProlatePair.normalizingDenominator_eq]
    exact Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg (pow_pos hI0 2) (sq_nonneg _))
  refine ⟨(|P.I4| * C0 + |P.I0| * C4) / P.normalizingDenominator,
    by positivity, ?_⟩
  intro x
  unfold prolateCombination
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  have hnum : ‖(P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x‖ ≤
      |P.I4| * C0 + |P.I0| * C4 := by
    calc
      ‖(P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x‖ ≤
          ‖(P.I4 : ℂ) * P.h0 x‖ + ‖(P.I0 : ℂ) * P.h4 x‖ :=
        norm_sub_le _ _
      _ = |P.I4| * ‖P.h0 x‖ + |P.I0| * ‖P.h4 x‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |P.I4| * C0 + |P.I0| * C4 := by
        gcongr
        · rw [hh0]
          exact hC0 x
        · rw [hh4]
          exact hC4 x
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)

/-- The `MemLp` field of the packet at every precommitted index. -/
theorem selectedFerrersPreAnchorPair_eStar_memLp (k : ℕ) :
    MemLp (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  obtain ⟨C, hC, hbound⟩ := selectedFerrersPreAnchorPair_combination_bound k
  exact prolateCombination_E_star_memLp_of_windowBound
    (selectedFerrersPreAnchorIndex k) (selectedFerrersPreAnchorPair k)
    (selectedFerrersPreAnchorPair_lambda_eq k)
    (selectedFerrersPreAnchorPair_combination_aestronglyMeasurable k)
    C hC hbound

/-- The selected Ferrers inhabitant of `SelectedProlatePreAnchorData` on the
precommitted schedule `k ↦ (k + 2, k + 2, 5 * (k + 2))`. -/
def selectedFerrersPreAnchorData : SelectedProlatePreAnchorData where
  index := selectedFerrersPreAnchorIndex
  pair := selectedFerrersPreAnchorPair
  mCofinal := by
    show Tendsto (fun k : ℕ => k + 2) atTop atTop
    exact tendsto_atTop_mono (fun k => by simp only [id_eq]; omega) tendsto_id
  nCofinal := by
    show Tendsto (fun k : ℕ => k + 2) atTop atTop
    exact tendsto_atTop_mono (fun k => by simp only [id_eq]; omega) tendsto_id
  lambda_eq := selectedFerrersPreAnchorPair_lambda_eq
  eStar_memLp := selectedFerrersPreAnchorPair_eStar_memLp

/-- Exact index formula (reducibility export). -/
@[simp] theorem selectedFerrersPreAnchorData_index (k : ℕ) :
    selectedFerrersPreAnchorData.index k =
      selectedFerrersPreAnchorIndex k := rfl

/-- Exact pair formula (reducibility export). -/
@[simp] theorem selectedFerrersPreAnchorData_pair (k : ℕ) :
    selectedFerrersPreAnchorData.pair k =
      selectedFerrersPreAnchorPair k := rfl

/-- Provenance of the packet pair: the data record stores, at every index,
exactly the Ferrers production witness pair. -/
theorem selectedFerrersPreAnchorData_pair_spec (k : ℕ) :
    (selectedFerrersPreAnchorData.pair k).h0 =
      (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode ∧
    (selectedFerrersPreAnchorData.pair k).h4 =
      (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode :=
  ⟨(selectedFerrersPreAnchorPair_spec k).2.1,
    (selectedFerrersPreAnchorPair_spec k).2.2.1⟩

#print axioms selectedFerrersPreAnchorSeparation
#print axioms selectedFerrersPreAnchorPair_spec
#print axioms selectedFerrersPreAnchorPair_lambda_eq
#print axioms normalizedPhysicalMode_aestronglyMeasurable
#print axioms normalizedPhysicalMode_norm_bound
#print axioms prolateCombination_E_star_memLp_of_windowBound
#print axioms selectedFerrersPreAnchorPair_eStar_memLp
#print axioms selectedFerrersPreAnchorData
#print axioms selectedFerrersPreAnchorData_pair_spec

end Q3.RouteB.D0Pstar
