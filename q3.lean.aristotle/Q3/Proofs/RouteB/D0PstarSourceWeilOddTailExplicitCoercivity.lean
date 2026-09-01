import Q3.Proofs.RouteB.D0PstarSourceLowBandModeDecay
import Q3.Proofs.RouteB.D0PstarSourceArchHighFrequencyLowerBound
import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailCoercivityClosure

set_option linter.mathlibStandardSet false
set_option maxRecDepth 2048

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Real

namespace Q3.RouteB.D0Pstar

/-!
# Explicit source-Weil coercivity on the literal odd tail

This file assembles the two source-locked analytic legs already proved in
Lean: the symbolic high-frequency lower bound for the production
archimedean multiplier and the uniform `1/R` low-band Fourier-mass estimate
for arbitrary finite odd-tail syntheses.  The bounded W02 and Prime forms are
then absorbed by one deliberately coarse, explicit natural cutoff.

No finite matrix floor, sampled frequency, or numerical certificate enters
the construction.
-/

/-- Archimedean target chosen one unit above the norms of both bounded
source perturbations. -/
noncomputable def sourceWeilOddTailHighTarget (i : PairIndex) : ℝ :=
  ‖sourceW02AmbientContinuousSesquilinearForm i‖ +
    ‖sourcePrimeContinuousSesquilinearForm i‖ + 1

/-- Symbolic frequency band beyond which the production archimedean
multiplier dominates `sourceWeilOddTailHighTarget`. -/
noncomputable def sourceWeilOddTailBandRadius (i : PairIndex) : ℝ :=
  Real.exp
    (sourceWeilOddTailHighTarget i + |Real.log Real.pi| + 6)

/-- Real precursor of the final mode cutoff.  Its two nontrivial branches
enforce respectively the safe-frequency condition and the `1/2` low-band
loss budget. -/
noncomputable def sourceWeilOddTailCutoffScale (i : PairIndex) : ℝ :=
  max 1 <| max
    (2 * L_m i * (sourceWeilOddTailBandRadius i + 1))
    (4 * sourceWeilOddTailBandRadius i *
      (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
      (sourceWeilOddTailHighTarget i +
        (|Real.log Real.pi| + Real.log 4 + 6)))

/-- Explicit natural source-Weil odd-tail cutoff.  The successor after the
ceiling makes positivity and all weak cutoff inequalities immediate. -/
noncomputable def sourceWeilOddTailCutoff (i : PairIndex) : ℕ :=
  Nat.ceil (sourceWeilOddTailCutoffScale i) + 1

theorem sourceWeilOddTailHighTarget_pos (i : PairIndex) :
    0 < sourceWeilOddTailHighTarget i := by
  unfold sourceWeilOddTailHighTarget
  positivity

theorem sourceWeilOddTailBandRadius_pos (i : PairIndex) :
    0 < sourceWeilOddTailBandRadius i := by
  unfold sourceWeilOddTailBandRadius
  positivity

theorem sourceWeilOddTailCutoff_pos (i : PairIndex) :
    0 < sourceWeilOddTailCutoff i := by
  unfold sourceWeilOddTailCutoff
  omega

private theorem sourceWeilOddTailCutoffScale_le_cutoff (i : PairIndex) :
    sourceWeilOddTailCutoffScale i ≤ (sourceWeilOddTailCutoff i : ℝ) := by
  have hceil : sourceWeilOddTailCutoffScale i ≤
      (Nat.ceil (sourceWeilOddTailCutoffScale i) : ℝ) :=
    Nat.le_ceil _
  unfold sourceWeilOddTailCutoff
  norm_num
  linarith

theorem sourceWeilOddTailCutoff_safeFrequency (i : PairIndex) :
    2 * L_m i * (sourceWeilOddTailBandRadius i + 1) ≤
      (sourceWeilOddTailCutoff i + 1 : ℝ) := by
  have hbranch :
      2 * L_m i * (sourceWeilOddTailBandRadius i + 1) ≤
        sourceWeilOddTailCutoffScale i := by
    unfold sourceWeilOddTailCutoffScale
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hscale := sourceWeilOddTailCutoffScale_le_cutoff i
  norm_num at hscale ⊢
  linarith

theorem sourceWeilOddTailCutoff_lowBandBudget (i : PairIndex) :
    (sourceWeilOddTailHighTarget i +
        (|Real.log Real.pi| + Real.log 4 + 6)) *
      ((2 * sourceWeilOddTailBandRadius i) *
        ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
          (1 / (sourceWeilOddTailCutoff i : ℝ)))) ≤
      1 / 2 := by
  have hbranch :
      4 * sourceWeilOddTailBandRadius i *
          (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
          (sourceWeilOddTailHighTarget i +
            (|Real.log Real.pi| + Real.log 4 + 6)) ≤
        sourceWeilOddTailCutoffScale i := by
    unfold sourceWeilOddTailCutoffScale
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hscale := sourceWeilOddTailCutoffScale_le_cutoff i
  have hR : 0 < (sourceWeilOddTailCutoff i : ℝ) := by
    exact_mod_cast sourceWeilOddTailCutoff_pos i
  have hraw :
      4 * sourceWeilOddTailBandRadius i *
          (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
          (sourceWeilOddTailHighTarget i +
            (|Real.log Real.pi| + Real.log 4 + 6)) ≤
        (sourceWeilOddTailCutoff i : ℝ) :=
    hbranch.trans hscale
  have heq :
      (sourceWeilOddTailHighTarget i +
          (|Real.log Real.pi| + Real.log 4 + 6)) *
        ((2 * sourceWeilOddTailBandRadius i) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
            (1 / (sourceWeilOddTailCutoff i : ℝ)))) =
        (4 * sourceWeilOddTailBandRadius i *
          (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
          (sourceWeilOddTailHighTarget i +
            (|Real.log Real.pi| + Real.log 4 + 6))) /
          (2 * (sourceWeilOddTailCutoff i : ℝ)) := by
    field_simp [hR.ne']
    ring
  rw [heq, div_le_iff₀ (by positivity :
    (0 : ℝ) < 2 * (sourceWeilOddTailCutoff i : ℝ))]
  convert hraw using 1
  all_goals ring

/-- Finite synthesis of literal shifted odd graph generators. -/
noncomputable def sourceWeilOddGraphFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    SourceWeilGraphCarrier i :=
  c.sum fun k z => z • sourceWeilGraphOddMode i (R + k)

theorem sourceWeilOddGraphFinsuppShift_mem_span
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    sourceWeilOddGraphFinsuppShift i R c ∈
      Submodule.span ℂ
        (Set.range (fun k : ℕ => sourceWeilGraphOddMode i (R + k))) := by
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  exact ⟨c, rfl⟩

theorem sourceWeilGraphAmbient_oddGraphFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    sourceWeilGraphAmbient i
        (sourceWeilOddGraphFinsuppShift i R c) =
      sourceWeilOddAmbientFinsuppShift i R c := by
  classical
  unfold sourceWeilOddGraphFinsuppShift
  unfold sourceWeilOddAmbientFinsuppShift
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro k hk
  rw [map_smul, sourceWeilGraphAmbient_oddMode]
  rfl

theorem coeFn_sourceLogWindowFourierL2Isometry_apply_oddGraphFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    ((sourceLogWindowFourierL2Isometry i
          (sourceWeilGraphDomain i
            (sourceWeilOddGraphFinsuppShift i R c) : H_m i) :
        MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ)
      =ᵐ[MeasureTheory.volume]
        sourceWeilOddFourierFinsuppShift i R c := by
  have h :=
    coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientFinsuppShift
      i R c
  rw [← sourceWeilGraphAmbient_oddGraphFinsuppShift i R c] at h
  simpa only [sourceWeilGraphDomain_coe] using h

/-- Parseval for the production whole-line Fourier isometry, in the real
integral form used by the coercivity estimate. -/
theorem integral_norm_sourceLogWindowFourierL2Isometry_sq
    (i : PairIndex) (x : H_m i) :
    (∫ t : ℝ,
        ‖(((sourceLogWindowFourierL2Isometry i x :
          MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t)‖ ^ 2) =
      ‖x‖ ^ 2 := by
  let F : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i x
  calc
    (∫ t : ℝ, ‖((F : ℝ → ℂ) t)‖ ^ 2) =
        ∫ t : ℝ,
          RCLike.re (inner ℂ ((F : ℝ → ℂ) t) ((F : ℝ → ℂ) t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact norm_sq_eq_re_inner (𝕜 := ℂ) ((F : ℝ → ℂ) t)
    _ = RCLike.re
        (∫ t : ℝ, inner ℂ ((F : ℝ → ℂ) t) ((F : ℝ → ℂ) t)) :=
      integral_re (MeasureTheory.L2.integrable_inner F F)
    _ = RCLike.re (inner ℂ F F) := by
      rw [MeasureTheory.L2.inner_def]
    _ = ‖F‖ ^ 2 := by
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) F).symm
    _ = ‖x‖ ^ 2 := by
      rw [(sourceLogWindowFourierL2Isometry i).norm_map]

/-- The positive shifted archimedean diagonal is exactly the real integral of
the nonnegative shifted multiplier against Fourier mass. -/
theorem sourceArchimedeanShiftedSesquilinearForm_re_self_eq_integral_norm_sq
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    (sourceArchimedeanShiftedSesquilinearForm i x x).re =
      ∫ t : ℝ,
        (sourceArchimedeanMultiplier t +
          (|Real.log Real.pi| + Real.log 4 + 6)) *
        ‖(((sourceLogWindowFourierL2Isometry i (x : H_m i) :
          MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t)‖ ^ 2 := by
  let W : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceArchimedeanShiftedWeightedLpLinearMap i x
  rw [sourceArchimedeanShiftedSesquilinearForm_apply]
  change RCLike.re (inner ℂ W W) = _
  rw [MeasureTheory.L2.inner_def]
  calc
    RCLike.re
        (∫ t : ℝ, inner ℂ ((W : ℝ → ℂ) t) ((W : ℝ → ℂ) t)) =
        ∫ t : ℝ,
          RCLike.re (inner ℂ ((W : ℝ → ℂ) t) ((W : ℝ → ℂ) t)) :=
      (integral_re (MeasureTheory.L2.integrable_inner W W)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards
        [coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i x] with t ht
      rw [ht, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sourceArchimedeanShiftedSqrtWeight_nonneg t)]
      rw [mul_pow, sourceArchimedeanShiftedSqrtWeight_sq]

/-- The shifted source multiplier times Fourier mass is integrable on the
whole line.  This is just the pointwise square of the production weighted
`L²` representative. -/
theorem integrable_sourceArchimedeanShiftedMultiplier_mul_fourierNorm_sq
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t +
          (|Real.log Real.pi| + Real.log 4 + 6)) *
        ‖(((sourceLogWindowFourierL2Isometry i (x : H_m i) :
          MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t)‖ ^ 2) := by
  let W : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceArchimedeanShiftedWeightedLpLinearMap i x
  have hWint : MeasureTheory.Integrable
      (fun t : ℝ => ‖((W : ℝ → ℂ) t)‖ ^ (2 : ℕ)) :=
    (MeasureTheory.Lp.memLp W).integrable_norm_pow (by norm_num)
  apply hWint.congr
  filter_upwards
    [coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i x] with t ht
  rw [ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sourceArchimedeanShiftedSqrtWeight_nonneg t)]
  rw [mul_pow, sourceArchimedeanShiftedSqrtWeight_sq]

/-- Elementary measure-theoretic engine for the high/low frequency split:
if a nonnegative weight is at least `D` off the central band, its weighted
integral controls `D` times the total mass minus the central-band mass. -/
theorem weightedIntegral_ge_const_mul_total_sub_band
    (F q : ℝ → ℝ) (T D : ℝ)
    (hFint : MeasureTheory.Integrable F)
    (hqFint : MeasureTheory.Integrable (fun t => q t * F t))
    (hFnonneg : ∀ t, 0 ≤ F t)
    (hqnonneg : ∀ t, 0 ≤ q t)
    (houtside : ∀ t ∈ (Set.Icc (-T) T)ᶜ, D ≤ q t) :
    D * ((∫ t, F t) - ∫ t in Set.Icc (-T) T, F t) ≤
      ∫ t, q t * F t := by
  have hscaledOutside :
      D * (∫ t in (Set.Icc (-T) T)ᶜ, F t) ≤
        ∫ t in (Set.Icc (-T) T)ᶜ, q t * F t := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_mono_on
    · exact (hFint.const_mul D).integrableOn
    · exact hqFint.integrableOn
    · exact measurableSet_Icc.compl
    · intro t ht
      exact mul_le_mul_of_nonneg_right (houtside t ht) (hFnonneg t)
  have hOutsideLeFull :
      (∫ t in (Set.Icc (-T) T)ᶜ, q t * F t) ≤
        ∫ t, q t * F t := by
    apply MeasureTheory.setIntegral_le_integral hqFint
    filter_upwards [] with t
    exact mul_nonneg (hqnonneg t) (hFnonneg t)
  have hsplit :=
    MeasureTheory.integral_add_compl
      (s := Set.Icc (-T) T) measurableSet_Icc hFint
  have hOutsideEq :
      (∫ t in (Set.Icc (-T) T)ᶜ, F t) =
        (∫ t, F t) - ∫ t in Set.Icc (-T) T, F t := by
    linarith
  calc
    D * ((∫ t, F t) - ∫ t in Set.Icc (-T) T, F t) =
        D * (∫ t in (Set.Icc (-T) T)ᶜ, F t) := by rw [hOutsideEq]
    _ ≤ ∫ t in (Set.Icc (-T) T)ᶜ, q t * F t := hscaledOutside
    _ ≤ ∫ t, q t * F t := hOutsideLeFull

/-- The raw archimedean diagonal on every finite shifted odd-tail synthesis
dominates the explicit high-frequency target, with only the registered
`1/2` low-band loss. -/
theorem sourceArchimedeanSesquilinearForm_re_self_lower_oddGraphFinsuppShift
    (i : PairIndex) (c : ℕ →₀ ℂ) :
    (sourceWeilOddTailHighTarget i - 1 / 2) *
        ‖sourceWeilOddAmbientFinsuppShift i
          (sourceWeilOddTailCutoff i) c‖ ^ 2 ≤
      (sourceArchimedeanSesquilinearForm i
        (sourceWeilGraphDomain i
          (sourceWeilOddGraphFinsuppShift i
            (sourceWeilOddTailCutoff i) c))
        (sourceWeilGraphDomain i
          (sourceWeilOddGraphFinsuppShift i
            (sourceWeilOddTailCutoff i) c))).re := by
  let R : ℕ := sourceWeilOddTailCutoff i
  let T : ℝ := sourceWeilOddTailBandRadius i
  let C : ℝ := sourceWeilOddTailHighTarget i
  let A0 : ℝ := |Real.log Real.pi| + Real.log 4 + 6
  let xg : SourceWeilGraphCarrier i :=
    sourceWeilOddGraphFinsuppShift i R c
  let x : sourceArchimedeanShiftedFormDomain i :=
    sourceWeilGraphDomain i xg
  let F : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i (x : H_m i)
  have hFint : MeasureTheory.Integrable
      (fun t : ℝ => ‖((F : ℝ → ℂ) t)‖ ^ (2 : ℕ)) :=
    (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hqFint : MeasureTheory.Integrable
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t + A0) *
          ‖((F : ℝ → ℂ) t)‖ ^ 2) := by
    simpa [F, A0, x] using
      integrable_sourceArchimedeanShiftedMultiplier_mul_fourierNorm_sq i x
  have hA0 : 0 ≤ A0 := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp only [A0]
    positivity
  have hOutside : ∀ t ∈ (Set.Icc (-T) T)ᶜ,
      C + A0 ≤ sourceArchimedeanMultiplier t + A0 := by
    intro t ht
    have htNot := ht
    change t ∉ Set.Icc (-T) T at htNot
    have habs : T ≤ |t| := by
      by_contra h
      have habslt : |t| < T := lt_of_not_ge h
      exact htNot (abs_le.mp (le_of_lt habslt))
    have harch : C ≤ sourceArchimedeanMultiplier t := by
      apply sourceArchimedeanMultiplier_ge_of_exp_shift_le_abs
      simpa [T, C, sourceWeilOddTailBandRadius] using habs
    linarith
  have hweighted :
      (C + A0) *
          ((∫ t : ℝ, ‖((F : ℝ → ℂ) t)‖ ^ 2) -
            ∫ t in Set.Icc (-T) T, ‖((F : ℝ → ℂ) t)‖ ^ 2) ≤
        ∫ t : ℝ,
          (sourceArchimedeanMultiplier t + A0) *
            ‖((F : ℝ → ℂ) t)‖ ^ 2 := by
    apply weightedIntegral_ge_const_mul_total_sub_band
    · exact hFint
    · exact hqFint
    · intro t
      positivity
    · intro t
      simpa [A0] using
        sourceArchimedeanMultiplier_add_explicitShift_nonneg t
    · exact hOutside
  have htotal :
      (∫ t : ℝ, ‖((F : ℝ → ℂ) t)‖ ^ 2) =
        ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 := by
    calc
      (∫ t : ℝ, ‖((F : ℝ → ℂ) t)‖ ^ 2) =
          ‖(x : H_m i)‖ ^ 2 := by
        simpa [F] using
          integral_norm_sourceLogWindowFourierL2Isometry_sq i (x : H_m i)
      _ = ‖sourceWeilGraphAmbient i xg‖ ^ 2 := by
        rw [sourceWeilGraphDomain_coe]
      _ = ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 := by
        rw [sourceWeilGraphAmbient_oddGraphFinsuppShift]
  have hinsideEq :
      (∫ t in Set.Icc (-T) T, ‖((F : ℝ → ℂ) t)‖ ^ 2) =
        ∫ t in Set.Icc (-T) T,
          ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ 2 := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Icc
    have hAE :=
      coeFn_sourceLogWindowFourierL2Isometry_apply_oddGraphFinsuppShift
        i R c
    filter_upwards [hAE] with t ht
    intro _htBand
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (by simpa [F, x, xg] using ht)
  have hlow :
      (∫ t in Set.Icc (-T) T, ‖((F : ℝ → ℂ) t)‖ ^ 2) ≤
        ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)))) *
          ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 := by
    rw [hinsideEq]
    apply integral_norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand
    · simpa [R] using sourceWeilOddTailCutoff_pos i
    · exact (sourceWeilOddTailBandRadius_pos i).le
    · simpa [R, T] using sourceWeilOddTailCutoff_safeFrequency i
  have hD : 0 ≤ C + A0 := by
    exact add_nonneg (sourceWeilOddTailHighTarget_pos i).le hA0
  have hmulLow := mul_le_mul_of_nonneg_left hlow hD
  have hbudget :
      (C + A0) *
        ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)))) ≤
        1 / 2 := by
    simpa [C, A0, T, R] using sourceWeilOddTailCutoff_lowBandBudget i
  have hbudgetMass := mul_le_mul_of_nonneg_right hbudget
    (sq_nonneg ‖sourceWeilOddAmbientFinsuppShift i R c‖)
  have hshift :
      (C + A0) * ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 -
          (1 / 2) * ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 ≤
        (sourceArchimedeanShiftedSesquilinearForm i x x).re := by
    rw [sourceArchimedeanShiftedSesquilinearForm_re_self_eq_integral_norm_sq]
    rw [htotal] at hweighted
    nlinarith
  have hinner :
      (inner ℂ x x).re =
        ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 := by
    have hxnorm : ‖(x : H_m i)‖ =
        ‖sourceWeilOddAmbientFinsuppShift i R c‖ := by
      calc
        ‖(x : H_m i)‖ = ‖sourceWeilGraphAmbient i xg‖ := by
          rw [sourceWeilGraphDomain_coe]
        _ = ‖sourceWeilOddAmbientFinsuppShift i R c‖ := by
          rw [sourceWeilGraphAmbient_oddGraphFinsuppShift]
    rw [← hxnorm]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [sourceArchimedeanSesquilinearForm_apply]
  simp only [sub_re, mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [hinner]
  change
    (sourceWeilOddTailHighTarget i - 1 / 2) *
        ‖sourceWeilOddAmbientFinsuppShift i
          (sourceWeilOddTailCutoff i) c‖ ^ 2 ≤ _
  dsimp only [C, A0, R, x, xg] at hshift
  nlinarith

/-- After subtracting the bounded Prime form and adding the bounded rank-two
W02 form, the same finite odd-tail synthesis retains the fixed positive
margin `1/2`. -/
theorem sourceWeilSesquilinearForm_re_self_lower_oddGraphFinsuppShift
    (i : PairIndex) (c : ℕ →₀ ℂ) :
    (1 / 2 : ℝ) *
        ‖sourceWeilOddAmbientFinsuppShift i
          (sourceWeilOddTailCutoff i) c‖ ^ 2 ≤
      (sourceWeilSesquilinearForm i
        (sourceWeilGraphDomain i
          (sourceWeilOddGraphFinsuppShift i
            (sourceWeilOddTailCutoff i) c))
        (sourceWeilGraphDomain i
          (sourceWeilOddGraphFinsuppShift i
            (sourceWeilOddTailCutoff i) c))).re := by
  let R : ℕ := sourceWeilOddTailCutoff i
  let xg : SourceWeilGraphCarrier i :=
    sourceWeilOddGraphFinsuppShift i R c
  let x : sourceArchimedeanShiftedFormDomain i :=
    sourceWeilGraphDomain i xg
  let v : H_m i := sourceWeilOddAmbientFinsuppShift i R c
  have hx : (x : H_m i) = v := by
    calc
      (x : H_m i) = sourceWeilGraphAmbient i xg := by
        rw [sourceWeilGraphDomain_coe]
      _ = v := by
        rw [sourceWeilGraphAmbient_oddGraphFinsuppShift]
  have harch :
      (sourceWeilOddTailHighTarget i - 1 / 2) * ‖v‖ ^ 2 ≤
        (sourceArchimedeanSesquilinearForm i x x).re := by
    simpa [R, x, xg, v] using
      sourceArchimedeanSesquilinearForm_re_self_lower_oddGraphFinsuppShift
        i c
  have hwNorm :=
    norm_sourceW02AmbientContinuousSesquilinearForm_apply_le i v v
  have hwLower :
      -(‖sourceW02AmbientContinuousSesquilinearForm i‖ * ‖v‖ ^ 2) ≤
        (sourceW02AmbientContinuousSesquilinearForm i v v).re := by
    have hre :=
      (abs_le.mp
        (Complex.abs_re_le_norm
          (sourceW02AmbientContinuousSesquilinearForm i v v))).1
    have hneg := neg_le_neg hwNorm
    simpa [pow_two, mul_assoc] using hneg.trans hre
  have hpNorm := norm_sourcePrimeSesquilinearForm_apply_le i v v
  have hpUpper :
      (sourcePrimeSesquilinearForm i v v).re ≤
        ‖sourcePrimeContinuousSesquilinearForm i‖ * ‖v‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using
      (Complex.re_le_norm _).trans hpNorm
  change (1 / 2 : ℝ) *
      ‖sourceWeilOddAmbientFinsuppShift i
        (sourceWeilOddTailCutoff i) c‖ ^ 2 ≤ _
  rw [sourceWeilSesquilinearForm_apply,
    sourceArchPrimeSesquilinearForm_apply]
  simp only [add_re, sub_re]
  change (1 / 2 : ℝ) *
      ‖sourceWeilOddAmbientFinsuppShift i
        (sourceWeilOddTailCutoff i) c‖ ^ 2 ≤
    (sourceW02AmbientContinuousSesquilinearForm i (x : H_m i) (x : H_m i)).re +
      ((sourceArchimedeanSesquilinearForm i x x).re -
        (sourcePrimeSesquilinearForm i (x : H_m i) (x : H_m i)).re)
  rw [hx]
  dsimp only [v, R] at harch hwLower hpUpper ⊢
  unfold sourceWeilOddTailHighTarget at harch
  nlinarith

/-- Production algebraic source supplier for B3.0AK: an explicit cutoff and
the fixed coercivity margin `1/2`, proved for every finite combination of the
literal high odd graph modes. -/
theorem sourceWeilOddTailAlgebraicCoercive_explicit (i : PairIndex) :
    SourceWeilOddTailAlgebraicCoercive i
      (sourceWeilOddTailCutoff i) (1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  intro x hx
  rcases (Finsupp.mem_span_range_iff_exists_finsupp.mp hx) with ⟨c, hc⟩
  have hc' :
      sourceWeilOddGraphFinsuppShift i (sourceWeilOddTailCutoff i) c = x := by
    simpa [sourceWeilOddGraphFinsuppShift] using hc
  rw [← hc', sourceWeilGraphAmbient_oddGraphFinsuppShift]
  exact sourceWeilSesquilinearForm_re_self_lower_oddGraphFinsuppShift i c

/-- Full B3.0AK closure: the explicit algebraic estimate passes through the
already-proved graph-topology closure seam to the literal closed odd tail. -/
theorem sourceWeilOddTailAmbientCoercive_explicit (i : PairIndex) :
    SourceWeilOddTailAmbientCoercive i
      (sourceWeilOddTailCutoff i) (1 / 2) :=
  sourceWeilOddTailAmbientCoercive_of_algebraic i
    (sourceWeilOddTailCutoff i) (1 / 2)
    (sourceWeilOddTailAlgebraicCoercive_explicit i)

#print axioms sourceWeilOddTailCutoff_safeFrequency
#print axioms sourceWeilOddTailCutoff_lowBandBudget
#print axioms sourceWeilGraphAmbient_oddGraphFinsuppShift
#print axioms coeFn_sourceLogWindowFourierL2Isometry_apply_oddGraphFinsuppShift
#print axioms integral_norm_sourceLogWindowFourierL2Isometry_sq
#print axioms sourceArchimedeanShiftedSesquilinearForm_re_self_eq_integral_norm_sq
#print axioms integrable_sourceArchimedeanShiftedMultiplier_mul_fourierNorm_sq
#print axioms sourceArchimedeanSesquilinearForm_re_self_lower_oddGraphFinsuppShift
#print axioms sourceWeilSesquilinearForm_re_self_lower_oddGraphFinsuppShift
#print axioms sourceWeilOddTailAlgebraicCoercive_explicit
#print axioms sourceWeilOddTailAmbientCoercive_explicit

end Q3.RouteB.D0Pstar
