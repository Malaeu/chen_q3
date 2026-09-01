import Q3.Proofs.RouteB.D0PstarSourceEvenNonzeroLowBandAssembly
import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailExplicitCoercivity

set_option linter.mathlibStandardSet false
set_option maxRecDepth 2048

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Real FourierTransform

namespace Q3.RouteB.D0Pstar

/-!
# Explicit source-Weil coercivity on the literal nonzero-even tail

The high-frequency argument used for the odd source tail is parity-blind at
the quantitative step: the normalized sum of the two reflected Fourier modes
obeys the same inverse-frequency low-band envelope as their normalized
difference.  This file proves that statement directly, combines it with the
existing source archimedean multiplier bound, absorbs the bounded W02 and
Prime forms, and transports the finite estimate through the exact graph
closure.

The theorem is unshifted.  It does not bound the selected Ferrers Rayleigh
scalar and does not assert a selected-shift floor or a Schur margin.
-/

/-- The parity-independent high target, exposed under an even-tail name. -/
abbrev sourceWeilEvenTailHighTarget (i : PairIndex) : ℝ :=
  sourceWeilOddTailHighTarget i

/-- The parity-independent frequency band, exposed under an even-tail name. -/
abbrev sourceWeilEvenTailBandRadius (i : PairIndex) : ℝ :=
  sourceWeilOddTailBandRadius i

/-- The common explicit cutoff, exposed under an even-tail name. -/
abbrev sourceWeilEvenTailCutoff (i : PairIndex) : ℕ :=
  sourceWeilOddTailCutoff i

/-- Ambient normalized symmetric pair underlying the nonzero-even graph
mode. -/
noncomputable def sourceWeilEvenAmbientMode
    (i : PairIndex) (k : ℕ) : H_m i :=
  sourceWeilGraphAmbient i (sourceWeilGraphEvenNonzeroMode i k)

theorem sourceWeilEvenAmbientMode_orthonormal (i : PairIndex) :
    Orthonormal ℂ (sourceWeilEvenAmbientMode i) := by
  simpa only [sourceWeilEvenAmbientMode] using
    sourceWeilGraphAmbient_evenNonzeroMode_orthonormal i

/-- Pointwise Fourier representative of one normalized nonzero-even mode. -/
noncomputable def sourceWeilEvenFourierModeFunction
    (i : PairIndex) (k : ℕ) (t : ℝ) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
    (𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t +
      𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t)

/-- The whole-line Fourier isometry of one even mode agrees almost everywhere
with the literal normalized sum of the two reflected mode transforms. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientMode
    (i : PairIndex) (k : ℕ) :
    ((sourceLogWindowFourierL2Isometry i (sourceWeilEvenAmbientMode i k) :
        MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ)
      =ᵐ[MeasureTheory.volume]
        sourceWeilEvenFourierModeFunction i k := by
  let c : ℂ := (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
  let A : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i (V_n_m i (k + 1 : ℕ))
  let B : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i
      (V_n_m i (-((k + 1 : ℕ) : ℤ)))
  have hpos :=
    coeFn_sourceLogWindowFourierL2Isometry_apply_mode i ((k + 1 : ℕ) : ℤ)
  have hneg :=
    coeFn_sourceLogWindowFourierL2Isometry_apply_mode i (-((k + 1 : ℕ) : ℤ))
  have hadd := MeasureTheory.Lp.coeFn_add A B
  have hsmul := MeasureTheory.Lp.coeFn_smul c (A + B)
  filter_upwards [hpos, hneg, hadd, hsmul] with t hpt hnt haddt hsmult
  rw [sourceWeilEvenAmbientMode,
    sourceWeilGraphAmbient_evenNonzeroMode, map_smul, map_add]
  change (((c • (A + B) :
      MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t) = _
  rw [hsmult]
  change c * (((A + B :
      MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t) = _
  rw [haddt]
  change c * (((A : ℝ → ℂ) t) + ((B : ℝ → ℂ) t)) = _
  rw [show (A : ℝ → ℂ) t =
      𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t by
        simpa [A] using hpt,
    show (B : ℝ → ℂ) t =
      𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t by
        simpa [B] using hnt]
  rfl

/-- The normalized symmetric pair has the same coarse inverse-frequency
low-band envelope as the antisymmetric pair. -/
theorem norm_sourceWeilEvenAmbientModeFourier_le_lowBand_inv
    (i : PairIndex) (k : ℕ) (T t : ℝ)
    (hT : 0 ≤ T)
    (hk : 2 * L_m i * (T + 1) ≤ (k + 1 : ℝ))
    (ht : |t| ≤ T) :
    ‖sourceWeilEvenFourierModeFunction i k t‖ ≤
      4 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ)) := by
  have hkpos : 0 ≤ (k + 1 : ℝ) := by positivity
  have habsneg :
      |((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)| = (k + 1 : ℝ) := by
    rw [abs_of_nonpos]
    · norm_num
    · exact_mod_cast
        (neg_nonpos.mpr (Int.natCast_nonneg (k + 1)))
  have hpos := norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv
    i ((k + 1 : ℕ) : ℤ) T t hT
      (by simpa [abs_of_nonneg hkpos] using hk) ht
  have hneg := norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv
    i (-((k + 1 : ℕ) : ℤ)) T t hT
      (by rw [habsneg]; exact hk) ht
  have hsqrt_one : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hc : ‖(((Real.sqrt 2 : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact (inv_le_one₀ (Real.sqrt_pos.2 (by norm_num))).2 hsqrt_one
  calc
    ‖sourceWeilEvenFourierModeFunction i k t‖ =
        ‖(((Real.sqrt 2 : ℝ) : ℂ)⁻¹)‖ *
          ‖𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t +
            𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t‖ := by
      rw [sourceWeilEvenFourierModeFunction, norm_mul]
    _ ≤ 1 *
        (‖𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t‖ +
          ‖𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 1 *
        (2 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ)) +
          2 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ))) := by
      gcongr
      · simpa [abs_of_nonneg hkpos] using hpos
      · rw [habsneg] at hneg
        exact hneg
    _ = 4 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ)) := by ring

/-- Literal finite Fourier synthesis of shifted nonzero-even modes. -/
noncomputable def sourceWeilEvenFourierFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (t : ℝ) : ℂ :=
  c.sum fun k z => z * sourceWeilEvenFourierModeFunction i (R + k) t

/-- Ambient synthesis of the same shifted nonzero-even coefficients. -/
noncomputable def sourceWeilEvenAmbientFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) : H_m i :=
  c.sum fun k z => z • sourceWeilEvenAmbientMode i (R + k)

/-- Graph synthesis of the same shifted nonzero-even coefficients. -/
noncomputable def sourceWeilEvenGraphFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    SourceWeilGraphCarrier i :=
  c.sum fun k z => z • sourceWeilGraphEvenNonzeroMode i (R + k)

theorem sourceWeilGraphAmbient_evenGraphFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    sourceWeilGraphAmbient i (sourceWeilEvenGraphFinsuppShift i R c) =
      sourceWeilEvenAmbientFinsuppShift i R c := by
  classical
  unfold sourceWeilEvenGraphFinsuppShift sourceWeilEvenAmbientFinsuppShift
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro k hk
  rw [map_smul]
  rfl

/-- Parseval for a shifted finite even synthesis. -/
theorem norm_sourceWeilEvenAmbientFinsuppShift_sq
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 =
      ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  classical
  have hinj : Function.Injective (fun k : ℕ => R + k) := by
    intro k l hkl
    exact Nat.add_left_cancel hkl
  have horth :
      Orthonormal ℂ (fun k : ℕ => sourceWeilEvenAmbientMode i (R + k)) :=
    (sourceWeilEvenAmbientMode_orthonormal i).comp _ hinj
  have hinner := horth.inner_finsupp_eq_sum_left c c
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change
    (inner ℂ
      (Finsupp.linearCombination ℂ
        (fun k : ℕ => sourceWeilEvenAmbientMode i (R + k)) c)
      (Finsupp.linearCombination ℂ
        (fun k : ℕ => sourceWeilEvenAmbientMode i (R + k)) c)).re = _
  rw [hinner]
  simp only [Finsupp.sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.mul_re]

/-- The Fourier image of a finite even synthesis is its literal finite sum. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    ((sourceLogWindowFourierL2Isometry i
          (sourceWeilEvenAmbientFinsuppShift i R c) :
        MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ)
      =ᵐ[MeasureTheory.volume]
        sourceWeilEvenFourierFinsuppShift i R c := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simpa [sourceWeilEvenAmbientFinsuppShift,
        sourceWeilEvenFourierFinsuppShift] using
        (MeasureTheory.Lp.coeFn_zero ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))
  | single_add k z c hk hz ih =>
      let A : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
        sourceLogWindowFourierL2Isometry i
          (sourceWeilEvenAmbientMode i (R + k))
      let B : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
        sourceLogWindowFourierL2Isometry i
          (sourceWeilEvenAmbientFinsuppShift i R c)
      have hmode :=
        coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientMode i (R + k)
      have hsmul := MeasureTheory.Lp.coeFn_smul z A
      have hadd := MeasureTheory.Lp.coeFn_add (z • A) B
      filter_upwards [hmode, ih, hsmul, hadd] with t hmodet iht hsmult haddt
      have hamb :
          sourceWeilEvenAmbientFinsuppShift i R (Finsupp.single k z + c) =
            z • sourceWeilEvenAmbientMode i (R + k) +
              sourceWeilEvenAmbientFinsuppShift i R c := by
        unfold sourceWeilEvenAmbientFinsuppShift
        rw [Finsupp.sum_add_index']
        · simp
        · intro a
          exact zero_smul ℂ _
        · intro a x y
          exact add_smul x y _
      have hfour :
          sourceWeilEvenFourierFinsuppShift i R
              (Finsupp.single k z + c) t =
            z * sourceWeilEvenFourierModeFunction i (R + k) t +
              sourceWeilEvenFourierFinsuppShift i R c t := by
        unfold sourceWeilEvenFourierFinsuppShift
        rw [Finsupp.sum_add_index']
        · simp
        · intro a
          exact zero_mul _
        · intro a x y
          exact add_mul x y _
      rw [hamb, map_add, map_smul]
      change (((z • A + B :
          MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t) = _
      rw [haddt]
      change (((z • A :
          MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t) +
        ((B : ℝ → ℂ) t) = _
      rw [hsmult]
      change z * ((A : ℝ → ℂ) t) + ((B : ℝ → ℂ) t) = _
      rw [show (A : ℝ → ℂ) t =
          sourceWeilEvenFourierModeFunction i (R + k) t by
            simpa [A] using hmodet,
        show (B : ℝ → ℂ) t =
          sourceWeilEvenFourierFinsuppShift i R c t by
            simpa [B] using iht,
        hfour]

/-- Cauchy--Schwarz bound for the shifted even synthesis. -/
theorem norm_sourceWeilEvenFourierFinsuppShift_sq_le
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (t : ℝ) :
    ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ 2 ≤
      (∑ k ∈ c.support, ‖c k‖ ^ 2) *
        ∑ k ∈ c.support,
          ‖sourceWeilEvenFourierModeFunction i (R + k) t‖ ^ 2 := by
  classical
  have hnorm :
      ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ≤
        ∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilEvenFourierModeFunction i (R + k) t‖ := by
    unfold sourceWeilEvenFourierFinsuppShift
    calc
      ‖c.sum fun k z => z * sourceWeilEvenFourierModeFunction i (R + k) t‖ ≤
          ∑ k ∈ c.support,
            ‖c k * sourceWeilEvenFourierModeFunction i (R + k) t‖ := by
        simpa only [Finsupp.sum, Finset.sum_attach] using
          (norm_sum_le c.support
            (fun k => c k * sourceWeilEvenFourierModeFunction i (R + k) t))
      _ = _ := by simp only [norm_mul]
  have hsum_nonneg :
      0 ≤ ∑ k ∈ c.support,
        ‖c k‖ * ‖sourceWeilEvenFourierModeFunction i (R + k) t‖ := by
    positivity
  have hsq :
      ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ 2 ≤
        (∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilEvenFourierModeFunction i (R + k) t‖) ^ 2 := by
    nlinarith [norm_nonneg (sourceWeilEvenFourierFinsuppShift i R c t)]
  exact hsq.trans
    (Finset.sum_mul_sq_le_sq_mul_sq c.support
      (fun k => ‖c k‖)
      (fun k => ‖sourceWeilEvenFourierModeFunction i (R + k) t‖))

/-- Pointwise low-band mass bound with the inverse-square tail collapsed to
`1/R`. -/
theorem norm_sourceWeilEvenFourierFinsuppShift_sq_le_lowBand
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (T t : ℝ)
    (hR : 0 < R) (hT : 0 ≤ T)
    (hcut : 2 * L_m i * (T + 1) ≤ (R + 1 : ℝ))
    (ht : |t| ≤ T) :
    ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ 2 ≤
      (∑ k ∈ c.support, ‖c k‖ ^ 2) *
        ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ))) := by
  refine (norm_sourceWeilEvenFourierFinsuppShift_sq_le i R c t).trans ?_
  have hcoeff : 0 ≤ ∑ k ∈ c.support, ‖c k‖ ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoeff
  calc
    (∑ k ∈ c.support,
        ‖sourceWeilEvenFourierModeFunction i (R + k) t‖ ^ 2) ≤
        ∑ k ∈ c.support,
          (4 * Real.sqrt (L_m i) /
            (Real.pi * ((R : ℝ) + (k : ℝ) + 1))) ^ 2 := by
      gcongr with k hk
      have hRk :
          2 * L_m i * (T + 1) ≤ (R + k + 1 : ℝ) := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        linarith
      have hmode := norm_sourceWeilEvenAmbientModeFourier_le_lowBand_inv
        i (R + k) T t hT (by simpa [Nat.cast_add] using hRk) ht
      simpa [Nat.cast_add] using hmode
    _ = (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
        (∑ k ∈ c.support,
          1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hden : (R : ℝ) + (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hpi, hden]
    _ ≤ (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_support_inv_nat_shift_sq_le R hR c.support) (sq_nonneg _)

/-- Integrated low-band mass for every finite nonzero-even tail synthesis. -/
theorem integral_norm_sourceWeilEvenFourierFinsuppShift_sq_le_lowBand
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (T : ℝ)
    (hR : 0 < R) (hT : 0 ≤ T)
    (hcut : 2 * L_m i * (T + 1) ≤ (R + 1 : ℝ)) :
    (∫ t in Set.Icc (-T) T,
        ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ 2) ≤
      ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)))) *
        ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 := by
  let A : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i
      (sourceWeilEvenAmbientFinsuppShift i R c)
  have hAint : MeasureTheory.Integrable
      (fun t : ℝ => ‖((A : ℝ → ℂ) t)‖ ^ (2 : ℕ))
      MeasureTheory.volume :=
    (MeasureTheory.Lp.memLp A).integrable_norm_pow (by norm_num)
  have hAE :=
    coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientFinsuppShift i R c
  have hFourierInt : MeasureTheory.Integrable
      (fun t : ℝ =>
        ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ (2 : ℕ))
      MeasureTheory.volume := by
    apply hAint.congr
    simpa [A] using hAE.fun_comp (fun z : ℂ => ‖z‖ ^ (2 : ℕ))
  have hConstInt : MeasureTheory.IntegrableOn
      (fun _ : ℝ =>
        ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ))))
      (Set.Icc (-T) T) := by
    exact MeasureTheory.integrableOn_const
      (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hvol : MeasureTheory.volume.real (Set.Icc (-T) T) = 2 * T := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc
    (∫ t in Set.Icc (-T) T,
        ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ 2) ≤
        ∫ _t in Set.Icc (-T) T,
          ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 *
            ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ))) := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hFourierInt.integrableOn
      · exact hConstInt
      · exact measurableSet_Icc
      · intro t ht
        have hpoint :=
          norm_sourceWeilEvenFourierFinsuppShift_sq_le_lowBand
            i R c T t hR hT hcut (abs_le.mpr ht)
        rw [norm_sourceWeilEvenAmbientFinsuppShift_sq i R c]
        exact hpoint
    _ = (2 * T) *
          (‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 *
            ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)))) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    _ = _ := by ring

/-- The raw archimedean form dominates the parity-independent high target on
every finite shifted nonzero-even synthesis. -/
theorem sourceArchimedeanSesquilinearForm_re_self_lower_evenGraphFinsuppShift
    (i : PairIndex) (c : ℕ →₀ ℂ) :
    (sourceWeilEvenTailHighTarget i - 1 / 2) *
        ‖sourceWeilEvenAmbientFinsuppShift i
          (sourceWeilEvenTailCutoff i) c‖ ^ 2 ≤
      (sourceArchimedeanSesquilinearForm i
        (sourceWeilGraphDomain i
          (sourceWeilEvenGraphFinsuppShift i
            (sourceWeilEvenTailCutoff i) c))
        (sourceWeilGraphDomain i
          (sourceWeilEvenGraphFinsuppShift i
            (sourceWeilEvenTailCutoff i) c))).re := by
  let R : ℕ := sourceWeilEvenTailCutoff i
  let T : ℝ := sourceWeilEvenTailBandRadius i
  let C : ℝ := sourceWeilEvenTailHighTarget i
  let A0 : ℝ := |Real.log Real.pi| + Real.log 4 + 6
  let xg : SourceWeilGraphCarrier i := sourceWeilEvenGraphFinsuppShift i R c
  let x : sourceArchimedeanShiftedFormDomain i := sourceWeilGraphDomain i xg
  let F : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i (x : H_m i)
  have hFint : MeasureTheory.Integrable
      (fun t : ℝ => ‖((F : ℝ → ℂ) t)‖ ^ (2 : ℕ)) :=
    (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hqFint : MeasureTheory.Integrable
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t + A0) * ‖((F : ℝ → ℂ) t)‖ ^ 2) := by
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
      simpa [T, C, sourceWeilEvenTailBandRadius,
        sourceWeilEvenTailHighTarget] using habs
    linarith
  have hweighted :
      (C + A0) *
          ((∫ t : ℝ, ‖((F : ℝ → ℂ) t)‖ ^ 2) -
            ∫ t in Set.Icc (-T) T, ‖((F : ℝ → ℂ) t)‖ ^ 2) ≤
        ∫ t : ℝ,
          (sourceArchimedeanMultiplier t + A0) * ‖((F : ℝ → ℂ) t)‖ ^ 2 := by
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
        ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 := by
    calc
      (∫ t : ℝ, ‖((F : ℝ → ℂ) t)‖ ^ 2) = ‖(x : H_m i)‖ ^ 2 := by
        simpa [F] using integral_norm_sourceLogWindowFourierL2Isometry_sq i (x : H_m i)
      _ = ‖sourceWeilGraphAmbient i xg‖ ^ 2 := by
        rw [sourceWeilGraphDomain_coe]
      _ = ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 := by
        rw [sourceWeilGraphAmbient_evenGraphFinsuppShift]
  have hinsideEq :
      (∫ t in Set.Icc (-T) T, ‖((F : ℝ → ℂ) t)‖ ^ 2) =
        ∫ t in Set.Icc (-T) T,
          ‖sourceWeilEvenFourierFinsuppShift i R c t‖ ^ 2 := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Icc
    have hAE :=
      coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientFinsuppShift i R c
    rw [← sourceWeilGraphAmbient_evenGraphFinsuppShift i R c] at hAE
    filter_upwards [hAE] with t ht
    intro _htBand
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (by simpa [F, x, xg] using ht)
  have hlow :
      (∫ t in Set.Icc (-T) T, ‖((F : ℝ → ℂ) t)‖ ^ 2) ≤
        ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)))) *
          ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 := by
    rw [hinsideEq]
    apply integral_norm_sourceWeilEvenFourierFinsuppShift_sq_le_lowBand
    · simpa [R, sourceWeilEvenTailCutoff] using sourceWeilOddTailCutoff_pos i
    · simpa [T, sourceWeilEvenTailBandRadius] using
        (sourceWeilOddTailBandRadius_pos i).le
    · simpa [R, T, sourceWeilEvenTailCutoff,
        sourceWeilEvenTailBandRadius] using
        sourceWeilOddTailCutoff_safeFrequency i
  have hD : 0 ≤ C + A0 := by
    exact add_nonneg (sourceWeilOddTailHighTarget_pos i).le hA0
  have hmulLow := mul_le_mul_of_nonneg_left hlow hD
  have hbudget :
      (C + A0) *
        ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ)))) ≤
        1 / 2 := by
    simpa [C, A0, T, R, sourceWeilEvenTailHighTarget,
      sourceWeilEvenTailBandRadius, sourceWeilEvenTailCutoff] using
      sourceWeilOddTailCutoff_lowBandBudget i
  have hbudgetMass := mul_le_mul_of_nonneg_right hbudget
    (sq_nonneg ‖sourceWeilEvenAmbientFinsuppShift i R c‖)
  have hshift :
      (C + A0) * ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 -
          (1 / 2) * ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 ≤
        (sourceArchimedeanShiftedSesquilinearForm i x x).re := by
    rw [sourceArchimedeanShiftedSesquilinearForm_re_self_eq_integral_norm_sq]
    rw [htotal] at hweighted
    nlinarith
  have hinner :
      (inner ℂ x x).re = ‖sourceWeilEvenAmbientFinsuppShift i R c‖ ^ 2 := by
    have hxnorm : ‖(x : H_m i)‖ =
        ‖sourceWeilEvenAmbientFinsuppShift i R c‖ := by
      calc
        ‖(x : H_m i)‖ = ‖sourceWeilGraphAmbient i xg‖ := by
          rw [sourceWeilGraphDomain_coe]
        _ = _ := by rw [sourceWeilGraphAmbient_evenGraphFinsuppShift]
    rw [← hxnorm]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [sourceArchimedeanSesquilinearForm_apply]
  simp only [sub_re, mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [hinner]
  dsimp only [C, A0, R, x, xg] at hshift ⊢
  nlinarith

/-- After bounded Prime absorption, the Arch-Prime form alone retains the
W02 norm plus the fixed margin `1/2` on every finite high-even synthesis. -/
theorem sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift
    (i : PairIndex) (c : ℕ →₀ ℂ) :
    (‖sourceW02AmbientContinuousSesquilinearForm i‖ + 1 / 2) *
        ‖sourceWeilEvenAmbientFinsuppShift i
          (sourceWeilEvenTailCutoff i) c‖ ^ 2 ≤
      (sourceArchPrimeSesquilinearForm i
        (sourceWeilGraphDomain i
          (sourceWeilEvenGraphFinsuppShift i
            (sourceWeilEvenTailCutoff i) c))
        (sourceWeilGraphDomain i
          (sourceWeilEvenGraphFinsuppShift i
            (sourceWeilEvenTailCutoff i) c))).re := by
  let R : ℕ := sourceWeilEvenTailCutoff i
  let xg : SourceWeilGraphCarrier i := sourceWeilEvenGraphFinsuppShift i R c
  let x : sourceArchimedeanShiftedFormDomain i := sourceWeilGraphDomain i xg
  let v : H_m i := sourceWeilEvenAmbientFinsuppShift i R c
  have hx : (x : H_m i) = v := by
    calc
      (x : H_m i) = sourceWeilGraphAmbient i xg := by
        rw [sourceWeilGraphDomain_coe]
      _ = v := by rw [sourceWeilGraphAmbient_evenGraphFinsuppShift]
  have harch :
      (sourceWeilEvenTailHighTarget i - 1 / 2) * ‖v‖ ^ 2 ≤
        (sourceArchimedeanSesquilinearForm i x x).re := by
    simpa [R, x, xg, v] using
      sourceArchimedeanSesquilinearForm_re_self_lower_evenGraphFinsuppShift i c
  have hpNorm := norm_sourcePrimeSesquilinearForm_apply_le i v v
  have hpUpper :
      (sourcePrimeSesquilinearForm i v v).re ≤
        ‖sourcePrimeContinuousSesquilinearForm i‖ * ‖v‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using (Complex.re_le_norm _).trans hpNorm
  change (‖sourceW02AmbientContinuousSesquilinearForm i‖ + 1 / 2) *
      ‖sourceWeilEvenAmbientFinsuppShift i
        (sourceWeilEvenTailCutoff i) c‖ ^ 2 ≤ _
  rw [sourceArchPrimeSesquilinearForm_apply]
  simp only [sub_re]
  rw [hx]
  dsimp only [v, R] at harch hpUpper ⊢
  unfold sourceWeilEvenTailHighTarget sourceWeilOddTailHighTarget at harch
  nlinarith

/-- After bounded W02/Prime absorption, every finite high-even synthesis has
the fixed source-Weil margin `1/2`. -/
theorem sourceWeilSesquilinearForm_re_self_lower_evenGraphFinsuppShift
    (i : PairIndex) (c : ℕ →₀ ℂ) :
    (1 / 2 : ℝ) *
        ‖sourceWeilEvenAmbientFinsuppShift i
          (sourceWeilEvenTailCutoff i) c‖ ^ 2 ≤
      (sourceWeilSesquilinearForm i
        (sourceWeilGraphDomain i
          (sourceWeilEvenGraphFinsuppShift i
            (sourceWeilEvenTailCutoff i) c))
        (sourceWeilGraphDomain i
          (sourceWeilEvenGraphFinsuppShift i
            (sourceWeilEvenTailCutoff i) c))).re := by
  let R : ℕ := sourceWeilEvenTailCutoff i
  let xg : SourceWeilGraphCarrier i := sourceWeilEvenGraphFinsuppShift i R c
  let x : sourceArchimedeanShiftedFormDomain i := sourceWeilGraphDomain i xg
  let v : H_m i := sourceWeilEvenAmbientFinsuppShift i R c
  have hx : (x : H_m i) = v := by
    calc
      (x : H_m i) = sourceWeilGraphAmbient i xg := by
        rw [sourceWeilGraphDomain_coe]
      _ = v := by rw [sourceWeilGraphAmbient_evenGraphFinsuppShift]
  have harch :
      (sourceWeilEvenTailHighTarget i - 1 / 2) * ‖v‖ ^ 2 ≤
        (sourceArchimedeanSesquilinearForm i x x).re := by
    simpa [R, x, xg, v] using
      sourceArchimedeanSesquilinearForm_re_self_lower_evenGraphFinsuppShift i c
  have hwNorm := norm_sourceW02AmbientContinuousSesquilinearForm_apply_le i v v
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
    simpa [pow_two, mul_assoc] using (Complex.re_le_norm _).trans hpNorm
  change (1 / 2 : ℝ) *
      ‖sourceWeilEvenAmbientFinsuppShift i
        (sourceWeilEvenTailCutoff i) c‖ ^ 2 ≤ _
  rw [sourceWeilSesquilinearForm_apply, sourceArchPrimeSesquilinearForm_apply]
  simp only [add_re, sub_re]
  change (1 / 2 : ℝ) *
      ‖sourceWeilEvenAmbientFinsuppShift i
        (sourceWeilEvenTailCutoff i) c‖ ^ 2 ≤
    (sourceW02AmbientContinuousSesquilinearForm i (x : H_m i) (x : H_m i)).re +
      ((sourceArchimedeanSesquilinearForm i x x).re -
        (sourcePrimeSesquilinearForm i (x : H_m i) (x : H_m i)).re)
  rw [hx]
  dsimp only [v, R] at harch hwLower hpUpper ⊢
  unfold sourceWeilEvenTailHighTarget sourceWeilOddTailHighTarget at harch
  nlinarith

/-- Algebraic source theorem for the literal high nonzero-even generators. -/
def SourceWeilEvenTailAlgebraicCoercive
    (i : PairIndex) (R : ℕ) (mu : ℝ) : Prop :=
  0 < mu ∧
    ∀ x : SourceWeilGraphCarrier i,
      x ∈ Submodule.span ℂ
          (Set.range (fun k : ℕ => sourceWeilGraphEvenNonzeroMode i (R + k))) →
        mu * ‖sourceWeilGraphAmbient i x‖ ^ 2 ≤
          (sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i x)).re

/-- Closed-tail source theorem for the literal high nonzero-even generators. -/
def SourceWeilEvenTailAmbientCoercive
    (i : PairIndex) (R : ℕ) (mu : ℝ) : Prop :=
  0 < mu ∧
    ∀ x : SourceWeilGraphEvenNonzeroTailCarrier i R,
      mu * ‖sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)‖ ^ 2 ≤
        (sourceWeilSesquilinearForm i
          (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
          (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))).re

theorem sourceWeilEvenTailAlgebraicCoercive_explicit (i : PairIndex) :
    SourceWeilEvenTailAlgebraicCoercive i
      (sourceWeilEvenTailCutoff i) (1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  intro x hx
  rcases (Finsupp.mem_span_range_iff_exists_finsupp.mp hx) with ⟨c, hc⟩
  have hc' : sourceWeilEvenGraphFinsuppShift i
      (sourceWeilEvenTailCutoff i) c = x := by
    simpa [sourceWeilEvenGraphFinsuppShift] using hc
  rw [← hc', sourceWeilGraphAmbient_evenGraphFinsuppShift]
  exact sourceWeilSesquilinearForm_re_self_lower_evenGraphFinsuppShift i c

/-- Explicit unshifted coercivity on the exact closed nonzero-even graph tail. -/
theorem sourceWeilEvenTailAmbientCoercive_explicit (i : PairIndex) :
    SourceWeilEvenTailAmbientCoercive i
      (sourceWeilEvenTailCutoff i) (1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  exact sourceWeilGraphTailAmbientCoercive_of_algebraic i
    (fun k : ℕ => sourceWeilGraphEvenNonzeroMode i
      (sourceWeilEvenTailCutoff i + k)) (1 / 2)
    (sourceWeilEvenTailAlgebraicCoercive_explicit i).2

#print axioms sourceWeilEvenAmbientMode_orthonormal
#print axioms coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientMode
#print axioms norm_sourceWeilEvenAmbientModeFourier_le_lowBand_inv
#print axioms norm_sourceWeilEvenAmbientFinsuppShift_sq
#print axioms integral_norm_sourceWeilEvenFourierFinsuppShift_sq_le_lowBand
#print axioms sourceArchimedeanSesquilinearForm_re_self_lower_evenGraphFinsuppShift
#print axioms sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift
#print axioms sourceWeilSesquilinearForm_re_self_lower_evenGraphFinsuppShift
#print axioms sourceWeilEvenTailAlgebraicCoercive_explicit
#print axioms sourceWeilEvenTailAmbientCoercive_explicit

end Q3.RouteB.D0Pstar
