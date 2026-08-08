import Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
import Q3.Proofs.RouteB.D0PstarSourceArchDiagonalRegularizerEndpointLedger

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

private theorem logWindowZeroExtendedMode_integrable_for_e4b2
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

private theorem fourier_logWindowZeroExtendedMode_memLp_two_for_e4b2
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · exact (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop)
      (logWindowZeroExtendedMode_integrable_for_e4b2 i n)).aestronglyMeasurable
  · filter_upwards [] with t
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) henv)]
    nlinarith [norm_nonneg (𝓕 (logWindowZeroExtendedMode i n) t)]

private theorem conj_fourier_logWindowZeroExtendedMode_memLp_two_for_e4b2
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => conj (𝓕 (logWindowZeroExtendedMode i n) t))
      2 volume := by
  have hleft := fourier_logWindowZeroExtendedMode_memLp_two_for_e4b2 i n
  refine hleft.congr_norm ?_ ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable hleft.1
  · filter_upwards [] with t
    exact (norm_conj _).symm

private def diagonalBareModeProduct
    (i : PairIndex) (n : ℤ) (t : ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) t) *
    𝓕 (logWindowZeroExtendedMode i n) t

private theorem diagonalBareModeProduct_integrable
    (i : PairIndex) (n : ℤ) :
    Integrable (diagonalBareModeProduct i n) := by
  have hn := conj_fourier_logWindowZeroExtendedMode_memLp_two_for_e4b2 i n
  have hr := fourier_logWindowZeroExtendedMode_memLp_two_for_e4b2 i n
  simpa only [diagonalBareModeProduct, Pi.mul_apply] using hn.integrable_mul hr

private def diagonalCosineModeProduct
    (i : PairIndex) (n : ℤ) (x t : ℝ) : ℂ :=
  (Real.cos (2 * Real.pi * t * x) : ℂ) *
    diagonalBareModeProduct i n t

private theorem diagonalCosineModeProduct_integrable
    (i : PairIndex) (n : ℤ) (x : ℝ) :
    Integrable (diagonalCosineModeProduct i n x) := by
  have hbare := diagonalBareModeProduct_integrable i n
  refine hbare.bdd_mul (c := 1) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun t : ℝ => (Real.cos (2 * Real.pi * t * x) : ℂ))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

private theorem diagonalBareModeProduct_integral_one
    (i : PairIndex) (n : ℤ) :
    ∫ t : ℝ, diagonalBareModeProduct i n t = 1 := by
  have htwo := sourceModeCosineCorrelation_control_diag_zero i n
  have htwo' :
      (2 : ℂ) * ∫ t : ℝ, diagonalBareModeProduct i n t = 2 := by
    simpa [diagonalCosineModeProduct, diagonalBareModeProduct,
      mul_comm, mul_left_comm, mul_assoc] using htwo
  apply (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0))
  simpa using htwo'

private theorem diagonalSourceKernelModeFiber_eq_cosine_sub_bare
    (i : PairIndex) (n : ℤ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    sourceArchimedeanKernelModeIntegrand i n n (t, x) =
      (((Real.exp (x / 2) /
          (Real.exp x - Real.exp (-x)) : ℝ) : ℂ) *
        diagonalCosineModeProduct i n x t) -
      (((Real.exp (-x) /
          (Real.exp x - Real.exp (-x)) : ℝ) : ℂ) *
        diagonalBareModeProduct i n t) := by
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    have heq : Real.exp x = Real.exp (-x) := sub_eq_zero.mp h
    have hxneg : x = -x := Real.exp_injective heq
    linarith
  unfold sourceArchimedeanKernelModeIntegrand
  unfold sourceArchimedeanRegularizedKernel diagonalCosineModeProduct
    diagonalBareModeProduct
  push_cast
  field_simp [hden]

private noncomputable def diagonalFiniteRegularizer (x : ℝ) : ℝ :=
  2 * (1 - Real.exp (-x)) /
    (Real.exp x - Real.exp (-x))

private noncomputable def diagonalTailRegularizer (x : ℝ) : ℝ :=
  2 * Real.exp (-x) /
    (Real.exp x - Real.exp (-x))

private noncomputable def diagonalFiberLedger
    (i : PairIndex) (n : ℤ) (x : ℝ) : ℂ :=
  if x ≤ L_m i then
    (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ) +
      (diagonalFiniteRegularizer x : ℂ)
  else
    -(diagonalTailRegularizer x : ℂ)

private theorem two_mul_diagonalSourceKernelModeFiber_integral_eq_ledger
    (i : PairIndex) (n : ℤ) {x : ℝ} (hx : 0 < x) :
    2 * ∫ t : ℝ,
        sourceArchimedeanKernelModeIntegrand i n n (t, x) =
      diagonalFiberLedger i n x := by
  let a : ℂ :=
    ((Real.exp (x / 2) /
      (Real.exp x - Real.exp (-x)) : ℝ) : ℂ)
  let b : ℂ :=
    ((Real.exp (-x) /
      (Real.exp x - Real.exp (-x)) : ℝ) : ℂ)
  have hcos := diagonalCosineModeProduct_integrable i n x
  have hbare := diagonalBareModeProduct_integrable i n
  have hfiber :
      (∫ t : ℝ,
          sourceArchimedeanKernelModeIntegrand i n n (t, x)) =
        a * (∫ t : ℝ, diagonalCosineModeProduct i n x t) -
          b * (∫ t : ℝ, diagonalBareModeProduct i n t) := by
    rw [show (fun t : ℝ =>
        sourceArchimedeanKernelModeIntegrand i n n (t, x)) =
      (fun t : ℝ =>
        a * diagonalCosineModeProduct i n x t -
          b * diagonalBareModeProduct i n t) by
        funext t
        exact diagonalSourceKernelModeFiber_eq_cosine_sub_bare i n hx t]
    rw [integral_sub (hcos.const_mul a) (hbare.const_mul b),
      integral_const_mul, integral_const_mul]
  have hbareOne := diagonalBareModeProduct_integral_one i n
  have hcorr :=
    two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
      i n n x hx.le
  have hcorr' :
      2 * ∫ t : ℝ, diagonalCosineModeProduct i n x t =
        if x ≤ L_m i then
          (Q3.RouteB.ccmQKernel (L_m i) n n x : ℂ)
        else
          0 := by
    simpa [diagonalCosineModeProduct, diagonalBareModeProduct,
      mul_comm, mul_left_comm, mul_assoc] using hcorr
  rw [hfiber, hbareOne]
  by_cases hxL : x ≤ L_m i
  · rw [if_pos hxL] at hcorr'
    rw [diagonalFiberLedger, if_pos hxL]
    unfold Q3.RouteB.ccmWRIntegrand diagonalFiniteRegularizer
    have hqZero : Q3.RouteB.ccmQKernel (L_m i) n n 0 = 2 := by
      simp [Q3.RouteB.ccmQKernel, (logLength_pos i).ne']
    rw [hqZero]
    dsimp [a, b]
    push_cast
    rw [← hcorr']
    ring
  · rw [if_neg hxL] at hcorr'
    have hcosZero :
        (∫ t : ℝ, diagonalCosineModeProduct i n x t) = 0 :=
      (mul_eq_zero.mp hcorr').resolve_left (by norm_num)
    rw [diagonalFiberLedger, if_neg hxL, hcosZero, mul_zero]
    unfold diagonalTailRegularizer
    dsimp [a, b]
    push_cast
    ring

private theorem diagonalFiniteRegularizer_eq
    (x : ℝ) (hx : 0 < x) :
    diagonalFiniteRegularizer x = 2 / (Real.exp x + 1) := by
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hexp_ne : Real.exp x ≠ 0 := ne_of_gt hexp_pos
  have hexp_one : Real.exp x ≠ 1 :=
    ne_of_gt ((Real.one_lt_exp_iff).2 hx)
  have hden_left : Real.exp x - Real.exp (-x) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.2 (by linarith)))
  have hden_right : Real.exp x + 1 ≠ 0 :=
    ne_of_gt (add_pos hexp_pos zero_lt_one)
  unfold diagonalFiniteRegularizer
  apply (div_eq_div_iff hden_left hden_right).2
  rw [Real.exp_neg]
  field_simp [hexp_ne, hexp_one]
  ring

private theorem diagonalFiniteRegularizer_integrableOn
    (L : ℝ) :
    IntegrableOn diagonalFiniteRegularizer (Ioc 0 L) := by
  have hcont : Continuous (fun x : ℝ => 2 / (Real.exp x + 1)) :=
    continuous_const.div
      (Real.continuous_exp.add continuous_const)
      (fun x => ne_of_gt (add_pos (Real.exp_pos x) zero_lt_one))
  have hbase : IntegrableOn (fun x : ℝ => 2 / (Real.exp x + 1))
      (Ioc 0 L) :=
    (hcont.integrableOn_Icc (a := 0) (b := L)).mono_set
      Set.Ioc_subset_Icc_self
  exact hbase.congr_fun
    (fun x hx => (diagonalFiniteRegularizer_eq x hx.1).symm)
    measurableSet_Ioc

private theorem diagonalFiberLedger_integrable
    (i : PairIndex) (n : ℤ) :
    Integrable (diagonalFiberLedger i n)
      (volume.restrict (Ioi 0)) := by
  have hjoint := sourceArchimedeanKernelModeIntegrand_integrable i n n
  have hfiber : Integrable (fun x : ℝ => ∫ t : ℝ,
      sourceArchimedeanKernelModeIntegrand i n n (t, x))
      (volume.restrict (Ioi 0)) := hjoint.integral_prod_right
  refine (hfiber.const_mul (2 : ℂ)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact two_mul_diagonalSourceKernelModeFiber_integral_eq_ledger i n hx

private theorem integral_diagonalFiberLedger_eq_split
    (i : PairIndex) (n : ℤ) :
    (∫ x in Ioi 0, diagonalFiberLedger i n x) =
      (∫ x in Ioc 0 (L_m i),
        (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ)) +
      (∫ x in Ioc 0 (L_m i), (diagonalFiniteRegularizer x : ℂ)) -
      (∫ x in Ioi (L_m i), (diagonalTailRegularizer x : ℂ)) := by
  have hL := logLength_pos i
  have hledger : IntegrableOn (diagonalFiberLedger i n) (Ioi 0) :=
    diagonalFiberLedger_integrable i n
  have hleft : IntegrableOn (diagonalFiberLedger i n) (Ioc 0 (L_m i)) :=
    hledger.mono_set (by
      intro x hx
      exact hx.1)
  have hright : IntegrableOn (diagonalFiberLedger i n) (Ioi (L_m i)) :=
    hledger.mono_set (by
      intro x hx
      exact hL.trans hx)
  have hsplit :
      (∫ x in Ioi 0, diagonalFiberLedger i n x) =
        (∫ x in Ioc 0 (L_m i), diagonalFiberLedger i n x) +
        ∫ x in Ioi (L_m i), diagonalFiberLedger i n x := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hleft hright, Ioc_union_Ioi_eq_Ioi hL.le]
  have hleftEq :
      (∫ x in Ioc 0 (L_m i), diagonalFiberLedger i n x) =
        ∫ x in Ioc 0 (L_m i),
          (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ) +
            (diagonalFiniteRegularizer x : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp [diagonalFiberLedger, hx.2]
  have hrightEq :
      (∫ x in Ioi (L_m i), diagonalFiberLedger i n x) =
        ∫ x in Ioi (L_m i), -(diagonalTailRegularizer x : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : L_m i < x := hx
    simp [diagonalFiberLedger, not_le_of_gt hx']
  have hsum : IntegrableOn
      (fun x : ℝ =>
        (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ) +
          (diagonalFiniteRegularizer x : ℂ))
      (Ioc 0 (L_m i)) := by
    exact hleft.congr_fun (fun x hx => by
      simp [diagonalFiberLedger, hx.2]) measurableSet_Ioc
  have hfiniteReal := diagonalFiniteRegularizer_integrableOn (L_m i)
  have hfinite : IntegrableOn
      (fun x : ℝ => (diagonalFiniteRegularizer x : ℂ))
      (Ioc 0 (L_m i)) := hfiniteReal.ofReal
  have hccm : IntegrableOn
      (fun x : ℝ => (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ))
      (Ioc 0 (L_m i)) := by
    have h := hsum.sub hfinite
    change Integrable
      (fun x : ℝ => (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ))
      (volume.restrict (Ioc 0 (L_m i)))
    convert h using 1
    funext x
    simp only [Pi.sub_apply, add_sub_cancel_right]
  have hnegTail : IntegrableOn
      (fun x : ℝ => -(diagonalTailRegularizer x : ℂ))
      (Ioi (L_m i)) := by
    exact hright.congr_fun (fun x hx => by
      have hx' : L_m i < x := hx
      simp [diagonalFiberLedger, not_le_of_gt hx']) measurableSet_Ioi
  have htail : IntegrableOn
      (fun x : ℝ => (diagonalTailRegularizer x : ℂ))
      (Ioi (L_m i)) := by
    change Integrable
      (fun x : ℝ => (diagonalTailRegularizer x : ℂ))
      (volume.restrict (Ioi (L_m i)))
    convert hnegTail.neg using 1
    funext x
    simp
  rw [hsplit, hleftEq, hrightEq, integral_add hccm hfinite]
  have hnegIntegral :
      (∫ x in Ioi (L_m i), -(diagonalTailRegularizer x : ℂ)) =
        -(∫ x in Ioi (L_m i), (diagonalTailRegularizer x : ℂ)) := by
    rw [integral_neg]
  rw [hnegIntegral]
  ring

private theorem sourceArchimedeanModePairing_eq_constant_sub_two_integral_fibers_diag
    (i : PairIndex) (n : ℤ) :
    sourceArchimedeanModePairing i n n =
      ((-Real.log Real.pi - Real.eulerMascheroniConstant : ℝ) : ℂ) -
        2 * ∫ x in Ioi 0, ∫ t : ℝ,
          sourceArchimedeanKernelModeIntegrand i n n (t, x) := by
  let c : ℂ :=
    ((-Real.log Real.pi - Real.eulerMascheroniConstant : ℝ) : ℂ)
  have hbare := diagonalBareModeProduct_integrable i n
  have hbareOne := diagonalBareModeProduct_integral_one i n
  have hjoint := sourceArchimedeanKernelModeIntegrand_integrable i n n
  have hinner : Integrable (fun t : ℝ => ∫ x in Ioi 0,
      sourceArchimedeanKernelModeIntegrand i n n (t, x)) :=
    hjoint.integral_prod_left
  have hswap :
      (∫ t : ℝ, ∫ x in Ioi 0,
          sourceArchimedeanKernelModeIntegrand i n n (t, x)) =
        ∫ x in Ioi 0, ∫ t : ℝ,
          sourceArchimedeanKernelModeIntegrand i n n (t, x) := by
    have hjoint' : Integrable
        (Function.uncurry (fun t x =>
          sourceArchimedeanKernelModeIntegrand i n n (t, x)))
        (volume.prod (volume.restrict (Ioi 0))) := by
      simpa [Function.uncurry] using hjoint
    simpa using (MeasureTheory.integral_integral_swap hjoint')
  have hpoint :
      (fun t : ℝ =>
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t) =
      (fun t : ℝ =>
        c * diagonalBareModeProduct i n t -
          2 * (∫ x in Ioi 0,
            sourceArchimedeanKernelModeIntegrand i n n (t, x))) := by
    funext t
    have hpull :
        (∫ x in Ioi 0,
          sourceArchimedeanKernelModeIntegrand i n n (t, x)) =
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (∫ x in Ioi 0,
              (sourceArchimedeanRegularizedKernel t x : ℂ)) *
            𝓕 (logWindowZeroExtendedMode i n) t := by
      unfold sourceArchimedeanKernelModeIntegrand
      calc
        (∫ x in Ioi 0,
            conj (𝓕 (logWindowZeroExtendedMode i n) t) *
                (sourceArchimedeanRegularizedKernel t x : ℂ) *
              𝓕 (logWindowZeroExtendedMode i n) t) =
            ∫ x in Ioi 0,
              conj (𝓕 (logWindowZeroExtendedMode i n) t) *
                ((sourceArchimedeanRegularizedKernel t x : ℂ) *
                  𝓕 (logWindowZeroExtendedMode i n) t) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x _
              ring
        _ = conj (𝓕 (logWindowZeroExtendedMode i n) t) *
              (∫ x in Ioi 0,
                (sourceArchimedeanRegularizedKernel t x : ℂ) *
                  𝓕 (logWindowZeroExtendedMode i n) t) := by
              rw [integral_const_mul]
        _ = conj (𝓕 (logWindowZeroExtendedMode i n) t) *
              ((∫ x in Ioi 0,
                (sourceArchimedeanRegularizedKernel t x : ℂ)) *
                  𝓕 (logWindowZeroExtendedMode i n) t) := by
              rw [integral_mul_const]
        _ = _ := by ring
    rw [integral_complex_ofReal] at hpull
    rw [sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral,
      hpull]
    dsimp [c]
    push_cast
    unfold diagonalBareModeProduct
    ring
  unfold sourceArchimedeanModePairing
  rw [hpoint]
  rw [integral_sub (hbare.const_mul c) (hinner.const_mul 2),
    integral_const_mul, integral_const_mul, hbareOne, mul_one, hswap]

theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
    (i : PairIndex) (n : ℤ) :
    sourceArchimedeanModePairing i n n =
      -(Q3.RouteB.ccmWREntry (L_m i) n n : ℂ) := by
  rw [sourceArchimedeanModePairing_eq_constant_sub_two_integral_fibers_diag]
  have hL := logLength_pos i
  have hqZero : Q3.RouteB.ccmQKernel (L_m i) n n 0 = 2 := by
    simp [Q3.RouteB.ccmQKernel, hL.ne']
  have hsplit := integral_diagonalFiberLedger_eq_split i n
  have hendpointReal :=
    sourceArchimedeanDiagonalRegularizer_endpointLedger (L_m i) hL
  have hendpointComplex :=
    congrArg (fun z : ℝ => (z : ℂ)) hendpointReal
  change
    (((-Real.log Real.pi -
          ∫ x in Ioc 0 (L_m i), diagonalFiniteRegularizer x) +
        ∫ x in Ioi (L_m i), diagonalTailRegularizer x : ℝ) : ℂ) =
      ((-Real.log
        (4 * Real.pi *
          ((Real.exp (L_m i) - 1) / (Real.exp (L_m i) + 1))) : ℝ) : ℂ)
    at hendpointComplex
  push_cast at hendpointComplex
  calc
    ((-Real.log Real.pi - Real.eulerMascheroniConstant : ℝ) : ℂ) -
          2 * (∫ x in Ioi 0, ∫ t : ℝ,
            sourceArchimedeanKernelModeIntegrand i n n (t, x)) =
        ((-Real.log Real.pi - Real.eulerMascheroniConstant : ℝ) : ℂ) -
          (∫ x in Ioi 0, diagonalFiberLedger i n x) := by
      rw [← integral_const_mul]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact two_mul_diagonalSourceKernelModeFiber_integral_eq_ledger i n hx
    _ = ((-Real.log Real.pi - Real.eulerMascheroniConstant : ℝ) : ℂ) -
          ((∫ x in Ioc 0 (L_m i),
              (Q3.RouteB.ccmWRIntegrand (L_m i) n n x : ℂ)) +
            (∫ x in Ioc 0 (L_m i),
              (diagonalFiniteRegularizer x : ℂ)) -
            (∫ x in Ioi (L_m i),
              (diagonalTailRegularizer x : ℂ))) := by
      rw [hsplit]
    _ = -(Q3.RouteB.ccmWREntry (L_m i) n n : ℂ) := by
      unfold Q3.RouteB.ccmWREntry
      rw [hqZero, integral_complex_ofReal]
      norm_num only [ofReal_ofNat, ofReal_add, ofReal_mul, ofReal_div,
        Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0), one_mul]
      rw [integral_complex_ofReal, integral_complex_ofReal]
      push_cast
      linear_combination hendpointComplex

end Q3.RouteB.D0Pstar
