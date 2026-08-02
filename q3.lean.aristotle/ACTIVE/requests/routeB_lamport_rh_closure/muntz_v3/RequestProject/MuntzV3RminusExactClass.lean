import RequestProject.MuntzV3EstarBoundExactClass
import RequestProject.MellinConvergentSqrtTail

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology BigOperators

namespace EStarMuntzZeroMassContinuation

/-- The locally finite E-star dilation sum is measurable on the exact v3 class.
The finite partial sums converge directly after multiplication by `sqrt u`, including at `u = 0`. -/
theorem Estar_measurable_v3Class
    (h : ℝ → ℂ) (b : ℝ)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0) :
    Measurable (Estar h) := by
  let e : ℕ ≃ ℕ+ := Equiv.pnatEquivNat.symm
  let F : ℕ → ℝ → ℂ := fun N u =>
    Real.sqrt u * ∑ n ∈ Finset.range N, h (((e n : ℕ) : ℝ) * u)
  apply measurable_of_tendsto_metrizable (f := F)
  · intro N
    apply Measurable.mul
    · exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable
    · apply Finset.measurable_sum
      intro n hn
      exact hmeas.comp (measurable_const.mul measurable_id)
  · apply tendsto_pi_nhds.2
    intro u
    by_cases hu : 0 < u
    · have hsummable : Summable (fun n : ℕ+ => h ((n : ℝ) * u)) := by
        let N : ℕ+ := ⟨Nat.ceil (b / u) + 1, Nat.succ_pos _⟩
        apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
        intro n hn
        apply hsupp
        simp only [Set.mem_Icc, not_and_or]
        right
        apply not_le_of_gt
        have hnN : N < n := by
          simp only [Finset.mem_Icc, PNat.one_le, true_and] at hn
          exact lt_of_not_ge hn
        have hceil : b / u ≤ Nat.ceil (b / u) := Nat.le_ceil (b / u)
        have hNn : (Nat.ceil (b / u) : ℝ) < (n : ℝ) := by
          have : Nat.ceil (b / u) + 1 ≤ (n : ℕ) := by exact_mod_cast hnN.le
          exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self _) this
        have hdiv : b / u < (n : ℝ) := lt_of_le_of_lt hceil hNn
        exact (div_lt_iff₀ hu).1 hdiv
      have hsum_tendsto :
          Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
            h (((e n : ℕ) : ℝ) * u)) atTop
            (𝓝 (∑' n : ℕ+, h ((n : ℝ) * u))) := by
        exact ((Equiv.hasSum_iff e).2 hsummable.hasSum).tendsto_sum_nat
      simpa only [F, Estar] using
        (tendsto_const_nhds.mul hsum_tendsto)
    · have hsqrt : Real.sqrt u = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hu)
      simp [F, Estar, hsqrt]

/-- Away from zero, the exact measurable/Icc-zero/Ico-Lipschitz v3 class makes E-star
locally integrable. Endpoint jumps at `b` are handled by a separate endpoint bound. -/
theorem Estar_locallyIntegrableOn_Ioi_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b)) :
    LocallyIntegrableOn (Estar h) (Set.Ioi 0) := by
  rw [locallyIntegrableOn_iff isLocallyClosed_Ioi]
  intro k hk hcompact
  by_cases hkempty : k = ∅
  · subst k
    exact integrableOn_empty
  have hkne : k.Nonempty := Set.nonempty_iff_ne_empty.mpr hkempty
  obtain ⟨c, hcpos, hc⟩ := hcompact.exists_forall_le'
    continuous_id.continuousOn (fun u hu => hk hu)
  obtain ⟨d, hdk, hd⟩ := hcompact.exists_isMaxOn hkne continuous_id.continuousOn
  have hd0 : 0 ≤ d := (hk hdk).le
  let N : ℕ+ := ⟨Nat.ceil (b / c) + 1, Nat.succ_pos _⟩
  let S : Finset ℕ+ := Finset.Icc 1 N
  have htail :
      ∀ u ∈ k, ∀ n : ℕ+, n ∉ S → h ((n : ℝ) * u) = 0 := by
    intro u hu n hn
    apply hsupp
    simp only [Set.mem_Icc, not_and_or]
    right
    apply not_le_of_gt
    have hnN : N < n := by
      simp only [S, Finset.mem_Icc, PNat.one_le, true_and] at hn
      exact lt_of_not_ge hn
    have hceil : b / c ≤ Nat.ceil (b / c) := Nat.le_ceil (b / c)
    have hNn : (Nat.ceil (b / c) : ℝ) < (n : ℝ) := by
      have : Nat.ceil (b / c) + 1 ≤ (n : ℕ) := by exact_mod_cast hnN.le
      exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self _) this
    have hdiv : b / c < (n : ℝ) := lt_of_le_of_lt hceil hNn
    have hnc : b < (n : ℝ) * c := (div_lt_iff₀ hcpos).1 hdiv
    have hcu : c ≤ u := hc u hu
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hsum :
      ∀ u ∈ k,
        (∑' n : ℕ+, h ((n : ℝ) * u)) = ∑ n ∈ S, h ((n : ℝ) * u) := by
    intro u hu
    exact tsum_eq_sum fun n hn => htail u hu n hn
  let C : ℝ := max (‖h 0‖ + (K : ℝ) * b) ‖h b‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound_Icc : ∀ v ∈ Set.Icc (0 : ℝ) b, ‖h v‖ ≤ C := by
    intro v hv
    by_cases hvb : v = b
    · subst v
      exact le_max_right _ _
    · have hvIco : v ∈ Set.Ico (0 : ℝ) b :=
        ⟨hv.1, lt_of_le_of_ne hv.2 hvb⟩
      have hdist := hlip.dist_le_mul v hvIco 0
        ⟨le_rfl, lt_of_le_of_lt hv.1 hvIco.2⟩
      apply le_trans ?_ (le_max_left _ _)
      calc
        ‖h v‖ ≤ dist (h v) (h 0) + ‖h 0‖ := by
          rw [dist_eq_norm]
          exact norm_le_norm_sub_add _ _
        _ ≤ (K : ℝ) * dist v 0 + ‖h 0‖ := by gcongr
        _ ≤ (K : ℝ) * b + ‖h 0‖ := by
          gcongr
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hv.1]
          exact hv.2
        _ = ‖h 0‖ + (K : ℝ) * b := by ring
  let D : ℝ := Real.sqrt d * ((S.card : ℝ) * C)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hbound : ∀ u ∈ k, ‖Estar h u‖ ≤ D := by
    intro u hu
    have hu0 : 0 < u := hk hu
    have hud : u ≤ d := hd hu
    have hsqrt : Real.sqrt u ≤ Real.sqrt d := Real.sqrt_le_sqrt hud
    have hsum_bound :
        ‖∑ n ∈ S, h ((n : ℝ) * u)‖ ≤ (S.card : ℝ) * C := by
      calc
        ‖∑ n ∈ S, h ((n : ℝ) * u)‖
            ≤ ∑ n ∈ S, ‖h ((n : ℝ) * u)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ S, C := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hnu : (n : ℝ) * u ∈ Set.Icc (0 : ℝ) b
          · exact hbound_Icc ((n : ℝ) * u) hnu
          · simpa [hsupp ((n : ℝ) * u) hnu] using hC
        _ = (S.card : ℝ) * C := by simp
    rw [Estar, hsum u hu]
    calc
      ‖(Real.sqrt u : ℂ) * ∑ n ∈ S, h ((n : ℝ) * u)‖ =
          Real.sqrt u * ‖∑ n ∈ S, h ((n : ℝ) * u)‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u)]
      _ ≤ Real.sqrt u * ((S.card : ℝ) * C) :=
        mul_le_mul_of_nonneg_left hsum_bound (Real.sqrt_nonneg u)
      _ ≤ D := by
        exact mul_le_mul_of_nonneg_right hsqrt
          (mul_nonneg (Nat.cast_nonneg _) hC)
  apply Measure.integrableOn_of_bounded hcompact.measure_ne_top
    (Estar_measurable_v3Class h b hmeas hsupp).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hcompact.measurableSet] with u hu
  exact hbound u hu

/-- Exact-class compact support forces E-star to vanish to the right of `b`. -/
theorem Estar_eq_zero_of_gt_v3Class
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0) :
    ∀ u, b < u → Estar h u = 0 := by
  intro u hu
  have hu0 : 0 < u := lt_of_le_of_lt hb hu
  have hterms : ∀ n : ℕ+, h ((n : ℝ) * u) = 0 := by
    intro n
    apply hsupp
    simp only [Set.mem_Icc, not_and_or]
    right
    apply not_le_of_gt
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.prop
    nlinarith
  simp [Estar, hterms]

/-- The zero-mass left tail is holomorphic on the shifted half-plane under the exact v3 class. -/
theorem rminus_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane := by
  let C : ℝ :=
    (K : ℝ) * b + (‖h 0‖ + (K : ℝ) * b) + ‖h b‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsqrt :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, ‖Estar h u‖ ≤ C * Real.sqrt u := by
    simpa only [C] using
      EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
        h b K hb hmeas hsupp hlip hmass
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let f : ℝ → ℂ := Set.Ioo (0 : ℝ) (Λ⁻¹) |>.indicator (Estar h)
  have hfmeas : Measurable f :=
    (Estar_measurable_v3Class h b hmeas hsupp).indicator measurableSet_Ioo
  have hlocal0 :=
    Estar_locallyIntegrableOn_Ioi_v3Class h b K hb hmeas hsupp hlip
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    apply hlocal0.mono hfmeas.aestronglyMeasurable
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    split_ifs <;> simp
  have htop : ∀ A : ℝ, f =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop (Λ⁻¹)] with x hx
      symm
      simp [f, (by linarith : ¬ x < Λ⁻¹)]
    · rfl
  have hbot :
      f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(-(1 : ℝ) / 2))) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (show 0 < (1 : ℝ) by norm_num))]
      with u hu hu1
    have hu0 : 0 < u := hu
    have hsqrt_u := hsqrt u ⟨hu0, hu1⟩
    simp only [f, Set.indicator_apply]
    by_cases hui : u ∈ Set.Ioo (0 : ℝ) (Λ⁻¹)
    · rw [if_pos hui]
      rw [Real.sqrt_eq_rpow] at hsqrt_u
      have hexp : (1 / 2 : ℝ) = -(-(1 : ℝ) / 2) := by norm_num
      rw [hexp] at hsqrt_u
      have hrpow_nonneg : 0 ≤ u ^ (-(-(1 : ℝ) / 2)) :=
        Real.rpow_nonneg hu0.le _
      rw [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg]
      exact hsqrt_u
    · rw [if_neg hui, norm_zero]
      positivity
  have heq : Rminus h Λ = mellin f := by
    funext s
    unfold Rminus mellin
    rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) (Λ⁻¹)
    · simp [hu, hu.1, smul_eq_mul, mul_comm]
    · by_cases hu0 : 0 < u
      · simp [hu, hu0]
      · simp [hu, hu0]
  have hdiff : DifferentiableOn ℂ (Rminus h Λ) shiftedHalfPlane := by
    intro s hs
    have hs' : (-1 : ℝ) / 2 < s.re := by
      change -(1 / 2 : ℝ) < s.re at hs
      norm_num at hs ⊢
      exact hs
    rw [heq]
    exact (mellin_differentiableAt_of_isBigO_rpow hlocal
      (htop (s.re + 1)) (by linarith) hbot hs').differentiableWithinAt
  exact hdiff.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Thin local assembly of the exact-class E-star Mellin convergence theorem. -/
theorem mellinConvergent_Estar_of_zeroMass_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (s : ℂ) (hs : (-1 : ℝ) / 2 < s.re) :
    MellinConvergent (Estar h) s := by
  let C : ℝ :=
    (K : ℝ) * b + (‖h 0‖ + (K : ℝ) * b) + ‖h b‖
  apply mellinConvergent_of_sqrtBound_eventuallyZero (Estar h)
    (Estar_locallyIntegrableOn_Ioi_v3Class h b K hb hmeas hsupp hlip)
    C b
  · simpa only [C] using
      EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
        h b K hb hmeas hsupp hlip hmass
  · exact Estar_eq_zero_of_gt_v3Class h b hb hsupp
  · exact hs

#print axioms Estar_measurable_v3Class
#print axioms Estar_locallyIntegrableOn_Ioi_v3Class
#print axioms Estar_eq_zero_of_gt_v3Class
#print axioms rminus_analyticOnNhd_shiftedHalfPlane_v3Class
#print axioms mellinConvergent_Estar_of_zeroMass_IccZero_IcoLipschitz

end EStarMuntzZeroMassContinuation
