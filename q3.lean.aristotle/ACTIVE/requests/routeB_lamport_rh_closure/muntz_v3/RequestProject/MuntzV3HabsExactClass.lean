import RequestProject.MuntzV3EStarMellinAbsolutePayload
import RequestProject.MuntzV3RminusExactClass

open scoped BigOperators Topology ENNReal
open Set Filter MeasureTheory Complex

namespace EStarMuntzZeroMassContinuation

private noncomputable def eStarCoreV3 (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, h (((n : ℕ) : ℝ) * u)

private def sourceWindowV3 (Λ : ℝ) : Set ℝ :=
  Set.Icc Λ⁻¹ Λ

private noncomputable def windowedMellinV3
    (Λ : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin ((sourceWindowV3 Λ).indicator f) s

private noncomputable def lowerMellinTailV3
    (Λ : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin ((Set.Iio Λ⁻¹).indicator f) s

private noncomputable def upperMellinTailV3
    (Λ : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin ((Set.Ioi Λ).indicator f) s

private theorem Estar_eq_cpow_smul_eStarCoreV3
    {h : ℝ → ℂ} {u : ℝ} (hu : 0 < u) :
    Estar h u =
      (u : ℂ) ^ ((1 : ℂ) / 2) • eStarCoreV3 h u := by
  unfold Estar eStarCoreV3
  simp only [smul_eq_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
  norm_num

private theorem mellin_Estar_eq_shifted_coreV3 (h : ℝ → ℂ) (s : ℂ) :
    mellin (Estar h) s = mellin (eStarCoreV3 h) (s + 1 / 2) := by
  calc
    mellin (Estar h) s =
        mellin
          (fun u : ℝ =>
            (u : ℂ) ^ ((1 : ℂ) / 2) • eStarCoreV3 h u) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [Estar_eq_cpow_smul_eStarCoreV3 hu]
    _ = mellin (eStarCoreV3 h) (s + 1 / 2) := by
      rw [mellin_cpow_smul]

private theorem mellin_eStarCoreV3_eq_tsum
    {h : ℝ → ℂ} {p : ℂ}
    (habs :
      (∀ n : ℕ+,
        AEStronglyMeasurable
          (fun u : ℝ =>
            (u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u))
          (volume.restrict (Set.Ioi 0))) ∧
      (∑' n : ℕ+,
        ∫⁻ u : ℝ,
          ‖(u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u)‖ₑ
          ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤) :
    mellin (eStarCoreV3 h) p =
      ∑' n : ℕ+,
        mellin (fun u => h (((n : ℕ) : ℝ) * u)) p := by
  unfold mellin eStarCoreV3
  rw [show
      (fun u : ℝ =>
          (u : ℂ) ^ (p - 1) •
            ∑' n : ℕ+, h (((n : ℕ) : ℝ) * u)) =
        (fun u : ℝ =>
          ∑' n : ℕ+,
            (u : ℂ) ^ (p - 1) •
              h (((n : ℕ) : ℝ) * u)) by
    funext u
    exact (tsum_const_smul'' ((u : ℂ) ^ (p - 1))).symm]
  exact MeasureTheory.integral_tsum habs.1 habs.2

private theorem pnatDirichletSeries_eq_riemannZetaV3
    {p : ℂ} (hp : 1 < p.re) :
    (∑' n : ℕ+, (n : ℂ) ^ (-p)) = riemannZeta p := by
  calc
    (∑' n : ℕ+, (n : ℂ) ^ (-p)) =
        ∑' k : ℕ,
          ((Nat.succPNat k : ℕ) : ℂ) ^ (-p) := by
      exact (Equiv.pnatEquivNat.symm.tsum_eq
        (fun n : ℕ+ => (n : ℂ) ^ (-p))).symm
    _ = ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℂ) ^ p := by
      apply tsum_congr
      intro k
      rw [Nat.succPNat_coe]
      simp [Complex.cpow_neg]
    _ = riemannZeta p := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (zeta_eq_tsum_one_div_nat_add_one_cpow hp).symm

private theorem mellin_Estar_eq_riemannZeta_mulV3
    {h : ℝ → ℂ} {s : ℂ}
    (hp : 1 < (s + 1 / 2).re)
    (habs :
      (∀ n : ℕ+,
        AEStronglyMeasurable
          (fun u : ℝ =>
            (u : ℂ) ^ ((s + 1 / 2) - 1) •
              h (((n : ℕ) : ℝ) * u))
          (volume.restrict (Set.Ioi 0))) ∧
      (∑' n : ℕ+,
        ∫⁻ u : ℝ,
          ‖(u : ℂ) ^ ((s + 1 / 2) - 1) •
            h (((n : ℕ) : ℝ) * u)‖ₑ
          ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤) :
    mellin (Estar h) s =
      riemannZeta (s + 1 / 2) * mellin h (s + 1 / 2) := by
  rw [mellin_Estar_eq_shifted_coreV3]
  rw [mellin_eStarCoreV3_eq_tsum habs]
  have hscale :
      ∀ n : ℕ+,
        mellin (fun u => h (((n : ℕ) : ℝ) * u)) (s + 1 / 2) =
          (n : ℂ) ^ (-(s + 1 / 2)) • mellin h (s + 1 / 2) := by
    intro n
    exact mellin_comp_mul_left h (s + 1 / 2)
      (show (0 : ℝ) < ((n : ℕ) : ℝ) by positivity)
  simp_rw [hscale, smul_eq_mul]
  rw [tsum_mul_right]
  rw [pnatDirichletSeries_eq_riemannZetaV3 hp]

private theorem mellinConvergent_indicatorV3
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s)
    (A : Set ℝ) (hA : MeasurableSet A) :
    MellinConvergent (A.indicator f) s := by
  unfold MellinConvergent at hf ⊢
  simpa only [← Set.indicator_smul] using hf.indicator hA

private theorem mellin_eq_lower_add_window_add_upperV3
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    mellin f s =
      lowerMellinTailV3 Λ f s +
        windowedMellinV3 Λ f s +
          upperMellinTailV3 Λ f s := by
  have hlower :
      MellinConvergent ((Set.Iio Λ⁻¹).indicator f) s :=
    mellinConvergent_indicatorV3 hf _ measurableSet_Iio
  have hwindow :
      MellinConvergent ((sourceWindowV3 Λ).indicator f) s :=
    mellinConvergent_indicatorV3 hf _ measurableSet_Icc
  have hupper :
      MellinConvergent ((Set.Ioi Λ).indicator f) s :=
    mellinConvergent_indicatorV3 hf _ measurableSet_Ioi
  unfold mellin lowerMellinTailV3 windowedMellinV3 upperMellinTailV3
  simp only [mellin]
  rw [← MeasureTheory.integral_add hlower hwindow]
  have hcombine :
      (∫ a : ℝ in Set.Ioi 0,
          (a : ℂ) ^ (s - 1) • (Set.Iio Λ⁻¹).indicator f a +
            (a : ℂ) ^ (s - 1) • (sourceWindowV3 Λ).indicator f a) +
        ∫ a : ℝ in Set.Ioi 0,
          (a : ℂ) ^ (s - 1) • (Set.Ioi Λ).indicator f a =
        ∫ a : ℝ in Set.Ioi 0,
          ((a : ℂ) ^ (s - 1) • (Set.Iio Λ⁻¹).indicator f a +
            (a : ℂ) ^ (s - 1) • (sourceWindowV3 Λ).indicator f a) +
              (a : ℂ) ^ (s - 1) • (Set.Ioi Λ).indicator f a := by
    exact (MeasureTheory.integral_add (hlower.add hwindow) hupper).symm
  rw [hcombine]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hΛinv : 0 < Λ⁻¹ := inv_pos.mpr hΛ0
  have hinv_le : Λ⁻¹ ≤ Λ :=
    (inv_le_one_of_one_le₀ hΛ).trans hΛ
  by_cases hlo : u < Λ⁻¹
  · have hnotwin : u ∉ sourceWindowV3 Λ := by
      intro huw
      exact (not_le_of_gt hlo) huw.1
    have hnotupper : u ∉ Set.Ioi Λ := by
      intro huu
      exact (not_lt_of_ge hinv_le) (huu.trans hlo)
    have hlo_mem : u ∈ Set.Iio Λ⁻¹ := hlo
    rw [Set.indicator_of_mem hlo_mem,
      Set.indicator_of_notMem hnotwin,
      Set.indicator_of_notMem hnotupper]
    simp
  · have hlowle : Λ⁻¹ ≤ u := le_of_not_gt hlo
    by_cases hhi : u ≤ Λ
    · have hwin : u ∈ sourceWindowV3 Λ := ⟨hlowle, hhi⟩
      have hnotlower : u ∉ Set.Iio Λ⁻¹ := not_lt.mpr hlowle
      have hnotupper : u ∉ Set.Ioi Λ := not_lt.mpr hhi
      rw [Set.indicator_of_notMem hnotlower,
        Set.indicator_of_mem hwin,
        Set.indicator_of_notMem hnotupper]
      simp
    · have hupp : u ∈ Set.Ioi Λ := lt_of_not_ge hhi
      have hnotlower : u ∉ Set.Iio Λ⁻¹ := not_lt.mpr hlowle
      have hnotwindow : u ∉ sourceWindowV3 Λ := by
        intro huw
        exact hhi huw.2
      rw [Set.indicator_of_notMem hnotlower,
        Set.indicator_of_notMem hnotwindow,
        Set.indicator_of_mem hupp]
      simp

private theorem Mellin_eq_mellinV3 (f : ℝ → ℂ) (s : ℂ) :
    Mellin f s = mellin f s := by
  unfold Mellin mellin
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  rw [mul_comm]

private theorem lowerMellinTailV3_eq_Rminus
    (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) :
    lowerMellinTailV3 Λ (Estar h) s = Rminus h Λ s := by
  unfold lowerMellinTailV3 Rminus mellin
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu0 : 0 < u
  · by_cases huΛ : u < Λ⁻¹
    · simp [hu0, huΛ, smul_eq_mul, mul_comm]
    · simp [hu0, huΛ]
  · simp [hu0]

private theorem windowedMellinV3_eq_Gwin
    (h : ℝ → ℂ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (s : ℂ) :
    windowedMellinV3 Λ (Estar h) s = Gwin h Λ s := by
  unfold windowedMellinV3 sourceWindowV3 Gwin mellin
  rw [← integral_Icc_eq_integral_Ioo]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hΛinv : 0 < Λ⁻¹ := inv_pos.mpr hΛ0
  by_cases hwin : u ∈ Set.Icc Λ⁻¹ Λ
  · have hu0 : 0 < u := hΛinv.trans_le hwin.1
    simp [hwin, hu0, smul_eq_mul, mul_comm]
  · by_cases hu0 : 0 < u
    · simp [hwin, hu0]
    · simp [hwin, hu0]

private theorem upperMellinTailV3_eq_Rplus
    (h : ℝ → ℂ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (s : ℂ) :
    upperMellinTailV3 Λ (Estar h) s = Rplus h Λ s := by
  unfold upperMellinTailV3 Rplus mellin
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases huΛ : Λ < u
  · have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (hΛ.trans huΛ.le)
    simp [huΛ, hu0, smul_eq_mul, mul_comm]
  · simp [huΛ]

/-- The exact v3 regularity class supplies the absolute-region identity consumed by
`continued_window_identity_of_analytic`.  This is the native v3 realization of the
Goal 012 T2 algebra; it uses the already proved absolute-dilate payload and aggregate
E-star Mellin convergence, then transports only names, scalar order, windows, and tails. -/
theorem habs_of_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∀ s : ℂ, 1 / 2 < s.re →
      Gwin h Λ s =
        riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
          Rminus h Λ s - Rplus h Λ s := by
  intro s hs
  have hp : 1 < (s + 1 / 2).re := by
    norm_num at hs ⊢
    linarith
  have habs :=
    eStarMellinAbsolute_payload_of_IccZero_IcoLipschitz
      h b K hb hmeas hsupp hlip (s + 1 / 2) hp
  have hEconv : MellinConvergent (Estar h) s :=
    mellinConvergent_Estar_of_zeroMass_IccZero_IcoLipschitz
      h b K hb hmeas hsupp hlip hmass s (by linarith)
  have hzeta := mellin_Estar_eq_riemannZeta_mulV3 hp habs
  have hsplit := mellin_eq_lower_add_window_add_upperV3 hΛ hEconv
  calc
    Gwin h Λ s = windowedMellinV3 Λ (Estar h) s :=
      (windowedMellinV3_eq_Gwin h Λ hΛ s).symm
    _ =
        (lowerMellinTailV3 Λ (Estar h) s +
            windowedMellinV3 Λ (Estar h) s +
              upperMellinTailV3 Λ (Estar h) s) -
          lowerMellinTailV3 Λ (Estar h) s -
            upperMellinTailV3 Λ (Estar h) s := by ring
    _ = mellin (Estar h) s -
          lowerMellinTailV3 Λ (Estar h) s -
            upperMellinTailV3 Λ (Estar h) s := by rw [hsplit]
    _ = riemannZeta (s + 1 / 2) * mellin h (s + 1 / 2) -
          lowerMellinTailV3 Λ (Estar h) s -
            upperMellinTailV3 Λ (Estar h) s := by rw [hzeta]
    _ = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
          Rminus h Λ s - Rplus h Λ s := by
      rw [Mellin_eq_mellinV3,
        lowerMellinTailV3_eq_Rminus,
        upperMellinTailV3_eq_Rplus h Λ hΛ]

#print axioms habs_of_IccZero_IcoLipschitz

end EStarMuntzZeroMassContinuation
