import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

set_option linter.mathlibStandardSet false
set_option maxRecDepth 2048

noncomputable section

open Complex
open scoped BigOperators FourierTransform Real

namespace Q3.RouteB.D0Pstar

/-!
# Source low-band decay of a single production Fourier mode

This is the first quantitative Fourier leg in the source-locked Yoshida
high-mode argument.  Once a literal mode lies beyond twice the prescribed
frequency band (with one unit of safety), its whole low-band Fourier image is
bounded by an explicit inverse-mode envelope.  No sampling and no finite
matrix truncation enter the statement.
-/

/-- The normalized antisymmetric source mode used by the literal odd graph
tail, stated independently on the ambient Hilbert space. -/
noncomputable def sourceWeilOddAmbientMode
    (i : PairIndex) (k : ℕ) : H_m i :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (V_n_m i (k + 1 : ℕ) - V_n_m i (-((k + 1 : ℕ) : ℤ)))

private theorem b3_0ak_invSqrtTwo_pair :
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) +
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 := by
  have hsR : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsC : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsR
  field_simp [hsC]
  norm_cast
  norm_num [Real.sq_sqrt]

/-- The infinite normalized antisymmetric source family is orthonormal in the
production ambient Hilbert space. -/
theorem sourceWeilOddAmbientMode_orthonormal (i : PairIndex) :
    Orthonormal ℂ (sourceWeilOddAmbientMode i) := by
  classical
  rw [orthonormal_iff_ite]
  intro r s
  let c : ℂ := (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
  change inner ℂ
      (c • (V_n_m i (r + 1 : ℕ) - V_n_m i (-((r + 1 : ℕ) : ℤ))))
      (c • (V_n_m i (s + 1 : ℕ) - V_n_m i (-((s + 1 : ℕ) : ℤ)))) = _
  rw [inner_smul_left, inner_smul_right]
  simp only [inner_sub_left, inner_sub_right]
  have hcstar : star c = c := by
    simp [c]
  change (starRingEnd ℂ) c = c at hcstar
  rw [hcstar]
  rw [orthonormal_iff_ite.mp (V_n_m_orthonormal i)]
  rw [orthonormal_iff_ite.mp (V_n_m_orthonormal i)]
  rw [orthonormal_iff_ite.mp (V_n_m_orthonormal i)]
  rw [orthonormal_iff_ite.mp (V_n_m_orthonormal i)]
  have hpos : (((r + 1 : ℕ) : ℤ) = ((s + 1 : ℕ) : ℤ)) ↔ r = s := by
    omega
  have hneg : (-((r + 1 : ℕ) : ℤ) = -((s + 1 : ℕ) : ℤ)) ↔ r = s := by
    omega
  have hcross₁ : ((r + 1 : ℕ) : ℤ) ≠ -((s + 1 : ℕ) : ℤ) := by
    omega
  have hcross₂ : -((r + 1 : ℕ) : ℤ) ≠ ((s + 1 : ℕ) : ℤ) := by
    omega
  simp only [hpos, hneg, hcross₁, hcross₂, if_false]
  by_cases hrs : r = s
  · rw [if_pos hrs]
    have hpair := b3_0ak_invSqrtTwo_pair
    change c * c + c * c = 1 at hpair
    linear_combination hpair
  · simp [hrs]

/-- The synthesized whole-line Fourier representative of an odd ambient mode
is almost everywhere the normalized difference of the two literal mode
transforms. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientMode
    (i : PairIndex) (k : ℕ) :
    ((sourceLogWindowFourierL2Isometry i (sourceWeilOddAmbientMode i k) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
      ℝ → ℂ) =ᵐ[MeasureTheory.volume]
        (fun t : ℝ =>
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
            (𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t -
              𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t)) := by
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
  have hsub := MeasureTheory.Lp.coeFn_sub A B
  have hsmul := MeasureTheory.Lp.coeFn_smul c (A - B)
  filter_upwards [hpos, hneg, hsub, hsmul] with t hpt hnt hsubt hsmult
  change
    ((sourceLogWindowFourierL2Isometry i
          ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
            (V_n_m i (k + 1 : ℕ) -
              V_n_m i (-((k + 1 : ℕ) : ℤ)))) : H_m i) :
        MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t = _
  rw [map_smul, map_sub]
  change
    (((c • (A - B) :
        MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t) = _
  rw [hsmult]
  change c * (((A - B :
      MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) t) = _
  rw [hsubt]
  change c * (((A : ℝ → ℂ) t) - ((B : ℝ → ℂ) t)) = _
  rw [show (A : ℝ → ℂ) t =
      𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t by
        simpa [A] using hpt,
    show (B : ℝ → ℂ) t =
      𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t by
        simpa [B] using hnt]

/-- If the carrier frequency of `V_n_m` is safely outside `[-T,T]`, its
zero-extended Fourier transform is uniformly `O(1 / |n|)` on that band. -/
theorem norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv
    (i : PairIndex) (n : ℤ) (T t : ℝ)
    (hT : 0 ≤ T)
    (hn : 2 * L_m i * (T + 1) ≤ |(n : ℝ)|)
    (ht : |t| ≤ T) :
    ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
      2 * Real.sqrt (L_m i) / (Real.pi * |(n : ℝ)|) := by
  let L : ℝ := L_m i
  let s : ℝ := Real.sqrt L
  let a : ℝ := |(n : ℝ)|
  let d : ℝ := |t - (n : ℝ) / L|
  have hL : 0 < L := by
    exact logLength_pos i
  have hs : 0 < s := by
    exact Real.sqrt_pos.mpr hL
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 < a := by
    have hprod : 0 < 2 * L * (T + 1) := by positivity
    exact lt_of_lt_of_le hprod (by simpa [L, a] using hn)
  have hcarrier : 2 * (T + 1) ≤ a / L := by
    rw [le_div_iff₀ hL]
    have h := hn
    dsimp [L, a] at h ⊢
    nlinarith
  have habsCarrier : |(n : ℝ) / L| = a / L := by
    rw [abs_div, abs_of_pos hL]
  have htriangle : |(n : ℝ) / L| ≤ |t| + d := by
    have h := abs_sub_le t 0 (t - (n : ℝ) / L)
    simpa [d, abs_sub_comm] using h
  have hhalf : a / (2 * L) ≤ d := by
    rw [habsCarrier] at htriangle
    have hhalf_band : T + 1 ≤ a / (2 * L) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * L)]
      have := hn
      dsimp [L, a] at this ⊢
      nlinarith
    have hsplit : a / L = 2 * (a / (2 * L)) := by
      field_simp [hL.ne']
    rw [hsplit] at htriangle
    nlinarith
  have hfar : 1 < d := by
    have hhalf_band : T + 1 ≤ a / (2 * L) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * L)]
      have := hn
      dsimp [L, a] at this ⊢
      nlinarith
    nlinarith
  have hmode := norm_fourier_logWindowZeroExtendedMode_le_far i n t
    (by simpa [L, d] using hfar)
  have hden_pos : 0 < Real.pi * s * d := by positivity
  have htarget_pos : 0 < Real.pi * a := by positivity
  calc
    ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
        1 / (Real.pi * s * d) := by simpa [L, s, d] using hmode
    _ ≤ 2 * s / (Real.pi * a) := by
      rw [div_le_div_iff₀ hden_pos htarget_pos]
      have hs_sq : s ^ 2 = L := Real.sq_sqrt hL.le
      have ha_le : a ≤ 2 * L * d := by
        rw [div_le_iff₀ (by positivity : 0 < 2 * L)] at hhalf
        simpa [mul_comm] using hhalf
      calc
        1 * (Real.pi * a) = Real.pi * a := by ring
        _ ≤ Real.pi * (2 * L * d) :=
          mul_le_mul_of_nonneg_left ha_le hpi.le
        _ = 2 * s * (Real.pi * s * d) := by
          rw [← hs_sq]
          ring
    _ = 2 * Real.sqrt (L_m i) / (Real.pi * |(n : ℝ)|) := rfl

/-- Uniform inverse-mode low-band envelope for the normalized antisymmetric
pair itself.  The constant `4` is intentionally coarse and avoids spending a
square-root optimization in the load-bearing argument. -/
theorem norm_sourceWeilOddAmbientModeFourier_le_lowBand_inv
    (i : PairIndex) (k : ℕ) (T t : ℝ)
    (hT : 0 ≤ T)
    (hk : 2 * L_m i * (T + 1) ≤ (k + 1 : ℝ))
    (ht : |t| ≤ T) :
    ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        (𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t -
          𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t)‖ ≤
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
  have hden : 0 < Real.pi * (k + 1 : ℝ) := by positivity
  calc
    ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        (𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t -
          𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t)‖ =
        ‖(((Real.sqrt 2 : ℝ) : ℂ)⁻¹)‖ *
          ‖𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t -
            𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t‖ :=
      norm_mul _ _
    _ ≤ 1 *
        (‖𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t‖ +
          ‖𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ 1 *
        (2 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ)) +
          2 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ))) := by
      gcongr
      · simpa [abs_of_nonneg hkpos] using hpos
      · rw [habsneg] at hneg
        exact hneg
    _ = 4 * Real.sqrt (L_m i) / (Real.pi * (k + 1 : ℝ)) := by
      field_simp
      ring

/-- Pointwise representative of the Fourier image of one normalized odd
ambient mode. -/
noncomputable def sourceWeilOddFourierModeFunction
    (i : PairIndex) (k : ℕ) (t : ℝ) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
    (𝓕 (logWindowZeroExtendedMode i (k + 1 : ℕ)) t -
      𝓕 (logWindowZeroExtendedMode i (-((k + 1 : ℕ) : ℤ))) t)

/-- Literal finite odd-mode Fourier synthesis. -/
noncomputable def sourceWeilOddFourierFinsupp
    (i : PairIndex) (c : ℕ →₀ ℂ) (t : ℝ) : ℂ :=
  c.sum fun k z => z * sourceWeilOddFourierModeFunction i k t

/-- Finite Cauchy--Schwarz for the literal odd Fourier synthesis. -/
theorem norm_sourceWeilOddFourierFinsupp_sq_le
    (i : PairIndex) (c : ℕ →₀ ℂ) (t : ℝ) :
    ‖sourceWeilOddFourierFinsupp i c t‖ ^ 2 ≤
      (∑ k ∈ c.support, ‖c k‖ ^ 2) *
        ∑ k ∈ c.support, ‖sourceWeilOddFourierModeFunction i k t‖ ^ 2 := by
  classical
  have hnorm :
      ‖sourceWeilOddFourierFinsupp i c t‖ ≤
        ∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilOddFourierModeFunction i k t‖ := by
    unfold sourceWeilOddFourierFinsupp
    calc
      ‖c.sum fun k z => z * sourceWeilOddFourierModeFunction i k t‖ ≤
          ∑ k ∈ c.support,
            ‖c k * sourceWeilOddFourierModeFunction i k t‖ := by
        simpa only [Finsupp.sum, Finset.sum_attach] using
          (norm_sum_le c.support
            (fun k => c k * sourceWeilOddFourierModeFunction i k t))
      _ = ∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilOddFourierModeFunction i k t‖ := by
        simp only [norm_mul]
  have hsum_nonneg :
      0 ≤ ∑ k ∈ c.support,
        ‖c k‖ * ‖sourceWeilOddFourierModeFunction i k t‖ := by
    positivity
  have hsq :
      ‖sourceWeilOddFourierFinsupp i c t‖ ^ 2 ≤
        (∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilOddFourierModeFunction i k t‖) ^ 2 := by
    nlinarith [norm_nonneg (sourceWeilOddFourierFinsupp i c t)]
  exact hsq.trans
    (Finset.sum_mul_sq_le_sq_mul_sq c.support
      (fun k => ‖c k‖)
      (fun k => ‖sourceWeilOddFourierModeFunction i k t‖))

/-- The low-band finite synthesis is controlled by coefficient energy times
the explicit inverse-square mode tail over its actual support. -/
theorem norm_sourceWeilOddFourierFinsupp_sq_le_lowBand
    (i : PairIndex) (c : ℕ →₀ ℂ) (T t : ℝ)
    (hT : 0 ≤ T)
    (hc : ∀ k ∈ c.support,
      2 * L_m i * (T + 1) ≤ (k + 1 : ℝ))
    (ht : |t| ≤ T) :
    ‖sourceWeilOddFourierFinsupp i c t‖ ^ 2 ≤
      (∑ k ∈ c.support, ‖c k‖ ^ 2) *
        ∑ k ∈ c.support,
          (4 * Real.sqrt (L_m i) /
            (Real.pi * (k + 1 : ℝ))) ^ 2 := by
  refine (norm_sourceWeilOddFourierFinsupp_sq_le i c t).trans ?_
  gcongr with k hk
  have hmode := norm_sourceWeilOddAmbientModeFourier_le_lowBand_inv
    i k T t hT (hc k hk) ht
  simpa [sourceWeilOddFourierModeFunction] using hmode

private theorem b3_0ak_one_div_add_one_sq_le_telescoping
    (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  field_simp [hx.ne', hx1.ne']
  nlinarith

private theorem b3_0ak_sum_range_inv_shift_sq_le
    (R N : ℕ) (hR : 0 < R) :
    (∑ k ∈ Finset.range N,
      1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2) ≤
        1 / (R : ℝ) - 1 / ((R : ℝ) + (N : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hx : 0 < (R : ℝ) + (N : ℝ) := by
        positivity
      have hterm :=
        b3_0ak_one_div_add_one_sq_le_telescoping
          ((R : ℝ) + (N : ℝ)) hx
      calc
        (∑ k ∈ Finset.range N,
            1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2) +
              1 / ((R : ℝ) + (N : ℝ) + 1) ^ 2 ≤
            (1 / (R : ℝ) - 1 / ((R : ℝ) + (N : ℝ))) +
              1 / ((R : ℝ) + (N : ℝ) + 1) ^ 2 :=
          by
            have h := add_le_add_right ih
              (1 / ((R : ℝ) + (N : ℝ) + 1) ^ 2)
            linarith
        _ ≤ 1 / (R : ℝ) -
            1 / ((R : ℝ) + ((N + 1 : ℕ) : ℝ)) := by
          have hcast :
              (R : ℝ) + ((N + 1 : ℕ) : ℝ) =
                (R : ℝ) + (N : ℝ) + 1 := by
            norm_num
            ring
          rw [hcast]
          linarith

/-- Explicit inverse-square tail bound used in the finite Yoshida estimate. -/
theorem sum_support_inv_nat_shift_sq_le
    (R : ℕ) (hR : 0 < R) (s : Finset ℕ) :
    (∑ k ∈ s, 1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2) ≤
      1 / (R : ℝ) := by
  let f : ℕ → ℝ := fun k =>
    1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    positivity
  have hrange : ∀ N, (∑ k ∈ Finset.range N, f k) ≤ 1 / (R : ℝ) := by
    intro N
    have h := b3_0ak_sum_range_inv_shift_sq_le R N hR
    have hlast : 0 ≤ 1 / ((R : ℝ) + (N : ℝ)) := by positivity
    dsimp [f]
    linarith
  have hsum : Summable f := summable_of_sum_range_le hf0 hrange
  calc
    (∑ k ∈ s, 1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2) =
        ∑ k ∈ s, f k := by rfl
    _ ≤ ∑' k, f k := hsum.sum_le_tsum s (fun k hk => hf0 k)
    _ ≤ 1 / (R : ℝ) := Real.tsum_le_of_sum_range_le hf0 hrange

/-- Finite Fourier synthesis of the literal graph-tail generators
`oddMode (R+k)`. -/
noncomputable def sourceWeilOddFourierFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (t : ℝ) : ℂ :=
  c.sum fun k z => z * sourceWeilOddFourierModeFunction i (R + k) t

/-- Ambient Hilbert-space synthesis of the same shifted odd-tail
coefficients. -/
noncomputable def sourceWeilOddAmbientFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) : H_m i :=
  c.sum fun k z => z • sourceWeilOddAmbientMode i (R + k)

/-- Parseval for the finite shifted odd-tail synthesis. -/
theorem norm_sourceWeilOddAmbientFinsuppShift_sq
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 =
      ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  classical
  have hinj : Function.Injective (fun k : ℕ => R + k) := by
    intro k l h
    exact Nat.add_left_cancel h
  have horth :
      Orthonormal ℂ (fun k : ℕ => sourceWeilOddAmbientMode i (R + k)) :=
    (sourceWeilOddAmbientMode_orthonormal i).comp _ hinj
  have hinner := horth.inner_finsupp_eq_sum_left c c
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change
    (inner ℂ
      (Finsupp.linearCombination ℂ
        (fun k : ℕ => sourceWeilOddAmbientMode i (R + k)) c)
      (Finsupp.linearCombination ℂ
        (fun k : ℕ => sourceWeilOddAmbientMode i (R + k)) c)).re = _
  rw [hinner]
  simp only [Finsupp.sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.mul_re]

/-- The whole-line `L²` image of a finite shifted odd synthesis agrees
almost everywhere with its literal finite Fourier sum. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientFinsuppShift
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) :
    ((sourceLogWindowFourierL2Isometry i
          (sourceWeilOddAmbientFinsuppShift i R c) :
        MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ)
      =ᵐ[MeasureTheory.volume]
        sourceWeilOddFourierFinsuppShift i R c := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      simpa [sourceWeilOddAmbientFinsuppShift,
        sourceWeilOddFourierFinsuppShift] using
        (MeasureTheory.Lp.coeFn_zero ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))
  | single_add k z c hk hz ih =>
      let A : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
        sourceLogWindowFourierL2Isometry i
          (sourceWeilOddAmbientMode i (R + k))
      let B : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
        sourceLogWindowFourierL2Isometry i
          (sourceWeilOddAmbientFinsuppShift i R c)
      have hmode :=
        coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientMode i (R + k)
      have hsmul := MeasureTheory.Lp.coeFn_smul z A
      have hadd := MeasureTheory.Lp.coeFn_add (z • A) B
      filter_upwards [hmode, ih, hsmul, hadd] with t hmodet iht hsmult haddt
      have hamb :
          sourceWeilOddAmbientFinsuppShift i R
              (Finsupp.single k z + c) =
            z • sourceWeilOddAmbientMode i (R + k) +
              sourceWeilOddAmbientFinsuppShift i R c := by
        unfold sourceWeilOddAmbientFinsuppShift
        calc
          (Finsupp.single k z + c).sum
              (fun k z => z • sourceWeilOddAmbientMode i (R + k)) =
              (Finsupp.single k z).sum
                  (fun k z => z • sourceWeilOddAmbientMode i (R + k)) +
                c.sum (fun k z => z • sourceWeilOddAmbientMode i (R + k)) := by
            apply Finsupp.sum_add_index'
            · intro a
              exact zero_smul ℂ _
            · intro a x y
              exact add_smul x y _
          _ = _ := by simp
      have hfour :
          sourceWeilOddFourierFinsuppShift i R
              (Finsupp.single k z + c) t =
            z * sourceWeilOddFourierModeFunction i (R + k) t +
              sourceWeilOddFourierFinsuppShift i R c t := by
        unfold sourceWeilOddFourierFinsuppShift
        calc
          (Finsupp.single k z + c).sum
              (fun k z => z * sourceWeilOddFourierModeFunction i (R + k) t) =
              (Finsupp.single k z).sum
                  (fun k z => z * sourceWeilOddFourierModeFunction i (R + k) t) +
                c.sum (fun k z =>
                  z * sourceWeilOddFourierModeFunction i (R + k) t) := by
            apply Finsupp.sum_add_index'
            · intro a
              exact zero_mul _
            · intro a x y
              exact add_mul x y _
          _ = _ := by simp
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
          sourceWeilOddFourierModeFunction i (R + k) t by
            simpa [A, sourceWeilOddFourierModeFunction] using hmodet,
        show (B : ℝ → ℂ) t =
          sourceWeilOddFourierFinsuppShift i R c t by
            simpa [B] using iht,
        hfour]

/-- Cauchy--Schwarz for the shifted odd-tail synthesis. -/
theorem norm_sourceWeilOddFourierFinsuppShift_sq_le
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (t : ℝ) :
    ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ 2 ≤
      (∑ k ∈ c.support, ‖c k‖ ^ 2) *
        ∑ k ∈ c.support,
          ‖sourceWeilOddFourierModeFunction i (R + k) t‖ ^ 2 := by
  classical
  have hnorm :
      ‖sourceWeilOddFourierFinsuppShift i R c t‖ ≤
        ∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilOddFourierModeFunction i (R + k) t‖ := by
    unfold sourceWeilOddFourierFinsuppShift
    calc
      ‖c.sum fun k z => z * sourceWeilOddFourierModeFunction i (R + k) t‖ ≤
          ∑ k ∈ c.support,
            ‖c k * sourceWeilOddFourierModeFunction i (R + k) t‖ := by
        simpa only [Finsupp.sum, Finset.sum_attach] using
          (norm_sum_le c.support
            (fun k => c k * sourceWeilOddFourierModeFunction i (R + k) t))
      _ = ∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilOddFourierModeFunction i (R + k) t‖ := by
        simp only [norm_mul]
  have hsum_nonneg :
      0 ≤ ∑ k ∈ c.support,
        ‖c k‖ * ‖sourceWeilOddFourierModeFunction i (R + k) t‖ := by
    positivity
  have hsq :
      ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ 2 ≤
        (∑ k ∈ c.support,
          ‖c k‖ * ‖sourceWeilOddFourierModeFunction i (R + k) t‖) ^ 2 := by
    nlinarith [norm_nonneg (sourceWeilOddFourierFinsuppShift i R c t)]
  exact hsq.trans
    (Finset.sum_mul_sq_le_sq_mul_sq c.support
      (fun k => ‖c k‖)
      (fun k => ‖sourceWeilOddFourierModeFunction i (R + k) t‖))

/-- Pointwise low-band estimate for every finite algebraic odd-tail vector,
with the infinite inverse-square tail already collapsed to `1/R`. -/
theorem norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (T t : ℝ)
    (hR : 0 < R)
    (hT : 0 ≤ T)
    (hcut : 2 * L_m i * (T + 1) ≤ (R + 1 : ℝ))
    (ht : |t| ≤ T) :
    ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ 2 ≤
      (∑ k ∈ c.support, ‖c k‖ ^ 2) *
        ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 * (1 / (R : ℝ))) := by
  refine (norm_sourceWeilOddFourierFinsuppShift_sq_le i R c t).trans ?_
  have hcoeff : 0 ≤ ∑ k ∈ c.support, ‖c k‖ ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoeff
  calc
    (∑ k ∈ c.support,
        ‖sourceWeilOddFourierModeFunction i (R + k) t‖ ^ 2) ≤
        ∑ k ∈ c.support,
          (4 * Real.sqrt (L_m i) /
            (Real.pi * ((R : ℝ) + (k : ℝ) + 1))) ^ 2 := by
      gcongr with k hk
      have hRk :
          2 * L_m i * (T + 1) ≤ (R + k + 1 : ℝ) := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        linarith
      have hmode :=
        norm_sourceWeilOddAmbientModeFourier_le_lowBand_inv
          i (R + k) T t hT (by simpa [Nat.cast_add] using hRk) ht
      simpa [sourceWeilOddFourierModeFunction, Nat.cast_add] using hmode
    _ = (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
        (∑ k ∈ c.support,
          1 / ((R : ℝ) + (k : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hden : (R : ℝ) + (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hpi, hden]
    _ ≤ (4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
        (1 / (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_support_inv_nat_shift_sq_le R hR c.support) (sq_nonneg _)

/-- Integrated low-band Fourier mass of every finite algebraic odd-tail
vector.  The right side is an explicit multiple of the ambient Hilbert norm,
uniformly over the coefficient support. -/
theorem integral_norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand
    (i : PairIndex) (R : ℕ) (c : ℕ →₀ ℂ) (T : ℝ)
    (hR : 0 < R)
    (hT : 0 ≤ T)
    (hcut : 2 * L_m i * (T + 1) ≤ (R + 1 : ℝ)) :
    (∫ t in Set.Icc (-T) T,
        ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ 2) ≤
      ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
            (1 / (R : ℝ)))) *
        ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 := by
  let A : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i
      (sourceWeilOddAmbientFinsuppShift i R c)
  have hAint : MeasureTheory.Integrable
      (fun t : ℝ => ‖((A : ℝ → ℂ) t)‖ ^ (2 : ℕ))
      MeasureTheory.volume :=
    (MeasureTheory.Lp.memLp A).integrable_norm_pow (by norm_num)
  have hAE :=
    coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientFinsuppShift
      i R c
  have hFourierInt : MeasureTheory.Integrable
      (fun t : ℝ =>
        ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ (2 : ℕ))
      MeasureTheory.volume := by
    apply hAint.congr
    simpa [A] using
      hAE.fun_comp (fun z : ℂ => ‖z‖ ^ (2 : ℕ))
  have hConstInt : MeasureTheory.IntegrableOn
      (fun _ : ℝ =>
        ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
            (1 / (R : ℝ))))
      (Set.Icc (-T) T) := by
    exact MeasureTheory.integrableOn_const
      (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hvol : MeasureTheory.volume.real (Set.Icc (-T) T) = 2 * T := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc
    (∫ t in Set.Icc (-T) T,
        ‖sourceWeilOddFourierFinsuppShift i R c t‖ ^ 2) ≤
        ∫ _t in Set.Icc (-T) T,
          ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 *
            ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
              (1 / (R : ℝ))) := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hFourierInt.integrableOn
      · exact hConstInt
      · exact measurableSet_Icc
      · intro t ht
        have hpoint :=
          norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand
            i R c T t hR hT hcut (abs_le.mpr ht)
        rw [norm_sourceWeilOddAmbientFinsuppShift_sq i R c]
        exact hpoint
    _ = (2 * T) *
          (‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 *
            ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
              (1 / (R : ℝ)))) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    _ = ((2 * T) *
          ((4 * Real.sqrt (L_m i) / Real.pi) ^ 2 *
            (1 / (R : ℝ)))) *
        ‖sourceWeilOddAmbientFinsuppShift i R c‖ ^ 2 := by ring

#print axioms norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv
#print axioms sourceWeilOddAmbientMode_orthonormal
#print axioms coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientMode
#print axioms norm_sourceWeilOddAmbientModeFourier_le_lowBand_inv
#print axioms norm_sourceWeilOddFourierFinsupp_sq_le
#print axioms norm_sourceWeilOddFourierFinsupp_sq_le_lowBand
#print axioms sum_support_inv_nat_shift_sq_le
#print axioms norm_sourceWeilOddAmbientFinsuppShift_sq
#print axioms coeFn_sourceLogWindowFourierL2Isometry_apply_oddAmbientFinsuppShift
#print axioms norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand
#print axioms integral_norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand

end Q3.RouteB.D0Pstar
