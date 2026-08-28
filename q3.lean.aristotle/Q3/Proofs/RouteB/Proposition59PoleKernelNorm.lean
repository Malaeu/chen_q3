import Q3.Proofs.RouteB.Proposition59EntireTransform

open Filter Set
open scoped Topology BigOperators

noncomputable section

namespace Q3.RouteB

private theorem scratch_summable_int_shift_normSq_inv (a : ℂ) :
    Summable (fun k : ℤ => (Complex.normSq (a - k))⁻¹) := by
  have h := EisensteinSeries.linear_right_summable a (-1) (k := (2 : ℤ)) (by norm_num)
  have hn := h.norm
  convert hn using 1
  funext k
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, zpow_ofNat, norm_inv, norm_pow,
    Complex.normSq_eq_norm_sq]
  rw [show -a + (k : ℂ) = -(a - (k : ℂ)) by ring, norm_neg]

private theorem scratch_inv_sub_int_im
    (a : ℂ) (k : ℤ) :
    (1 / (a - (k : ℂ))).im =
      -a.im * (Complex.normSq (a - (k : ℂ)))⁻¹ := by
  rw [one_div, Complex.inv_im]
  simp only [Complex.sub_im, Complex.intCast_im, sub_zero, div_eq_mul_inv]

private theorem scratch_int_shift_normSq_inv_tsum_eq_cot_im
    (a : ℂ) (ha : a.im ≠ 0) :
    ∑' k : ℤ, (Complex.normSq (a - (k : ℂ)))⁻¹ =
      -(Real.pi * Complex.cot (Real.pi * a)).im / a.im := by
  have haIC : a ∈ Complex.integerComplement := by
    rw [Complex.integerComplement, Set.mem_compl_iff]
    intro hmem
    rcases hmem with ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp only [Complex.intCast_im] at this
    exact ha this.symm
  let f : ℤ → ℝ := fun k => (Complex.normSq (a - (k : ℂ)))⁻¹
  have hf : Summable f := scratch_summable_int_shift_normSq_inv a
  have hfpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hfneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun x y h => by omega)
  have hterm (n : ℕ) :
      (cotTerm a n).im =
        -a.im * (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
    unfold cotTerm f
    rw [Complex.add_im]
    rw [show (n : ℂ) + 1 = (((n : ℤ) + 1 : ℤ) : ℂ) by norm_num]
    rw [scratch_inv_sub_int_im a ((n : ℤ) + 1)]
    rw [show a + ((((n : ℤ) + 1 : ℤ) : ℂ)) =
        a - ((-((n : ℤ) + 1) : ℤ) : ℂ) by push_cast; ring]
    rw [scratch_inv_sub_int_im a (-((n : ℤ) + 1))]
    ring
  have hcot := cot_series_rep' haIC
  have hcotsum := Summable_cotTerm haIC
  have him := congrArg Complex.im hcot
  rw [Complex.im_tsum hcotsum] at him
  simp_rw [hterm] at him
  rw [tsum_mul_left] at him
  have hpair :
      ∑' n : ℕ, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) =
        (∑' n : ℕ, f ((n : ℤ) + 1)) +
          ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
    (Summable.tsum_add hfpos hfneg)
  rw [hpair] at him
  have hsplit := tsum_of_add_one_of_neg_add_one hfpos hfneg
  change (∑' k : ℤ, f k) = _
  rw [hsplit]
  rw [Complex.sub_im] at him
  have hinv0 := scratch_inv_sub_int_im a 0
  simp only [Int.cast_zero, sub_zero] at hinv0
  rw [hinv0] at him
  unfold f at him ⊢
  simp only [Int.cast_zero, sub_zero] at him ⊢
  apply (eq_div_iff ha).2
  linear_combination him

private theorem scratch_cot_im_closedForm (z : ℂ) :
    (Complex.cot z).im =
      -Real.sinh (2 * z.im) /
        (Real.cosh (2 * z.im) - Real.cos (2 * z.re)) := by
  have hsinre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    rw [Complex.sin_eq]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hsinim : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    rw [Complex.sin_eq]
    simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hcosre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hcosim : (Complex.cos z).im = -Real.sin z.re * Real.sinh z.im := by
    rw [Complex.cos_eq]
    simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hnorm : Complex.normSq (Complex.sin z) =
      (Real.cosh (2 * z.im) - Real.cos (2 * z.re)) / 2 := by
    rw [Complex.normSq_apply, hsinre, hsinim, Real.cosh_two_mul,
      Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq z.re,
      Real.cosh_sq_sub_sinh_sq z.im]
  rw [Complex.cot, Complex.div_im, hsinre, hsinim, hcosre, hcosim, hnorm,
    Real.sinh_two_mul]
  let D := Real.cosh (2 * z.im) - Real.cos (2 * z.re)
  change _ / (D / 2) - _ / (D / 2) = _ / D
  by_cases hD : D = 0
  · simp [hD]
  · field_simp [hD]
    calc
      Real.sinh z.im * (-Real.sin z.re ^ 2 - Real.cos z.re ^ 2) =
          -Real.sinh z.im * (Real.sin z.re ^ 2 + Real.cos z.re ^ 2) := by ring
      _ = -Real.sinh z.im * 1 := by rw [Real.sin_sq_add_cos_sq]
      _ = -Real.sinh z.im := by ring

private theorem scratch_normSq_sin_closedForm (z : ℂ) :
    Complex.normSq (Complex.sin z) =
      (Real.cosh (2 * z.im) - Real.cos (2 * z.re)) / 2 := by
  have hsinre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    rw [Complex.sin_eq]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hsinim : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    rw [Complex.sin_eq]
    simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [Complex.normSq_apply, hsinre, hsinim, Real.cosh_two_mul,
    Real.cos_two_mul']
  nlinarith [Real.sin_sq_add_cos_sq z.re,
    Real.cosh_sq_sub_sinh_sq z.im]

private theorem scratch_int_shift_normSq_inv_hasSum_closedForm
    (a : ℂ) (ha : a.im ≠ 0) :
    HasSum
      (fun k : ℤ => (Complex.normSq (a - (k : ℂ)))⁻¹)
      (Real.pi * Real.sinh (2 * Real.pi * a.im) /
        (a.im * (Real.cosh (2 * Real.pi * a.im) -
          Real.cos (2 * Real.pi * a.re)))) := by
  have hs := (scratch_summable_int_shift_normSq_inv a).hasSum
  rw [scratch_int_shift_normSq_inv_tsum_eq_cot_im a ha] at hs
  convert hs using 1
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [scratch_cot_im_closedForm]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    Complex.mul_re]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

private theorem scratch_pi_shift_normSq_inv_hasSum_closedForm
    (w : ℂ) (hw : w.im ≠ 0) :
    HasSum
      (fun k : ℤ => (Complex.normSq (w - (k : ℂ) * (Real.pi : ℂ)))⁻¹)
      (Real.sinh (2 * w.im) /
        (w.im * (Real.cosh (2 * w.im) - Real.cos (2 * w.re)))) := by
  let a : ℂ := w / (Real.pi : ℂ)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have haim : a.im = w.im / Real.pi := by
    simp [a, Complex.div_im]
    field_simp [hpi]
  have hare : a.re = w.re / Real.pi := by
    simp [a, Complex.div_re]
    field_simp [hpi]
  have ha : a.im ≠ 0 := by
    rw [haim]
    exact div_ne_zero hw hpi
  have hs := scratch_int_shift_normSq_inv_hasSum_closedForm a ha
  have hscaled := hs.mul_left (Real.pi ^ (-2 : ℤ))
  convert hscaled using 1
  · funext k
    have hfactor :
        w - (k : ℂ) * (Real.pi : ℂ) =
          (Real.pi : ℂ) * (a - (k : ℂ)) := by
      simp [a]
      field_simp [hpi]
    rw [hfactor, Complex.normSq_mul]
    simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    field_simp [hpi]
    norm_num
  · rw [haim, hare]
    have him : 2 * Real.pi * (w.im / Real.pi) = 2 * w.im := by
      field_simp [hpi]
    have hre : 2 * Real.pi * (w.re / Real.pi) = 2 * w.re := by
      field_simp [hpi]
    rw [him, hre]
    field_simp [hpi]

private theorem scratch_proposition59PoleKernel_eq_scaled_pi_quotient
    {L : ℝ} (hL : 0 < L) (k : ℤ) {z : ℂ} (hz : z.im ≠ 0) :
    proposition59PoleKernel L k z =
      (L : ℂ) * Complex.sin (z * (L : ℂ) / 2) /
        (z * (L : ℂ) / 2 - (k : ℂ) * (Real.pi : ℂ)) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hzpole : z ≠ proposition59Pole L k := by
    intro h
    have him := congrArg Complex.im h
    simp [proposition59Pole] at him
    exact hz him
  have hden :
      z * (L : ℂ) / 2 - (k : ℂ) * (Real.pi : ℂ) ≠ 0 := by
    intro hzero
    apply hzpole
    unfold proposition59Pole
    apply (eq_div_iff hLC).2
    have hzL : z * (L : ℂ) = 2 * (k : ℂ) * (Real.pi : ℂ) := by
      linear_combination 2 * hzero
    exact hzL
  rw [proposition59PoleKernel_eq_quotient hL.ne' k hzpole]
  unfold proposition59Numerator proposition59Pole
  field_simp [hLC, hden]

/-- The full unnormalised Proposition-5.9 pole row has the exact squared
`ℓ²` norm `L² sinh(L Im z) / (L Im z)` away from the removable real-axis
singularity.  The index set here is the whole integer lattice. -/
theorem proposition59PoleKernel_normSq_hasSum
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z.im ≠ 0) :
    HasSum
      (fun k : ℤ => ‖proposition59PoleKernel L k z‖ ^ 2)
      (L ^ 2 * (Real.sinh (L * z.im) / (L * z.im))) := by
  let w : ℂ := z * (L : ℂ) / 2
  have hwim : w.im = z.im * L / 2 := by
    simp [w, Complex.mul_im]
  have hw : w.im ≠ 0 := by
    rw [hwim]
    exact div_ne_zero (mul_ne_zero hz hL.ne') (by norm_num)
  have hs := scratch_pi_shift_normSq_inv_hasSum_closedForm w hw
  let C : ℝ := L ^ 2 * Complex.normSq (Complex.sin w)
  have hscaled := hs.mul_left C
  have hnormsin := scratch_normSq_sin_closedForm w
  let D : ℝ := Real.cosh (2 * w.im) - Real.cos (2 * w.re)
  have hsin : Complex.sin w ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have him := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.intCast_re, Complex.ofReal_im,
      Complex.intCast_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero] at him
    exact hw him
  have hD : D ≠ 0 := by
    intro hDz
    have hnzero : Complex.normSq (Complex.sin w) = 0 := by
      rw [hnormsin]
      simp [D] at hDz
      rw [hDz]
      norm_num
    exact hsin (Complex.normSq_eq_zero.mp hnzero)
  convert hscaled using 1
  · funext k
    have hk := scratch_proposition59PoleKernel_eq_scaled_pi_quotient hL k hz
    change proposition59PoleKernel L k z =
      (L : ℂ) * Complex.sin w /
        (w - (k : ℂ) * (Real.pi : ℂ)) at hk
    rw [hk]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div,
      Complex.normSq_mul]
    have hnormL : Complex.normSq (L : ℂ) = L ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
    rw [hnormL]
    change
      L ^ 2 * Complex.normSq (Complex.sin w) /
          Complex.normSq (w - (k : ℂ) * (Real.pi : ℂ)) =
        C * (Complex.normSq (w - (k : ℂ) * (Real.pi : ℂ)))⁻¹
    dsimp [C]
    rw [div_eq_mul_inv]
  · change
      L ^ 2 * (Real.sinh (L * z.im) / (L * z.im)) =
        C * (Real.sinh (2 * w.im) /
          (w.im * (Real.cosh (2 * w.im) - Real.cos (2 * w.re))))
    dsimp [C]
    rw [hnormsin]
    change
      L ^ 2 * (Real.sinh (L * z.im) / (L * z.im)) =
        (L ^ 2 * (D / 2)) *
          (Real.sinh (2 * w.im) / (w.im * D))
    have htwoim : 2 * w.im = L * z.im := by
      rw [hwim]
      ring
    rw [htwoim, hwim]
    field_simp [hD, hL.ne', hz]

/-- The closed form for the full row norm has removable real-axis limit `L²`.
The punctured filter is load-bearing: the displayed quotient itself takes the
field-default value `0` at `y = 0`, while its analytic continuation takes
the limit proved here. -/
theorem proposition59PoleKernel_normSq_closedForm_tendsto_realAxis
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun y : ℝ => L ^ 2 * (Real.sinh (L * y) / (L * y)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (L ^ 2)) := by
  have hslope := (Real.hasDerivAt_sinh 0).tendsto_slope_zero
  have hratio :
      Tendsto
        (fun t : ℝ => Real.sinh t / t)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hslope
  have hscale :
      Tendsto
        (fun y : ℝ => L * y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    simpa using
      ((hasDerivAt_id 0).const_mul L).tendsto_nhdsNE
        (mul_ne_zero hL.ne' one_ne_zero)
  have hcomp := hratio.comp hscale
  convert (tendsto_const_nhds.mul hcomp) using 1 <;> simp

#print axioms proposition59PoleKernel_normSq_hasSum
#print axioms proposition59PoleKernel_normSq_closedForm_tendsto_realAxis

end Q3.RouteB
