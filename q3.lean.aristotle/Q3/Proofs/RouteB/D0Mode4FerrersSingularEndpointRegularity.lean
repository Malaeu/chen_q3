import Q3.Proofs.RouteB.D0Mode4FerrersInteriorZeroSimplicity

/-!
# Goal 058 G3: nonvanishing at the singular Ferrers endpoints

The accepted mode-four Ferrers solution is continuous on the closed source
interval, solves the prolate equation on its interior, and has zero Legendre
flux at both singular endpoints.  A one-sided contraction argument shows that
zero value and zero flux at an endpoint would force the solution to vanish on
an interior interval, contradicting interior-zero simplicity.

This is only the first bounded leaf of the singular Sturm library selected by
the source-locked Goal 058 review.  It does not count zeros, prove that the
bottom selected mode is zero-free, or identify the coefficient-space index
with a function-space nodal index.

Knowledge preflight before the write:

`./orchestrator/kb.py ask "Mode4FerrersRegularEvenProlateSolution endpoint_values_ne_zero singular endpoint zero flux interior_zero_simple"`

returned no hits.  The retrieval result is only a discovery receipt.
-/

namespace Q3.RouteB

private noncomputable def mode4FerrersFlux
    (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * mode4FerrersFirstDerivativeSeries a x

private theorem Mode4FerrersRegularEvenProlateSolution.flux_hasDerivAt
    {mProject K : ℕ} {Λ x : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (mode4FerrersFlux S.coefficients)
      (-(Λ + mode4JacobiG mProject * (1 - x ^ 2)) *
        mode4FerrersSeries S.coefficients x)
      x := by
  have hFactor : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa [id_eq, mul_comm] using
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
  have hFirst :=
    S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx
  have hRaw := hFactor.mul hFirst
  have hODE := S.prolateDifferentialEquation x hx
  change HasDerivAt (mode4FerrersFlux S.coefficients) _ x at hRaw
  apply hRaw.congr_deriv
  ring_nf at hODE ⊢
  linarith

private theorem endpoint_norm_sub_le_of_deriv_bound
    {F F' : ℝ → ℝ} {L C s : ℝ}
    (hs : s < 1)
    (hderiv : ∀ x ∈ Set.Ico s 1, HasDerivAt F (F' x) x)
    (hbound : ∀ x ∈ Set.Ico s 1, ‖F' x‖ ≤ C)
    (hlim : Filter.Tendsto F (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds L)) :
    ‖L - F s‖ ≤ C * (1 - s) := by
  have hleft :
      Filter.Tendsto (fun t : ℝ => ‖F t - F s‖)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds ‖L - F s‖) :=
    (hlim.sub tendsto_const_nhds).norm
  have hright :
      Filter.Tendsto (fun t : ℝ => C * (t - s))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (C * (1 - s))) := by
    exact
      ((continuousAt_const.mul
        (continuousAt_id.sub continuousAt_const)).tendsto).mono_left
          nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hs)] with t ht hst
  have hst' : s < t := hst
  have ht1 : t < 1 := ht
  have hsegment :=
    (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := F')
      (fun x hx =>
        (hderiv x ⟨hx.1, hx.2.trans_lt ht1⟩).hasDerivWithinAt)
      (fun x hx => hbound x ⟨hx.1, hx.2.trans_lt ht1⟩)
      (Set.left_mem_Icc.mpr hst'.le)
      (Set.right_mem_Icc.mpr hst'.le)
  simpa [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hst')] using hsegment

/-- A regular even mode-four Ferrers solution cannot vanish at either singular
endpoint.  The right-endpoint proof uses the zero-flux limit and a contraction
on a sufficiently short terminal interval; the left endpoint follows from
evenness. -/
theorem Mode4FerrersRegularEvenProlateSolution.endpoint_values_ne_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    mode4FerrersSeries S.coefficients (-1) ≠ 0 ∧
      mode4FerrersSeries S.coefficients 1 ≠ 0 := by
  have hRight : mode4FerrersSeries S.coefficients 1 ≠ 0 := by
    intro hEndpoint
    let f : ℝ → ℝ := mode4FerrersSeries S.coefficients
    let g : ℝ → ℝ := mode4FerrersFirstDerivativeSeries S.coefficients
    let flux : ℝ → ℝ := mode4FerrersFlux S.coefficients
    let G : ℝ := mode4JacobiG mProject
    let C : ℝ := |Λ| + |G|
    let a : ℝ := C / (C + 1)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hC1 : 0 < C + 1 := by linarith
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have ha_lt_one : a < 1 := by
      dsimp [a]
      rw [div_lt_one hC1]
      linarith
    have ha_gt_neg_one : (-1 : ℝ) < a := lt_of_lt_of_le (by norm_num) ha_nonneg
    have hsource : Set.Icc a 1 ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      exact ⟨ha_gt_neg_one.le.trans hx.1, hx.2⟩
    have hfContinuous : ContinuousOn f (Set.Icc a 1) := by
      exact S.continuousOn_closed.mono hsource
    have habsContinuous : ContinuousOn (fun x => |f x|) (Set.Icc a 1) :=
      hfContinuous.abs
    have hintervalNonempty : (Set.Icc a 1).Nonempty :=
      ⟨1, Set.right_mem_Icc.mpr ha_lt_one.le⟩
    obtain ⟨z, hz, hzmax⟩ :=
      isCompact_Icc.exists_isMaxOn hintervalNonempty habsContinuous
    let M : ℝ := |f z|
    have hM : 0 ≤ M := by
      dsimp [M]
      exact abs_nonneg _
    have hfBound : ∀ x ∈ Set.Icc a 1, |f x| ≤ M := by
      intro x hx
      exact hzmax hx
    have hCoefficientBound :
        ∀ x ∈ Set.Icc a 1,
          |Λ + G * (1 - x ^ 2)| ≤ C := by
      intro x hx
      have hx0 : 0 ≤ x := ha_nonneg.trans hx.1
      have hx1 : x ≤ 1 := hx.2
      have hxSquareLower : 0 ≤ 1 - x ^ 2 := by nlinarith
      have hxSquareUpper : 1 - x ^ 2 ≤ 1 := by nlinarith
      calc
        |Λ + G * (1 - x ^ 2)| ≤ |Λ| + |G * (1 - x ^ 2)| := abs_add_le _ _
        _ = |Λ| + |G| * |1 - x ^ 2| := by rw [abs_mul]
        _ = |Λ| + |G| * (1 - x ^ 2) := by
          rw [abs_of_nonneg hxSquareLower]
        _ ≤ |Λ| + |G| := by
          have hp : |G| * (1 - x ^ 2) ≤ |G| := by
            simpa using
              (mul_le_mul_of_nonneg_left hxSquareUpper (abs_nonneg G))
          linarith
        _ = C := rfl
    have hFluxLimit :
        Filter.Tendsto flux
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
      simpa [flux, mode4FerrersFlux] using S.zeroFlux_at_endpoints.1
    have hFluxBound :
        ∀ s ∈ Set.Ico a 1, |flux s| ≤ C * M * (1 - s) := by
      intro s hs
      have hsSource : s ∈ Set.Ioo (-1 : ℝ) 1 :=
        ⟨ha_gt_neg_one.trans_le hs.1, hs.2⟩
      have hderiv :
          ∀ x ∈ Set.Ico s 1,
            HasDerivAt flux
              (-(Λ + G * (1 - x ^ 2)) * f x) x := by
        intro x hx
        have hxSource : x ∈ Set.Ioo (-1 : ℝ) 1 :=
          ⟨hsSource.1.trans_le hx.1, hx.2⟩
        simpa [flux, G, f] using S.flux_hasDerivAt hxSource
      have hbound :
          ∀ x ∈ Set.Ico s 1,
            ‖-(Λ + G * (1 - x ^ 2)) * f x‖ ≤ C * M := by
        intro x hx
        have hxShort : x ∈ Set.Icc a 1 :=
          ⟨hs.1.trans hx.1, hx.2.le⟩
        rw [Real.norm_eq_abs, abs_mul, abs_neg]
        exact mul_le_mul
          (hCoefficientBound x hxShort) (hfBound x hxShort)
          (abs_nonneg _) hC
      have h := endpoint_norm_sub_le_of_deriv_bound hs.2 hderiv hbound hFluxLimit
      simpa [Real.norm_eq_abs, abs_neg, mul_assoc] using h
    have hgBound :
        ∀ s ∈ Set.Ico a 1, |g s| ≤ C * M / (1 + a) := by
      intro s hs
      have hs0 : 0 ≤ s := ha_nonneg.trans hs.1
      have hOneSub : 0 < 1 - s := sub_pos.mpr hs.2
      have hOneAdd : 0 < 1 + a := by linarith
      have hSquare : 0 ≤ 1 - s ^ 2 := by nlinarith
      have hFluxAbs : |flux s| = (1 - s ^ 2) * |g s| := by
        dsimp [flux, mode4FerrersFlux, g]
        rw [abs_mul, abs_of_nonneg hSquare]
      have hraw := hFluxBound s hs
      rw [hFluxAbs] at hraw
      have hfactor : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
      rw [hfactor] at hraw
      have hcancel : (1 + s) * |g s| ≤ C * M := by
        nlinarith [abs_nonneg (g s)]
      have hdenom : (1 + a) * |g s| ≤ C * M := by
        have hsge : 1 + a ≤ 1 + s := by linarith [hs.1]
        exact (mul_le_mul_of_nonneg_right hsge (abs_nonneg _)).trans hcancel
      exact (le_div_iff₀ hOneAdd).2 (by simpa [mul_comm] using hdenom)
    have hfLimit :
        Filter.Tendsto f
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
      have hcont := S.continuousOn_closed (1 : ℝ) (by simp)
      have hIccEventually :
          Set.Icc (-1 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
        filter_upwards
            [self_mem_nhdsWithin,
              mem_nhdsWithin_of_mem_nhds
                (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with x hx hxmin
        exact ⟨hxmin.le, hx.le⟩
      have hfilter :
          nhdsWithin (1 : ℝ) (Set.Iio 1) ≤
            nhdsWithin (1 : ℝ) (Set.Icc (-1 : ℝ) 1) :=
        le_inf inf_le_left (Filter.le_principal_iff.mpr hIccEventually)
      simpa [f, hEndpoint] using hcont.tendsto.mono_left hfilter
    have hfShortBound :
        ∀ s ∈ Set.Ico a 1,
          |f s| ≤ (C * M / (1 + a)) * (1 - s) := by
      intro s hs
      have hderiv :
          ∀ x ∈ Set.Ico s 1, HasDerivAt f (g x) x := by
        intro x hx
        have hxSource : x ∈ Set.Ioo (-1 : ℝ) 1 :=
          ⟨ha_gt_neg_one.trans_le (hs.1.trans hx.1), hx.2⟩
        simpa [f, g] using
          S.ferrersSeries_hasDerivAt_firstDerivativeSeries x hxSource
      have hbound :
          ∀ x ∈ Set.Ico s 1, ‖g x‖ ≤ C * M / (1 + a) := by
        intro x hx
        rw [Real.norm_eq_abs]
        exact hgBound x ⟨hs.1.trans hx.1, hx.2⟩
      have h := endpoint_norm_sub_le_of_deriv_bound hs.2 hderiv hbound hfLimit
      simpa [Real.norm_eq_abs, abs_neg] using h
    have hContraction : C * (1 - a) / (1 + a) < 1 := by
      have hden : 0 < 1 + a := by linarith
      rw [div_lt_one hden]
      dsimp [a]
      field_simp [hC1.ne']
      nlinarith
    have hMle : M ≤ (C * (1 - a) / (1 + a)) * M := by
      by_cases hzOne : z = 1
      · subst z
        simp [M, f, hEndpoint]
      · have hzlt : z < 1 := lt_of_le_of_ne hz.2 hzOne
        have hzco : z ∈ Set.Ico a 1 := ⟨hz.1, hzlt⟩
        have hshort := hfShortBound z hzco
        change M ≤ _
        calc
          M = |f z| := rfl
          _ ≤ (C * M / (1 + a)) * (1 - z) := hshort
          _ ≤ (C * M / (1 + a)) * (1 - a) := by
            exact mul_le_mul_of_nonneg_left (by linarith [hz.1])
              (div_nonneg (mul_nonneg hC hM) (by linarith : 0 ≤ 1 + a))
          _ = (C * (1 - a) / (1 + a)) * M := by ring
    have hMzero : M = 0 := by
      nlinarith [hContraction]
    let x : ℝ := (a + 1) / 2
    have hxShort : x ∈ Set.Ioo a 1 := by
      dsimp [x]
      constructor <;> linarith
    have hxSource : x ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨ha_gt_neg_one.trans hxShort.1, hxShort.2⟩
    have hxZero : f x = 0 := by
      have habs := hfBound x ⟨hxShort.1.le, hxShort.2.le⟩
      rw [hMzero] at habs
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    have hEventuallyZero : f =ᶠ[nhds x] (fun _ : ℝ => 0) := by
      filter_upwards
          [Ioo_mem_nhds hxShort.1 hxShort.2] with y hy
      have habs := hfBound y ⟨hy.1.le, hy.2.le⟩
      rw [hMzero] at habs
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    have hDerivZero : deriv f x = 0 := by
      have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x :=
        hasDerivAt_const x 0
      exact ((hEventuallyZero.hasDerivAt_iff).mpr hconst).deriv
    have hSimple : deriv f x ≠ 0 := by
      simpa [f] using S.interior_zero_simple hxSource (by simpa [f] using hxZero)
    exact hSimple hDerivZero
  refine ⟨?_, hRight⟩
  intro hLeft
  apply hRight
  simpa using (S.even (1 : ℝ)).symm.trans hLeft

#print axioms Mode4FerrersRegularEvenProlateSolution.endpoint_values_ne_zero

end Q3.RouteB
