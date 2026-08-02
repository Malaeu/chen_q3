import Q3.Proofs.RouteB.ProlateLayer

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The canonical two-mode packet is even whenever the stored prolate modes
are even.  This is a representation theorem for a supplied `ProlatePair`; it
does not construct the modes. -/
theorem prolateCombination_even (P : ProlatePair) :
    Function.Even (prolateCombination P) := by
  intro x
  simp only [prolateCombination_apply]
  rw [P.h0_even x, P.h4_even x]

/-- The canonical packet has the same symmetric support bound as its two
stored modes. -/
theorem prolateCombination_eq_zero_outside (P : ProlatePair) :
    ∀ x, x ∉ Icc (-P.pw.lambda) P.pw.lambda →
      prolateCombination P x = 0 := by
  intro x hx
  have h0x : P.h0 x = 0 := by
    by_contra hne
    exact hx (P.h0_support hne)
  have h4x : P.h4 x = 0 := by
    by_contra hne
    exact hx (P.h4_support hne)
  simp [prolateCombination_apply, h0x, h4x]

/-- Integrability is preserved by the fixed two-mode scalar combination.
No nonvanishing of the denominator is required for this statement. -/
theorem prolateCombination_integrable (P : ProlatePair) :
    Integrable (prolateCombination P) := by
  have h0i : Integrable (fun x : ℝ => (P.I4 : ℂ) * P.h0 x) :=
    P.h0_integrable.const_mul (P.I4 : ℂ)
  have h4i : Integrable (fun x : ℝ => (P.I0 : ℂ) * P.h4 x) :=
    P.h4_integrable.const_mul (P.I0 : ℂ)
  simpa only [prolateCombination] using
    (h0i.sub h4i).div_const (P.normalizingDenominator : ℂ)

/-- The total integral of the canonical packet vanishes algebraically. -/
theorem integral_prolateCombination_eq_zero (P : ProlatePair) :
    (∫ x : ℝ, prolateCombination P x) = 0 := by
  have h0i : Integrable (fun x : ℝ => (P.I4 : ℂ) * P.h0 x) :=
    P.h0_integrable.const_mul (P.I4 : ℂ)
  have h4i : Integrable (fun x : ℝ => (P.I0 : ℂ) * P.h4 x) :=
    P.h4_integrable.const_mul (P.I0 : ℂ)
  simp only [prolateCombination]
  rw [integral_div, integral_sub h0i h4i, integral_const_mul,
    integral_const_mul, ← P.I0_eq_integral, ← P.I4_eq_integral]
  ring

/-- For an even integrable complex function, vanishing of the full integral
forces vanishing of its positive-half integral. -/
private theorem integral_Ioi_zero_of_even_integrable
    (f : ℝ → ℂ) (heven : Function.Even f) (hint : Integrable f)
    (hfull : (∫ x : ℝ, f x) = 0) :
    (∫ x in Ioi (0 : ℝ), f x) = 0 := by
  have hleft : (∫ x in Iic (0 : ℝ), f x) =
      ∫ x in Ioi (0 : ℝ), f x := by
    calc
      (∫ x in Iic (0 : ℝ), f x) =
          ∫ x in Iic (0 : ℝ), f (-x) := by
            apply integral_congr_ae
            filter_upwards with x
            exact (heven x).symm
      _ = ∫ x in Ioi (0 : ℝ), f x := by
        simpa only [neg_zero] using integral_comp_neg_Iic (0 : ℝ) f
  have hsplit : (∫ x : ℝ, f x) =
      (∫ x in Iic (0 : ℝ), f x) + ∫ x in Ioi (0 : ℝ), f x := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Iic_union_Ioi]
    simp
  have htwo : (2 : ℂ) * (∫ x in Ioi (0 : ℝ), f x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in Ioi (0 : ℝ), f x) =
          (∫ x in Iic (0 : ℝ), f x) + ∫ x in Ioi (0 : ℝ), f x := by
            rw [hleft, two_mul]
      _ = ∫ x : ℝ, f x := hsplit.symm
      _ = 0 := hfull
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The positive-half mass of the canonical packet vanishes.  This is the
load-bearing mass certificate for the symmetric Müntz receiver. -/
theorem integral_Ioi_prolateCombination_eq_zero (P : ProlatePair) :
    (∫ x in Ioi (0 : ℝ), prolateCombination P x) = 0 :=
  integral_Ioi_zero_of_even_integrable
    (prolateCombination P) (prolateCombination_even P)
    (prolateCombination_integrable P) (integral_prolateCombination_eq_zero P)

/-- Conditional representation gate from mode-level regularity to exactly the
properties consumed by the symmetric Müntz-v3 theorem.

This theorem does not assert existence of a source prolate pair, denominator
nonvanishing, midpoint endpoint values, `MemLp` for `E_star`, projected-trial
nonvanishing, or any ground/cofinal identification. -/
theorem prolateCombination_muntzRegularity_of_modes
    (P : ProlatePair) (K0 K4 : NNReal)
    (h0meas : Measurable P.h0)
    (h4meas : Measurable P.h4)
    (h0lip : LipschitzOnWith K0 P.h0 (Ico (0 : ℝ) P.pw.lambda))
    (h4lip : LipschitzOnWith K4 P.h4 (Ico (0 : ℝ) P.pw.lambda)) :
    ∃ K : NNReal,
      Function.Even (prolateCombination P) ∧
      Measurable (prolateCombination P) ∧
      (∀ u, u ∉ Icc (-P.pw.lambda) P.pw.lambda →
        prolateCombination P u = 0) ∧
      LipschitzOnWith K (prolateCombination P)
        (Ico (0 : ℝ) P.pw.lambda) ∧
      (∫ u in Ioi (0 : ℝ), prolateCombination P u) = 0 := by
  let a : ℂ := (P.I4 : ℂ) / (P.normalizingDenominator : ℂ)
  let c : ℂ := (P.I0 : ℂ) / (P.normalizingDenominator : ℂ)
  let K : NNReal := ‖a‖₊ * K0 + ‖c‖₊ * K4
  have hformula : ∀ x : ℝ,
      prolateCombination P x = a * P.h0 x - c * P.h4 x := by
    intro x
    simp only [a, c, prolateCombination_apply]
    simp only [div_eq_mul_inv]
    ring
  have hmeas : Measurable (prolateCombination P) := by
    have hnum : Measurable
        (fun x : ℝ => (P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) :=
      (h0meas.const_mul (P.I4 : ℂ)).sub
        (h4meas.const_mul (P.I0 : ℂ))
    simpa only [prolateCombination] using
      hnum.div_const (P.normalizingDenominator : ℂ)
  have hlip : LipschitzOnWith K (prolateCombination P)
      (Ico (0 : ℝ) P.pw.lambda) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hformula x, hformula y, dist_eq_norm]
    calc
      ‖(a * P.h0 x - c * P.h4 x) -
          (a * P.h0 y - c * P.h4 y)‖ =
          ‖a * (P.h0 x - P.h0 y) -
            c * (P.h4 x - P.h4 y)‖ := by
              congr 1
              ring
      _ ≤ ‖a * (P.h0 x - P.h0 y)‖ +
          ‖c * (P.h4 x - P.h4 y)‖ := norm_sub_le _ _
      _ = ‖a‖ * ‖P.h0 x - P.h0 y‖ +
          ‖c‖ * ‖P.h4 x - P.h4 y‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖a‖ * ((K0 : ℝ) * dist x y) +
          ‖c‖ * ((K4 : ℝ) * dist x y) := by
            gcongr
            · simpa [dist_eq_norm] using h0lip.dist_le_mul x hx y hy
            · simpa [dist_eq_norm] using h4lip.dist_le_mul x hx y hy
      _ = (K : ℝ) * dist x y := by
        simp only [K, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm]
        ring
  exact ⟨K, prolateCombination_even P, hmeas,
    prolateCombination_eq_zero_outside P, hlip,
    integral_Ioi_prolateCombination_eq_zero P⟩

#print axioms prolateCombination_even
#print axioms prolateCombination_eq_zero_outside
#print axioms prolateCombination_integrable
#print axioms integral_prolateCombination_eq_zero
#print axioms integral_Ioi_prolateCombination_eq_zero
#print axioms prolateCombination_muntzRegularity_of_modes

end Q3.RouteB.D0Pstar
