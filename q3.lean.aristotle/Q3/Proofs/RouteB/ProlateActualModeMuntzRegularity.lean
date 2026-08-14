import Q3.Proofs.RouteB.ProlateActualModeSourceLock
import Q3.Proofs.RouteB.ProlateCombinationMuntzRegularity

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Actual prolate modes supply the production Muntz regularity contract

The external source predicate `IsActualProlateModePair` stores the exact
nonzero finite-Fourier eigenrelations for the unchanged production modes.
Those relations make both modes measurable and Lipschitz on the positive
source half-window, so the already proved `prolateCombination` receiver needs
no extra analytic binders once an actual pair has been constructed.

This file proves only that implication.  It does not construct an actual
prolate pair, prove CCM Lemma 7.2, produce a projected denominator floor, or
close Goal 058 G1/G3.
-/

/-- A compactly supported finite-Fourier eigenfunction with nonzero
eigenvalue is measurable.  The proof rewrites the function as the measurable
window indicator of the globally Lipschitz finite-Fourier action. -/
theorem measurable_of_finiteFourier_eigenrelation
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (h : ℝ → ℂ) (chi : ℂ)
    (hchi : chi ≠ 0)
    (hsupp : Function.support h ⊆ Icc (-lambda) lambda)
    (hint : Integrable h)
    (heigen : ∀ x ∈ Icc (-lambda) lambda,
      finiteFourierAction lambda h x = chi * h x) :
    Measurable h := by
  obtain ⟨K, hK⟩ :=
    finiteFourierAction_lipschitzWith
      lambda hlambda h hint.integrableOn
  have haction : Measurable (finiteFourierAction lambda h) :=
    hK.continuous.measurable
  have hformula :
      h = (Icc (-lambda) lambda).indicator
        (fun x => chi⁻¹ * finiteFourierAction lambda h x) := by
    funext x
    by_cases hx : x ∈ Icc (-lambda) lambda
    · rw [indicator_of_mem hx, heigen x hx]
      simp [hchi]
    · have hhx : h x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      rw [indicator_of_notMem hx, hhx]
  rw [hformula]
  exact (haction.const_mul chi⁻¹).indicator measurableSet_Icc

/-- The exact source meaning of an unchanged production `ProlatePair`
supplies the complete regularity package consumed by the symmetric
Müntz-v3 receiver.  No separate measurability or mode-Lipschitz hypotheses
remain. -/
theorem prolateCombination_muntzRegularity_of_actualModes
    (P : ProlatePair)
    (hP : IsActualProlateModePair P) :
    ∃ K : NNReal,
      Function.Even (prolateCombination P) ∧
      Measurable (prolateCombination P) ∧
      (∀ u, u ∉ Icc (-P.pw.lambda) P.pw.lambda →
        prolateCombination P u = 0) ∧
      LipschitzOnWith K (prolateCombination P)
        (Ico (0 : ℝ) P.pw.lambda) ∧
      (∫ u in Ioi (0 : ℝ), prolateCombination P u) = 0 := by
  rcases hP with
    ⟨hlambda, _hI0, _hI4, hchi2, hchi20,
      _hreal0, _hreal4, _hC20, _hC24, _horth,
      _hode, heigen0, heigen4, _hz0finite, _hz0card,
      _hz4finite, _hz4card⟩
  have hchi0pos : 0 < P.chi0 := hchi2.trans hchi20
  have hchi0ne : (P.chi0 : ℂ) ≠ 0 := by
    exact_mod_cast hchi0pos.ne'
  have hchi2ne : (P.chi2 : ℂ) ≠ 0 := by
    exact_mod_cast hchi2.ne'
  have h0meas : Measurable P.h0 :=
    measurable_of_finiteFourier_eigenrelation
      P.pw.lambda hlambda.le P.h0 (P.chi0 : ℂ) hchi0ne
      P.h0_support P.h0_integrable heigen0
  have h4meas : Measurable P.h4 :=
    measurable_of_finiteFourier_eigenrelation
      P.pw.lambda hlambda.le P.h4 (P.chi2 : ℂ) hchi2ne
      P.h4_support P.h4_integrable heigen4
  obtain ⟨K0, h0lip⟩ :=
    positiveHalfLipschitz_of_finiteFourier_eigenrelation
      P.pw.lambda hlambda.le P.h0 (P.chi0 : ℂ) hchi0ne
      P.h0_integrable.integrableOn
      (fun x hx => heigen0 x ⟨by linarith [hlambda, hx.1], hx.2.le⟩)
  obtain ⟨K4, h4lip⟩ :=
    positiveHalfLipschitz_of_finiteFourier_eigenrelation
      P.pw.lambda hlambda.le P.h4 (P.chi2 : ℂ) hchi2ne
      P.h4_integrable.integrableOn
      (fun x hx => heigen4 x ⟨by linarith [hlambda, hx.1], hx.2.le⟩)
  exact prolateCombination_muntzRegularity_of_modes
    P K0 K4 h0meas h4meas h0lip h4lip

/-- An actual degree-zero/degree-four source pair has a strictly positive
normalizing denominator.  This is a source consequence of the positive
integrals, not an extra production assumption. -/
theorem ProlatePair.normalizingDenominator_pos_of_actualModes
    (P : ProlatePair)
    (hP : IsActualProlateModePair P) :
    0 < P.normalizingDenominator := by
  rcases hP with
    ⟨_hlambda, hI0, _hI4, _hchi2, _hchi20,
      _hreal0, _hreal4, _hC20, _hC24, _horth,
      _hode, _heigen0, _heigen4, _hz0finite, _hz0card,
      _hz4finite, _hz4card⟩
  rw [ProlatePair.normalizingDenominator_eq]
  exact Real.sqrt_pos.2 (by
    nlinarith [sq_pos_of_pos hI0, sq_nonneg P.I4])

/-- The exact Sturm zero-count selectors prohibit the canonical two-mode
packet from vanishing identically: the degree-four mode has an interior zero,
whereas the degree-zero mode has none. -/
theorem prolateCombination_ne_zero_of_actualModes
    (P : ProlatePair)
    (hP : IsActualProlateModePair P) :
    prolateCombination P ≠ 0 := by
  have hdenpos : 0 < P.normalizingDenominator :=
    P.normalizingDenominator_pos_of_actualModes hP
  rcases hP with
    ⟨_hlambda, _hI0, hI4, _hchi2, _hchi20,
      _hreal0, _hreal4, _hC20, _hC24, _horth,
      _hode, _heigen0, _heigen4, hz0finite, hz0card,
      hz4finite, hz4card⟩
  have hz4ne : (prolateInteriorZeros P.pw.lambda P.h4).ncard ≠ 0 := by
    omega
  obtain ⟨x, hxint, hx4⟩ :=
    Set.nonempty_of_ncard_ne_zero hz4ne
  intro hzero
  have hvalue := congrFun hzero x
  have hden : (P.normalizingDenominator : ℂ) ≠ 0 := by
    exact_mod_cast hdenpos.ne'
  have hI4ne : (P.I4 : ℂ) ≠ 0 := by
    exact_mod_cast hI4.ne'
  have hx0 : P.h0 x = 0 := by
    rw [prolateCombination_apply, hx4, Pi.zero_apply] at hvalue
    field_simp [hden] at hvalue
    have hmul : (P.I4 : ℂ) * P.h0 x = 0 := by
      simpa using hvalue
    exact (mul_eq_zero.mp hmul).resolve_left hI4ne
  have hx0mem : x ∈ prolateInteriorZeros P.pw.lambda P.h0 :=
    ⟨hxint, hx0⟩
  have hz0empty : prolateInteriorZeros P.pw.lambda P.h0 = ∅ :=
    (Set.ncard_eq_zero hz0finite).mp hz0card
  rw [hz0empty] at hx0mem
  exact hx0mem

#print axioms measurable_of_finiteFourier_eigenrelation
#print axioms prolateCombination_muntzRegularity_of_actualModes
#print axioms ProlatePair.normalizingDenominator_pos_of_actualModes
#print axioms prolateCombination_ne_zero_of_actualModes

end Q3.RouteB.D0Pstar
