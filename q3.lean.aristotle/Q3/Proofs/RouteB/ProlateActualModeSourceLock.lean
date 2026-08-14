import Q3.Proofs.RouteB.ProlateSourceRegularity

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Actual prolate-mode source lock

`ProlatePair` is the unchanged production data carrier.  It intentionally
stores only facts already consumed downstream, so inhabiting that record is
not evidence that its functions are the source degree-0/degree-4 prolate
modes.  This file adds an external predicate which states that missing source
meaning and a permanent plant showing that the bare record is strictly
weaker.
-/

/-- Interior zeros used to source-lock the Sturm--Liouville indices. -/
def prolateInteriorZeros (lambda : ℝ) (h : ℝ → ℂ) : Set ℝ :=
  {x | x ∈ Ioo (-lambda) lambda ∧ h x = 0}

/-- Source meaning of the production degree-0/degree-4 prolate pair.

The predicate is external to `ProlatePair`: downstream production types stay
unchanged.  It records the literal differential and restricted finite-Fourier
eigenrelations, the positive phase convention, orthogonality, and the exact
Sturm zero-count selectors `0` and `4`.

Source locks:
* `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:45-75,232-267`;
* `ACTIVE/requests/routeB_lamport_rh_closure/
  PSWF_STURM_LIOUVILLE_SOURCE_DOSSIER.md:175-225`;
* Slepian--Pollak (1961), equations (23)--(28), pinned scan
  `docs/routeB_bus/litreview/pdfs/bstj40-1-43_text.pdf`.

This definition asserts no existence theorem. -/
def IsActualProlateModePair (P : ProlatePair) : Prop :=
  0 < P.pw.lambda ∧
  0 < P.I0 ∧ 0 < P.I4 ∧
  0 < P.chi2 ∧ P.chi2 < P.chi0 ∧
  (∫ x : ℝ, starRingEnd ℂ (P.h0 x) * P.h4 x) = 0 ∧
  (∃ theta0 theta4 : ℝ,
    theta0 < theta4 ∧
    (∀ x ∈ Ioo (-P.pw.lambda) P.pw.lambda,
      prolateWaveExpression P.pw.lambda P.h0 x =
        (theta0 : ℂ) * P.h0 x) ∧
    (∀ x ∈ Ioo (-P.pw.lambda) P.pw.lambda,
      prolateWaveExpression P.pw.lambda P.h4 x =
        (theta4 : ℂ) * P.h4 x)) ∧
  (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
    finiteFourierAction P.pw.lambda P.h0 x =
      (P.chi0 : ℂ) * P.h0 x) ∧
  (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
    finiteFourierAction P.pw.lambda P.h4 x =
      (P.chi2 : ℂ) * P.h4 x) ∧
  (prolateInteriorZeros P.pw.lambda P.h0).Finite ∧
  (prolateInteriorZeros P.pw.lambda P.h0).ncard = 0 ∧
  (prolateInteriorZeros P.pw.lambda P.h4).Finite ∧
  (prolateInteriorZeros P.pw.lambda P.h4).ncard = 4

/-- A normalized even compactly-supported function used only to demonstrate
that non-mode pairs can inhabit the old record surface. -/
def looseProlateIndicator (x : ℝ) : ℂ :=
  (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun _ => (1 : ℂ)) x

private theorem looseProlateIndicator_even :
    Function.Even looseProlateIndicator := by
  intro x
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
  · have hnx : -x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [looseProlateIndicator, looseProlateIndicator,
      indicator_of_mem hnx, indicator_of_mem hx]
  · have hnx : -x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      intro h
      exact hx ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [looseProlateIndicator, looseProlateIndicator,
      indicator_of_notMem hnx, indicator_of_notMem hx]

private theorem looseProlateIndicator_support :
    Function.support looseProlateIndicator ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  have hinner : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    by_contra hnot
    have hz : looseProlateIndicator x = 0 := by
      rw [looseProlateIndicator, indicator_of_notMem hnot]
    exact hx hz
  constructor <;> linarith [hinner.1, hinner.2]

private theorem looseProlateIndicator_integrable :
    Integrable looseProlateIndicator := by
  exact ((integrableOn_const (μ := volume) (C := (1 : ℂ))
    isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)

private theorem looseProlateIndicator_sqNorm_integrable :
    Integrable (fun x : ℝ => ‖looseProlateIndicator x‖ ^ 2) := by
  have hfun : (fun x : ℝ => ‖looseProlateIndicator x‖ ^ 2) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
    · rw [looseProlateIndicator, indicator_of_mem hx,
        indicator_of_mem hx]
      norm_num
    · rw [looseProlateIndicator, indicator_of_notMem hx,
        indicator_of_notMem hx]
      norm_num
  rw [hfun]
  exact ((integrableOn_const (μ := volume)
    (s := Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (C := (1 : ℝ)) isCompact_Icc.measure_ne_top).integrable_indicator
      measurableSet_Icc)

private theorem integral_looseProlateIndicator :
    (∫ x : ℝ, looseProlateIndicator x) = 1 := by
  unfold looseProlateIndicator
  rw [integral_indicator_const (μ := volume) (1 : ℂ) measurableSet_Icc]
  norm_num [Measure.real, Real.volume_Icc]

private theorem integral_sqNorm_looseProlateIndicator :
    (∫ x : ℝ, ‖looseProlateIndicator x‖ ^ 2) = 1 := by
  have hfun : (fun x : ℝ => ‖looseProlateIndicator x‖ ^ 2) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) <;>
      simp only [looseProlateIndicator]
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      norm_num
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      norm_num
  rw [hfun, integral_indicator_const (μ := volume) (1 : ℝ) measurableSet_Icc]
  norm_num [Measure.real, Real.volume_Icc]

/-- Permanent weak-record plant: both stored candidates are the same
normalized interval indicator.  It satisfies every field of `ProlatePair`,
but it is not an actual degree-0/degree-4 source pair. -/
def looseProlatePairPlant : ProlatePair where
  pw := {
    lambda := 1
    action := prolateWaveExpression 1
    action_eq := rfl }
  h0 := looseProlateIndicator
  h4 := looseProlateIndicator
  chi0 := 1
  chi2 := 1
  I0 := 1
  I4 := 1
  h0_even := looseProlateIndicator_even
  h4_even := looseProlateIndicator_even
  h0_support := looseProlateIndicator_support
  h4_support := looseProlateIndicator_support
  h0_integrable := looseProlateIndicator_integrable
  h4_integrable := looseProlateIndicator_integrable
  h0_sqNorm_integrable := looseProlateIndicator_sqNorm_integrable
  h4_sqNorm_integrable := looseProlateIndicator_sqNorm_integrable
  h0_normalized := integral_sqNorm_looseProlateIndicator
  h4_normalized := integral_sqNorm_looseProlateIndicator
  I0_eq_integral := by
    norm_num [integral_looseProlateIndicator]
  I4_eq_integral := by
    norm_num [integral_looseProlateIndicator]
  h0_fourier_center := by
    norm_num [looseProlateIndicator]
  h4_fourier_center := by
    norm_num [looseProlateIndicator]

/-- Kernel-checked discriminator: record inhabitation is not actual-mode
construction.  The plant already violates the source eigenvalue ordering. -/
theorem looseProlatePairPlant_not_actual :
    ¬ IsActualProlateModePair looseProlatePairPlant := by
  intro h
  exact (lt_irrefl (1 : ℝ)) (by simpa [IsActualProlateModePair,
    looseProlatePairPlant] using h.2.2.2.2)

#print axioms IsActualProlateModePair
#print axioms looseProlatePairPlant
#print axioms looseProlatePairPlant_not_actual

end Q3.RouteB.D0Pstar
