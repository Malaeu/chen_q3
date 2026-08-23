import Q3.Proofs.RouteB.G6N1FuchsProjectOperatorIntertwining
import Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.3B — the Fuchs selected eigenvalue defect-rate port

Floor `F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT` of verdict
`b2099885`.

The paper (Fuchs) eigenvalue data stays an explicit typed input: the two
eigenrelations of the paper operator on the rescaled exact selected modes and
the two concentration-defect rates in the paper window unit.  The kernel
content is the exact crosswalk `mu = sqrt(2*pi) * chi`, obtained by comparing
the paper and project eigenrelations at the centre through the exact F72.3A
intertwining and cancelling the nonzero rescaled centre value — never by
defining `mu` to be that product.

The positive Fuchs branch is load-bearing: the concentration value sees only
`chi^2`, which cannot distinguish `chi` from `-chi`.  The private plant
records the refutation of any square-only port.  For the positive branch,
`|1 - chi| ≤ |1 - chi^2|`, and the exact window identity
`paperWindowRadius(lambda)^2 = 2*pi*lambda^2` with `2*pi ≥ 1` converts the
paper `a^(-2)` rate into the project `lambda^(-2)` rate without any fitted
factor.

LEDGER:
  CLOSES: [F72_3_SELECTED_PROJECT_FUCHS_EIGENVALUE_CROSSWALK,
           F72_3B_SELECTED_EIGENVALUE_DEFECT_RATE_PORT]
  OPENS:  []
-/

/-- **The plant.**  A concentration eigenvalue equal to one is compatible
with transform scalar `-1`: the squared crosswalk alone proves nothing about
`|1 - chi|`.  The positive Fuchs phase is load-bearing. -/
private theorem fuchs_positive_branch_guard_plant :
    |1 - ((-1 : ℝ) ^ 2)| = 0 ∧ |1 - (-1 : ℝ)| = 2 := by
  norm_num

private theorem selectedLambda_pos_defectPort (k : ℕ) :
    0 < selectedFerrersPaperLambda k := by
  rw [selectedFerrersPaperLambda]
  apply Real.sqrt_pos.mpr
  positivity

/-- The exact eigenvalue crosswalk at the centre: comparing the paper and
project eigenrelations through the F72.3A intertwining and cancelling the
nonzero rescaled centre value gives `mu = sqrt(2*pi) * chi`. -/
private theorem mu_crosswalk
    (lambda mu chi : ℝ) (h : ℝ → ℂ)
    (hlambda : 0 ≤ lambda)
    (hcenter : h 0 ≠ 0)
    (heigen0 : finiteFourierAction lambda h 0 = (chi : ℂ) * h 0)
    (hFuchs0 : paperFiniteFourierAction (paperWindowRadius lambda)
        (paperRescale h) 0 = (mu : ℂ) * paperRescale h 0) :
    mu = Real.sqrt (2 * Real.pi) * chi := by
  have hint :=
    paperFiniteFourierAction_paperRescale_eq_smul_paperRescale_finiteFourierAction
      lambda hlambda h 0
  rw [hFuchs0] at hint
  have hU1 : paperRescale h 0
      = (((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * h 0 := by
    rw [paperRescale, zero_div]
  have hU2 : paperRescale (finiteFourierAction lambda h) 0
      = (((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * ((chi : ℂ) * h 0) := by
    rw [paperRescale, zero_div, heigen0]
  rw [hU1, hU2] at hint
  have hcne : (((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (by positivity)
  have hz : (((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * h 0 ≠ 0 :=
    mul_ne_zero hcne hcenter
  have hfinal : (mu : ℂ) * ((((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * h 0)
      = ((Real.sqrt (2 * Real.pi) * chi : ℝ) : ℂ) *
          ((((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * h 0) := by
    rw [hint]
    push_cast
    ring
  have hcast := mul_right_cancel₀ hz hfinal
  exact_mod_cast hcast

/-- The positive-branch defect transfer: for a positive project scalar tied
to the paper eigenvalue by the exact square-root crosswalk, the paper
concentration defect in the paper window unit bounds the project scalar
defect in the project window unit. -/
private theorem chi_defect_of_mu
    (lambda mu chi C : ℝ)
    (hlambda : 0 < lambda) (hC : 0 ≤ C)
    (hmupos : 0 < mu)
    (hmu : mu = Real.sqrt (2 * Real.pi) * chi)
    (hdefect : |1 - mu ^ 2 / (2 * Real.pi)| ≤
      C / (paperWindowRadius lambda) ^ 2) :
    |1 - chi| ≤ C / lambda ^ 2 := by
  have hpi := Real.pi_pos
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hchipos : 0 < chi := by
    by_contra hle
    push_neg at hle
    have : mu ≤ 0 := by
      rw [hmu]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hle
    linarith
  have hchi2 : mu ^ 2 / (2 * Real.pi) = chi ^ 2 := by
    rw [hmu, mul_pow, hsq]
    field_simp
  have h1 : |1 - chi| ≤ |1 - chi ^ 2| := by
    have hfact : (1 : ℝ) - chi ^ 2 = (1 - chi) * (1 + chi) := by ring
    rw [hfact, abs_mul]
    have h2 : (1 : ℝ) ≤ |1 + chi| := by
      rw [abs_of_pos (by linarith)]
      linarith
    nlinarith [abs_nonneg (1 - chi)]
  have hwin : (paperWindowRadius lambda) ^ 2 = 2 * Real.pi * lambda ^ 2 := by
    rw [paperWindowRadius, mul_pow, hsq]
  have h3 : C / (paperWindowRadius lambda) ^ 2 ≤ C / lambda ^ 2 := by
    rw [hwin]
    apply div_le_div_of_nonneg_left hC (by positivity)
    nlinarith [Real.pi_gt_three, sq_nonneg lambda]
  calc |1 - chi| ≤ |1 - chi ^ 2| := h1
    _ = |1 - mu ^ 2 / (2 * Real.pi)| := by rw [hchi2]
    _ ≤ C / (paperWindowRadius lambda) ^ 2 := hdefect
    _ ≤ C / lambda ^ 2 := h3

/-- **F72.3B.**  Explicit Fuchs eigenrelations and concentration-defect rates
on the rescaled exact selected modes transfer to a common eventual defect
rate for the project transform scalars, at the project `lambda^(-2)` unit. -/
theorem selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates
    (mu0 mu4 : ℕ → ℝ)
    (C0 C4 : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hmu0pos : ∀ k, 0 < mu0 k)
    (hmu4pos : ∀ k, 0 < mu4 k)
    (hFuchsEigen0 :
      ∀ k t, t ∈ Set.Icc
          (-(paperWindowRadius (selectedFerrersPaperLambda k)))
          (paperWindowRadius (selectedFerrersPaperLambda k)) →
        paperFiniteFourierAction
            (paperWindowRadius (selectedFerrersPaperLambda k))
            (paperRescale (selectedFerrersPreAnchorPair k).h0) t =
          (mu0 k : ℂ) *
            paperRescale (selectedFerrersPreAnchorPair k).h0 t)
    (hFuchsEigen4 :
      ∀ k t, t ∈ Set.Icc
          (-(paperWindowRadius (selectedFerrersPaperLambda k)))
          (paperWindowRadius (selectedFerrersPaperLambda k)) →
        paperFiniteFourierAction
            (paperWindowRadius (selectedFerrersPaperLambda k))
            (paperRescale (selectedFerrersPreAnchorPair k).h4) t =
          (mu4 k : ℂ) *
            paperRescale (selectedFerrersPreAnchorPair k).h4 t)
    (hFuchsDefect0 :
      ∀ᶠ k in Filter.atTop,
        |1 - (mu0 k) ^ 2 / (2 * Real.pi)| ≤
          C0 / (paperWindowRadius (selectedFerrersPaperLambda k)) ^ 2)
    (hFuchsDefect4 :
      ∀ᶠ k in Filter.atTop,
        |1 - (mu4 k) ^ 2 / (2 * Real.pi)| ≤
          C4 / (paperWindowRadius (selectedFerrersPaperLambda k)) ^ 2) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 := by
  refine ⟨C0 + C4, by linarith, ?_⟩
  filter_upwards [hFuchsDefect0, hFuchsDefect4] with k hd0 hd4
  have hlam := selectedLambda_pos_defectPort k
  have hwin0 : (0 : ℝ) ∈ Set.Icc
      (-(paperWindowRadius (selectedFerrersPaperLambda k)))
      (paperWindowRadius (selectedFerrersPaperLambda k)) := by
    have ha : 0 ≤ paperWindowRadius (selectedFerrersPaperLambda k) := by
      rw [paperWindowRadius]
      positivity
    constructor <;> linarith
  have hlameq := selectedFerrersPreAnchorPair_lambda_eq_paperLambda k
  -- mode zero crosswalk
  have heigen0 : finiteFourierAction (selectedFerrersPaperLambda k)
      (selectedFerrersPreAnchorPair k).h0 0 =
        (((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) *
          (selectedFerrersPreAnchorPair k).h0 0 := by
    have hspec := (selectedFerrersPreAnchorPair_spec k).2.2.2.2.2.2.2.1
    have h0mem : (0 : ℝ) ∈ Icc
        (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda := by
      rw [hlameq]
      constructor <;> [linarith [hlam.le]; linarith [hlam.le]]
    have := hspec 0 h0mem
    rwa [hlameq] at this
  have hcenter0 : (selectedFerrersPreAnchorPair k).h0 0 ≠ 0 := by
    have := selectedFerrersCenterZero_ne k
    rwa [selectedFerrersCenterZero] at this
  have hmu0eq := mu_crosswalk (selectedFerrersPaperLambda k) (mu0 k)
    (selectedFerrersPreAnchorPair k).chi0
    (selectedFerrersPreAnchorPair k).h0
    hlam.le hcenter0 heigen0
    (hFuchsEigen0 k 0 hwin0)
  have hchi0 := chi_defect_of_mu (selectedFerrersPaperLambda k) (mu0 k)
    (selectedFerrersPreAnchorPair k).chi0 C0 hlam hC0 (hmu0pos k) hmu0eq hd0
  -- mode four crosswalk
  have heigen4 : finiteFourierAction (selectedFerrersPaperLambda k)
      (selectedFerrersPreAnchorPair k).h4 0 =
        (((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) *
          (selectedFerrersPreAnchorPair k).h4 0 := by
    have hspec := (selectedFerrersPreAnchorPair_spec k).2.2.2.2.2.2.2.2.1
    have h0mem : (0 : ℝ) ∈ Icc
        (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda := by
      rw [hlameq]
      constructor <;> [linarith [hlam.le]; linarith [hlam.le]]
    have := hspec 0 h0mem
    rwa [hlameq] at this
  have hcenter4 : (selectedFerrersPreAnchorPair k).h4 0 ≠ 0 := by
    have := selectedFerrersCenterFour_ne k
    rwa [selectedFerrersCenterFour] at this
  have hmu4eq := mu_crosswalk (selectedFerrersPaperLambda k) (mu4 k)
    (selectedFerrersPreAnchorPair k).chi2
    (selectedFerrersPreAnchorPair k).h4
    hlam.le hcenter4 heigen4
    (hFuchsEigen4 k 0 hwin0)
  have hchi4 := chi_defect_of_mu (selectedFerrersPaperLambda k) (mu4 k)
    (selectedFerrersPreAnchorPair k).chi2 C4 hlam hC4 (hmu4pos k) hmu4eq hd4
  have hmono0 : C0 / (selectedFerrersPaperLambda k) ^ 2
      ≤ (C0 + C4) / (selectedFerrersPaperLambda k) ^ 2 := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    linarith
  have hmono4 : C4 / (selectedFerrersPaperLambda k) ^ 2
      ≤ (C0 + C4) / (selectedFerrersPaperLambda k) ^ 2 := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    linarith
  exact ⟨le_trans hchi0 hmono0, le_trans hchi4 hmono4⟩

#print axioms selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates

end Q3.RouteB.D0Pstar

end
