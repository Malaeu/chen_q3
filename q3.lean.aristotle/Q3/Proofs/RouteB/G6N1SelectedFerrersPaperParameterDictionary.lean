import Q3.Proofs.RouteB.G6N1SelectedFerrersPreAnchorDataInhabitant
import Q3.Proofs.RouteB.D0Mode4FerrersDimensionlessFourierScaling

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Filter MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.0A — project-side parameter and index dictionary

Floor F72.0A of the L73.2 wall, per the judge's verdict on REQ-2026-08-20-G
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_G_F72_0_SELECTED_FERRERS_PAPER_OBJECT_DICTIONARY_2026-08-20.md`).

Knowledge preflight: `mode4SlepianC` already carries `2 * pi * mProject` on the
shelf, so this file connects the paper-facing names to an existing object
instead of introducing a second bandwidth parameter.

What is proved here is only project-side arithmetic on the precommitted
schedule `k -> (m, N, K) = (k + 2, k + 2, 5 * (k + 2))`:

* the degree law `n = 2 * j`, so carrier index `0, 2` means full degree `0, 4`;
* the window `lambda_k = sqrt (k + 2)`;
* the bandwidth `gamma_k = 2 * pi * lambda_k ^ 2 = 2 * pi * (k + 2)`;
* `gamma_k ^ 2 = mode4JacobiG (k + 2)`, the spectral parameter already used by
  the Ferrers layer;
* `gamma_k = mode4SlepianC (k + 2)`, tying the new name to the existing one;
* the selected pair sits at exactly this window and carries exactly the
  selected Ferrers modes, re-exported from `pair_spec`.

Deliberately absent, per the verdict's forbidden list: no `ps_n` or paper
`h_{n,lambda}` is defined, no statement of the form `project mode = scalar *
ps_n` appears, no Satz 9 or Fuchs hypothesis is assumed, the factor `4` of the
port normalization does not occur, `CCMLemma73PreAnchorPort` is untouched, and
floors F72.1 and F72.3 are not started.

LEDGER:
  CLOSES: [SELECTED_FERRERS_PROJECT_PARAMETER_INDEX_DICTIONARY]
  OPENS:  []
-/

/-- Degree law of the selected carrier: even carrier index `j` names full
spheroidal degree `2 * j`.  Project field `chi2` therefore belongs to full
degree `4`, not to degree `2`. -/
def selectedFerrersPaperDegree (j : ℕ) : ℕ := 2 * j

/-- The window half-width of the precommitted schedule. -/
noncomputable def selectedFerrersPaperLambda (k : ℕ) : ℝ :=
  Real.sqrt ((k + 2 : ℕ) : ℝ)

/-- The paper bandwidth attached to that window. -/
noncomputable def selectedFerrersPaperGamma (k : ℕ) : ℝ :=
  2 * Real.pi * (selectedFerrersPaperLambda k) ^ 2

@[simp] theorem selectedFerrersPaperDegree_zero :
    selectedFerrersPaperDegree 0 = 0 := rfl

@[simp] theorem selectedFerrersPaperDegree_two :
    selectedFerrersPaperDegree 2 = 4 := rfl

/-- The window half-width is nonnegative. -/
theorem selectedFerrersPaperLambda_nonneg (k : ℕ) :
    0 ≤ selectedFerrersPaperLambda k :=
  Real.sqrt_nonneg _

/-- Squaring the window undoes the square root. -/
theorem selectedFerrersPaperLambda_sq (k : ℕ) :
    (selectedFerrersPaperLambda k) ^ 2 = ((k + 2 : ℕ) : ℝ) := by
  rw [selectedFerrersPaperLambda, Real.sq_sqrt]
  positivity

/-- Exact bandwidth of the schedule. -/
theorem selectedFerrersPaperGamma_eq (k : ℕ) :
    selectedFerrersPaperGamma k = 2 * Real.pi * ((k + 2 : ℕ) : ℝ) := by
  rw [selectedFerrersPaperGamma, selectedFerrersPaperLambda_sq]

/-- The new bandwidth name is the existing dimensionless Slepian bandwidth;
no second parameter is introduced. -/
theorem selectedFerrersPaperGamma_eq_slepianC (k : ℕ) :
    selectedFerrersPaperGamma k = mode4SlepianC (k + 2) := by
  rw [selectedFerrersPaperGamma_eq, mode4SlepianC]

/-- The squared bandwidth is exactly the spectral parameter already consumed
by the Ferrers layer. -/
theorem selectedFerrersPaperGamma_sq_eq_jacobiG (k : ℕ) :
    (selectedFerrersPaperGamma k) ^ 2 = mode4JacobiG (k + 2) := by
  rw [selectedFerrersPaperGamma_eq, mode4JacobiG]

/-- The selected pair sits at exactly the window of the schedule. -/
theorem selectedFerrersPreAnchorPair_lambda_eq_paperLambda (k : ℕ) :
    (selectedFerrersPreAnchorPair k).pw.lambda =
      selectedFerrersPaperLambda k :=
  (selectedFerrersPreAnchorPair_spec k).1

/-- Same statement through the data packet. -/
theorem selectedFerrersPreAnchorData_lambda_eq_paperLambda (k : ℕ) :
    (selectedFerrersPreAnchorData.pair k).pw.lambda =
      selectedFerrersPaperLambda k :=
  selectedFerrersPreAnchorPair_lambda_eq_paperLambda k

/-- The window of the schedule is the D0 window of its index. -/
theorem selectedFerrersPaperLambda_eq_lambda_m (k : ℕ) :
    selectedFerrersPaperLambda k =
      lambda_m (selectedFerrersPreAnchorIndex k) := by
  rw [← selectedFerrersPreAnchorPair_lambda_eq_paperLambda]
  exact selectedFerrersPreAnchorPair_lambda_eq k

/-- Carrier index `0` of the packet is the selected mode-zero Ferrers
solution; its full degree is `selectedFerrersPaperDegree 0 = 0`. -/
theorem selectedFerrersPreAnchorPair_h0_eq_selectedMode (k : ℕ) :
    (selectedFerrersPreAnchorPair k).h0 =
      (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode :=
  (selectedFerrersPreAnchorPair_spec k).2.1

/-- Carrier index `2` of the packet is the selected mode-four Ferrers
solution; its full degree is `selectedFerrersPaperDegree 2 = 4`. -/
theorem selectedFerrersPreAnchorPair_h4_eq_selectedMode (k : ℕ) :
    (selectedFerrersPreAnchorPair k).h4 =
      (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode :=
  (selectedFerrersPreAnchorPair_spec k).2.2.1

/-- The two stored finite-Fourier scalars are nonzero.  The one named `chi2`
belongs to full degree four by the degree law above. -/
theorem selectedFerrersPreAnchorPair_chi_ne (k : ℕ) :
    (selectedFerrersPreAnchorPair k).chi0 ≠ 0 ∧
      (selectedFerrersPreAnchorPair k).chi2 ≠ 0 :=
  ⟨(selectedFerrersPreAnchorPair_spec k).2.2.2.2.2.1,
    (selectedFerrersPreAnchorPair_spec k).2.2.2.2.2.2.1⟩

#print axioms selectedFerrersPaperDegree
#print axioms selectedFerrersPaperLambda_sq
#print axioms selectedFerrersPaperGamma_eq
#print axioms selectedFerrersPaperGamma_eq_slepianC
#print axioms selectedFerrersPaperGamma_sq_eq_jacobiG
#print axioms selectedFerrersPreAnchorPair_lambda_eq_paperLambda
#print axioms selectedFerrersPaperLambda_eq_lambda_m
#print axioms selectedFerrersPreAnchorPair_h0_eq_selectedMode
#print axioms selectedFerrersPreAnchorPair_h4_eq_selectedMode
#print axioms selectedFerrersPreAnchorPair_chi_ne

end Q3.RouteB.D0Pstar
