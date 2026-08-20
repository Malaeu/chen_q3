import Q3.Proofs.RouteB.G6N1ParabolicCylinderD0D4Exact
import Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
import Q3.Proofs.RouteB.D0Mode4FerrersNormalizedZeroCountTransport
import Q3.Proofs.RouteB.D0Mode4FerrersNormalizedActualModeLocalFields

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.0B1 — the center-anchor scalar lock

Floor F72.0B1 of the L73.2 wall, `NEXT_EXECUTABLE_NODE` at cost 1/10 in the
judge's REQ-2026-08-20-J verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_J_F72_0B_CENTER_ANCHORED_DIRECT_CYLINDER_RATE_2026-08-20.md`),
which selected representation R2, the center-anchored direct cylinder rate.

The point of anchoring at the center is that it makes the transfer scalar
**source-derived and precommitted** rather than fitted. The two cylinder
targets already have known center values, proved in
`G6N1ParabolicCylinderD0D4Exact.lean`:

```
D_0(sqrt (4 pi) * 0) = 1        D_4(sqrt (4 pi) * 0) = 3
```

so the only scalar that can possibly send a selected mode onto its target is
the one that matches those centers. It is defined here, before any rate is
stated, which is the C09 precommit firewall; and it is read off the source
rather than chosen to minimise an observed error, which is the C10 firewall.
The judge names both kills explicitly: `c10_kill:
SOURCE_REPRESENTATIVE_DEFINED_BY_PROJECT_TARGET`, `c09_kill:
SCALAR_FITTED_AFTER_ERROR_INSPECTION`.

This file proves only the lock: the centers are nonzero, the scalars are
therefore well defined and nonzero, and they do send the centers to `1` and
`3`. No rate, no asymptotics, no source bind.

LEDGER:
  CLOSES: [F72_0B1_CENTER_ANCHOR_SCALAR_LOCK]
  OPENS:  []
-/

/-- The mode-zero center value of the selected pair at index `k`. -/
noncomputable def selectedFerrersCenterZero (k : ℕ) : ℂ :=
  (selectedFerrersPreAnchorPair k).h0 0

/-- The mode-four center value of the selected pair at index `k`. -/
noncomputable def selectedFerrersCenterFour (k : ℕ) : ℂ :=
  (selectedFerrersPreAnchorPair k).h4 0

theorem selectedFerrersCenterZero_ne (k : ℕ) :
    selectedFerrersCenterZero k ≠ 0 := by
  rw [selectedFerrersCenterZero, (selectedFerrersPreAnchorPair_spec k).2.1]
  exact normalizedPhysicalMode_zero_ne (selectedFerrersPreAnchorSolution0 k)
    (by omega)

theorem selectedFerrersCenterFour_ne (k : ℕ) :
    selectedFerrersCenterFour k ≠ 0 := by
  rw [selectedFerrersCenterFour, (selectedFerrersPreAnchorPair_spec k).2.2.1]
  exact normalizedPhysicalMode_zero_ne (selectedFerrersPreAnchorSolution4 k)
    (by omega)

/-- Both center values are real: the selected modes are real-valued, so the
anchoring scalars below are real too. -/
theorem selectedFerrersCenterZero_im (k : ℕ) :
    (selectedFerrersCenterZero k).im = 0 := by
  rw [selectedFerrersCenterZero, (selectedFerrersPreAnchorPair_spec k).2.1]
  exact normalizedPhysicalMode_im_eq_zero (selectedFerrersPreAnchorSolution0 k) 0

theorem selectedFerrersCenterFour_im (k : ℕ) :
    (selectedFerrersCenterFour k).im = 0 := by
  rw [selectedFerrersCenterFour, (selectedFerrersPreAnchorPair_spec k).2.2.1]
  exact normalizedPhysicalMode_im_eq_zero (selectedFerrersPreAnchorSolution4 k) 0

/-- The mode-zero anchoring scalar, fixed by the target center `D_0(0) = 1`. -/
noncomputable def centerAnchorScalarZero (k : ℕ) : ℂ :=
  1 / selectedFerrersCenterZero k

/-- The mode-four anchoring scalar, fixed by the target center `D_4(0) = 3`. -/
noncomputable def centerAnchorScalarFour (k : ℕ) : ℂ :=
  3 / selectedFerrersCenterFour k

theorem centerAnchorScalarZero_ne (k : ℕ) :
    centerAnchorScalarZero k ≠ 0 :=
  div_ne_zero one_ne_zero (selectedFerrersCenterZero_ne k)

theorem centerAnchorScalarFour_ne (k : ℕ) :
    centerAnchorScalarFour k ≠ 0 :=
  div_ne_zero three_ne_zero (selectedFerrersCenterFour_ne k)

/-- The lock at mode zero: the anchored center hits the target center. -/
theorem centerAnchorScalarZero_mul_center (k : ℕ) :
    centerAnchorScalarZero k * selectedFerrersCenterZero k = 1 := by
  rw [centerAnchorScalarZero, one_div,
    inv_mul_cancel₀ (selectedFerrersCenterZero_ne k)]

/-- The lock at mode four: the anchored center hits the target center. -/
theorem centerAnchorScalarFour_mul_center (k : ℕ) :
    centerAnchorScalarFour k * selectedFerrersCenterFour k = 3 := by
  rw [centerAnchorScalarFour, div_mul_cancel₀]
  exact selectedFerrersCenterFour_ne k

/-- The two target centers, restated from the cylinder file so that the lock
reads as one statement: the anchored source centers equal the cylinder centers
at the project argument. -/
theorem cylinder_centers :
    parabolicCylinderD 0 (projectCylinderArgument 0) = 1 ∧
      parabolicCylinderD 4 (projectCylinderArgument 0) = 3 := by
  constructor
  · rw [parabolicCylinderD_zero_projectArgument]
    simp
  · rw [parabolicCylinderD_four_projectArgument]
    simp

/-- The lock in the form the next floor consumes: at the center, the anchored
selected modes agree with their cylinder targets. -/
theorem centerAnchor_matches_cylinder_centers (k : ℕ) :
    centerAnchorScalarZero k * selectedFerrersCenterZero k =
        ((parabolicCylinderD 0 (projectCylinderArgument 0) : ℝ) : ℂ) ∧
      centerAnchorScalarFour k * selectedFerrersCenterFour k =
        ((parabolicCylinderD 4 (projectCylinderArgument 0) : ℝ) : ℂ) := by
  obtain ⟨h0, h4⟩ := cylinder_centers
  constructor
  · rw [centerAnchorScalarZero_mul_center, h0]
    norm_num
  · rw [centerAnchorScalarFour_mul_center, h4]
    norm_num

#print axioms selectedFerrersCenterZero_ne
#print axioms selectedFerrersCenterFour_ne
#print axioms selectedFerrersCenterZero_im
#print axioms selectedFerrersCenterFour_im
#print axioms centerAnchorScalarZero_ne
#print axioms centerAnchorScalarFour_ne
#print axioms centerAnchorScalarZero_mul_center
#print axioms centerAnchorScalarFour_mul_center
#print axioms cylinder_centers
#print axioms centerAnchor_matches_cylinder_centers

end Q3.RouteB.D0Pstar
