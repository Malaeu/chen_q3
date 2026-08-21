import Q3.Proofs.RouteB.D0CenteredCriticalMoment

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# The critical-moment ratio is exactly a uniform leakage bound

`D0CenteredCriticalMoment.lean` already proves the factorization

```text
centeredCriticalMoment = centeredMomentLeakage * ‖rawFplus 0‖
```

and `rawFplus_zero_ne` gives a strictly positive denominator at every central
index. Those two together make the guarded target and a bare uniform bound on
the leakage quotient **the same statement**, not merely related ones.

This matters for the shape of the remaining obligation, not for its difficulty.
The recorded route to `G5_CRITICAL_MOMENT` treated two things as separate
inputs: an upper bound on the weighted moment, and a uniform lower floor on the
denominator (`SelectedCentralFloor`, itself still an open hole reduced to
`SelectedAnchorRatioData`). The equivalence below shows the floor is not an
input to this particular target at all — it cancels. What remains is one
quantity, the quotient, and the work is to bound it.

⚠️ **This is a restatement and nothing more.** It proves no estimate, removes no
analytic difficulty, and must not be read as progress on the bound itself. Its
only content is that the target has one obligation rather than two, and that the
one it has is scale-free in the coefficient row: numerator and denominator carry
the same factor.

LEDGER:
  CLOSES: []
  OPENS:  []
-/

/-- At a central index the guarded moment bound and the leakage bound are the
same inequality.  The denominator is nonzero there, so it cancels in both
directions. -/
theorem centeredCriticalMoment_le_iff_leakage_le
    (D : CoefficientFamily) (i : CentralIndex D) (σ C : ℝ) :
    centeredCriticalMoment D i.1 σ ≤ C * ‖rawFplus D i.1 0‖
      ↔ centeredMomentLeakage D i σ ≤ C := by
  have hden : (0 : ℝ) < ‖rawFplus D i.1 0‖ :=
    norm_pos_iff.mpr (rawFplus_zero_ne D i)
  rw [centeredMomentLeakage, div_le_iff₀ hden]

/-- The named contract is equivalent to a uniform bound on the leakage
quotient along the same cofinal path, with the same constant and the same
`σ`-range. -/
theorem centeredTrialCriticalMomentRatio_iff_uniform_leakage
    (D : CoefficientFamily) (p : ℕ → CentralIndex D) :
    CenteredTrialCriticalMomentRatio D p
      ↔ PairCofinal p ∧
        ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 →
          ∃ Cσ : ℝ, 0 ≤ Cσ ∧
            ∀ k : ℕ, centeredMomentLeakage D (p k) σ ≤ Cσ := by
  constructor
  · rintro ⟨hcof, h⟩
    refine ⟨hcof, ?_⟩
    intro σ hσ0 hσ2
    obtain ⟨Cσ, hC0, hbound⟩ := h σ hσ0 hσ2
    refine ⟨Cσ, hC0, ?_⟩
    intro k
    exact (centeredCriticalMoment_le_iff_leakage_le D (p k) σ Cσ).mp (hbound k)
  · rintro ⟨hcof, h⟩
    refine ⟨hcof, ?_⟩
    intro σ hσ0 hσ2
    obtain ⟨Cσ, hC0, hbound⟩ := h σ hσ0 hσ2
    refine ⟨Cσ, hC0, ?_⟩
    intro k
    exact (centeredCriticalMoment_le_iff_leakage_le D (p k) σ Cσ).mpr (hbound k)

#print axioms centeredCriticalMoment_le_iff_leakage_le
#print axioms centeredTrialCriticalMomentRatio_iff_uniform_leakage

end Q3.RouteB.D0Pstar
