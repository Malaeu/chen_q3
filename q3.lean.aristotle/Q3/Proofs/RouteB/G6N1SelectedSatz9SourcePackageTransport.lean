import Q3.Proofs.RouteB.G6N1SpheroidalSourcePhysicalLift
import Q3.Proofs.RouteB.G6N1FiniteLimitSelectedThetaModularBind
import Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Q3.RouteB

/-!
# Selected Satz-9 source package transport

Floor `SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT` of verdict `de86b9bc`.

A mechanical rewrite, not new analysis: take an arbitrary source-pure even
package `P`, pull its two regular eigenvalues at ordinals `0` and `2` (V3.2
already ties these to the project carrier, so no project mode enters as a
source witness), lift each through the ratified physical lift at the exact
selected-schedule window, and rewrite the resulting separation values to the
project carrier plus the shared parameter shift, using the exact parameter
dictionary identity `selectedFerrersPaperGamma_sq_eq_jacobiG`.

`Satz9SourceData` is consumed only as a receiver payload; no Ferrers/project
mode is ever substituted as the source witness, and no Satz-9 rate is
claimed.

LEDGER:
  CLOSES: [W13_7E_SELECTED_THETA_PACKAGE_TRANSPORT,
           SELECTED_SOURCE_PHYSICAL_DATA_AT_PROJECT_THETA]
  OPENS:  []
-/

/-- **The transport.**  For every source-pure even package `P` at the
selected-schedule bandwidth, the physical receiver payload exists at the
project theta values for degrees zero and four. -/
theorem selectedSatz9SourceData_at_projectTheta_degree_zero_four
    (k : ℕ)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG (k + 2))) :
    Nonempty
        (D0Pstar.Satz9SourceData
          (D0Pstar.selectedFerrersPaperLambda k)
          (mode4ClassicalEvenEigenvalue
              (mode4JacobiG (k + 2)) 0 +
            mode4JacobiG (k + 2))) ∧
      Nonempty
        (D0Pstar.Satz9SourceData
          (D0Pstar.selectedFerrersPaperLambda k)
          (mode4ClassicalEvenEigenvalue
              (mode4JacobiG (k + 2)) 2 +
            mode4JacobiG (k + 2))) := by
  have hlambda : 0 < D0Pstar.selectedFerrersPaperLambda k := by
    rw [D0Pstar.selectedFerrersPaperLambda]
    apply Real.sqrt_pos.mpr
    positivity
  have hGeq :
      (2 * Real.pi * (D0Pstar.selectedFerrersPaperLambda k) ^ 2) ^ 2
        = mode4JacobiG (k + 2) := by
    have := D0Pstar.selectedFerrersPaperGamma_sq_eq_jacobiG k
    rwa [D0Pstar.selectedFerrersPaperGamma] at this
  have hrank :=
    finiteLimit_selected_theta_equality_degree_zero_four_modular
      (k + 2) (5 * (k + 2)) (by omega) (by omega)
      (D0Pstar.selectedFerrersPreAnchorSeparation k) P
  refine ⟨?_, ?_⟩
  · have hreg0 : RegularEvenSpheroidalEigenvalue
        (mode4JacobiG (k + 2)) (P.evenBranch 0) := P.evenBranch_regular 0
    generalize hL0 : P.evenBranch 0 = L0 at hreg0
    rw [← hGeq] at hreg0
    have hpayload := regularEvenSpheroidalEigenvalue_physicalSatz9SourceData
      hlambda hreg0
    rw [hGeq] at hpayload
    have hL0full : mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 = L0 :=
      hrank.1.trans hL0
    rwa [hL0full]
  · have hreg0 : RegularEvenSpheroidalEigenvalue
        (mode4JacobiG (k + 2)) (P.evenBranch 2) := P.evenBranch_regular 2
    generalize hL2 : P.evenBranch 2 = L2 at hreg0
    rw [← hGeq] at hreg0
    have hpayload := regularEvenSpheroidalEigenvalue_physicalSatz9SourceData
      hlambda hreg0
    rw [hGeq] at hpayload
    have hL2full : mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 = L2 :=
      hrank.2.trans hL2
    rwa [hL2full]

#print axioms selectedSatz9SourceData_at_projectTheta_degree_zero_four

end Q3.RouteB
