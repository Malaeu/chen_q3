import Q3.Proofs.RouteB.D0Mode4FerrersCenterValueNonzero
import Q3.Proofs.RouteB.SpheroidalSourceEvenPackage

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB

/-!
# The reverse crosswalk: a project characteristic root is a source eigenvalue

This is the adapter module the integration order (verdict `f414829c`) names as
its third step, and the direction of W13.7B that the reference does **not**
state: from the project's continued-fraction characteristic root to membership
in the source spectrum.

The two sides meet without a single estimate. The project's root-to-solution
bridge produces a Ferrers object whose fields — evenness, continuity on the
closed interval, the two derivative series on the open interval, the exact
shifted equation, and zero endpoint flux — are *literally* the clauses of the
ported source predicate `RegularEvenSpheroidalEigenvalue` at
`G := mode4JacobiG mProject`, with nontriviality supplied by the centre value.
The crosswalk is a repackaging of witnesses, which is precisely what the
category ruling demands of an adapter: it may translate, it may not prove new
analysis or synthesize cargo.

Composed with the inhabited even package, every characteristic root below the
project cutoff is a value of the ordered source branch. That is the reverse
inclusion of the set equality fixed by verdict `d7e6f060`, now with the book's
exhaustiveness carried by the kernel instead of by a typed hole.

The forward direction — a branch value satisfies the DLMF characteristic
equation — is *not* here. It remains the separate paper-locked port, exactly
as the verdict keeps the two provenances apart.

LEDGER:
  CLOSES: [W13_7B_REVERSE_INCLUSION_SOURCE_SIDE]
  OPENS:  []
-/

/-- **A characteristic root is a regular even spheroidal eigenvalue.**  The
Ferrers witness translates clause by clause; no analysis enters. -/
theorem regularEvenSpheroidal_of_mode4Root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    RegularEvenSpheroidalEigenvalue (mode4JacobiG mProject) Λ := by
  obtain ⟨S⟩ :=
    exists_mode4FerrersRegularEvenProlateSolution_of_root
      mProject K Λ hm hK hsep hΛ hroot
  refine ⟨mode4FerrersSeries S.coefficients,
    mode4FerrersFirstDerivativeSeries S.coefficients,
    mode4FerrersSecondDerivativeSeries S.coefficients,
    ⟨0, by norm_num, S.center_value_ne_zero⟩,
    fun x => S.even (-x) |>.symm.trans (by rw [neg_neg]),
    S.continuousOn_closed,
    fun x hx => ⟨S.ferrersSeries_hasDerivAt_firstDerivativeSeries x hx,
      S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx⟩,
    fun x hx => S.prolateDifferentialEquation x hx,
    S.zeroFlux_at_endpoints.1,
    S.zeroFlux_at_endpoints.2⟩

/-- **The reverse inclusion, landed on the ordered branch.**  Every
characteristic root below the cutoff is a value of the source enumeration. -/
theorem mode4Root_mem_evenBranch
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject)) :
    ∃ r : ℕ, P.evenBranch r = Λ :=
  P.regular_evenBranch Λ
    (regularEvenSpheroidal_of_mode4Root mProject K Λ hm hK hsep hΛ hroot)

#print axioms regularEvenSpheroidal_of_mode4Root
#print axioms mode4Root_mem_evenBranch

end Q3.RouteB
