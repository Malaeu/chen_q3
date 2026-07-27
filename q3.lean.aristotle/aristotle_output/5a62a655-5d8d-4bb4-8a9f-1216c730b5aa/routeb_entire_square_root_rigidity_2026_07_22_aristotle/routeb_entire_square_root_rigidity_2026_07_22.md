# Route B: entire square-root rigidity

Formalize the following theorem in Lean 4 with Mathlib.

```lean
import Mathlib

noncomputable section

namespace Q3.RouteB

/-- Two entire functions with identical pointwise squares differ by one
global sign.  The sign may not vary across zeros. -/
theorem entireSquareRootRigidity
    (F G : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G)
    (hsquare : ∀ z : ℂ, F z * F z = G z * G z) :
    F = G ∨ F = -G := by
  -- Supply a complete kernel-checked proof.

#print axioms entireSquareRootRigidity

end Q3.RouteB
```

Proof route: factor the square identity pointwise as
`(F-G)*(F+G)=0`.  Mathlib already exposes the intended identity-theorem
receiver as
`AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero` in
`Mathlib.Analysis.Analytic.IsolatedZeros`.  Apply it on the preconnected set
`Set.univ` to the analytic functions `F-G` and `F+G`; the conversion from the
input hypotheses is
`Complex.analyticOnNhd_univ_iff_differentiable.mpr`.  Then convert the two
pointwise-zero alternatives into `F=G` or `F=-G` by function extensionality.

Constraints:

- do not introduce any new axiom;
- do not use `sorry`, `admit`, `exact?`, `native_decide`, or
  `@[implemented_by]`;
- keep the exact theorem statement above unless a purely syntactic Mathlib
  normalization is required;
- return a self-contained `.lean` file that compiles with the project toolchain.
- report `SOFT_L2_ENTIRE_SQUARE_ROOT_RIGIDITY_LEAN` only after that build
  succeeds and the axiom print contains only standard Mathlib foundations.

This is one analytic uniqueness component of the Round-12 reconstruction.  It
does not prove existence of an entire square root, Paley--Wiener support, or RH.
