import Q3.Proofs.RouteB.G6N1CenterNormalizedUniquenessReceiver

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# The centre of a nontrivial even solution cannot vanish

The provenance card for Meixner–Schäfke §3.22 Satz 1
(`docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md`) records that
the existence theorem supplies five of the six fields of `Satz9SourceData` and
says nothing at all about the sixth, the nonzero centre value. That looked like
an unsourced hypothesis.

It is not a hypothesis. It is a consequence of the other fields:

```
even                  ⟹  the derivative at the centre vanishes
value at centre = 0   ⟹  centre data identical to the zero function
zero function solves the same homogeneous equation
uniqueness            ⟹  the solution is identically zero on the window
```

so a solution that is not identically zero cannot vanish at the centre. The
argument uses only parity, the equation, and nontriviality — never a paper
statement, and never a project object.

Consequence for the seam: the `center_ne` field of `Satz9SourceData` need not be
sourced. An inhabitant that exhibits a nontrivial even solution gets it for
free, which is one of the two gaps the card named.

LEDGER:
  CLOSES: [EVEN_PROLATE_SOLUTION_CENTER_NONVANISHING,
           SATZ9_SOURCE_CENTER_FIELD_UNSOURCED_GAP]
  OPENS:  []
-/

/-- The zero function solves the divergence-form prolate equation at every
separation value.  Stated separately because it is the comparison partner in
the argument below. -/
theorem zero_solves_prolate (lambda theta : ℝ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (0 : ℂ)))
      (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * (0 : ℂ)) x := by
  simpa using (hasDerivAt_const x (0 : ℂ))

/-- **A nontrivial even solution does not vanish at the centre.**

No paper input and no project object enters: the hypotheses are parity, the
equation, and the existence of one point of the open window where the solution
is nonzero. -/
theorem center_ne_zero_of_even_of_nontrivial
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (p dp : ℝ → ℂ)
    (hderiv : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt p (dp x) x)
    (hflux : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dp y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * p x) x)
    (heven : Function.Even p)
    (hnontrivial : ∃ x ∈ Ioo (-lambda) lambda, p x ≠ 0) :
    p 0 ≠ 0 := by
  intro hcenter
  have hzeroMem : (0 : ℝ) ∈ Ioo (-lambda) lambda := by
    constructor <;> linarith
  -- parity kills the derivative at the centre
  have hdp0 : dp 0 = 0 :=
    hasDerivAt_zero_of_even p (dp 0) heven (hderiv 0 hzeroMem)
  -- compare with the zero function, which has the same centre data
  have hEq : EqOn p (fun _ : ℝ ↦ (0 : ℂ)) (Ioo (-lambda) lambda) :=
    complex_prolate_divergence_solution_unique_of_center
      lambda theta hlambda
      p dp (fun _ : ℝ ↦ (0 : ℂ)) (fun _ : ℝ ↦ (0 : ℂ))
      hderiv
      (fun x _ => hasDerivAt_const x (0 : ℂ))
      hflux
      (fun x _ => zero_solves_prolate lambda theta x)
      (by simpa using hcenter)
      (by simpa using hdp0)
  obtain ⟨x, hx, hxne⟩ := hnontrivial
  exact hxne (hEq hx)

/-- The same statement in the contrapositive shape a supplier will want: an
even solution vanishing at the centre is identically zero on the window. -/
theorem eq_zero_of_even_of_center_eq_zero
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (p dp : ℝ → ℂ)
    (hderiv : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt p (dp x) x)
    (hflux : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dp y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * p x) x)
    (heven : Function.Even p)
    (hcenter : p 0 = 0) :
    EqOn p (fun _ : ℝ ↦ (0 : ℂ)) (Ioo (-lambda) lambda) := by
  by_contra hne
  have hnontrivial : ∃ x ∈ Ioo (-lambda) lambda, p x ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (fun x hx => by simpa using hall x hx)
  exact center_ne_zero_of_even_of_nontrivial lambda theta hlambda p dp
    hderiv hflux heven hnontrivial hcenter

#print axioms zero_solves_prolate
#print axioms center_ne_zero_of_even_of_nontrivial
#print axioms eq_zero_of_even_of_center_eq_zero

end Q3.RouteB.D0Pstar
