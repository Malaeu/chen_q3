# Fixed-parameter even regular spheroidal spectrum, order m = 0

## Goal

Formalize in Lean 4 with **only** `import Mathlib` the source-pure theorem below.
Do not import Q3 and do not introduce any axiom, constant, opaque theorem,
`sorry`, or `admit`.

For fixed real numbers `G` and `Λ`, call `Λ` a regular-even spheroidal
eigenvalue if there exist real functions `f`, `f1`, and `f2` such that:

1. `f` is not the zero function;
2. `f` is even;
3. `f` is continuous on `Set.Icc (-1) 1`;
4. for every `x ∈ Set.Ioo (-1) 1`,
   `HasDerivAt f (f1 x) x` and `HasDerivAt f1 (f2 x) x`;
5. for every `x ∈ Set.Ioo (-1) 1`,

   `-(1 - x^2) * f2 x + 2*x*f1 x + G*x^2*f x = (Λ + G)*f x`;

6. the natural flux tends to zero at both endpoints:

   `(1-x^2) * f1 x → 0` as `x → 1` from the left, and
   `(1-x^2) * f1 x → 0` as `x → -1` from the right.

The displayed ODE is equivalently

`- d/dx ((1-x^2) f'(x)) - G*(1-x^2)*f(x) = Λ*f(x)`.

Prove:

```lean
∀ G : ℝ, ∃ μ : ℕ → ℝ,
  StrictMono μ ∧
  Set.range μ = {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ}
```

You may choose an equivalent Lean definition of
`RegularEvenSpheroidalEigenvalue`, but it must preserve the exact endpoint,
evenness, differentiability, and ODE quantifiers above.

## Ordered milestones

Prove and name intermediate lemmas in this order so that a partial result can be
harvested:

1. the exact Green/Lagrange or Wronskian identity with the degenerate coefficient
   `1-x^2`, including the actual endpoint limits;
2. one-dimensionality of a regular even eigenspace at a fixed eigenvalue;
3. a lower-bounded self-adjoint even-sector realization with discrete exhaustive
   spectrum, or a fully proved equivalent ODE theorem;
4. the final `StrictMono` sequence and exact range equality.

The final theorem is the goal. Milestones 1 and 2 are useful partial results but
do not count as completion.

## Mandatory semantic controls

- At `G = 0`, `f(x)=1` is an even regular eigenfunction with `Λ=0`.
- At `G = 0`, `f(x)=x` has `Λ=2` but is odd and must not enter the even spectrum.
- At `G = 0`, `(3*x^2-1)/2` is even regular with `Λ=6`.
- A logarithmically singular Legendre second-kind solution must be excluded by
  endpoint regularity.

These controls fix the sign, the `Λ` versus `Λ+G` shift, parity, and the endpoint
class.

## Forbidden shortcuts

- Do not replace `[-1,1]` by `[-1+ε,1-ε]` without proving the endpoint limit.
- Do not apply a regular Sturm–Liouville theorem requiring a strictly positive
  leading coefficient on the closed interval.
- Do not assume compact resolvent, discreteness, exhaustiveness, or simplicity.
- Do not replace the theorem by finite matrices, finite Legendre truncations, or
  numerical evidence.
- Do not construct unused odd branch values by interpolation.
- Do not use any project definition or project theorem.

Any Mathlib theorem you use may be discovered during the proof, but it must
exist in the pinned environment and its hypotheses must be instantiated
explicitly for this singular endpoint problem.
