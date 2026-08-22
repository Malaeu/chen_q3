import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Set Filter Topology MeasureTheory

/-!
# Fixed-parameter even regular spheroidal spectrum, order `m = 0`

This file develops the even, regular spectrum of the (prolate/oblate) spheroidal operator of
order `m = 0`,
`L f = - d/dx ((1 - x^2) f'(x)) - G * (1 - x^2) * f(x)`
on the interval `[-1, 1]`, with the natural (flux) endpoint condition
`(1 - x^2) f'(x) → 0` at both endpoints.
-/

/-- `Λ` is a *regular even spheroidal eigenvalue* for the parameter `G` when there is a nonzero
even function `f` on `[-1,1]`, twice differentiable on `(-1,1)`, solving

`-(1 - x^2) f''(x) + 2 x f'(x) + G x^2 f(x) = (Λ + G) f(x)`,

whose flux `(1 - x^2) f'(x)` tends to `0` at both endpoints.

Non-triviality is expressed as `f` not vanishing identically on `[-1,1]`: the values of `f`
outside `[-1,1]` are not constrained by any of the other conditions. -/
def RegularEvenSpheroidalEigenvalue (G Λ : ℝ) : Prop :=
  ∃ f f1 f2 : ℝ → ℝ,
    (∃ x ∈ Icc (-1 : ℝ) 1, f x ≠ 0) ∧
    (∀ x : ℝ, f (-x) = f x) ∧
    ContinuousOn f (Icc (-1 : ℝ) 1) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x) ∧
    Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
    Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0)
