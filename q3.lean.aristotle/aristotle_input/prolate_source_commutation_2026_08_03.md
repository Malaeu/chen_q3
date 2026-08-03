# Prolate finite-Fourier / Sturm--Liouville intertwining

## Goal

Produce a hole-free Lean 4.26 proof of the following theorem in the existing
namespace.  Return a complete file importing the indicated project module.

```lean
import Q3.Proofs.RouteB.ProlateSourceRegularity

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

theorem finiteFourierAction_intertwines_prolateWaveExpression
    (lambda : ℝ) (hlambda : 0 < lambda)
    (phi : ℝ → ℂ)
    (hphi : ContDiff ℝ 2 phi) :
    ∀ x : ℝ,
      prolateWaveExpression lambda
          (finiteFourierAction lambda phi) x =
        finiteFourierAction lambda
          (prolateWaveExpression lambda phi) x := by
  -- Supply the proof here.

end Q3.RouteB.D0Pstar
```

## Existing definitions

Use the repository definitions literally.  Do not redeclare or renormalize
them.

```lean
def finiteFourierKernel (x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ))

def finiteFourierAction (lambda : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Icc (-lambda) lambda, finiteFourierKernel x y * h y

def prolateWaveExpression
    (lambda : ℝ)
    (f : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  -fderiv ℝ
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1))
      x 1
    + (((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) * f x
```

The Fourier phase is exactly `exp(+2*pi*i*x*y)`.  Do not introduce a minus
phase, a fitted scalar, a `1 / sqrt (2*pi)` normalization, or a sinc operator.

## Required proof structure

1. Prove the exact pointwise kernel identity saying that the prolate
   differential expression in `x` equals the same expression in `y` when
   applied to `finiteFourierKernel x y`.
2. Justify two derivatives under the interval integral using `hphi` and the
   compact interval.
3. Integrate by parts twice in `y`.
4. Eliminate the boundary terms using
   `lambda ^ 2 - (±lambda) ^ 2 = 0`.
5. Conclude the displayed pointwise intertwining theorem for every real `x`.

The smooth function `phi` is an interior representative.  Do not introduce a
zero extension, midpoint endpoint convention, PSWF existence, eigenvalue,
parity, normalization, or simplicity assertion in this theorem.

## Acceptance policy

- No `sorry`, `admit`, `axiom`, `native_decide`, or `exact?` in the returned
  production proof.
- Do not modify `ProlatePair` or add an eigenrelation as a record field.
- Use only standard Mathlib axioms; expected audit is
  `[propext, Classical.choice, Quot.sound]`.
- Keep any helper lemmas private to the new source-commutation file when
  practical.
- The result must compile with `lake env lean` under Lean/Mathlib 4.26.

## Scope firewall

This is one abstract commutation theorem only.  It does not construct
`sourceProlateH0`/`sourceProlateH4`, discharge D0.7e.5a, authorize Bus 010,
promote Route B, or prove RH.
