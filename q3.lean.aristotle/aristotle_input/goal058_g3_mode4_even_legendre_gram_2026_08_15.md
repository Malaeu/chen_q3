# Goal 058 G3 — exact even ordinary-Legendre Gram leaf

Work in the supplied Lean project. Create exactly one production file:

`Q3/Proofs/RouteB/D0Mode4OrdinaryLegendreGram.lean`

Use exactly these direct imports unless Lean itself proves one is redundant:

```lean
import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreXSquaredAction
import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreIntervalBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
```

The second Q3 import is required by the physical current tree: it is the file
that actually exports the two differential-equation suppliers listed below.
Do not assume those names are transitively available from `XSquaredAction`.

Prove these exact public theorem heads in namespace `Q3.RouteB`:

```lean
theorem mode4OrdinaryLegendre_even_gram
    (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      mode4OrdinaryLegendre (2 * q) x *
        mode4OrdinaryLegendre (2 * r) x) =
      if q = r then
        2 / (((4 * q + 1 : ℕ) : ℝ))
      else 0

theorem mode4OrdinaryLegendre_even_derivative_gram
    (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
        (mode4OrdinaryLegendrePolynomial
          (2 * q)).derivative.eval x *
        (mode4OrdinaryLegendrePolynomial
          (2 * r)).derivative.eval x) =
      if q = r then
        (((2 * q : ℕ) : ℝ) *
          (((2 * q + 1 : ℕ) : ℝ))) *
          (2 / (((4 * q + 1 : ℕ) : ℝ)))
      else 0
```

## Exact permitted suppliers already in the project

- `mode4OrdinaryLegendrePolynomial_differentialEquation`
- `mode4OrdinaryLegendre_differentialEquation`
- `mode4OrdinaryLegendrePolynomial_X_sq_mul`
- ordinary polynomial derivative/evaluation identities
- interval-integral FTC and ordinary algebra

The first proof must be universal in `q r`; it must not consume a selected
PSWF, a root, a zero count, a minimizer, a positivity premise, or any field of
`Mode4FerrersRegularEvenProlateSolution`.

Recommended proof order:

1. Prove off-diagonal orthogonality by subtracting the two exact Legendre ODEs
   and integrating the Wronskian derivative.
2. Kill endpoint flux exactly with the factor `1 - x^2`.
3. Prove the diagonal norm from the exact `X^2` action, with base `I_0 = 2`
   and recurrence `I_(q+1) = (4q+1)/(4q+5) * I_q`.
4. Derive the derivative Gram identity by integration by parts and the first
   theorem.

Mandatory exact controls:

- `q=0,r=0`: integral is `2`.
- `q=0,r=1`: integral of `P_0 P_2` is `0`.
- `q=1,r=1`: integral of `P_2^2` is `2/5`.
- the proof must genuinely depend on endpoint flux `1-x^2`; do not replace it
  by `1+x^2`.

Forbidden:

- `sorry`, `admit`, `exact?`, custom `axiom`, `unsafe`, `native_decide`;
- numerical quadrature;
- assuming either Gram identity;
- using the later finite quadratic-form identity to prove this leaf;
- importing a classical PSWF zero count or ordered mode identity;
- opaque placeholder proof constants.

Allowed axioms after kernel checking are only the standard project triple:
`propext`, `Classical.choice`, `Quot.sound`.

Add `#print axioms` for both public theorems. Do not edit any other file. Do
not claim Goal 058 G3, Route B, or RH.

External contract provenance:

- Proshka primary: `A_GRAM_LEAF`.
- Proshka continuation text SHA-256:
  `463a4720b1b55d7b4ead6ac23e16b9ff02cedaba53ff8a6c3ad369caaecf0ca4`.
- Scope authorization: `G3_MODE4_EVEN_LEGENDRE_GRAM` only.
