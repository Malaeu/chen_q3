# Goal 058 G3 — exact finite even-Legendre quadratic form

Work in the supplied Lean project. Create exactly one production file:

`Q3/Proofs/RouteB/D0Mode4FiniteEvenLegendreQuadraticForm.lean`

Use exactly these direct imports:

```lean
import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreGram
import Q3.Proofs.RouteB.D0Mode4LegendreHermitianCoordinateScale
```

In namespace `Q3.RouteB`, define exactly:

```lean
noncomputable def mode4FiniteEvenLegendrePolynomial
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) : ℝ[X] :=
  ∑ q : Fin d,
    Polynomial.C
      (((-1 : ℝ) ^ q.val) *
        mode4DLMFEvenSimilarityScale G q.val * b q) *
      mode4OrdinaryLegendrePolynomial (2 * q.val)
```

Then prove both exact public theorem heads in the same owned file:

```lean
theorem mode4FiniteEvenLegendrePolynomial_l2
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) (hG : 0 < G) :
    (∫ x in (-1 : ℝ)..1,
      (mode4FiniteEvenLegendrePolynomial G b).eval x ^ 2) =
      2 * (b ⬝ᵥ b)

theorem mode4FiniteEvenLegendrePolynomial_energy
    (G Λ : ℝ) {d : ℕ} (b : Fin d → ℝ) (hG : 0 < G) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
          ((mode4FiniteEvenLegendrePolynomial G b).derivative.eval x) ^ 2 +
        G * x ^ 2 *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2 -
        (Λ + G) *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2) =
      2 *
        (b ⬝ᵥ
          (mode4ForwardHermitianFiniteMatrix G Λ d *ᵥ b))
```

## Exact locked suppliers

- `mode4OrdinaryLegendre_even_gram`
- `mode4OrdinaryLegendre_even_derivative_gram`
- `mode4OrdinaryLegendrePolynomial_X_sq_mul`
- `mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight`
- the literal definition of `mode4ForwardHermitianFiniteMatrix`
- ordinary finite sums, polynomial evaluation/derivative algebra, and exact
  interval-integral linearity

The first two suppliers are already kernel-checked in the supplied project.
Do not reprove them and do not use either target theorem as a premise.

## Exact mathematics and required proof order

For

`f_b(x) = sum_{q<d} (-1)^q D_q b_q P_(2q)(x)` with `D_q^2=4q+1`, prove:

1. Expand evaluation of the polynomial finite sum.
2. Expand the square as the double finite sum in `q,r`.
3. Apply the exact even Gram theorem and `D_q^2=4q+1` to prove the L2 head.
4. Expand the derivative part and apply the exact derivative Gram theorem.
5. Expand the `G*x^2` part and use the exact `X^2` action.
6. The `P_(2d)` component from the last retained row must disappear by exact
   Gram orthogonality. Do not add a cutoff correction or endpoint premise.
7. The phase `(-1)^q` must turn neighboring cross terms into the negative
   off-diagonal entries of the literal current Hermitian matrix.
8. Add the `-(Lambda+G)` mass term and assemble exactly
   `2 * (b dot (H * b))`.

Use `D_q`, not its inverse. Without `(-1)^q`, the form represents `J*H*J`
rather than the literal current matrix `H`.

Keep the public surface to the definition and two theorem heads. Private
helpers may cover evaluation expansion, derivative expansion, `X^2` pairing,
last-row orthogonality, and matrix-form assembly.

## Mandatory exact controls and plants

- `d=1, b0=1`: the L2 integral is `2`; deleting factor `2` must fail.
- support only at `q=1`: `D_1^2=5` cancels `integral P_2^2=2/5`;
  deleting the scale must fail.
- `d=2` with both neighboring coefficients nonzero: deleting `(-1)^q`
  must give the wrong off-diagonal sign (`J*H*J`).
- changing `+G*x^2` to `-G*x^2` must fail.
- support at `q=d-1`: folding the `P_(2d)` term into the last row or adding a
  cutoff correction must fail.
- reversing the interval without changing the RHS must fail.

## Forbidden

- `sorry`, `admit`, `exact?`, custom `axiom`, `unsafe`, `native_decide`, or an
  opaque placeholder proof constant;
- numerical quadrature;
- P0 sign or zero-freeness;
- a global minimizer or min-max theorem;
- any regular singular-endpoint solution;
- a classical PSWF zero count or ordered psi0/psi4 identity;
- fields of `Mode4FerrersRegularEvenProlateSolution`.

Allowed axioms after kernel checking are only:
`propext`, `Classical.choice`, `Quot.sound`.

Add `#print axioms` for both public theorems. Do not edit any other file. Do
not prove or state the later P0/min-max leaf. Do not claim Goal 058 G3, Route B,
or RH.

External contract provenance:

- Proshka PRIMARY: `A_FINITE_FORM_BOTH_HEADS`.
- packet SHA-256:
  `7b8ab29dbe27f2c742c44101a50a9c725ed0d54fcca13408a6bf9f08c6d05be8`.
- captured verdict text SHA-256:
  `e384042a5821046fadccfc7f6ee0c100024112f923577af5850b30b500d99fcd`.
- Aristotle scope: `G3_MODE4_FINITE_EVEN_LEGENDRE_QUADRATIC_FORM` only.
- P0/min-max authorization: false.
- commit/push authorization: false.
