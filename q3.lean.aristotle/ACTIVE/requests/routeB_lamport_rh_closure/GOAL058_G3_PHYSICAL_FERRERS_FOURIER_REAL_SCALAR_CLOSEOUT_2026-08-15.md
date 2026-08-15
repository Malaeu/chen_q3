# Goal 058 G3 — physical Ferrers Fourier real scalar closeout

Date: 2026-08-15

Verdict: `G3_PHYSICAL_FERRERS_FOURIER_REAL_SCALAR_PASS`

## Exact Lean result

The new module
`Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierRealScalar.lean`
proves

`Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_scalar_mul`.

For every accepted regular even Ferrers witness `S`, with only
`2 <= mProject`, it constructs `chi : Real` such that

`finiteFourierAction (sqrt mProject) h x = (chi : Complex) * h x`

for every `x` in the exact closed physical window.  No real scalar or Fourier
relation is supplied as an input.

## Proof architecture

The preceding theorem supplies a complex scalar and the restricted relation.
At `x = 0`, the positive-phase Fourier kernel is exactly one.  The physical
Ferrers source is the complex embedding of a real function, so the Fourier
integral at the center has zero imaginary part.  The accepted
`center_value_ne_zero` theorem makes the source value at the center nonzero.
Taking imaginary parts of the center relation therefore forces
`Complex.im chi = 0`, and `Complex.re chi` is the required real scalar.

## Search and validation

The exact fresh knowledge query

`physical Ferrers finite Fourier scalar real center ratio integral of real-valued source mode4`

returned `no hits` before the write.

Checks:

- direct Lean: PASS;
- named build: PASS, `7780` jobs;
- `q3_check`: PASS;
- diff/forbidden scan: PASS;
- public theorem axioms: only `propext`, `Classical.choice`, `Quot.sound`.

## Boundary and next seam

This leaf proves realness only.  It does not prove `chi != 0`, its sign, or
the ordering of the mode-zero and mode-four scalars.  It does not instantiate
`ProlatePair`, prove the CCM floor, close G1/G3, promote Route B, or make an RH
claim.

Next exact seam: compact-support Fourier analytic continuation plus existing
Fourier inversion nonvanishing, yielding `chi != 0` without adding a source
assumption.  Sign/order remains a separate primary-source spectral step.

Stop code:

`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_REAL_SCALAR_PROVED_NONZERO_SIGN_ORDER_AND_PROLATEPAIR_NEXT`
