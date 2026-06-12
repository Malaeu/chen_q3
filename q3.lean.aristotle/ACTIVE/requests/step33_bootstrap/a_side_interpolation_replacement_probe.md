# Experiment Card EC-001 -- A-side interpolation replacement probe

Date: 2026-06-12

Status: planned, monitoring only.  This card does not close Step33, does not
emit payload Lean, and does not change the active route.

## Atlas Anchor

Primary trick: `docs/RH_TRICK_ATLAS.md`, card 2
`Cohn-Kumar-Miller-Radchenko-Viazovska Interpolation`.

Supporting control surface: card 5 `Margin Ledger`.

The useful idea is not to import the CKMRV theorem into Step33.  The useful
idea is the proof pattern: replace many pointwise checks by a finite node/jet
package plus a certified interpolation remainder, while preserving the exact
object required by the active receiver.

## Exact Step33 Target

Active gate:

```text
Step33A.1-A raw-Omega A-side finite/tail bounds certs
```

First probe cell:

```text
family        = primary_finite
row           = 0
parent chunk  = 0
subchunk      = 0
cell          = [0, 1/10]
anchor        = 1/20
worst slack   = 9.127351807129486100E-19
```

Current checked landing surface:

```lean
primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_hRawCenterCoeffAbs_and_deriv_norm_bound
```

It needs exactly:

```lean
hRawCenterCoeffAbs
hResidualDerivBoundOnCell
```

and then lands in:

```lean
RawOmegaATaylorModelCertificate.
  ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
```

which feeds:

```lean
RawOmegaAChunkTaylorPayload.CellSlopeDirectEnvelopeRefinedPayloadFin
  -> RawOmegaAChunkTaylorPayload.RefinedPayloadFin
  -> RawOmegaAChunkIntegralBoundsCert.toDirectTailWindowInputs
```

## Replacement Hypothesis

Try to replace scalar Taylor/interval replay for the first A-side subchunk by a
finite rational interpolation certificate for the residual

```text
r(eta) = rawOmega A integrand(eta) - generated polynomial(eta).
```

The candidate certificate should prove one of these exact current fields:

```lean
∀ eta ∈ Set.Icc L U, ‖deriv cert.residual eta‖ <= derivSlope
```

or, if stronger/easier,

```lean
|rawOmega A integrand anchor - coeff0| <= sampleRadius
```

together with the derivative norm field above.  The receiver must still be the
raw-Omega Step22 A source, not a transformed or centered-nearby surrogate.

## Candidate Lean Shape

First theorem-shaped receiver to test:

```lean
ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound
```

Inputs:

```text
interp : rational polynomial or finite jet model for deriv cert.residual
hInterpError :
  ∀ eta ∈ Set.Icc L U, |deriv cert.residual eta - interp eta| <= err
hInterpBound :
  ∀ eta ∈ Set.Icc L U, |interp eta| <= interpBound
hBudget :
  interpBound + err <= derivSlope
```

Output:

```lean
ResidualDerivativeDirectNormCert.Valid cert derivCert
```

This deliberately keeps the interpolation theorem below the existing compact
direct-norm receiver.  If it works, no Step33 theorem statement changes.

## Local Search Synthesis

- `q3_docs` finds older `HatInterpolation` / `HatInterpBounded` material.  That
  is useful as local interpolation experience, but it is not a Step33 receiver.
- The active Step33 documents point back to the first-cell
  `hRawCenterCoeffAbs + hResidualDerivBoundOnCell` surface and the margin
  ledger worst cell.
- The existing checked helper
  `abs_sub_anchor_le_of_deriv_bound_on_Icc` is already a derivative-bound to
  value-bound bridge; the missing piece is the proof of the derivative bound
  itself, not another envelope wrapper.

External anchors:

- CKMRV reconstruct radial Schwartz functions from discrete values and
  derivatives of a function and its Fourier transform.  This is inspiration
  for finite node/jet compression, not a direct Step33 theorem:
  https://arxiv.org/abs/1902.05438.
- Hermite's interpolation paper is the historical node/derivative model:
  https://eudml.org/doc/148345.
- Mathlib has Taylor remainder infrastructure, so a later Lean proof should
  prefer existing Taylor/remainder APIs where they fit before hand-rolling a
  large analytic theorem:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Taylor.html.

## K3 Danger

The lost-structure risk is concrete:

```text
interpolation of the wrong function, on the wrong node set, or on a transformed
normalization can certify a nearby object while the active raw-Omega A hbox
remains open.
```

A successful card must preserve:

- `step22PositiveAxisOmegaAIntegrand`;
- the exact cell `[0, 1/10]` and anchor `1/20`;
- the raw-center coefficient convention;
- the closed-cell derivative norm field;
- the current `sampleRadius + max 0 derivSlope * mesh <= remainder` budget.

## Success Check

The probe is successful only if it produces a theorem-shaped receiver or a
first-cell Lean stub that:

- has no `axiom`, `sorry`, `admit`, or `exact?`;
- maps to the existing first-cell receiver without changing its statement;
- keeps all numeric nodes and endpoint data rational;
- leaves CSV, `ARadius`, radius-floor, LDL, `Q3.Main`, H1, and PO3 untouched;
- is validated by `lake env lean` and `scripts/q3_check.sh` before any status
  upgrade from planned to checked.

## Failure Check

Mark this card false-for-now if:

- the interpolation error theorem needs the same high-order digamma source
  theorem that already blocks the direct route;
- the interpolation model only fits diagnostic Arb/acb samples;
- the proof lands in a transformed A-side model instead of raw-Omega Step22 A;
- the bound consumes more margin than the current `9.127e-19` worst-cell slack.

## Next Action

Do not scale this to all `2392` cells.  First write or request one tiny
receiver theorem for the first cell:

```text
interpolation error bound + rational polynomial bound
  -> ResidualDerivativeDirectNormCert.Valid
  -> existing first-cell exact-integral proof data
```

Then decide whether the next Aristotle request should target this
interpolation-error lemma or stay on the current high-order digamma source
lemma.
