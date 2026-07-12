# H2b2b2b2 quotient-by-radical metric and symmetric operator

Date: 2026-07-12
Transaction: Route B revision 40
Status: `GENERIC CORE PROVED / EXACT WEIL RADICAL-METRIC CROSSWALK OPEN / NOT_RH`

## Scope

Let `B` be a symmetric positive-semidefinite real bilinear form.  Quotienting
by `ker B` produces a well-defined positive-definite bilinear form.  Any
endomorphism symmetric for `B` preserves `ker B`, descends to the quotient,
and remains symmetric for the quotient form.

This is the universal modified-Hilbert-space mechanism.  It does not assert
that the exact Route B Weil form is positive, that its radical is the
calibration line, or that the resulting quotient objects are the source's
named matrix/operator.

## Lean result

`Q3/Proofs/RouteB/QuotientByRadicalSelfAdjoint.lean` defines and proves:

- `quotientRadicalRight` and `quotientByRadicalForm`;
- `quotientByRadicalForm_mk_mk`;
- `quotientByRadicalForm_nonneg`;
- `quotientByRadicalForm_definite`;
- `maps_ker_of_bilinForm_selfAdjoint`;
- `quotientByRadicalEnd` and `quotientByRadicalEnd_mk`;
- `quotientByRadicalEnd_isSelfAdjoint`.

The form is built by two `Submodule.liftQ` applications; the operator uses
`Submodule.mapQ`.  Positive definiteness uses the positive-semidefinite
Cauchy--Schwarz equality characterization already available for bilinear
forms.  Direct `lake env lean` validation is hole-free.  The printed axiom set
is only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

H2b2b2b2b must still instantiate the generic core with the exact Route B form
and correction.  In particular it must prove `T >= 0`, identify
`ker(B_T)=span{xi}`, transport the quotient to the source modified-Hilbert
object, and retain the exact removable factor, complement determinant,
nonvanishing phase, all-z identity and same-family crosswalk.  None of these is
inferred from weighted symmetry alone.

## DAG transaction

```text
H2b2b2b2  ExactRemovableFactorRouteInstantiation       OPEN
|-- H2b2b2b2.0 DecompositionContract                    PROVED
|-- H2b2b2b2a GenericQuotientRadicalMetricCore          PROVED / LEAN
|-- H2b2b2b2b ExactWeilRadicalMetricRouteInstantiation  OPEN / INELIGIBLE
`-- H2b2b2b2c ExactQuotientMetricAssembly               OPEN / INELIGIBLE
```

H2b2b2b, H2b2b2, H2b2b, H2b2, H2b and H2 remain
OPEN/CONDITIONAL.  D0.7e.5a remains the unique active leaf, Bus 010 is absent,
and Route B remains `CHALLENGER / NOT_RH`.

## Verdict

`H2B2B2_GENERIC_QUOTIENT_RADICAL_METRIC_SELFADJOINT_LEAN`
