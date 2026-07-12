# H2b2b2 rank-one quotient descent

Date: 2026-07-12
Transaction: Route B revision 38
Status: `GENERIC CORE PROVED / EXACT RADICAL-METRIC INSTANTIATION OPEN / NOT_RH`

## Scope

If a linear endomorphism `f` kills a vector `xi`, it maps the line
`span{xi}` into itself and therefore induces an endomorphism of
`E / span{xi}`.  Applying this universal fact to the normalized rank-one
correction gives a quotient operator because the correction already satisfies
`D' xi = 0`.

## Lean result

`Q3/Proofs/RouteB/RankOneCorrectionQuotientDescent.lean` defines and proves:

- `quotientSpanSingletonEnd`;
- `quotientSpanSingletonEnd_mk`;
- `rankOneCorrectionQuotientEnd`;
- `rankOneCorrectionQuotientEnd_mk`.

The construction uses Mathlib `Submodule.mapQ`.  Direct `lake env lean`
validation is hole-free.  The printed axiom set is only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact boundary

This quotient is purely algebraic.  It does not prove that the radical of the
exact Weil matrix is precisely `span{xi}`, that the matrix is positive, that
the quotient carries the source modified-Hilbert metric, or that the induced
operator is self-adjoint in that metric.  It also does not close the spectral-
point extension, complement determinant, phase or all-z factorization.  Those
inputs remain in H2b2b2b under
`H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`.

## DAG transaction

```text
H2b2b2  ExactQuotientLatticeAllZInstantiation      OPEN
|-- H2b2b2.0 DecompositionContract                 PROVED
|-- H2b2b2a GenericQuotientDescent                 PROVED / LEAN
|-- H2b2b2b ExactRadicalMetricLatticeInstantiation OPEN / INELIGIBLE
`-- H2b2b2c ExactQuotientAllZAssembly              OPEN / INELIGIBLE
```

H2b2b, H2b2, H2b and H2 remain OPEN/CONDITIONAL as before.  D0.7e.5a remains
the unique active leaf, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.

## Verdict

`H2B2B2_GENERIC_RANK_ONE_QUOTIENT_DESCENT_LEAN`
