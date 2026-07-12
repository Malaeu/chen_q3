# H2b2b2b all-spectral-point determinant extension

Date: 2026-07-12
Transaction: Route B revision 39
Status: `GENERIC CORE PROVED / EXACT REMOVABLE FACTOR INSTANTIATION OPEN / NOT_RH`

## Scope

The inverse form of the matrix determinant lemma used in revision 37 requires
`det(A)` to be a unit.  The adjugate identity

```text
det(A + u v^T) = det(A) + v^T adj(A) u
```

holds over every commutative ring and at singular matrices.  Applied to the
Route B rank-one correction with `A = D - sI`, it therefore gives a polynomial
identity at every spectral parameter `s`, including spectral/lattice points.
A second generic theorem records the complementary analytic mechanism: two
continuous complex-valued functions that agree away from a finite exceptional
set agree everywhere.

## Lean result

`Q3/Proofs/RouteB/RankOneCorrectionAllSpectralPoints.lean` proves:

- `det_add_vecMulVec_adjugate`;
- `det_rankOneCorrection_sub_smul_one_all`;
- `continuous_eq_of_eq_off_finite`.

The adjugate formula is proved directly by finite-column multilinearity and
Cramer's rule; it does not divide by `det(A)`.  Direct `lake env lean`
validation is hole-free.  The printed axiom set is only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact boundary

The generic core does not identify the exact Weil matrix `T`, prove its
positivity or `rad(T)=span{xi}`, construct the modified-Hilbert quotient metric,
or prove self-adjointness there.  It also does not provide the source-specific
complement determinant, nonvanishing boundary phase, continuous/removable
factor on the exact exceptional set, or final all-z Theorem-5.10 crosswalk.
Those inputs remain in H2b2b2b2.

## DAG transaction

```text
H2b2b2b  ExactRadicalMetricLatticeInstantiation        OPEN
|-- H2b2b2b.0 DecompositionContract                     PROVED
|-- H2b2b2b1 GenericAllSpectralPointExtension           PROVED / LEAN
|-- H2b2b2b2 ExactRemovableFactorAndRouteInstantiation  OPEN / INELIGIBLE
`-- H2b2b2b3 ExactAllSpectralPointAssembly              OPEN / INELIGIBLE
```

H2b2b2, H2b2b, H2b2, H2b and H2 remain OPEN/CONDITIONAL.
D0.7e.5a remains the unique active leaf, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.

## Verdict

`H2B2B_GENERIC_ADJUGATE_AND_FINITE_EXCEPTION_SPECTRAL_EXTENSION_LEAN`
