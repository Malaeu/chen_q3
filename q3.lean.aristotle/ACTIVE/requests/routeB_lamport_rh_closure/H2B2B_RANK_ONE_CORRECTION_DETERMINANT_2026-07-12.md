# H2b2b off-spectrum rank-one determinant factorization

Date: 2026-07-12
Transaction: Route B revision 37
Status: `GENERIC CORE PROVED / EXACT ALL-Z INSTANTIATION OPEN / NOT_RH`

## Scope

For the already-proved source correction

```text
D' = D - |D xi><eta|,
```

set `A = D - s I`.  Whenever `det A` is a unit, the matrix determinant lemma
gives the finite-dimensional off-spectrum identity

```text
det(D' - s I)
  = det(A) * det(1 + row(eta) * A^-1 * col(-D xi)).
```

## Lean result

`Q3/Proofs/RouteB/RankOneCorrectionDeterminant.lean` proves
`det_rankOneCorrection_sub_smul_one` directly from Mathlib's
`Matrix.det_add_replicateCol_mul_replicateRow`.

Direct `lake env lean` validation is hole-free.  The printed axiom set is only
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

The hypothesis `IsUnit det(D-sI)` deliberately excludes the spectrum.  This
generic theorem therefore does not prove the lattice/spectral-point extension,
quotient positivity and radical, quotient self-adjointness, the complement
determinant identity, nonvanishing boundary phase, exact H8 normalization, or
same-family Route B identification.  Those inputs remain in H2b2b2 under
`H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`.

## DAG transaction

```text
H2b2b  ExactModifiedHilbertFactorization           OPEN
|-- H2b2b.0 DecompositionContract                  PROVED
|-- H2b2b1 GenericOffSpectrumDeterminantCore       PROVED / LEAN
|-- H2b2b2 ExactQuotientLatticeAllZInstantiation   OPEN / INELIGIBLE
`-- H2b2b3 ExactAllZAssembly                       OPEN / INELIGIBLE
```

H2b2, H2b and H2 remain OPEN/CONDITIONAL as before.  D0.7e.5a remains the
unique active leaf, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.

## Verdict

`H2B2B_GENERIC_RANK_ONE_DETERMINANT_OFF_SPECTRUM_LEAN`
