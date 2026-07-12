# H2b2 rank-one correction / weighted-symmetry transfer

Date: 2026-07-12
Transaction: Route B revision 34
Status: `GENERIC CORE PROVED / EXACT INSTANTIATION OPEN / NOT_RH`

## Exact scope

H2b2 needs two logically different inputs:

1. the universal algebra of the source rank-one correction
   `D' = D - |D xi><eta|`;
2. its exact Route B instantiation on the same H1c3/D0.8/H2a family, including
   positivity and radical of the Weil matrix, quotient descent, complement
   determinant, nonvanishing phase, and the all-complex-z factorization.

This transaction proves only item 1.

## Lean theorem

`Q3/Proofs/RouteB/RankOneCorrectionWeightedSymmetry.lean` proves:

- `rankOneCorrection_kills_vector`: `eta dot xi = 1` makes the corrected
  matrix kill `xi`;
- `rankOneCorrection_weightedSymmetric`: the source commutator, symmetry of
  `T` and `D`, and `T(D xi) = -beta` imply
  `T D' = (D')^T T`;
- `rankOneCorrection_kernel_and_weightedSymmetric`: the two conclusions on
  one common datum.

Direct `lake env lean` validation is hole-free.  The printed axiom set is only
`propext`, `Classical.choice`, and `Quot.sound`.

## What remains exact

The theorem is weighted symmetry of a finite real matrix.  It does not prove:

- positivity of the exact Route B `T`;
- `ker T = C xi` or descent to the quotient by the radical;
- complex-Hermitian self-adjointness of the exact quotient operator;
- the `E_N` direct-sum/complement determinant identity;
- nonvanishing of the boundary/scaling phase;
- the lattice-safe identity for every complex `z`;
- identification with the same raw H1c3/D0.8/H2a family.

Therefore the residual stop remains
`H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`.

## DAG transaction

```text
H2b2  ExactTheorem510Factorization                 OPEN
|-- H2b2.0 DecompositionContract                   PROVED
|-- H2b2a GenericRankOneWeightedSymmetry           PROVED / LEAN
|-- H2b2b ExactModifiedHilbertInstantiation        OPEN / INELIGIBLE
`-- H2b2c ExactFactorizationAssembly               OPEN / INELIGIBLE
```

H2b remains `CONDITIONAL`; H2 and L0 remain `OPEN`.  The scheduler remains on
`D0.7e.5a`, Bus 010 is absent, and Route B remains `CHALLENGER / NOT_RH`.

## Verdict

`H2B2_GENERIC_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_LEAN`
