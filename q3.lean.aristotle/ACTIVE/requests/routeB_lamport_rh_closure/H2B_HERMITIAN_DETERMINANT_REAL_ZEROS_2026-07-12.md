# Route B H2b Hermitian determinant real-zero transfer — revision 25

Status: `H2B1_PROVED / EXACT_THEOREM_5_10_FACTORIZATION_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`

This transaction formalizes the universal real-zero mechanisms used by an
H8-style determinant argument.  It does not construct the exact modified-
Hilbert Hermitian matrix, identify its complement determinant with the Route B
approximant, prove the all-complex-variable factorization, close H2b/H2, create
Bus 010, or prove RH.

## 1. Periodic determinant

For real nonzero `L`, define

```text
periodicScalingDet(L,z) = 1-exp(-i L z).
```

If it vanishes, Mathlib's exact exponential fiber theorem gives

```text
-i L z = 2 pi i n
```

for an integer `n`.  Comparing real parts gives `L*Im(z)=0`; since `L!=0`,
`Im(z)=0`.  Lean therefore proves

```text
periodicScalingDet_zerosRealOn.
```

This is the full periodic determinant from the source shape.  It is not, by
definition, the exact finite-removed `E_N^perp` complement determinant.

The helper

```text
zerosRealOn_right_factor
```

records the legal transfer: once an exact product `f*g` has only real zeros,
the right factor `g` does too.  H2b2 must still prove the required product
identity for the source complement.

## 2. Hermitian characteristic determinant

Let `M` be a finite complex Hermitian matrix.  Assume an all-`z` identity

```text
F(z) = unit(z) * (charpoly(M)(z) * realFactor(z)),
```

where `unit(z)` never vanishes and `realFactor` has only real zeros.

At any zero of `F`, nonvanishing of `unit` leaves a zero of the characteristic
polynomial or of `realFactor`.  In the first branch:

```text
charpoly(M)(z)=0
  -> z is in spectrum(M)
  -> z is a real Hermitian eigenvalue.
```

Lean proves

```text
zerosRealOn_of_hermitian_charpoly_mul.
```

The theorem is insensitive to the source convention difference between
`det(zI-M)` and `det(M-zI)`: the finite-dimensional sign can be absorbed only
into a genuinely nonvanishing unit.

Verdict:

```text
GENERIC_HERMITIAN_DETERMINANT_REAL_ZERO_TRANSFER_LEAN.
```

## 3. Mandatory falsifiers

Two exact one-dimensional plants keep the hypotheses live.

### Non-Hermitian plant

```text
M = [i].
```

Its characteristic polynomial vanishes at `z=i`, whose imaginary part is
nonzero.  Thus dropping Hermitianity permits nonreal zeros:

```text
NONHERMITIAN_CHARPOLY_NONREAL_ZERO.
```

### Vanishing-unit plant

Take the Hermitian zero matrix and multiply its harmless characteristic
factor by `unit(z)=z-i`.  The product vanishes at `i`.  Thus a factor called a
"unit" must be proved nonvanishing:

```text
VANISHING_UNIT_NONREAL_ZERO.
```

## 4. Exact Route B obligation left open

H2b2 must instantiate the generic theorem with the same H1c3/D0.8/H2a family.
It must provide all of:

1. the exact `T`-induced quotient Hilbert metric;
2. the finite scaled `D''` matrix and proof it is Hermitian in that metric;
3. the exact `E_N^perp` complement determinant;
4. a nonvanishing boundary/scaling phase;
5. an identity valid for every complex `z`, including lattice cancellation
   points, not merely away from poles;
6. the source normalization such as `delta_N(xi)=1` only after its denominator
   is proved nonzero;
7. an exact crosswalk to the selected raw Route B approximant.

The main stop is

```text
H2B_EXACT_THEOREM510_FACTORIZATION_MISSING.
```

`PertRaw` is not declared Hermitian in the standard ambient metric, and the
already killed completed tracker is not revived.

## 5. Honest DAG split

```text
H2b SameVectorRealZeros                           CONDITIONAL / AND
|-- H2b.0 H2bDecompositionContract               PROVED
|-- H2b1 GenericHermitianDeterminantRealZeros     PROVED / LEAN
|-- H2b2 ExactTheorem510Factorization             OPEN / INELIGIBLE
`-- H2b3 H2bAssembly                              OPEN / INELIGIBLE
```

The parent deliberately stays `CONDITIONAL`.  Under the compiler invariant,
a conditional node never discharges H2, even though its generic child is now
proved.

## 6. Mathlib source boundary

Official APIs used by the proof:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/Log.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html

They certify the exponential fibers and Hermitian spectrum.  They do not
supply the H8/Route B factorization, metric, matrix, complement, or family.

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean
```

It compiles without `sorry`, `admit`, or `exact?`; printed axiom sets contain
only

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_THEOREM510_FACTORIZATION
NO_MODIFIED_HILBERT_MATRIX_CONSTRUCTION
NO_COMPLEMENT_DETERMINANT_CROSSWALK
NO_BOUNDARY_NORMALIZATION_NONZERO
NO_RAW_MASTER_SELECTION
NO_H2B_PARENT_CLOSURE
NO_H2_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
