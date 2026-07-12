# Route B H2a simple-even ground sector criterion — revision 20

Status: `H2A1_PROVED / EXACT_SELECTED_FAMILY_SECTOR_ORDERING_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS + FALSIFICATION_PROGRESS`

This transaction proves the universal finite-dimensional algebra below H2a.
It does not prove either strict spectral inequality for the exact finite Weil
operator, choose the H1 master family, close H2a/H2, create Bus 010, or prove
RH.

## 1. Source boundary

The primary H8 source does not prove H2a.  Its logical order is explicit:

1. Lemma 5.2 proves that the finite real symmetric matrix commutes with the
   parity grading `gamma`.
2. Definition 5.3 defines `even-simple` to mean that the smallest eigenvalue
   is simple and its eigenvector has parity `+1`.
3. Theorem 5.10 assumes that condition and then proves that the raw transform
   of the normalized ground vector is entire with only real zeros.
4. Section 8 names proof of simple-even for the truncated Weil form as the
   first missing step of the tentative RH argument.

Source pin:

```text
literature/zotero/H8ULBMAL/fulltext.md
sha256 7ba4b01845df2989cdd763a19c83904e4114e26fc51d5d7f93d09489d52871d4
```

The external Mathlib joint-eigenspace documentation independently confirms
the generic finite-dimensional mechanism: commuting symmetric operators
decompose into simultaneous eigenspaces.  That mechanism supplies parity
reduction, but it does not decide whether the ground parity is `+1` or `-1`:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/JointEigenspace.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Basic.html

## 2. Ordered eigenvector interface

For a complex-linear operator `A`, real number `mu`, and vector `x`, the Lean
artifact defines

```text
IsRealEigenvector A mu x :=
  x != 0 AND A x = (mu : C) * x.
```

The real eigenvalue interface is appropriate for the exact Route B
self-adjoint operator and makes sector ordering explicit.  It does not assert
self-adjointness of an arbitrary generic `A`.

Parity is recorded as

```text
IsEvenVector J x := J x = x,
IsOddVector  J x := J x = -x.
```

The target predicate `IsSimpleEvenGround A J mu0 v0` says:

1. `v0` is a nonzero real eigenvector at `mu0`;
2. `v0` is even;
3. every real eigenvalue is at least `mu0`;
4. every eigenvector at `mu0` is a scalar multiple of `v0`.

## 3. Parity dichotomy

If `A` commutes with an involution `J`, then `J xi` lies in the same
eigenspace as `xi`.  When that eigenspace is one-dimensional,

```text
J xi = c xi.
```

Applying `J` again gives `c^2=1`, hence

```text
J xi = xi OR J xi = -xi.
```

This is Lean theorem

```text
parity_dichotomy_of_simple_eigenspace.
```

It deliberately stops at a dichotomy.  Simplicity and commutation alone do
not select the plus sign.

## 4. Generic sector-ordering theorem

For an involution `J`, define the algebraic sector parts

```text
xPlus  = (x + J x)/2,
xMinus = (x - J x)/2.
```

Lean proves exactly:

```text
xPlus + xMinus = x,
J xPlus = xPlus,
J xMinus = -xMinus.
```

If `A` commutes with `J` and `x` is an eigenvector of `A`, then every nonzero
sector part is an eigenvector at the same eigenvalue.  Assume now:

```text
v0 is an even eigenvector at mu0;
every nonzero even eigenvector has eigenvalue >= mu0;
every even eigenvector at mu0 is a scalar multiple of v0;
every nonzero odd eigenvector has eigenvalue > mu0.
```

For an arbitrary eigenvector, at least one sector part is nonzero.  The even
floor or the strict odd floor gives the global lower bound.  At equality the
odd part must vanish, and even-sector simplicity makes the vector a scalar
multiple of `v0`.

This is Lean theorem

```text
simpleEvenGround_of_sector_order.
```

Verdict: `GENERIC_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_LEAN`.

## 5. Mandatory odd-ground falsifier

On `C x C`, let

```text
J = diag(1,-1),
A = diag(1,0),
eOdd = (0,1).
```

The Lean artifact proves:

```text
A J = J A,
J^2 = I,
eOdd is the simple global ground vector of A at eigenvalue 0,
J eOdd = -eOdd.
```

The executable theorem is

```text
commute_simple_ground_does_not_force_even.
```

This plant rejects any future inference

```text
commutation + simple ground  ==>  even ground.
```

The missing input is a strict comparison between the two parity sectors.

## 6. Exact Route B residual obligation

D0.4 already gives the exact orthogonal parity decomposition and the ordered
sector spectra.  D0.5 gives

```text
nu1(m,N) = min(epsilonPlus1(m,N), epsilonMinus1(m,N))
```

without choosing the winning sector or proving multiplicity one.  Therefore
the exact H2a instantiation must prove, on the one selected H1c3/D0.8 family,

```text
epsilonPlus1(m,N) < epsilonPlus2(m,N),
epsilonPlus1(m,N) < epsilonMinus1(m,N).
```

The first inequality gives simplicity at the even bottom.  The second makes
that bottom strictly lower than the odd bottom.  Together they supply the
positive isolation radius and instantiate the generic Lean theorem.

No such inequalities occur in H8 or in the currently locked D0 artifacts.
The statement that the analogous prolate-wave ground is simple-even concerns
a different operator and cannot close this node.

Residual exact stop:

```text
H2A_EXACT_SECTOR_ORDERING_MISSING
```

## 7. Honest DAG split

```text
H2a SimpleEvenGround                                  OPEN / AND
|-- H2a.0 H2aDecompositionContract                   PROVED
|-- H2a1 GenericSimpleEvenGroundSectorCriterion      PROVED / LEAN
|-- H2a2 ExactSelectedFamilySectorOrdering           OPEN / INELIGIBLE
`-- H2a3 H2aAssembly                                 OPEN / INELIGIBLE
```

`H2a2` depends on `D0.4`, `D0.5`, `D0.8`, `H1c3`, and `H2a1`.  The dependency
on `H1c3` prevents silently proving parity for one family while H1/H2 consume
another.  If the selected even sector is one-dimensional, the exact
instantiation must handle that case directly rather than inventing
`epsilonPlus2`.

## 8. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/SimpleEvenGroundSectorCriterion.lean
```

It compiles without `sorry`, `admit`, or `exact?`.  All three printed theorem
axiom sets are within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_SECTOR_ORDERING
NO_EVEN_INTERNAL_GAP
NO_EVEN_ODD_BOTTOM_ORDER
NO_H1_MASTER_FAMILY_SELECTION
NO_D0_8_CROSSWALK
NO_H2A_PARENT_CLOSURE
NO_H2_PARENT_CLOSURE
NO_H4_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
