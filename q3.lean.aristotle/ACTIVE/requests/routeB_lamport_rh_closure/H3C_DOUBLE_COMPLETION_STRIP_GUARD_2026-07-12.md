# Route B H3c normalized double-completion strip guard — revision 24

Status: `H3C1_PROVED / EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves that applying a second central-normalized completion
factor to the already completed `centeredXi` cannot equal `centeredXi` on the
open centered critical strip.  It does not select the correct Route B family,
prove any convergence to Xi, choose a joint filter, close H3c/H3/L0, create
Bus 010, or prove RH.

## 1. Candidate under test

The source-locked completion factor is `gammaC`.  Define only the falsifier
candidate

```text
normalizedDoubleCompletedXi(z)
  = gammaC(1/2+i z) / gammaC(1/2) * centeredXi(z).
```

Lean proves `gammaC(1/2) != 0`, so this normalization has a legitimate
denominator.  This is not a proposed H3c limit object; it is the object being
killed.

## 2. Boundary values

Let

```text
z0 = -i/2.
```

The existing exact identities give

```text
1/2+i z0 = 1,
gammaC(1) = 0,
centeredXi(z0) = riemannXi(1) = 1/2.
```

Therefore

```text
normalizedDoubleCompletedXi(z0) = 0 != 1/2 = centeredXi(z0).
```

The point `z0` is on the boundary, not in the open strip
`|Im z| < 1/2`.

## 3. From boundary mismatch to an interior mismatch

Lean constructs points

```text
z_delta = -i/2 + i*delta,
0 < delta <= 1/4,
```

inside the open strip and arbitrarily close to `z0`.  Thus `z0` belongs to
the closure of `centeredCriticalStrip`, and the corresponding neighborhood
filter within the strip is non-bottom.

Both functions are continuous at `z0`:

- `centeredXi` is entire;
- the Gamma factor is continuous because its argument is `1`, away from the
  nonpositive-integer singularity convention, and the denominator is nonzero.

If the functions were equal at every point of the open strip, they would be
eventually equal on the within-strip neighborhood of `z0`.  Hausdorff limit
uniqueness would then force equality at `z0`, contradicting `0 != 1/2`.

Lean therefore proves both

```text
not EqOn normalizedDoubleCompletedXi centeredXi centeredCriticalStrip
```

and the stronger operational form

```text
exists z in centeredCriticalStrip,
  normalizedDoubleCompletedXi(z) != centeredXi(z).
```

The interior witness is existential, not a pre-named coordinate.

Verdict:

```text
H3C_NORMALIZED_DOUBLE_COMPLETION_STRIP_MISMATCH_LEAN.
```

## 4. Exact positive obligation left open

Killing one wrong object does not identify the right one.  H3c2 must still:

1. select the same exact H1c3/D0.8 Route B family;
2. choose one source-locked joint `(m,N)` filter;
3. prove convergence of the raw tracker directly to `centeredXi`, or prove an
   exact inverse-completion crosswalk before normalization;
4. connect the finite ground state to the continuum object on that family;
5. export the exact limit identification into Lean.

The primary exact stop is

```text
H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING.
```

The route-selection stop is

```text
H3C_RAW_OR_INVERSE_COMPLETION_SELECTION_MISSING.
```

`XI_LIMIT_OBJECT_MISMATCH` and `XI_LIMIT_IDENTIFICATION_MISSING` stay live:
the wrong object is excluded, but the right object is not constructed.

## 5. Honest DAG split

```text
H3c XiLimitIdentification                         OPEN / AND
|-- H3c.0 H3cDecompositionContract                PROVED
|-- H3c1 NormalizedDoubleCompletionStripGuard     PROVED / LEAN
|-- H3c2 ExactRawOrCompensatedXiLimitAndFilter    OPEN / INELIGIBLE
`-- H3c3 H3cAssembly                              OPEN / INELIGIBLE
```

The obsolete uncertainty `H3C_DOUBLE_COMPLETION_NOT_EXCLUDED` is retired
because H3c1 proves exactly its negation.  No positive H3c hypothesis is
discharged by that retirement.

## 6. Mathlib source boundary

Official APIs used by the proof:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Hausdorff.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/NhdsWithin.html

They certify Gamma regularity and uniqueness of limits.  They do not supply a
Route B approximant family, joint filter, or convergence theorem.

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/DoubleCompletionStripMismatch.lean
```

It compiles without `sorry`, `admit`, or `exact?`.  Printed axiom sets contain
only

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_H3C_PARENT_CLOSURE
NO_EXACT_XI_LIMIT_IDENTIFICATION
NO_CORRECT_LIMIT_OBJECT_SELECTION
NO_JOINT_FILTER_SELECTION
NO_H3_PARENT_CLOSURE
NO_L0C2_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
