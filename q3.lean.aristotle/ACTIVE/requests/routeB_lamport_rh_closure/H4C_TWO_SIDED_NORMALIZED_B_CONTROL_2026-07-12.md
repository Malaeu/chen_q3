# Route B H4c normalized two-sided b control — revision 26

Status: `H4C1_PROVED / EXACT_SAFE_SIGN_AND_B_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS + FALSIFICATION_PROGRESS`

This transaction proves the generic consequences of Contract v2's two-sided
normalized b bound.  It does not define the exact b object, choose its
orientation, prove the bound or q_b for Route B, define alpha, prove the true
gap positive, close H4c/H4, create Bus 010, or prove RH.

## 1. Generic pointwise contract

Fix real values with

```text
0 < scale,
0 < c_b,
c_b <= |b| * scale^(-q_b),
|b| * scale^(-q_b) <= C_b.
```

Since real powers of a positive scale are positive,

```text
scale^(-q_b) * scale^q_b = 1.
```

Lean multiplies both sides of the normalized inequalities by the positive
factor `scale^q_b` and proves

```text
b != 0,
|b| <= C_b * scale^q_b,
|b|^-1 <= c_b^-1 * scale^(-q_b).
```

Verdict:

```text
H4C_GENERIC_TWO_SIDED_NORMALIZED_B_CONTROL_LEAN.
```

## 2. Filter and normalized-error receivers

The eventual wrapper consumes all hypotheses on one non-bottom filter and
returns eventual nonvanishing, the polynomial upper bound, and the reciprocal
bound on that same filter.  It does not select the filter.

For any nonnegative absolute error, the reciprocal estimate gives

```text
err / |b|
  <= c_b^-1 * scale^(-q_b) * err.
```

This is a legal generic input for the H3e relative-normalization transfer and
for the H4d2 nonzero/reciprocal duties.  It does not prove the exact error
decays at the required rate.

## 3. Scale-dependent guard

The conclusion is scale-dependent.  It does not imply a uniform positive
lower bound for `|b|` or a bounded unweighted reciprocal.

The existing executable plant remains mandatory:

```text
b_n = 1/(n+1),
lambda_n = (n+1)^2,
|b_n| * sqrt(lambda_n) = 1,
b_n -> 0.
```

Thus a normalized lower-product bound can coexist with `b_n -> 0`.

## 4. Exact Route B obligation left open

H4c2 must prove on the same exact cofinal carrier/filter:

1. the canonical H0/A1 definition of alpha and `0 <= alpha`;
2. strict positivity of the true same-parity gap `DeltaE`;
3. the exact b formula and its direct Contract-v2 orientation;
4. `0 < c_b` and the full two-sided normalized bound;
5. the exact value/law of `q_b`;
6. identity of the scalar, carrier, and filter used by H3e and H4d2.

The primary stop is

```text
H4C_EXACT_SIGN_AND_B_INSTANTIATION_MISSING.
```

The exact nonzero and reciprocal stops stay live until H4c2 instantiates the
generic theorem:

```text
H4D_COFINAL_NONZERO_LOCUS_MISSING,
H4D_BDET_RECIPROCAL_CONTROL_MISSING.
```

## 5. Honest DAG split

```text
H4c SafeSignAndB                                  OPEN / AND
|-- H4c.0 H4cDecompositionContract                PROVED
|-- H4c1 GenericTwoSidedNormalizedBControl        PROVED / LEAN
|-- H4c2 ExactSafeSignAndBInstantiation           OPEN / INELIGIBLE
`-- H4c3 H4cAssembly                              OPEN / INELIGIBLE
```

## 6. Mathlib source boundary

Official real-power API:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html

Mathlib certifies the real-power cancellation and ordered-field steps.  It
does not supply the exact Route B b formula, constants, exponent, or filter.

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/TwoSidedNormalizedBControl.lean
```

It compiles without `sorry`, `admit`, or `exact?`; printed axiom sets contain
only

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_B_DEFINITION_OR_ORIENTATION
NO_EXACT_TWO_SIDED_B_BOUND
NO_QB_VALUE
NO_UNIFORM_POSITIVE_B_LOWER_BOUND
NO_CANONICAL_ALPHA_SIGN_OR_TRUE_GAP_POSITIVITY
NO_H4C_PARENT_CLOSURE
NO_H4_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
