# Route B H4d2 SAFE bounds to WPrime square envelope — revision 23

Status: `H4D2A_PROVED / EXACT_SAFE_INPUTS_AND_JOINT_FILTER_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves the generic Contract-v2 arithmetic that turns SAFE
bounds and an independently supplied WPrime identity into the squared envelope
consumed by H4d1.  It does not define WPrime, supply exact SAFE bounds,
constants, exponents, a joint filter, close H4d2/H4d/H4, create Bus 010, or
prove RH.

## 1. Common-envelope SAFE inputs

Fix positive real numbers `scale`, `envelope`, and `c_Delta`.  Assume

```text
0 <= alpha,
alpha <= C_alpha * scale^r_alpha * envelope,
c_Delta * scale^r_Delta * envelope <= gap,
|b| <= C_b * scale^q_b,
0 <= C_b,
0 <= C_alpha.
```

The same positive `envelope` must occur in both the alpha upper and gap lower
bounds.  Only then may it cancel from the quotient.

The WPrime input is the independent identity

```text
W^2 = |b|^2 * scale * alpha / gap.
```

It is a hypothesis to the generic theorem, not a definition of `W`.

## 2. Quotient and b-square bounds

Positivity and the gap lower bound give `0 < gap`.  Ordered division yields

```text
alpha/gap
  <= (C_alpha/c_Delta) * scale^(r_alpha-r_Delta).
```

The proof explicitly uses the common envelope cancellation and
`Real.rpow_sub`.

From the b upper bound and nonnegativity,

```text
|b|^2 <= (C_b * scale^q_b)^2.
```

Multiplying the nonnegative factors gives

```text
W^2 <=
  (C_b * scale^q_b)^2 * scale *
  (C_alpha/c_Delta) * scale^(r_alpha-r_Delta).
```

## 3. Exact square-envelope normal form

Using

```text
sqrt(C_alpha/c_Delta)^2 = C_alpha/c_Delta
```

and real-power exponent arithmetic, Lean proves the exact normal form

```text
W^2 <=
  (C_b * sqrt(C_alpha/c_Delta) *
    scale^(q_b+(1+r_alpha-r_Delta)/2))^2.
```

This is theorem

```text
safe_bounds_to_square_envelope_pointwise.
```

Verdict: `GENERIC_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_LEAN`.

## 4. One-filter wrapper

The theorem

```text
safe_bounds_to_square_envelope_eventually
```

accepts all positivity, SAFE bounds, b bound, and WPrime identity eventually
on one non-bottom filter and returns the squared envelope eventually on that
same filter.  This is exactly the `hWsq`-shape consumed by the already proved
H4d1 cofinal rate theorem.

The wrapper does not select or prove:

- the joint `(m,N)` filter;
- cofinality of its scale;
- eventual nonnegativity of the independently defined WPrime branch;
- exact constants;
- the value/convention of `q_b`;
- the strict Contract-v2 exponent margin;
- the independent WPrime consumer identity;
- a central nonzero/reciprocal normalization locus.

## 5. Exact Route B residual obligation

H4d2b must instantiate every generic input on one exact non-bottom joint
filter.  Its dependencies are

```text
D0.7e.5c, H4a, H4b, H4c.
```

In particular:

1. `D0.7e.5c` must supply the non-tautological WPrime identity;
2. H4a must supply the canonical alpha upper bound;
3. H4b must supply the true same-parity gap lower bound;
4. H4c must supply alpha sign, strict gap, and the exact b control;
5. the alpha and gap bounds must use the same exponential envelope;
6. `C_b,C_alpha >= 0`, `c_Delta > 0`, and the scale is eventually positive
   and cofinal to infinity;
7. the independently defined WPrime branch is eventually nonnegative, as
   required by the H4d1 square-to-linear convergence receiver;
8. all inputs must live on the same non-bottom cofinal filter with fixed
   constants.

The primary exact stop is

```text
H4D_EXACT_SQUARE_ENVELOPE_INSTANTIATION_MISSING.
```

The legacy parent stop remains live for validator compatibility and semantic
clarity:

```text
H4D_WPRIME_SQUARE_ENVELOPE_MISSING.
```

## 6. Honest DAG split

```text
H4d2 ExactSafeRateConstantsAndFilter              OPEN / AND
|-- H4d2.0 H4d2DecompositionContract             PROVED
|-- H4d2a GenericSafeBoundsToSquareEnvelope       PROVED / LEAN
|-- H4d2b ExactSafeInputsAndJointFilter            OPEN / INELIGIBLE
`-- H4d2c H4d2Assembly                           OPEN / INELIGIBLE
```

H4d3 remains the assembly of the already proved H4d1 generic decay package
with the exact H4d2 result.

## 7. Mathlib source boundary

The proof uses official real-power and square-root identities:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html

These APIs certify the exponent algebra only; they do not supply the Route B
SAFE hypotheses.

## 8. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/SafeBoundsToSquareEnvelope.lean
```

It compiles without `sorry`, `admit`, or `exact?`; both printed axiom sets are
within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_WPRIME_DEFINITION_FROM_TARGET_IDENTITY
NO_EXACT_SAFE_ALPHA_UPPER
NO_EXACT_SAFE_GAP_LOWER
NO_EXACT_B_CONSTANT_OR_QB
NO_JOINT_FILTER_SELECTION
NO_WPRIME_NONNEGATIVITY_EXPORT
NO_COMMON_ENVELOPE_INSTANTIATION
NO_H4D2_PARENT_CLOSURE
NO_H4D_PARENT_CLOSURE
NO_H4_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
