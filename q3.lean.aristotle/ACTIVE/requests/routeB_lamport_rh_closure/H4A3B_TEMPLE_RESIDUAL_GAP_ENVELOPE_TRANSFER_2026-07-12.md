# Route B H4a3b Temple residual-gap envelope transfer — revision 33

Status: `H4A3B1_PROVED / EXACT_RESIDUAL_GAP_ENVELOPES_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves the universal rate arithmetic between the local Temple
core and Contract-v2 SafeAlphaUpper. It does not instantiate the exact Route B
operator/eigenbasis, canonical alpha, residual variance, half-gap locus, true
gap, common filter, or prove RH.

## 1. Generic Temple transfer

Assume the half-gap locus and Temple inequality

```text
2 alpha <= gap,
alpha (gap-alpha) <= etaSq,
```

together with

```text
etaSq <= C_eta scale^r_eta envelope^2,
c_Delta scale^r_Delta envelope <= gap.
```

The already-proved Temple core gives `alpha <= 2 etaSq/gap`. Division by the
positive lower-gap envelope and `Real.rpow_sub` then yields

```text
alpha <= (2 C_eta/c_Delta)
           scale^(r_eta-r_Delta) envelope.
```

Thus the universal receiver exposes

```text
C_alpha = 2 C_eta/c_Delta,
r_alpha = r_eta-r_Delta.
```

The pointwise and non-bottom-filter theorems are

```text
safe_alpha_envelope_of_temple_residual_gap_bounds,
eventually_safe_alpha_envelope_of_temple_residual_gap_bounds.
```

## 2. Live squared-envelope plant

The compiled fixed example

```text
envelope=1/16, gap=1/4, alpha=1/8, etaSq=1/64
```

satisfies the half-gap locus, Temple inequality, `etaSq<=envelope`, and
`envelope<=gap`, but violates `alpha<=envelope`. Therefore the second envelope
factor in the residual-square rate is essential.

## 3. Exact Route B obligation left open

H4a3b2 must still supply on one exact same-family filter:

1. the canonical alpha and normalized spectral weights;
2. the exact domain-safe operator/eigenbasis and same-parity complementary floor;
3. the exact ambient residual variance crosswalk;
4. the Temple half-gap locus;
5. the residual-square envelope with two exponential factors;
6. the true-gap floor from H4b with one exponential factor;
7. constants/exponents and Lean export without form/operator mismatch.

The exact stop is

```text
H4A_EXACT_RESIDUAL_SQUARE_AND_GAP_ENVELOPE_MISSING.
```

The generic transaction retires only
`H4A_RESIDUAL_RATE_TO_ALPHA_RATE_MISSING`.

## 4. Honest DAG split

```text
H4a3b ExactRouteBResidualSpectralInstantiation       OPEN / AND
|-- H4a3b.0 H4a3bDecompositionContract               PROVED
|-- H4a3b1 GenericTempleResidualGapEnvelopeTransfer  PROVED / LEAN
|-- H4a3b2 ExactRouteBSpectralResidualRateInstantiation OPEN
`-- H4a3b3 H4a3bAssembly                             OPEN
```

The dependency on H4b is acyclic and names the true-gap source explicitly.

## 5. Lean and source boundary

Proof artifact:

```text
Q3/Proofs/RouteB/TempleResidualGapEnvelopeTransfer.lean
```

It imports the local weighted-spectral Temple core and compiles without holes;
every printed axiom set is within `propext`, `Classical.choice`, `Quot.sound`.
Mathlib's real-power API supplies exponent algebra, not Route B objects.

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_SPECTRAL_INSTANTIATION
NO_CANONICAL_ALPHA_CROSSWALK
NO_EXACT_RESIDUAL_VARIANCE_CROSSWALK
NO_EXACT_TEMPLE_HALF_GAP_LOCUS
NO_EXACT_RESIDUAL_SQUARE_ENVELOPE
NO_EXACT_TRUE_GAP_ENVELOPE
NO_H4A3B_PARENT_CLOSURE
NO_H4A3_PARENT_CLOSURE
NO_H4A_PARENT_CLOSURE
NO_H4_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the active stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
