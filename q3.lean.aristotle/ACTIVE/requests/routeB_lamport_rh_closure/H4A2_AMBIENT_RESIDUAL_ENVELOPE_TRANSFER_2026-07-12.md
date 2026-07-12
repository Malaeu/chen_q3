# Route B H4a2 ambient-residual envelope transfer — revision 30

Status: `H4A2A_PROVED / EXACT_COMPONENT_RATE_INSTANTIATION_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS + FALSIFICATION_PRESERVATION`

This transaction proves the universal norm-envelope consequences of the H4a1
ambient/compressed/leakage split.  It does not identify the exact Route B
operator domain or projection, prove either component rate, close
H4a2/H4a/H4, create Bus 010, or prove RH.

## 1. Norm receiver for the exact split

H4a1a proved

```text
ambientResidual
  = compressedResidual + projectionLeakage.
```

The triangle inequality now gives

```text
||ambientResidual||
  <= ||compressedResidual|| + ||projectionLeakage||.
```

This is theorem

```text
ambient_residual_norm_le_compressed_add_leakage.
```

No idempotence, orthogonality, self-adjointness, or finite-dimensional
assumption is needed at this generic level.

## 2. Component and squared envelopes

Given separate component estimates

```text
||compressedResidual|| <= compressedBound,
||projectionLeakage||  <= leakageBound,
```

Lean proves

```text
||ambientResidual|| <= compressedBound + leakageBound
```

and the squared receiver consumed by H4a3a,

```text
||ambientResidual||^2 <= (compressedBound+leakageBound)^2.
```

The theorems are

```text
ambient_residual_envelope_of_component_envelopes,
ambient_residual_sq_envelope_of_component_envelopes.
```

## 3. Ritz specialization and filter wrappers

If the compressed Ritz equation holds,

```text
P(A v) = mu v,
```

H4a1a identifies the ambient residual with leakage.  Therefore a leakage
envelope alone gives the ambient bound:

```text
ambient_residual_envelope_of_leakage_envelope.
```

Two wrappers transfer component bounds and the Ritz/leakage specialization
eventually on one non-bottom filter:

```text
eventually_ambient_residual_envelope_of_components,
eventually_ambient_residual_envelope_of_leakage_envelope.
```

Verdict:

```text
GENERIC_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_LEAN.
```

## 4. Mandatory falsifier remains live

`compressed_residual_zero_ambient_residual_nonzero` from H4a1a has zero
compressed residual but nonzero ambient residual equal to the leakage.  It
continues to reject both invalid shortcuts:

```text
compressed residual = 0  ==>  ambient residual = 0,
delete leakage estimate from the H4a2 hypotheses.
```

Revision 30 imports and consumes H4a1a; it does not weaken or replace this
plant.

## 5. Exact Route B obligation left open

H4a2b must still provide, on the same exact carrier/filter used downstream:

1. the domain-safe Route B operator and source-locked projection from H4a1b;
2. the normalized trial/Ritz vector and scalar in the correct domain;
3. the exact crosswalk from project residual objects to `compressedResidual`
   and `projectionLeakage`;
4. a uniform compressed-residual envelope;
5. a uniform projection-leakage envelope with the required cofinal rate;
6. either the exact Ritz equation or the nonzero compressed component budget;
7. the combined squared rate required by the H4a3 Temple instantiation;
8. a Lean export on the same family/filter, without form/operator conflation.

The exact stop is

```text
H4A2_EXACT_COMPONENT_RATE_INSTANTIATION_MISSING.
```

`H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING`,
`H4A1_LEAKAGE_NORM_RATE_MISSING`, `H4A_OPERATOR_DOMAIN_GAP`, and
`H4A_FORM_COMPRESSION_NOT_OPERATOR_COMPRESSION` remain live.

## 6. Honest DAG split

```text
H4a2 UniformResidualUpper                         OPEN / AND
|-- H4a2.0 H4a2DecompositionContract             PROVED
|-- H4a2a GenericAmbientResidualEnvelopeTransfer PROVED / LEAN
|-- H4a2b ExactRouteBComponentRateInstantiation  OPEN / INELIGIBLE
`-- H4a2c H4a2Assembly                           OPEN / INELIGIBLE
```

The generic triangle inequality cannot supply the source-level component
estimates.

## 7. Mathlib source boundary

Official normed-group API:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Group/Basic.html

The API supplies `norm_add_le`; it does not supply the Route B objects or
component rates.

## 8. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/AmbientResidualEnvelopeTransfer.lean
```

It compiles after building the imported H4a1 module, without `sorry`, `admit`,
or `exact?`; every printed axiom set is within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_OPERATOR_DOMAIN
NO_EXACT_ROUTE_B_PROJECTION
NO_FORM_TO_OPERATOR_CROSSWALK
NO_EXACT_COMPRESSED_RESIDUAL_RATE
NO_EXACT_LEAKAGE_RATE
NO_SAFE_ALPHA_UPPER
NO_H4A2_PARENT_CLOSURE
NO_H4A_PARENT_CLOSURE
NO_H4_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
