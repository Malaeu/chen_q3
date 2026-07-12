# Route B H3b2 weighted projective-evaluation transfer — revision 32

Status: `H3B2A_PROVED / EXACT_WEIGHTED_PROJECTIVE_INPUTS_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This transaction composes two already-proved generic interfaces: H3a1 controls
phase-aligned vector error by a projective square root, and H3b1 transfers a
vanishing evaluation majorant to uniform convergence on a supplied set. It does
not select the exact Route B family, operator, envelope, filter, or prove RH.

## 1. Generic composition

For eventual unit vectors `u_i,v_i`, nonnegative compact envelopes `C_i`, and
phase-aligned evaluation errors bounded by `C_i ||e_i||`, H3a1 gives

```text
||e_i|| <= sqrt(2*(1-||<u_i,v_i>||^2)).
```

If the weighted projective quantity on the right tends to zero, squeeze gives
`C_i||e_i|| -> 0`. H3b1 then proves

```text
TendstoUniformlyOn (fun i z => T_i(e_i)(z)) 0 l K.
```

The theorem is

```text
tendstoUniformlyOn_zero_of_weighted_projective_defect.
```

The filter is explicitly `[NeBot l]`, and nonnegativity of `C_i` is explicit.

## 2. Exact Route B obligation left open

H3b2b must still pin on one exact family/filter:

1. the normalized simple-even ground and nonzero trial vectors;
2. the exact compact-strip evaluation map `T_i`;
3. the compact-uniform nonnegative envelope `C_i`;
4. the exact weighted projective-defect decay rate;
5. the same cofinal joint `(m,N)` filter used by H3a/H3c/H3e;
6. the exact target and Lean export without topology or object mismatch.

The exact stop remains

```text
H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING.
```

## 3. Honest DAG split

```text
H3b2 ExactWeightedEvaluationInstantiation          OPEN / AND
|-- H3b2.0 H3b2DecompositionContract               PROVED
|-- H3b2a GenericWeightedProjectiveEvaluationCore  PROVED / LEAN
|-- H3b2b ExactWeightedProjectiveInstantiation     OPEN / INELIGIBLE
`-- H3b2c H3b2Assembly                             OPEN / INELIGIBLE
```

## 4. Source and Lean boundary

The proof imports only the pinned H3a1 and H3b1 modules. Official Mathlib
inner-product, metric uniform-convergence, and nontrivial-filter APIs support
the generic composition; they do not provide the Route B exact rate.

Proof artifact:

```text
Q3/Proofs/RouteB/WeightedProjectiveEvaluationTransfer.lean
```

It compiles without holes and prints only the allowed axioms
`propext`, `Classical.choice`, and `Quot.sound`.

Explicit nonclaims:

```text
NO_EXACT_GROUND_TRIAL_FAMILY
NO_EXACT_COMPACT_EVALUATION_OPERATOR
NO_EXACT_COMPACT_ENVELOPE
NO_EXACT_WEIGHTED_PROJECTIVE_RATE
NO_EXACT_JOINT_FILTER
NO_H3B2_PARENT_CLOSURE
NO_H3B_PARENT_CLOSURE
NO_H3_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the active stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
