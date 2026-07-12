# Route B H3b compact evaluation-rate transfer — revision 21

Status: `H3B1_PROVED / EXACT_WEIGHTED_RATE_INSTANTIATION_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS + FALSIFICATION_PROGRESS`

This transaction proves the generic topology and norm estimate below H3b.  It
does not prove a uniform Route B evaluation bound, improve the exact
ground/trial rate, select a master family or joint filter, close H3b/H3, create
Bus 010, or prove RH.

## 1. Exact generic input

Let `l` be a filter indexing errors `e_i` in a normed group `V`.  Let

```text
T_i : V -> alpha -> E
```

be an evaluation family into a normed group `E`.  On a fixed compact set `K`,
assume the eventual uniform bound

```text
||T_i(e_i)(z)|| <= C_i ||e_i||     for every z in K
```

and the scalar rate

```text
C_i ||e_i|| -> 0 along l.
```

For every `epsilon>0`, the rate is eventually smaller than `epsilon`; the
uniform bound then gives

```text
dist(0,T_i(e_i)(z)) < epsilon
```

simultaneously for all `z in K`.  By Mathlib's metric characterization this
is exactly `TendstoUniformlyOn`.

The Lean theorem is

```text
tendstoUniformlyOn_zero_of_evaluation_rate.
```

Verdict: `GENERIC_COMPACT_EVALUATION_RATE_TRANSFER_LEAN`.

## 2. Compact-open wrapper

Let `U` be an open subset of a locally compact domain.  Suppose every compact
`K subset U` has a scalar envelope `b_i(K)` satisfying

```text
b_i(K) -> 0,
||F_i(z)|| <= b_i(K) eventually for every z in K.
```

The same epsilon argument gives uniform convergence on each compact `K`.
Mathlib's theorem

```text
tendstoLocallyUniformlyOn_iff_forall_isCompact
```

then gives locally uniform convergence on `U`.  The Lean theorem is

```text
tendstoLocallyUniformlyOn_zero_of_compact_envelopes.
```

This is the exact compact-open topology used by the Route B H3 contract.  It
does not assert uniform convergence on an unbounded closed strip.

Primary Mathlib sources:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Pseudo/Basic.html

## 3. Mandatory fixed-bound falsifier

A bound without a vanishing rate does not imply convergence.  The Lean file
uses the constant family on the singleton domain:

```text
F_n(*) = 1.
```

It has the fixed uniform bound

```text
||F_n(*)|| <= 1
```

but cannot converge uniformly to zero, because uniform convergence would
imply the false pointwise limit `1 -> 0`.  The executable theorem is

```text
fixed_bound_without_vanishing_rate_not_uniform_zero.
```

This plant rejects every future inference

```text
bounded evaluation  ==>  compact-strip convergence
```

that omits a vanishing product/envelope.

## 4. Exact Route B boundary

D0.6 proves only a fixed-window evaluation estimate.  Its constant depends on
`m`, and the D0.6 artifact explicitly refuses a uniform-in-`m` conclusion.
For the current raw bound on a compact set `K`, the exact scale is
schematically

```text
C_i(K) = sqrt(L_i) * lambda_i^a.
```

Thus H3b2 must prove, on the same exact selected family and joint filter,

```text
sqrt(L_i) * lambda_i^a * ||ground_i - trial_i|| -> 0,
```

or provide a separately proved weighted/cancellation evaluation theorem with
a better envelope.  D0.6 fixed-window boundedness alone does not supply this.

The Pro review records the same gap as

```text
PO_XWALK_UNIFORM_EVAL:
  a weighted evaluation/cancellation theorem beating the raw
  sqrt(L_m) lambda_m^a norm bound.
```

Changing the exponent convention for `b` cannot repair it: the unabsorbed
evaluation factor remains divergent under the presently recorded inputs.

Residual exact stop:

```text
H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING
```

## 5. Honest DAG split

```text
H3b CompactStripEvaluation                       OPEN / AND
|-- H3b.0 H3bDecompositionContract              PROVED
|-- H3b1 GenericCompactEvaluationRateTransfer   PROVED / LEAN
|-- H3b2 ExactWeightedEvaluationInstantiation   OPEN / INELIGIBLE
`-- H3b3 H3bAssembly                            OPEN / INELIGIBLE
```

`H3b2` depends on `D0`, `H3a`, and `H3b1`.  It owns:

1. the exact error vector and its norm;
2. the exact compact set and selected strip domain;
3. a same-family evaluation operator;
4. the eventual uniform bound on each compact;
5. the weighted rate tending to zero;
6. the same joint `(m,N)` filter consumed by later H3/H4 nodes.

The generic theorem does not manufacture any of these exact inputs.

## 6. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/CompactEvaluationRateTransfer.lean
```

It compiles without `sorry`, `admit`, or `exact?`.  The three printed theorem
axiom sets are within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_EVALUATION_ENVELOPE
NO_EXACT_GROUND_TRIAL_RATE
NO_UNIFORM_IN_M_FROM_D0_6
NO_UNBOUNDED_STRIP_UNIFORMITY
NO_H3B_PARENT_CLOSURE
NO_H3_PARENT_CLOSURE
NO_H4_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
