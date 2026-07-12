# Route B H3e normalized-tracking rate transfer — revision 31

Status: `H3E1_PROVED / EXACT_RELATIVE_TRACKING_INPUTS_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves only the universal normalization and uniform-rate
receiver required by H3e. It does not define or reconstruct `WPrime`, select the
exact Route B family, supply the absolute tracking theorem, close H3e/H3/L0,
create Bus 010, or prove RH.

## 1. Exact normalization identity

For a nonzero scalar `b`, Lean proves

```text
b⁻¹ • F - X = b⁻¹ • (F - b • X),
||b⁻¹ • F - X|| = ||b||⁻¹ ||F - b • X||.
```

Thus an absolute tracking estimate for `F-b•X` can be normalized only after a
reciprocal bound for `b` is supplied. The scalar called `W` in the receiver is
an arbitrary external majorant; the proof never declares a Route B detector.

## 2. Relative-rate receiver

On a non-bottom filter, suppose

```text
||b_i||⁻¹ <= R_i,
||F_i(z)-b_i X(z)|| <= A (W_i+eps_i)   for z in K,
R_i W_i -> 0,
R_i eps_i -> 0.
```

Then Lean proves

```text
TendstoUniformlyOn (fun i z => b_i⁻¹ • F_i(z)) X l K.
```

This is

```text
tendstoUniformlyOn_normalized_tracking_of_relative_rates.
```

The explicit `[NeBot l]` firewall prevents bottom-filter vacuity.

## 3. H4c1 specialization

The already-proved two-sided normalized `b` control supplies

```text
R_i = c_b⁻¹ scale_i^(-q_b).
```

Lean therefore packages the direct H4c1 receiver

```text
tendstoUniformlyOn_normalized_tracking_of_two_sided_b.
```

It still requires both relative products `R_i W_i` and `R_i eps_i` to tend to
zero. The generic theorem does not supply either rate.

## 4. Two live falsifiers

First, the normalized lower-product plant satisfies

```text
lowerProductB_n -> 0,
|lowerProductB_n|⁻¹ lowerProductB_n = 1.
```

Hence detector decay alone does not survive division by `b`. Second, the
Contract-v2 margin

```text
r_Delta-r_alpha > 2 q_b+1
```

does not by itself imply the relative normalized margin

```text
r_Delta-r_alpha > 1.
```

The compiled witness is `q_b=-1`, `r_alpha=0`, `r_Delta=0`. These plants block
both a detector-decay-only shortcut and a safe-margin-only shortcut.

## 5. Exact Route B obligation left open

H3e2 must still supply on one exact same-family joint filter:

1. the independently sourced and owner-ratified WPrime consumer from D0.7e.5;
2. the canonical `alpha`, true gap, and exact `b` formula/orientation;
3. the compact-substrip absolute tracking estimate for the exact finite family;
4. the exact Xi limit object, without double-completion mismatch;
5. the H4c1 two-sided reciprocal control on that same family;
6. `R*WPrime -> 0`;
7. `R*eps -> 0`;
8. one non-bottom joint `(m,N)` filter and Lean export.

The exact stop is

```text
H3E_EXACT_RELATIVE_TRACKING_INPUTS_MISSING.
```

The two rate sub-stops are

```text
H3E_RELATIVE_WPRIME_RATE_MARGIN_MISSING,
H3E_RELATIVE_RESIDUAL_RATE_MISSING.
```

## 6. Honest DAG split

```text
H3e ExactWPrimeTrackingTheorem                 OPEN / AND
|-- H3e.0 H3eDecompositionContract             PROVED
|-- H3e1 GenericNormalizedTrackingRateTransfer PROVED / LEAN
|-- H3e2 ExactRelativeTrackingInstantiation    OPEN / INELIGIBLE
`-- H3e3 H3eAssembly                           OPEN / INELIGIBLE
```

## 7. Source and API boundary

Local source review found no pinned exact H3e theorem or relative-rate supply.
The formal receiver uses Mathlib's uniform-convergence, normed scalar-action,
real-power, and nontrivial-filter APIs:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/MulAction.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html

Those APIs implement the receiver; they do not supply any Route B exact object
or rate.

## 8. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/NormalizedTrackingRateTransfer.lean
```

It compiles without `sorry`, `admit`, or `exact?`; every printed axiom set is
within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_WPRIME_DEFINITION_OR_RECONSTRUCTION
NO_EXACT_ABSOLUTE_TRACKING_BOUND
NO_EXACT_B_INSTANTIATION
NO_EXACT_RELATIVE_WPRIME_RATE
NO_EXACT_RELATIVE_RESIDUAL_RATE
NO_CURRENT_CONTRACT_MARGIN_IMPLICATION
NO_H3E_PARENT_CLOSURE
NO_H3_PARENT_CLOSURE
NO_L0C2_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
