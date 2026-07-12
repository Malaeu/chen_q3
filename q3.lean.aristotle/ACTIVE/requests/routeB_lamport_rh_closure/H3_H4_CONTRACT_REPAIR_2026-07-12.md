# Route B H3/H4 contract repair — revision 15

Status: `CONTRACT_V2_DAG_REPAIRED / THREE_GAPS_REGISTERED / NOT_RH`

Progress class: `FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS + GENERIC_PROOF_PROGRESS`

Authority: `docs/ROUTE_B_THEOREM_CONTRACT_v2.md`, which explicitly supersedes
v1 and replaces H4 by the four safe leaves in §§1,3,4.

This transaction does not alter `D0.7e.5a`, create Bus 010, select the joint
filter, define alpha, prove any exact safe leaf, or prove RH.

## 1. Residual bridge direction is false

The migrated historical wording contains

```text
sqrt(alpha/DeltaE) <= eta/DeltaE.
```

For `A=diag(0,1)` and `u=(e0+e1)/sqrt(2)`, the Rayleigh excess, ground gap,
and centered residual norm are

```text
alpha = 1/2,   DeltaE = 1,   eta = 1/2.
```

The displayed bridge becomes `1/sqrt(2) <= 1/2`, which is false.  The correct
residual denominator is the distance from the Rayleigh center to the
complementary spectrum; in this example it is `DeltaE-alpha=1/2`, not
`DeltaE`.  The direct Rayleigh-angle estimate
`sin(theta) <= sqrt(alpha/DeltaE)` is a different theorem and cannot be
composed by the registered false direction.

`Q3/Proofs/RouteB/SafeBridgeFalsifiers.lean` proves the scalar contradiction
hole-free.

Verdict: `PO_XWALK_RESIDUAL_BRIDGE_DIRECTION_FALSE`.

`D0.7e.5d` remains PROVED only as wording/address migration.  It never
certified the quoted mathematics; the falsified bridge is now an explicit H4
repair obligation.

## 2. I-b2 does not give reciprocal normalization control

The owner lower bound

```text
|b_j| * sqrt(lambda_j) >= c
```

does not imply `liminf |b_j| > 0`.  The compiled counterexample is

```text
b_j = 1/(j+1),   lambda_j = (j+1)^2.
```

Then `|b_j|sqrt(lambda_j)=1` for every j while `b_j -> 0`.  Hence an absolute
tracking inequality for

```text
Fhat_j - b_j Xi
```

does not automatically imply normalized tracking for `G_j=Fhat_j/b_j`:
division produces `W_j/|b_j|` and `eps_j/|b_j|`.  One of those relative
quantities must be estimated directly, or a separate reciprocal bound must be
proved.

Verdict: `H3E_IB2_LIMINF_MISIDENTIFICATION` and
`H3E_ABSOLUTE_TO_NORMALIZED_ERROR_GAP`.

## 3. Limit object is not yet identified

H8 Lemma 7.1 identifies Xi as the raw Fourier transform of `E(h)`; Lemma 7.3
proves that the raw transforms of `E(h_lambda)` converge uniformly on closed
substrips to Xi.  The owner object additionally multiplies its raw trial
transform by

```text
gammaC(1/2+i z).
```

After central normalization, the formally expected limit is therefore

```text
[gammaC(1/2+i z)/gammaC(1/2)] * Xi(z),
```

not Xi, unless an exact compensating crosswalk shows that the owner raw object
has the inverse completion built into it.  No such crosswalk is pinned.

Verdict: `XI_LIMIT_OBJECT_MISMATCH` and
`H3C_DOUBLE_COMPLETION_NOT_EXCLUDED`.

## 4. Contract-v2 H4 repair

The canonical H4 parent remains the top-level detector-decay obligation, but
its four children are now exactly the contract leaves:

```text
H4a SafeAlphaUpper
H4b SafeGapLower
H4c SafeSignAndB
H4d SafeRateAssembly
```

The old residual work is not discarded.  It is re-homed below H4a:

```text
H4a1 AmbientResidualIdentity
H4a2 UniformResidualUpper
H4a3 ResidualToCanonicalAlphaUpper
H4a4 SafeAlphaUpperAssembly
```

Only H4a3 is allowed to export the exact Contract-v2 alpha bound.  It must use
the canonical H0/A1 alpha, the true Rayleigh-center spectral distance, and a
domain/carrier-safe operator or form theorem.  The false bridge is a mandatory
plant.

The H3e dependency IDs are remapped by meaning, not by stale labels: the old
`H4c` true-gap dependency is now `H4b SafeGapLower`, and the old `H4d`
normalization dependency is now `H4c SafeSignAndB`.  H3e therefore depends on
`H4b,H4c`, not on the newly retyped rate parent H4d.

SafeRateAssembly is decomposed into:

```text
H4d1 GenericSafeRateExponentCore
H4d2 ExactSafeRateConstantsAndFilter
H4d3 SafeRateAssembly
```

The generic core is Lean-proved: the strict margin

```text
r_Delta-r_alpha > 2q_b+1
```

makes `q_b+(1+r_alpha-r_Delta)/2` negative, so the corresponding natural-scale
real power tends to zero.  It does not supply the exact constants, filter,
alpha bound, gap bound, or b control.

## 5. Exact remaining stops

- `H4A_OPERATOR_DOMAIN_GAP`;
- `H4A_FORM_COMPRESSION_NOT_OPERATOR_COMPRESSION`;
- `H4A_TRIAL_RITZ_OBJECT_MISMATCH`;
- `H4_RESIDUAL_TO_ALPHA_BRIDGE_MISSING`;
- `SAFE_GAP_LOWER_NO_SOURCE`;
- `H4_LIMIT_FILTER_UNSELECTED`;
- `H4D_COFINAL_NONZERO_LOCUS_MISSING`;
- `H4D_BDET_RECIPROCAL_CONTROL_MISSING`;
- `PO_XWALK_ERROR_SUBSPACE_UNPINNED`;
- `PO_XWALK_CANCELLATION_ESTIMATE_MISSING`;
- `XI_LIMIT_OBJECT_MISMATCH`.

The unique active canonical leaf remains `D0.7e.5a` with stop
`D0_7E_WPRIME_CONSUMER_MISSING`.  Route B remains
`CHALLENGER / NOT_RH`.
