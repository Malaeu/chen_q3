# Goal 058 G3 — PSWF4 DLMF coefficient/root crosswalk closeout

Date: 2026-08-14

```text
VERDICT: G3_PSWF4_DLMF_COEFFICIENT_ROW_TO_CURRENT_ROOT_PROVED
STOP: CLASSICAL_INDEXED_PSI4_COEFFICIENT_SUPPLIER_MODE0_FOURIER_AND_LEMMA72_MISSING
SCOPE: ABSTRACT_SOURCE_FAMILY / LEAN
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Exact source correction

Official NIST DLMF §30.8(i), equations 30.8.1--30.8.5, uses degree
`n = 4`, order `m = 0`, and coefficient index `k >= -2`.  Reindexing by
`q = k + 2` gives the current even Legendre degrees `2*q` and changes the
30.8.5 normalization to

```text
sum_q a_q^2 / (4*q + 1) = 1/9.
```

The current canonical-tail receiver expects right-hand side `1`.  The exact
source-faithful bridge is the homogeneous rescaling `a_q -> 3*a_q`.  The
older comment calling this an `m = n = 0` specialization described the
reindexed weight but not the degree-four source normalization; it has been
corrected.

Primary pins:

- <https://dlmf.nist.gov/30.8.E1> — Ferrers expansion;
- <https://dlmf.nist.gov/30.8.E2> — coefficient integral;
- <https://dlmf.nist.gov/30.8.E3> and
  <https://dlmf.nist.gov/30.8.E4> — recurrence;
- <https://dlmf.nist.gov/30.8.E5> — normalization.

## Kernel-checked suppliers

- `mode4DLMF3085_degreeFour_rescale_three`;
- `mode4DLMF3084_3085_degreeFour_rescaledTail_eq_c_mul_canonical`;
- `mode4DLMF3084_3085_degreeFour_shiftedBoundaryRatio_eq_canonical`;
- `mode4DLMF3084_3085_degreeFour_sourceBoundaryFlux_eq_schurCorrection`;
- `mode4DLMF3084_3085_degreeFour_coefficients_force_root`.

The final theorem consumes only:

1. the literal reindexed DLMF 30.8.4 recurrence;
2. the literal raw degree-four 30.8.5 normalization `1/9`;
3. the existing tail-domain inequalities.

It proves the exact current output

```text
mode4RootFunction mProject K Lambda = 0.
```

The proof establishes nonzero coefficient zero, identifies the whole finite
left recurrence row with `mode4LeftPair`, transports the square-summable
source tail through the Hermitian canonical tail, cancels the boundary scale,
and discharges the literal left/right matching equation.  The desired root is
not accepted as a hypothesis.

## Knowledge preflight

Four sequential `ask.sh --deep` queries are recorded in

```text
ACTIVE/pipeline/oracle_questions/
2026_08_14_goal058_g3_pswf4_dlmf_normalization_crosswalk.md
```

They found the anonymous unit-normalized receiver but no degree-four
`1/9 -> 1` rescaling theorem and no classical indexed `psi_4` coefficient
supplier.

## Validation boundary

Direct Lean passes for every changed proof file.  Every new public theorem has
axiom surface exactly

```text
[propext, Classical.choice, Quot.sound].
```

No `sorry` or project `axiom` is used.  The recurring `UnicodeBasic`
dependency-local-change warning predates this batch.

## Remaining G3 source wall

The coefficient-to-root implication is now closed.  The next honest theorem
must construct or extract the actual indexed classical `psi_4` row and prove:

1. the reindexed DLMF 30.8.4 recurrence;
2. the raw 30.8.5 normalization `1/9`;
3. equality of the source `psi_4` with its alternating even-Legendre series
   under the exact normalization.

After that, the current root-conditioned Ferrers and physical constructors
start without a hidden root binder.  Still independently missing are the
mode-zero companion, restricted plus-phase finite-Fourier pair, construction
of the unchanged production `ProlatePair`, CCM Lemma 7.2, denominator floor,
and one coupled cofinal schedule.

## Nonclaims

```text
NO_CLASSICAL_PSI4_CONSTRUCTOR_YET
NO_ORDERED_PSI4_FUNCTION_IDENTITY_YET
NO_MODE_ZERO_CONSTRUCTOR
NO_RESTRICTED_FINITE_FOURIER_PAIR
NO_LEMMA_7_2_RATE
NO_DENOMINATOR_FLOOR
NO_G3
NO_G1
NO_ROUTE_B_PROMOTION
NO_RH
```
