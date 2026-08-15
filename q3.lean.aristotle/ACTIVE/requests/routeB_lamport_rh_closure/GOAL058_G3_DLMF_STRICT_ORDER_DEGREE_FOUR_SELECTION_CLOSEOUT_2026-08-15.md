# Goal 058 G3 — strict carrier order and degree-four selection closeout

Date: 2026-08-15

## Verdict

```text
G3_DLMF3035_STRICT_CARRIER_ORDER_AND_DEGREE_FOUR_INDEX_TWO_PROVED
G1_STATUS: OPEN
G3_STATUS: OPEN
STOP_CODE: G3_DEGREE_FOUR_DLMF_ROW_SELECTED_PHYSICAL_PSWF_IDENTITY_AND_FINITE_FOURIER_NEXT
ROUTE: CHALLENGER_NOT_RH
```

Below the strict production endpoint `Lambda < 20`, the zero-based
finite-limit even carrier is now proved collision-free and strictly ordered.
The singular literal Schur negative count at a carrier value is exactly its
carrier index. Consequently the third even carrier is uniquely index `2`,
the parity-compressed DLMF degree-four mode `2p = 4`, and its normalized DLMF
30.3.5 coefficient row is square-summable.

This closes the strict-order/index-selection seam only. It does not yet turn
the selected row into the physical Ferrers/PSWF function, prove the restricted
finite-Fourier eigenrelation, supply CCM Lemma 7.2, or close G1/G3.

## Kernel-checked files

### Singular inertia semicontinuity

`Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean`

SHA-256:

```text
d3fd5e0b0dc22d3d640dcff46cbb215e307d65bfd735a10fab43d51da33db56f
```

New public theorem:

```lean
mode4HermitianNegativeEigenvalueCount_eventually_between_of_tendsto
```

For Hermitian matrices converging to a possibly singular Hermitian limit, the
eventual negative count is bounded below by the limiting negative count and
above by that count plus the limiting nullity. The proof uses the exact
negative and positive spectral subspaces; it assumes no determinant guard.

### Carrier index and degree-four selection

`Q3/Proofs/RouteB/D0Mode4ClassicalCarrierToDLMF3035EvenL2.lean`

SHA-256:

```text
1d702df09f657b4c76d8eddf8e27ee8ba9aa2da869c2fc4ddb4f247f6e1775b0
```

New public theorems:

```lean
mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
mode4ClassicalEvenEigenvalue_lt_of_index_lt_of_upper_lt_twenty
mode4ClassicalEvenEigenvalue_eq_two_iff_index_eq_two
mode4DLMF3035EvenLeftCoefficient_degreeFour_sqSummable
```

The index theorem chooses nonsingular parameters converging from below and
above to the simple carrier root. Singular inertia semicontinuity gives
`r <= countBelow` and `countAbove <= r + 1`; convergence of the same finite
`j`-th eigenvalue gives `countBelow <= j` and `j + 1 <= countAbove`. Hence
`r = j`. Carrier monotonicity is therefore strict below twenty, and the
existing finite-head theorem `carrier 2 < 20` yields unique degree-four index
`2` and the normalized square-summable row.

The helper `exists_mode4HermitianSchurMatrix_det_ne_zero_between` in
`D0Mode4DLMF3035EvenL2ToFiniteLimitSpectrum.lean` was made public; its final
SHA-256 is:

```text
60320d609e5cebb5e21bb9e019ac4224b4e30bbe657892a9a5eb747aecae7d16
```

## Search and environment receipt

The exact supplier query was:

```text
mode4 classical even eigenvalue index equals Hermitian Schur negative count strict order below twenty singular root semicontinuity
```

The first fresh env dump correctly returned an incomplete denominator. All
50 missing/stale Route B modules were built; 27 cache-replayed modules whose
`.olean` timestamps remained older than their sources were then compiled
directly from current source with explicit `lean -o`. The final declared
EnvDump completed with 256/256 current source-backed modules, 2328 declarations,
zero stale modules, zero uncovered modules, zero `sorryAx`, and zero other
axioms. Six source-less orphan `.olean` files remained excluded.

On that complete denominator `supplier_preflight.py` returned
`CANDIDATE_ONLY`: its Ferrers and finite-spectrum hits were neighboring or
textual candidates, not an exact theorem of the requested type.

## Validation

- direct `lake env lean`: PASS for all three changed Lean files;
- named target build: PASS, 7774 jobs;
- `scripts/q3_check.sh`: PASS for all three files;
- `git diff --check`: PASS;
- new public axiom surfaces: exactly
  `[propext, Classical.choice, Quot.sound]`;
- no `sorry`, `admit`, new `axiom`, or `unsafe` declaration was introduced.

The recurring `UnicodeBasic` local-change warning belongs to the dependency
checkout and did not alter an exit status or tracked artifact.

## Next exact seam

Connect the uniquely selected normalized DLMF degree-four row to the existing
Ferrers regular even prolate solution and its physical scaling, without
assuming the function identity or finite-Fourier eigenrelation. Mode zero,
the degree-zero/four `ProlatePair`, the restricted finite-Fourier constants,
CCM Lemma 7.2, the overlap/denominator floor, and the cofinal schedule remain
separate downstream obligations.

## Mandatory nonclaims

This node proves no physical PSWF identity, actual `ProlatePair`,
finite-Fourier eigenrelation, CCM Lemma 7.2 rate, central-overlap floor,
coupled schedule, G1, G3, Route B promotion, or RH claim.
