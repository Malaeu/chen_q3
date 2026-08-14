# Goal 058 G3 — Sturm nodal-interval comparison closeout

Date: 2026-08-14

```text
VERDICT: G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON_PROVED
STOP: MODE4_STURM_NODAL_COMPARISON_PROVED_COMPACT_ZERO_FINITE_SELECTION_MODE0_FOURIER_AND_LEMMA72_MISSING
SCOPE: ABSTRACT_SOURCE_FAMILY / LEAN
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Exact result

The production file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean
```

proves

```lean
Q3.RouteB.exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval
```

with the exact Proshka-repaired head.  Two accepted
`Mode4FerrersRegularEvenProlateSolution` objects share the same `mProject`
and `K`; only `LambdaLo < LambdaHi` changes.  If two simple interior zeros of
the lower-parameter solution delimit one zero-free nodal interval, the
higher-parameter solution has a zero strictly between them.

The proof uses the weighted Wronskian

```text
(1 - x^2) * (u(x) * v'(x) - u'(x) * v(x))
```

whose derivative is exactly `(LambdaLo - LambdaHi) * u(x) * v(x)`.  The
common `mProject` cancels the common prolate potential.  Constant-sign
normalization on the nodal interval, actual `HasDerivAt` interfaces, and the
already-proved simple endpoint zeros give the strict endpoint contradiction.

## Source and judgment locks

- Proshka verdict:
  `GOAL058_G3_STURM_NODAL_COMPARISON_PROSHKA_VERDICT_2026-08-14.md`;
- accepted UI-rendered prompt extract:
  `PROSHKA_GOAL058_STURM_NODAL_COMPARISON_ARISTOTLE_PROMPT_2026-08-14_UI_RENDERED_EXTRACT.md`;
- exact primary-source pins and index crosswalk:
  `GOAL058_G3_PSWF_INDEX_SOURCE_PIN_PACKET_2026-08-14.md`;
- allowed direct import only:
  `Q3.Proofs.RouteB.D0Mode4FerrersInteriorZeroSimplicity`.

The accepted Aristotle request is preserved as provenance but was not sent.
The local kernel proof superseded the need for a paid duplicate run:

```text
ARISTOTLE: NOT_SENT_LOCAL_PROOF_SUPERSEDED_REQUEST
```

## Validation

All commands ran from the canonical `rh_clean` checkout on the final source:

```text
lake env lean Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean  PASS
lake build Q3.Proofs.RouteB.D0Mode4FerrersSturmComparison          PASS (7773 jobs)
bash ../scripts/q3_check.sh Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean
                                                                    PASS
lake build                                                        PASS (7817 jobs)
forbidden-token scan                                              PASS (zero hits)
forbidden-claim/import scan                                       PASS (zero hits)
git diff --check                                                  PASS
```

Public axiom audit:

```text
[propext, Classical.choice, Quot.sound]
```

The proof file is `18554` bytes, `452` newline-terminated lines, has a final
LF, and SHA-256
`cfd36331b647f44b97651bf74796655c04c0749ff13913c5d431a76da42d64f5`.

Five kernel-checked plants pin parameter direction, the counter-direction,
the nodal-interval guard, common-potential cancellation, and exclusion of the
singular endpoints.

The `UnicodeBasic` dependency emitted its pre-existing local-changes warning;
it did not change the exit code or the public axiom surface.

## SEARCH_FLAGS

```text
QUERY: exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval
RESULT: exact production declaration found in one of six stores
EXTERNAL_SEARCH: NOT_NEEDED
BOUNDARY: RETRIEVAL_CANDIDATE_CONFIRMED_BY_DIRECT_LEAN_NOT_BY_SEARCH
```

## What moved

The bounded Sturm comparison kernel is no longer part of the G3 wall.  The
next honest source work is:

1. compact-interior finiteness of the zero set and consecutive nodal-pair
   extraction;
2. an oscillation/order argument that locates the matching root at index 4;
3. the analogous index-0 construction;
4. the dimensionless-to-physical scale and normalization bridge;
5. assembly of the unchanged production `ProlatePair` satisfying
   `IsActualProlateModePair`;
6. the CCM Lemma 7.2 rate and projected denominator floor.

The theorem does not prove root existence, a global zero count, ordered
`psi_4` selection, a finite-Fourier eigenrelation, a production mode pair, or
any cofinal tracking statement.

## Nonclaims

- `NO_COMPACT_ZERO_SET_FINITE_THEOREM`
- `NO_GLOBAL_ZERO_COUNT`
- `NO_ORDERED_PSI4_IDENTIFICATION`
- `NO_MATCHING_ROOT_EXISTENCE`
- `NO_MODE_ZERO_CONSTRUCTOR`
- `NO_PHYSICAL_SCALE_BRIDGE`
- `NO_FINITE_FOURIER_EIGENRELATION`
- `NO_PRODUCTION_PROLATEPAIR_CONSTRUCTION`
- `NO_LEMMA_7_2_RATE`
- `NO_DENOMINATOR_FLOOR`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`
