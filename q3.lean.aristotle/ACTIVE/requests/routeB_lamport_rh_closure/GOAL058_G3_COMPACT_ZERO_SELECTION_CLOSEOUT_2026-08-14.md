# Goal 058 G3 — compact zero selection closeout

Date: 2026-08-14

```text
VERDICT: G3_MODE4_UNRESTRICTED_STURM_COMPARISON_PROVED
STOP: MODE4_UNRESTRICTED_STURM_COMPARISON_PROVED_INDEX4_MODE0_FOURIER_AND_LEMMA72_MISSING
SCOPE: ABSTRACT_SOURCE_FAMILY / LEAN
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Exact result

The production file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersCompactZeroSelection.lean
```

proves two public declarations:

```lean
Q3.RouteB.Mode4FerrersRegularEvenProlateSolution.interior_zeros_on_Icc_finite
Q3.RouteB.exists_mode4Ferrers_zero_between_of_lt_Lambda_between_lower_zeros
```

For any compact interval strictly inside `(-1,1)`, the zeros of an accepted
mode-four Ferrers solution form a finite set.  Hence, between any two distinct
interior zeros of a lower-spectral-parameter accepted solution, the
higher-parameter accepted solution has an interior zero.

The proof consumes the existing semantic derivative interface and
`interior_zero_simple`.  `HasDerivAt.eventually_ne` isolates each zero;
closedness of the restricted zero set and compactness of the interval give a
compact discrete set, which `IsCompact.finite` makes finite.  `Finset.min'`
then selects the first zero to the right of the lower endpoint, and the
previous one-nodal-interval Sturm theorem supplies the higher zero.

## Knowledge preflight

The question card

```text
ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g3_compact_zero_selection.md
```

records four sequential `q3_docs` queries.  They found the current
interior-zero and Sturm nodes but no exact project supplier for compact
finiteness or consecutive-pair extraction.  External search and outbound
review were not needed: the missing layer reduced to existing Mathlib
primitives and compiled locally.

## Validation

```text
lake env lean Q3/Proofs/RouteB/D0Mode4FerrersCompactZeroSelection.lean  PASS
lake build Q3.Proofs.RouteB.D0Mode4FerrersCompactZeroSelection          PASS (7774 jobs)
bash ../scripts/q3_check.sh Q3/Proofs/RouteB/D0Mode4FerrersCompactZeroSelection.lean
                                                                        PASS
lake build                                                             PASS (7817 jobs)
forbidden-token scan                                                   PASS (zero hits)
forbidden-claim scan                                                   PASS (zero hits)
git diff --check                                                       PASS
```

Public axiom audit for both declarations:

```text
[propext, Classical.choice, Quot.sound]
```

The proof file is `7122` bytes, `167` newline-terminated lines, has a final
LF, and SHA-256
`f9d8aa2f9f646a0d6e01726cd5c42fcc3c1cf301c8f0e3f82524718ea4cccdfe`.

The `UnicodeBasic` dependency emitted its pre-existing local-changes warning;
it did not change any exit code or axiom surface.

## What moved

The separate compact-zero and consecutive-nodal-pair wall is closed.  The
Sturm comparison no longer requires the caller to supply a zero-free lower
interval.  The next honest source work is ordered oscillation/index selection:

1. relate the matching-root family to an ordered Sturm spectrum;
2. prove the selected root is degree/index `4`, not merely an accepted regular
   solution;
3. construct and select the degree/index `0` companion;
4. transport both through physical scaling and finite-Fourier normalization;
5. prove CCM Lemma 7.2 and the projected denominator floor.

## Nonclaims

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
