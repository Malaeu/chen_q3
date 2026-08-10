# D0.7e.5a — Proshka independent source-audit verdict

```yaml
STATUS: OPEN
PRIMARY: MYTHOS_SOURCE_PARTIAL_REPAIR_REQUIRED
PRIMARY_COUNT: 1
PROVENANCE: PROSHKA_INDEPENDENT_SOURCE_AUDIT
DATE: 2026-08-03
PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 6af9170d15a38e451a76f8dbf2ad8725d62b6f5f
  ACTIVE_ADDRESS: RB-LAMPORT-D0 / D0.7e.5a
  PHYSICAL_BUS_GOAL: NONE
  BUS_010: VOID
ROUTE:
  STATUS: CHALLENGER_NOT_RH
  STATE_PROMOTION: false
  RH_CLAIMED: false
  LEAN_EDITS: false
  ROUTE_STATE_EDITS: false
  GOAL_051_AUTHORIZED: false
SUCCESS_CODE:
  ISSUED: false
  TARGET: D0_7E_B_ORIENTATION_LOCKED
STOP_CODE: D0_7E_WPRIME_CONSUMER_MISSING
SOURCE_INPUT: D0_7E_5A_MYTHOS_SOURCE_ACQUISITION_VERDICT.md
```

This document materializes the completed Proshka audit. The response was
requested with `Respond in English only` and was allowed to finish without
using any early-answer control.

## Primary adjudication

`MYTHOS_SOURCE_PARTIAL_REPAIR_REQUIRED`

Mythos correctly recovered a source-defined neighboring operator and a
source-proved determinant observable from CCM. It also correctly retained the
existing stop. Those are substantive source-acquisition results, so rejection
of the whole acquisition would be too strong.

The classification `SOURCE_PARTIAL_B_ORIENTATION_OPEN` nevertheless requires
repair. It compresses several independent missing obligations into one alleged
orientation row. The determinant theorem does not instantiate the pinned
`IndependentWPrimeConsumer` contract: it supplies neither a source-defined
nonnegative `WPrime`, nor an `FZeo = G` crosswalk, nor equation 5c.

The weakest ratifiable classification is:

```text
SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY
```

## Findings

```yaml
MYTHOS_FINDINGS:
  CCM_PERTURBED_OPERATOR_RECOVERED: true
  CCM_REGULARIZED_DETERMINANT_THEOREM_RECOVERED: true
  INDEPENDENT_SEMANTIC_OBSERVABLE_RECOVERED: true
  SOURCE_DEFINED_NONNEGATIVE_WPRIME_RECOVERED: false
  SOURCE_DEFINED_FZEO_RECOVERED: false
  FZEO_EQ_PROJECT_G_CROSSWALK_RECOVERED: false
  SOURCE_TO_PROJECT_PARAMETER_MAP_RECOVERED: false
  LEGAL_NONZERO_DOMAIN_CROSSWALK_RECOVERED: false
  EXACT_5C_THEOREM_RECOVERED: false
  B_ORIENTATION_RECOVERED: false

ADJUDICATION:
  SOURCE_PARTIAL: true
  ONLY_ONE_GAP_REMAINS: false
  B_ORIENTATION_IS_A_MISSING_OBLIGATION: true
  B_ORIENTATION_IS_THE_ONLY_MISSING_OBLIGATION: false
  CURRENT_STOP_RETAINED: true

SOURCE_CLASS:
  CCM_OPERATOR: DEFINITION_THEOREM
  CCM_DETERMINANT: THEOREM
  CCM_XI_NORMALIZATION: OUTLOOK_CONJECTURE
  PROJECT_BCAL_BZEOMUL: PROJECT_CROSSWALK
  HISTORICAL_WPRIME_FORMULA: OWNER_MINT_OR_HEURISTIC
  ZERO_HIT_RESULTS: NEGATIVE_SEARCH_RESULT

HASH_AUDIT:
  OFFICIAL_VERSION_METADATA: VERIFIED
  REPORTED_TRUNCATED_ARCHIVE_HASHES: NOT_RECOMPUTED
  FULL_IMMUTABLE_ARCHIVE_HASHES: NOT_ESTABLISHED_BY_THIS_AUDIT
```

## Source-verification result

### Ratified source package

- arXiv:2511.22755 has one listed version, v1, submitted 27 November 2025.
- CCM defines the base scaling operator on
  `L²([lambda^-1,lambda], d*u)` and keeps `lambda > 1` and `N` independent.
- The Dirichlet functional

  \[
  \delta_N=L^{-1/2}\sum_{n=-N}^{N}V_n
  \]

  approximates boundary evaluation: `⟨delta_N,f⟩ -> f(lambda)`.
- Under the even-simple truncated Weil hypothesis, CCM Proposition 5.7 gives
  the unique perturbed operator agreeing with the base operator on
  `ker delta_N` and killing `xi`. With `delta_N(xi)=1`, the rank-one formula is

  \[
  D_{\log}^{(\lambda,N)}
    =D_{\log}^{(\lambda)}
      -|D_{\log}^{(\lambda)}\xi\rangle\langle\delta_N|.
  \]

- The self-adjointness statement is on
  `E'_N \oplus E_N^perp`, with `E'_N = E_N / C xi` carrying the metric induced
  by `QW_lambda^N - epsilon_N <.,.>`. It is not an unqualified statement in
  the original standard `L²` metric.
- CCM proves

  \[
  \det_{\mathrm{reg}}(D_{\log}^{(\lambda,N)}-z)
    =-i\lambda^{-iz}\widehat\xi(z),
  \]

  with `xi-hat` entire and its zeros equal to the real operator spectrum.
  This is an independently meaningful determinant observable.
- CvS arXiv:2511.23257v1 supplies a real-zero theorem for the Fourier
  transform of a simple, isolated, even lowest eigenfunction of the relevant
  lower-bounded self-adjoint quadratic-form operator. It is a real-zero
  engine, not a central-value or `WPrime` definition.
- The zeta-cycles/CCM functional `W_{0,2}` is a linear Weil functional or
  distribution, not the requested nonnegative scalar detector.

### Required source repairs

- The reported numbers `297–299`, `984`, `997–1001`, `1085`, and
  `1223–1224` are TeX/source extraction-line coordinates, not PDF page
  numbers. Stable locators should use Proposition 5.7, Theorem 5.10,
  equations (5.14)–(5.27), §7 Outlook, and §8.
- Proposition 5.7 initially requires `delta_N(xi) != 0`; the normalized
  rank-one display uses the additional choice `delta_N(xi)=1`.
- The Outlook statement that the continuum objects, after multiplication by
  “suitable constants,” should converge to `Xi` is conjectural. It is not a
  proved normalization theorem and does not select `bCal` or `bCal^(-1)`.
- Mythos reported only prefix/suffix fragments for the three archive hashes.
  The official version metadata was checked, but Proshka did not recompute
  complete immutable archive SHA-256 values.

## Object-separation verdict

| Object | Verified status | Contract role |
| --- | --- | --- |
| `D_log^(lambda,N)` | Source-defined rank-one perturbed operator | Neighboring finite operator |
| `xi-hat_(lambda,N)` | Source-defined entire Fourier transform | Neighboring finite approximant |
| `det_reg(D_log^(lambda,N)-z)` | Complex entire observable linked to `xi-hat` by theorem | Independent determinant semantics |
| source `FZeo` / project `G` | No identity or proved gauge/scalar relation recovered | Missing crosswalk |
| `WPrime : D -> R>=0` | No source definition recovered | Missing consumer object |
| equation 5c | No source theorem recovered | Missing separate theorem |

The determinant passes the independent-semantics test in its own category. It
does not pass the `IndependentWPrimeConsumer` contract merely because a
determinant is one possible kind of semantics. A separate theorem would still
have to identify a source-defined nonnegative `WPrime` with a norm, residual,
defect, modulus, approximation error, or another exact observable derived from
that determinant.

## True missing obligations

The missing set contains at least these independent rows:

1. `SourceWPrimeDefinition`: a verbatim pre-existing map
   `WPrime : D -> R>=0`.
2. `SourceWPrimeIndependentSemantics`: a theorem connecting that scalar to
   the determinant or another independent observable.
3. A source definition of the exact approximant used in the `WPrime`
   statement; CCM's `xi-hat_(lambda,N)` is not thereby historical `FZeo`.
4. `FZeoToProjectGCrosswalk`: either `FZeo = G` or
   `FZeo = c * gamma * G`, with `c != 0` and `gamma` zero-free on the
   declared domain.
5. A source-to-project parameter and carrier crosswalk: `lambda² = m`, basis,
   midpoint convention, and finite operator identity. The source leaves
   `(lambda,N)` independent.
6. A finite-normalization theorem relating `delta_N(xi)=1` to the project
   normalization. The continuum Outlook normalization is not a finite-N
   replacement.
7. A legal-domain theorem into `CentralValueNonzero` whenever
   `bCal^(-1)` is used. `TrialNonzero` is insufficient.
8. The exact orientation: `bW=bCal`, `bW=bCal^(-1)`, or a proved third-scalar
   relation.
9. `WPrimeEquation5c`, proved separately rather than by unfolding the
   definition.
10. Complete archive hashes, if immutable-source hashes remain part of the
    acceptance criteria.

Thus the smallest honest statement is:

```text
CCM operator + determinant semantics recovered;
IndependentWPrimeConsumer still not recovered.
```

## b-orientation result

The project-side algebra is already locked on `CentralValueNonzero`:

\[
bCal=\widehat F(0)/\Xi(0),
\qquad
bZeoMul=\Xi(0)/\widehat F(0)=bCal^{-1},
\]

and

\[
G=bZeoMul\,\widehat F=\widehat F/bCal.
\]

These two scalars cannot be aliased without the additional condition
`bCal²=1`. CCM's `delta_N(xi)=1` and continuum `xi_lambda(lambda)=1` are
boundary normalizations, not central-value divisors. “Suitable constants” in
an Outlook passage selects neither scalar.

```yaml
b_ORIENTATION: OPEN
b_ORIENTATION_IS_THE_ONLY_OPEN_OBLIGATION: false
```

## Negative-search boundary

The strongest admissible claim is:

```text
NO_INDEPENDENT_WPRIME_CONSUMER_FOUND_ON_CHECKED_SURFACES
```

It is not legitimate to claim `NO_SUCH_OBJECT_EXISTS_ANYWHERE`. The broader
negative claims about all author GitHub repositories, Zenodo deposits,
unpublished Mathematica files, and journal supplements were not independently
reproduced in full and remain bounded Mythos-reported evidence.

## Acceptance tests 1–9

| Test | Verdict | Reason |
| --- | --- | --- |
| 1 | PASS, limited scope | CCM operator/determinant do not depend on project `alpha`, `DeltaE`, or the 5c RHS. |
| 2 | PASS, limited scope | Perturbing project `alpha`/`DeltaE` does not alter the CCM objects. |
| 3 | PASS, limited scope | 5c is neither definitionally forced nor proved by CCM. |
| 4 | PARTIAL / CONTRACT FAIL | Determinant identity is a theorem; `Xi` normalization is Outlook; no `WPrime` semantics theorem exists. |
| 5 | FAIL / OPEN | No `FZeo=G` or zero-free gauge/scalar relation was recovered. |
| 6 | FAIL / OPEN | Boundary normalization is not `bCal`, `bCal^(-1)`, or a proved third scalar. |
| 7 | NOT REACHED / OPEN | Any inverse calibration still needs `CentralValueNonzero`; `TrialNonzero` is insufficient. |
| 8 | PASS | No H3c/H4, RH, cofinal selector, `kappa`, or desired `Xi` convergence was imported. |
| 9 | PASS WITH CROSSWALK OPEN | CCM keeps `lambda` and `N` independent; `lambda²=m` and carrier equivalence remain unproved. |

The suite ratifies only a non-tautological neighboring determinant package,
not an `IndependentWPrimeConsumer`.

## Control-plane effect

```text
LEAN_EDITS:                    NONE
ROUTE_STATE_EDITS:             NONE
PHYSICAL_BUS_GOAL:             NONE
BUS_010:                       VOID
ROUTE_PROMOTION:               NONE
RH_CLAIM:                      NONE
GOAL_051_AUTHORIZATION:        NONE
D0.7e.5a STATUS:               BLOCKED
D0_7E_B_ORIENTATION_LOCKED:    NOT ISSUED
D0_7E_WPRIME_CONSUMER_MISSING: RETAINED
```

## Admissible continuations

### R1 — neighboring-H2b reclassification

Move the CCM operator/determinant package to the finite real-zero/H2b source
ledger and remove it from the `WPrime` candidate column. This fixes the type
error but does not close D0.7e.5a. Proshka scored cost `1/5`.

### R2 — explicit new-definition transaction

With explicit owner approval, mint a typed consumer with independent semantics
and prove 5c separately. This is new mathematics, never recovered provenance.
Proshka scored cost `4/5`.

### R3 — contract replacement by determinant observable

Replace the historical `WPrime` contract by a determinant-based downstream
theorem and re-prove every consumer interface. This is a major route revision;
existing 5c does not survive automatically. Proshka scored cost `5/5`.

## Strongest attack and forbidden moves

The categorical objection is:

> A complex regularized determinant is not a nonnegative scalar `WPrime`.

The normalization objection is:

> `delta_N(xi)=1` does not orient `bCal = Fhat(0)/Xi(0)`.

The domain objection is:

> A nonzero trial vector need not have nonzero central value.

Do not repeat any of these moves:

- rename the CCM determinant as `WPrime`;
- take its absolute value and call that source recovery;
- identify `bCal` with its inverse;
- use `TrialNonzero` as the inverse-calibration domain;
- define `WPrime` by the 5c right-hand side;
- cite the Outlook as a normalization theorem;
- present truncated reported hashes as independently verified full hashes.

## Final response ledger

```text
Exact CCM rank-one operator recovered: CONFIRMED
Independent determinant semantics recovered: CONFIRMED
No WPrime found on checked surfaces: CONFIRMED AS BOUNDED NEGATIVE EVIDENCE
Only b orientation remains: REFUTED
SOURCE_PARTIAL_B_ORIENTATION_OPEN: REQUIRES REPAIR
Existing stop remains: CONFIRMED
```

```yaml
iteration:
  target: D0.7e.5a external source acquisition
  status: OPEN
  failed_strategy: collapse_neighboring_determinant_observable_into_WPrime_consumer
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: SourceWPrimeDefinitionAndSemanticCrosswalk
  invariant_learned: operator, determinant, approximant, nonnegative detector scalar, normalization, and 5c are distinct typed objects
  forbidden_future_move: treat_outlook_normalization_or_determinant_modulus_as_source_recovery
  next_decisive_test: exact_source_defined_nonnegative_WPrime_with_independent_semantics
  progress_class: FALSIFICATION_PROGRESS_AND_REPRESENTATION_PROGRESS
  route_score: 5
```
