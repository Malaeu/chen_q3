# STATUS: OPEN — ZERO-TRANSFER IDENTITY RATIFIED; THE ZERO-FREE-STRENGTH CLOSEOUT IS NOT YET PROVED

```yaml
PRIMARY: RATIFY_ZERO_TRANSFER_IDENTITY_AND_REPAIR_PREMATURE_CIRCULARITY_KILL
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 0acfef971a273117b42f47f0f4a4622db512ca9d
  REPORT_PATH: docs/routeB_bus/LINUX_ZERO_TRANSFER_CIRCULARITY_PREFLIGHT_GOAL058_2026-08-28.md
  REPORT_BLOB: cf9b9ca36e58379bbcd769b19d8db747dc54907c
  REPORT_LINES: 163
  PARENT_VERDICT_COMMIT: ac8b183b8d11c1fc1b7274ab9cea2e9c3cb34b42
  REPORT_WAS_BRANCH_HEAD_AT_ADJUDICATION: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY_PLUS_DECLARED_NUMERIC_VERIFICATION
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: FAIL
  REPORTED_CODE: SIGNED_ORIENTED_STIELTJES_RATE_IS_ZERO_FREE_REGION_STRENGTH
  DECISION: HOLD_REPAIRED

  FINITE_LAPLACE_TRANSFER_FORMULA: PAPER_PASS
  POLARIZED_SOURCE_PAIRING_IDENTITY: PAPER_PASS
  P59_KERNEL_ROWS_LINEAR_SPAN: PAPER_PASS
  EXACT_IDENTICALLY_ZERO_CRITERION: PAPER_PASS

  ENDPOINT_AND_Q_ORTHOGONALITY_FORCE_ANNIHILATION: REFUTED
  AUTOMATIC_VOLTERRA_ANNIHILATOR: REFUTED

  LITERAL_SELECTED_FERRERS_Q_FAILS_EIGENVECTOR_CRITERION: NOT_PROVED
  FIXED_COMPACT_QUANTITATIVE_OBSERVABILITY: OPEN
  SELECTED_TRANSFER_LOWER_ENVELOPE: OPEN
  QUARTET_CANCELLATION_LOWER_ENVELOPE: OPEN
  CROSS_ZERO_ISOLATION: OPEN

  REPORT_CLAIM_GRAPH_SOLVE_GIVES_LOWER_BOUND_ON_Y: REFUTED
  REQUIRED_SIGNED_RATE_IS_ZERO_FREE_REGION_STRENGTH: NOT_ESTABLISHED
  ARITHMETIC_GATE_CLOSED_NEGATIVE: false
  EXACT_ANNIHILATION_SHORTCUT_CLOSED_NEGATIVE: true
  TRACKING_CORRIDOR_THAWED: false

REPORT_REPAIRS:
  ranges_over_all_q_perp:
    report_phrase: "y ranges over all of q-perp as z varies"
    replacement: >-
      The linear span of the vectors y(z)=C^(-1)Q*kappa(z) is q-perp.
      A one-complex-parameter curve need not be set-theoretically surjective onto
      a higher-dimensional vector space.  Linear span is sufficient for the
      exact identically-zero criterion, but not for a uniform lower bound.

  exact_nonzero_vs_quantitative_rate:
    report_inference: >-
      Q*Phi(a) != 0, or failure of exact eigenvector alignment, forces a
      consumer-strength lower bound.
    verdict: REFUTED_AS_AN_IMPLICATION
    reason: >-
      A nonzero finite-dimensional vector may approach the annihilating line
      arbitrarily fast along the cofinal family.  Exact nonannihilation supplies
      no lower envelope in m.

  graph_inverse_lower_bound:
    report_phrase: "||y|| is bounded below by the graph solve"
    verdict: REFUTED
    reason: >-
      Positivity or a complement floor bounds ||C^(-1)v|| from above.  A uniform
      lower bound requires an upper envelope for C and a lower envelope for the
      observed P59 row.  Invertibility alone gives neither.

  compact_quantifier:
    verdict: REPAIRED
    reason: >-
      Locally uniform tracking is tested on one fixed compact K.  Algebraic span
      on the full spectral plane proves injectivity for each finite cell, but the
      associated observability constant may decay arbitrarily fast as the cell
      grows.

  quartet_claim:
    report_phrase: >-
      The two growing quartet terms vanish identically only by the same criterion
      Q*Phi(a)=0.
    verdict: NOT_YET_EXACT
    reason: >-
      On a real spectral slice the growing pair is governed by the real part of
      exp(2*pi*a)*Phi(a).  The exact cancellation criterion must be derived in
      the real/complex source category; it is generally weaker than Phi(a) lying
      on the q-line.

  circularity_semantics:
    verdict: REPAIRED
    replacement: >-
      Proving a rate that implies a zero-free region is not, by itself, a circular
      proof.  It classifies theorem strength.  Circularity requires an audit of
      the proof inputs.  Operational route-kill is justified only after a
      quantitative converse or lower envelope is proved.

EXACT_RATIFIED_IDENTITIES:
  transfer_coefficients:
    r: "exp(-2*pi*a)"
    S_n: "n*(1-r)/(a^2+n^2)"
    C_n: "(a^2-n^2)*(1-r)/(a^2+n^2)^2 - 2*pi*a*r/(a^2+n^2)"
  transfer: >-
    T_m,z(a)=integral_0^(2*pi) J_m,z(t)*exp(-a*t) dt
            = < y_m,z, Phi_m(a) >.
  y: "C_m^(-1)*Q_m*kappa_m(z)"
  Phi: "([S_a,H_m]+C_a)*q_m"
  exact_annihilation: >-
    z |-> T_m,z(a) is identically zero iff Q_m*Phi_m(a)=0, equivalently
    q_m is an eigenvector of [S_a,H_m]+C_a.
  scope: FINITE_CELL
  verifier: PAPER

COMPACT_OBSERVABILITY_COMPUTING_OBJECT:
  K: "one fixed compact with nonempty interior in the tracking strip"
  observation_map: >-
    O_m,K(v) = sup_{z in K} |<C_m^(-1)Q_m*kappa_m(z),v>|,
    for v in q_m-perp.
  observability_constant: >-
    Obs_m,K = inf_{v in q_m-perp, ||v||=1} O_m,K(v).
  finite_cell_fact: >-
    Obs_m,K > 0 for each fixed finite m, because the observation map is injective
    on the finite-dimensional q_m-perp space.
  missing_cofinal_fact: >-
    No lower envelope for Obs_m,K, or for
    Obs_m,K * ||Q_m*Phi_m(a_rho)||, has been proved along the selected schedule.

ZERO_FREE_STRENGTH_CONDITION:
  rho: "a hypothetical zero with sigma=Re(rho)-1/2>0"
  a_rho: "(rho-1/2)*log(m)/(2*pi)"
  necessary_quantitative_object: >-
    Z_m,K(rho)=m^sigma*(log m)^(3/2)*
      sup_{z in K}|T_m,z(a_rho)|.
  required_for_reported_kill: >-
    A source-locked lower envelope or nonvanishing limsup for the exact quartet
    contribution, together with a theorem preventing cancellation by the other
    zero terms.
  current_status: OPEN

FALSIFIERS:
  NONZERO_IS_NOT_A_RATE:
    construction: >-
      A sequence Q_m*Phi_m != 0 may have norm exp(-m).  Then the exact
      annihilation criterion fails at every cell while every polynomial or fixed
      power amplification still tends to zero.
    conclusion: >-
      Exact nonannihilation does not imply zero-free-region strength.

  INVERTIBLE_GRAPH_IS_NOT_LOWER_BOUNDED:
    construction: >-
      On q-perp take C_m=m^(2*sigma)*I.  Then C_m is positive and invertible and
      preserves q-perp, but ||C_m^(-1)v||=m^(-2*sigma)||v||.
    conclusion: >-
      The graph solve can suppress a transfer despite exact span and
      nonannihilation.

  GENERIC_TWO_MODE_PLANT:
    status: ACCEPTED
    conclusion: >-
      Endpoint zeros and Q-orthogonality alone do not annihilate the exponential
      transfer.  This kills only the generic shortcut, not the literal selected
      cofinal lower envelope.

SMOOTH_AND_REPRESENTATION_ASSETS:
  ORIENTED_ONE_FUNCTIONAL_IDENTITY: PRESERVED
  SMOOTH_W02_PRIME_MAIN_TV_CEILING_6_OVER_PI: PRESERVED
  POLARIZED_VOLTERRA_DUHAMEL_IDENTITY: PRESERVED
  P59_FULL_LATTICE_NORM_IDENTITY: PRESERVED
  CENTER_SPECTRAL_NORMAL_FORM: PRESERVED
  LEAN_ASSETS: PRESERVED

CLOSES:
  - ZERO_TRANSFER_FINITE_CLOSED_FORM
  - ZERO_TRANSFER_POLARIZED_SOURCE_PAIRING
  - ZERO_TRANSFER_EXACT_IDENTICALLY_ZERO_CRITERION
  - ENDPOINT_Q_ORTHOGONALITY_AS_AUTOMATIC_ANNIHILATOR

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - QPROJECTED_P59_KERNEL_COMPACT_RATE
  - SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
  - SelectedPhysicalFourierEnergyControl
  - ZERO_TRANSFER_COMPACT_OBSERVABILITY_LOWER_ENVELOPE
  - QUARTET_AND_CROSS_ZERO_CANCELLATION_CLASSIFICATION
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

EXECUTION_PRIORITY:
  keep_other_five_inputs_frozen: true
  reason: >-
    They remain wasted work until the arithmetic lower-envelope question is
    classified.  The report did not yet classify it.
  owner_representation_rerank_now: PREMATURE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_ZERO_TRANSFER_COMPACT_OBSERVABILITY_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_TRANSACTION_REQUIRED_OUTPUTS:
  - exact source-locked full zero contribution, including signs and all scalar factors
  - replace global algebraic span by the fixed-compact observation operator O_m,K
  - exact finite-cell proof Obs_m,K > 0
  - cofinal lower or upper envelope for O_m,K(Q_m*Phi_m(a_rho))
  - exact growing-quartet vector and its cancellation criterion
  - theorem or counterexample for cancellation among all zeros with maximal real part
  - no use of "no supplier found" or "no reason to hold" as mathematical evidence
  - explicit comparison with the threshold m^(-sigma)*(log m)^(-3/2)

NEXT_DISCRIMINATOR:
  PASS: ZERO_TRANSFER_COMPACT_LOWER_ENVELOPE_ESTABLISHES_ZERO_FREE_STRENGTH
  HOLD: ZERO_TRANSFER_EXACT_WITHOUT_QUANTITATIVE_COMPACT_OBSERVABILITY
  FAIL: SOURCE_SPECIFIC_ZERO_TRANSFER_DECAYS_BELOW_OFFLINE_SCALE

CANDIDATE_REPRESENTATIONS:
  R1_DIRECT_COMPACT_OBSERVATION_PRODUCT:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 3/10
    object: >-
      Estimate the one literal scalar function
      O_m,K(Q_m*Phi_m(a_rho)) directly, retaining graph inverse, selected row,
      P59 kernel and the fixed compact in one object.

  R2_EXPLICIT_FORMULA_CONVERSE_FOR_SELECTED_TEST_FAMILY:
    rank: RUNNER_UP
    kill_power: 9/10
    proof_cost: 8/10
    object: >-
      Prove an Ingham/Turan-style converse for the complete m-dependent selected
      test family, including quartet and equal-real-part zero cancellation.

REGISTERED_PREDICTIONS:
  P_COMPACT_OBS_1:
    probability: 0.55
    prediction: >-
      Exact finite observability closes, but its cofinal constant decays too fast
      or remains uncontrolled; result HOLD.
  P_COMPACT_OBS_2:
    probability: 0.30
    prediction: >-
      The literal selected vector has a source-specific lower envelope strong
      enough to classify the rate as zero-free-region strength; operational
      rerank becomes justified.
  P_COMPACT_OBS_3:
    probability: 0.15
    prediction: >-
      Selected q asymptotically approaches the exponential-source eigenline or
      the graph inverse suppresses the observation, refuting the reported kill.

PRIOR_PREDICTION_FATE:
  P_ZERO_TRANSFER_1_0_74: PARTIAL_ONLY
  P_ZERO_TRANSFER_1_NOTE: >-
    Automatic exact annihilation was not found, but zero-free-region strength was
    not proved because the quantitative compact lower envelope is missing.
  P_ZERO_TRANSFER_2_0_18: NOT_REALIZED_AS_A_GENERIC_IDENTITY
  P_ZERO_TRANSFER_2_NOTE: >-
    Literal selected-family asymptotic annihilation remains unclassified.
  P_ZERO_TRANSFER_3_0_08: PARTIAL_REPAIR_REQUIRED
  P_ZERO_TRANSFER_3_NOTE: >-
    Source sign did not fail, but compact observability and quartet categories
    require repair before the conclusion can be scored.

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| The finite Laplace-transfer coefficient has the displayed closed form | Accepted. | `[FINITE_CELL][PAPER]` |
| `T(a)=<y,([S_a,H]+C_a)q>` | Accepted with the report's star-first convention. | `[FINITE_CELL][PAPER]` |
| P59 rows span the carrier | Accepted as a linear-span statement; at lattice points they give scaled coordinate vectors. | `[FINITE_CELL][PAPER]` |
| `T_m,z(a)` is identically zero iff `q_m` is an eigenvector of the exponential-source Loewner matrix | Accepted for a fixed finite cell. | `[FINITE_CELL][PAPER]` |
| The literal selected Ferrers row fails that eigenvector condition | Not proved. Absence of a catalogue supplier is not a negation theorem. | `[COFINAL_FAMILY][CONDITIONAL]` |
| Exact nonannihilation forces a consumer-strength lower bound | Refuted as an implication. | `[ABSTRACT][PAPER]` |
| The graph inverse supplies a uniform lower bound | Refuted; the available floor supplies the opposite inequality. | `[ABSTRACT][PAPER]` |
| Quartet symmetry cannot cancel the growing terms | Not yet proved in the exact real/complex category. | `[COFINAL_FAMILY][CONDITIONAL]` |
| The required signed rate is proved to be zero-free-region strength | Not established. | `[COFINAL_FAMILY][CONDITIONAL]` |
| The arithmetic gate is closed in the negative | No. Only the exact-annihilation shortcut is closed. | `[COFINAL_FAMILY][PAPER]` |

## FINAL PROPOSAL

Keep the five nonarithmetic suppliers frozen.  Do not rerank the whole route yet.
Run one last paper-only discriminator on the exact fixed-compact observation
product

\[
\sup_{z\in K}
\left|
\left\langle
C_m^{-1}Q_m\kappa_m(z),
Q_m([S_{a_\rho},H_m]+C_{a_\rho})q_m
\right\rangle
\right|.
\]

The report has proved that this scalar is not forced to vanish identically by the
generic geometry.  It has not proved how fast it can decay on the literal selected
family.  That rate, together with quartet and cross-zero isolation, is the exact
remaining decision point.

## STRONGEST ATTACK

The report substitutes three weaker facts for the required lower envelope:

```text
nonzero vector;
linear span;
invertible graph operator.
```

None is quantitative.  For example, an invertible graph operator may have size
`m^(2*sigma)` on `q-perp`, so its inverse suppresses every observed vector by
`m^(-2*sigma)`.  Likewise a selected row may approach the exponential-source
eigenline without ever lying on it exactly.  Both cases satisfy the report's exact
criterion while defeating its claimed lower bound.

Therefore the report closes a sharp finite identity and kills an automatic
annihilator.  It does not yet prove a zero-free-region converse.

## CODEX DIRECTIVE

```text
NO LEAN OR CODEX EXECUTION AUTHORIZED.

NEXT PAPER-ONLY TASK:
  GOAL058_SELECTED_FERRERS_ZERO_TRANSFER_COMPACT_OBSERVABILITY_PREFLIGHT

Compute exactly:
  O_m,K(Q_m*Phi_m(a_rho))

on the literal selected family and one fixed compact K.

PASS only from a source-locked lower envelope strong enough to beat
  m^(-sigma)*(log m)^(-3/2).

FAIL only from a source-faithful upper envelope showing the transfer can decay
below that scale.

Otherwise return HOLD with the exact uncontrolled factor.
```

## META CLOSEOUT

**What became smaller?**

The signed arithmetic wall is now one explicit compact observation scalar, not an
unknown oscillatory integral.

**What was killed?**

Endpoint vanishing, Q-orthogonality, P59 span, and Volterra structure do not by
themselves create an exact annihilator.

**What must not be tried again?**

Do not promote `Q*Phi != 0` to a cofinal lower bound.  Do not infer a lower bound
from invertibility or a complement floor.  Do not call theorem strength
"circularity" without auditing proof dependencies.

**Current smallest named gap?**

```text
ZERO_TRANSFER_COMPACT_OBSERVABILITY_LOWER_ENVELOPE
```

**Next cheapest decisive test?**

The direct fixed-compact observation-product preflight above.

**Prediction fate?**

`P_ZERO_TRANSFER_1` is only partially confirmed; its load-bearing zero-free-strength
half remains unproved.  No retroactive repair is applied.

**Memory entry?**

```yaml
iteration:
  target: SIGNED_ORIENTED_STIELTJES_EVALUATION_OR_ITS_CIRCULARITY_VERDICT
  status: PROGRESS
  failed_strategy: EXACT_NONANNIHILATION_AS_QUANTITATIVE_LOWER_BOUND
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: ZERO_TRANSFER_COMPACT_OBSERVABILITY_LOWER_ENVELOPE
  invariant_learned: exact span and nonzero do not control a cofinal rate
  forbidden_future_move: infer lower bounds from invertibility or source absence
  next_decisive_test: fixed-compact literal observation-product envelope
```
