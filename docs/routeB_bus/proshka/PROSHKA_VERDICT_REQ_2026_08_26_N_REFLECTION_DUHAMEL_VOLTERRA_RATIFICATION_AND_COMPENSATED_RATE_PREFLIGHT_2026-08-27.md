# STATUS: CONDITIONAL — DUHAMEL/VOLTERRA IDENTITY RATIFIED; REFLECTION-RATE TARGET REPAIRED

```yaml
PRIMARY: RATIFY_DUHAMEL_VOLTERRA_IDENTITY_AND_SELECT_COMPENSATED_REFLECTION_RATE_PREFLIGHT
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD_REPORT_COMMIT: 6c5f307f5bd93db49e14ecce703b24bf54016e59
  HEAD_REPORT_PATH: docs/routeB_bus/LINUX_REFLECTION_DUHAMEL_CROSSCHECK_GOAL058_2026-08-27.md
  HEAD_REPORT_BLOB: 028e730f19a7c5937dd17721e91d395ef2f33055
  CORRECTION_9_COMMIT: 78ee4b29b80e4f8340730f83c1a33c35cb33bcc2
  CORRECTION_9_PATH: docs/routeB_bus/LINUX_CORRECTION_9_MEASURE_DOES_NOT_ANNIHILATE_GOAL058_2026-08-27.md
  PARALLEL_CHAT_PIN: 5a02a6fdbeb861b101176950676c6c0929273dcc
  PARALLEL_CHAT_ROLE: RELAYED_PROPOSAL_NOT_VERDICT
  RELAY_RULE_SOURCE: 880cf3a064fbb2e130a23e3f4ee4fec0ac0436a6

MODE:
  REPORT_MODE: PAPER_PLUS_DECLARED_NUMERIC_CHECK
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: PASS
  REPORTED_CODE: TWO_INDEPENDENT_DERIVATIONS_ARE_ONE_IDENTITY
  DECISION: PASS_RATIFIED_FOR_EXACT_ALGEBRA_WITH_RATE_AND_CATEGORY_REPAIRS

  RELAY_PROVENANCE_HANDLING: PASS
  REFLECTION_TEST_ANTISYMMETRY: PAPER_PROVED
  RANK_ONE_HILBERT_COMMUTATOR: PAPER_PROVED
  DUHAMEL_COMMUTATOR_FACTORIZATION: PAPER_PROVED
  POLARIZED_VOLTERRA_EQUALS_DUHAMEL_CONVOLUTION: PAPER_PROVED
  DIAGONAL_TERM_IS_PRESENTATION_CONVERSION_TERM: PAPER_PROVED

  POSITIVE_MEASURE_ANNIHILATES_SMOOTH_TESTS: REFUTED
  POINTWISE_MODE_LOCALIZATION_OF_X_IS_REQUIRED: REFUTED
  NORM_OF_X_IS_FREE_BY_NORMALIZATION: REFUTED
  FULL_COMPLETED_OBJECT_IS_A_FINITE_MEASURE: REFUTED
  NAIVE_CUMULATIVE_NU_OF_T_IS_WELL_DEFINED: REFUTED
  REFLECTION_DISCREPANCY_IS_NONARITHMETIC: REFUTED

  PRIME_MAIN_TO_W02_LEADING_MATCH: PAPER_PASS_WITH_PERIODIC_FOLD_REPAIR
  CONSUMER_STRENGTH_RATE: OPEN
  TRACKING_CORRIDOR_THAWED: false

EXACT_IDENTITIES:
  MODE_OPERATOR: "N = diag(n_i)"
  HILBERT_MATRIX: "H_ij = 1/(n_i-n_j) for i != j; H_ii = 0"
  COMMUTATOR: "[N,H] = eta*eta^T - I"
  UNITARY_GROUP: "U_t = exp(i*t*N)"
  DUHAMEL: >-
    [U_t,H] = i * integral_0^t U_s*(eta*eta^T-I)*U_(t-s) ds.
  FACTORS:
    A_x_of_t: "<x,U_t eta>"
    B_q_of_t: "<eta,U_t q>"
  CONVOLUTION: "C_xq(t) = integral_0^t A_x(s)*B_q(t-s) ds"
  VOLTERRA_CROSSWALK: "K_xq(w) = (1/pi) * C_xq(2*pi*w)"

CATEGORY_REPAIR:
  ARCH_DENSITY_NEAR_ZERO: "approximately 1/(2*pi*t) dt after the angle change"
  CONSEQUENCE: >-
    The completed source acts on endpoint-vanishing test functions, but it is not
    a finite measure.  Reflection is legal as an identity of convergent
    functionals on the exact test class; it is not yet a finite signed measure
    with a naive total mass or cumulative distribution.
  FORBIDDEN_OBJECT:
    - "nu_m([0,t]) without endpoint compensation"
    - "total mass zero of a finite signed measure"
  REQUIRED_OBJECT: COMPENSATED_REFLECTION_FUNCTIONAL_OR_DISTRIBUTION

PERIODIC_FOLD_REPAIR:
  a: "L/(4*pi)"
  raw_W02_density: >-
    [L/(2*pi^2)]*(sqrt(m)-2+1/sqrt(m))*exp(-a*t) dt on t>0.
  reason_to_fold: "the test function is 2*pi-periodic"
  folded_W02_density_on_circle: >-
    [L/(2*pi^2)]*(sqrt(m)-1)*exp(-a*t) dt on 0<t<=2*pi.
  reflected_continuous_prime_main: >-
    [L*sqrt(m)/(2*pi^2)]*exp(-a*t) dt.
  exact_folded_difference: >-
    -[L/(2*pi^2)]*exp(-a*t) dt.
  remaining_source_terms:
    - weighted_Stieltjes_discrepancy_from_d_psi_minus_dx
    - lower_endpoint_1_to_2_correction
    - archimedean_endpoint_singular_functional
  guard: >-
    The O(log m) coefficient match is exact for the continuous main model after
    folding.  It is not an O(log m) bound for the full arithmetic discrepancy.

REGULARITY_REPAIR:
  exact_L2_norms:
    A_x: "||A_x||_L2_0_2pi = sqrt(2*pi)*||x||_2"
    B_q: "||B_q||_L2_0_2pi = sqrt(2*pi)*||q||_2"
    derivative_B_q: "||B_q'||_L2_0_2pi = sqrt(2*pi)*||N q||_2"
  valid_conclusion: >-
    A dimension-free Volterra H1/Hölder bound can be derived from ||x||_2,
    ||q||_2 and ||Nq||_2, using the one-dimensional trace bound for B_q(0).
    Pointwise mode-index control of x is unnecessary.
  rejected_shortcut: >-
    x=C^{-1}kappa(z) is not a unit vector.  Its compact L2 envelope must remain
    explicit or be derived from the graph floor and the P59 kernel envelope.
  q_normalization: "||q||_2 = 1 on the literal selected row"

CATALOG_CROSSWALK:
  existing_energy_contract: SelectedPhysicalFourierEnergyControl
  existing_normalizer_contract: SelectedTrialNormalizerBounded
  existing_first_order_route: selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget
  instruction: >-
    Do not mint TRIAL_MODE_ENERGY_BOUND_ALONG_THE_SCHEDULE as an unrelated
    supplier before checking the exact conversion from the existing physical
    Fourier-energy / first-order coefficient ledgers to ||Nq||_2.

CLOSES:
  - DUHAMEL_AND_VOLTERRA_AS_TWO_SEPARATE_CANDIDATES
  - POINTWISE_MODE_LOCALIZATION_OF_GRAPH_TEST_VECTOR_AS_NECESSARY_INPUT
  - LEADING_W02_PRIME_MAIN_CANCELLATION_MECHANISM_UNLOCATED

OPENS: []

CARRIES_OPEN:
  - GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE
  - SELECTED_TRIAL_MODE_ENERGY_RATE_FROM_EXISTING_FIRST_ORDER_LEDGER
  - COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_COMPENSATED_REFLECTION_DUHAMEL_RATE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: COMPENSATED_REFLECTION_DUHAMEL_CONSUMER_RATE_READY
  HOLD: COMPENSATED_REFLECTION_DUHAMEL_IDENTITY_WITHOUT_CONSUMER_RATE
  FAIL: REFLECTION_DUHAMEL_REIMPORTS_PRIME_DISCREPANCY_OR_GRAPH_INVERSE_WALL

CANDIDATE_REPRESENTATIONS:
  R1_COMPENSATED_CIRCLE_STIELTJES_DUHAMEL:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 4/10
    object: >-
      Fold the periodic W02 tail to the angle circle, subtract the continuous
      prime main term exactly, compensate the archimedean endpoint singularity,
      and pair the remaining source discrepancy with the Duhamel H1 kernel.
  R2_FULL_VOLTERRA_COEFFICIENT_CARLESON:
    rank: RUNNER_UP
    kill_power: 8/10
    proof_cost: 6/10
    object: >-
      Stay in the finite alpha/beta coefficient representation and prove a
      consumer-weighted square-function or Carleson estimate without forming a
      cumulative signed measure.

REGISTERED_PREDICTIONS:
  P_REFLECTION_DUHAMEL_1:
    probability: 0.55
    prediction: >-
      Exact compensated identity closes, but the weighted d(psi-x) discrepancy
      or the graph-test-vector compact norm prevents the required rate; HOLD.
  P_REFLECTION_DUHAMEL_2:
    probability: 0.30
    prediction: >-
      Folded W02 cancellation plus an existing selected-trial first-order energy
      supplier gives the consumer-strength rate; PASS.
  P_REFLECTION_DUHAMEL_3:
    probability: 0.15
    prediction: >-
      Endpoint-category or normalization audit shows the proposed cumulative
      representation is the wrong object; FAIL for R1, R2 remains alive.

PRIOR_PREDICTION_FATE:
  P_COMPLETED_SPECTRUM_1_0_70: CONFIRMED_WITH_REPRESENTATION_PROGRESS
  P_VOLTHILBERT_LEAN_1_0_88: NOT_TESTED

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - REPRESENTATION_PROGRESS
  - FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| The parallel-chat artifact is a verdict for the live branch | Rejected.  It was correctly treated as a relayed proposal pinned before the Volterra branch. | `[ABSTRACT][PAPER]` |
| Reflection antisymmetry of the exact test | Accepted. | `[FINITE_CELL][PAPER]` |
| `[N,H]=eta eta^T-I` | Accepted. | `[FINITE_CELL][PAPER]` |
| Duhamel formula for `[U_t,H]` | Accepted. | `[FINITE_CELL][PAPER]` |
| Polarized Volterra kernel and Duhamel convolution are different routes | Rejected.  They are one identity after `t=2*pi*w`. | `[FINITE_CELL][PAPER]` |
| The positive completed measure annihilates smooth functions | Refuted.  Cancellation comes from reflection antisymmetry. | `[COFINAL_FAMILY][PAPER]` |
| The completed source object is a finite measure | Refuted.  The Arch density has an endpoint `1/t` singularity; the exact pairing survives because the test vanishes at the endpoint. | `[COFINAL_FAMILY][PAPER]` |
| Pointwise mode localization of `x` is necessary | Refuted.  A dimension-free Volterra regularity bound uses `||x||`, `||q||`, `||Nq||`. | `[FINITE_CELL][PAPER]` |
| `||x||` is free by normalization | Refuted.  `x=C^{-1}kappa(z)` is not the normalized trial row. | `[COFINAL_FAMILY][PAPER]` |
| W02 matches the reflected prime main term | Accepted after periodic folding and support repair; the exact circle-level coefficient mismatch is order `L`. | `[COFINAL_FAMILY][PAPER]` |
| This proves the full arithmetic reflection discrepancy is order `L` | Rejected.  The weighted Stieltjes discrepancy from `d psi-dx` remains. | `[COFINAL_FAMILY][PAPER]` |
| Consumer-strength rate follows | Not proved. | `[COFINAL_FAMILY][CONDITIONAL]` |

## FINAL PROPOSAL

Run one paper-only transaction on the **full combined consumer**, not separate W02, Prime or Arch bounds.

The transaction must produce an exact identity of the form

\[
\Psi_{m,z}
=
\mathfrak L_m\bigl(K_{x_{m,z},q_m}\bigr),
\qquad
x_{m,z}=C_m^{-1}\kappa_m(z),
\]

where `mathfrak L_m` is the completed source functional with:

1. the W02 tail folded to the `2*pi` circle;
2. the reflected continuous prime main term subtracted exactly;
3. the Arch endpoint singularity compensated in the same functional category;
4. the actual von-Mangoldt remainder retained as a weighted Stieltjes discrepancy.

It must then derive a dimension-free regularity estimate for the Duhamel kernel.  A legitimate target is

\[
\|K_{x,q}\|_{H^1(0,1)}
\le
C\,\|x\|_2\bigl(\|q\|_2+\|Nq\|_2\bigr),
\]

with the exact `2*pi` rescaling and trace term written out.  The left factor `||x||` must remain in the final ledger.

Finally it must substitute source-locked estimates for all three remaining factors:

```text
compact graph-test envelope for ||C^{-1}kappa(z)||;
selected trial mode energy ||Nq||;
compensated reflection discrepancy of the completed source.
```

`PASS` is earned only if their product meets the existing compact tracking budget.  An exact identity plus a divergent or unclassified product is `HOLD`, not progress by relabeling.

## STRONGEST ATTACK

The strongest objection is the arithmetic one:

> Matching W02 with the reflected continuous main term does not estimate the difference between the actual von-Mangoldt atoms and `dx`.

Correct.  The remainder is a weighted Stieltjes transform of `d(psi-x)`.  If its best unconditional bound, after the exact consumer regularity ledger, still returns the old sub-power-versus-power mismatch, then R1 has merely exposed the retained-prime wall in the right coordinates.  That earns `FAIL` for R1, not permission to split the source components again.

The second objection is functional-analytic:

> The report calls the completed object a finite measure and then forms a cumulative discrepancy, but the Arch density has logarithmically infinite mass at the lower endpoint.

Correct.  The next transaction must compensate the `1/t` endpoint singularity or move to R2.  A naive cumulative distribution is not a legal object.

The third objection is normalization:

> The Duhamel estimate still contains `||x||`; why is it harmless?

It is not harmless by declaration.  `x=C^{-1}kappa(z)` is not unit-normalized.  Its compact envelope must be derived from the literal graph floor and the P59 kernel or remain an open factor.

## CODEX DIRECTIVE

```text
NO LEAN, NUMERICS, ARISTOTLE, OR CODEX EXECUTION.

TASK_ID:
  GOAL058_SELECTED_FERRERS_COMPENSATED_REFLECTION_DUHAMEL_RATE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

Required output:
  1. Exact full-source functional identity in one category.
  2. Exact periodic folding of the W02 tail.
  3. Exact endpoint compensation for the Arch 1/t singularity.
  4. Exact Duhamel/Volterra H1 bound with ||x||, ||q|| and ||Nq||.
  5. Exact crosswalk from existing selected physical Fourier-energy or
     first-order coefficient suppliers to ||Nq||.
  6. Exact compact envelope for ||C^{-1}kappa(z)||, or a named missing supplier.
  7. Weighted Stieltjes discrepancy ledger for d(psi-x), with all boundary terms.
  8. Final product/rate against the literal tracking consumer.

Mandatory plants:
  P1. Arch endpoint singularity: naive cumulative nu([0,t]) must fail.
  P2. High-mode x with fixed norm: no pointwise x localization may be assumed.
  P3. Exact-ground case: the full combined consumer must vanish identically.
  P4. Continuous-prime-main replacement: the folded W02 mismatch must equal the
      explicit order-L density, not the unfurled coefficient.
  P5. A graph operator with collapsing floor: ||C^{-1}kappa|| must expose the
      inverse-floor cost.

PASS:
  COMPENSATED_REFLECTION_DUHAMEL_CONSUMER_RATE_READY

HOLD:
  COMPENSATED_REFLECTION_DUHAMEL_IDENTITY_WITHOUT_CONSUMER_RATE

FAIL:
  REFLECTION_DUHAMEL_REIMPORTS_PRIME_DISCREPANCY_OR_GRAPH_INVERSE_WALL
```

## META CLOSEOUT

**What became smaller?**

Two apparently independent ideas collapsed to one exact finite identity.  The unknown is no longer pointwise mode behavior of the graph solve; it is one product of a graph-test norm, a trial first-mode energy and a compensated source discrepancy.

**What was killed?**

```text
positive-measure annihilation;
finite-measure language for the Arch source;
pointwise x localization as a necessary supplier;
free normalization of x;
unfolded W02/main-term comparison.
```

**What must not be tried again?**

```text
componentwise W02/Prime/Arch norm bounds;
naive cumulative discrepancy across the Arch endpoint;
dropping the diagonal term;
calling x normalized;
using the continuous prime main term as the actual prime measure.
```

**Current smallest named gap**

```text
COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE
```

**Next cheapest decisive test**

Derive the exact compensated Stieltjes/Duhamel product ledger before any formalization.

**Memory entry**

```yaml
iteration:
  target: completed reflection/Duhamel consumer rate
  status: OPEN
  failed_strategy: positive measure annihilation plus naive cumulative discrepancy
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE
  invariant_learned: cancellation lives in reflection antisymmetry on one full source functional
  forbidden_future_move: split W02, Arch and Prime or discard endpoint singular structure
  next_decisive_test: compensated circle Stieltjes/Duhamel rate audit
```
