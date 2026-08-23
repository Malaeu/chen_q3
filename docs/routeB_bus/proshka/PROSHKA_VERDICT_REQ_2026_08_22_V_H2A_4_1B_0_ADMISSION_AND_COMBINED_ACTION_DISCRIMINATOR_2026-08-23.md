# STATUS: CONDITIONAL — H2A.4.1B.0 CLASSIFICATION ADMITTED; GENERIC `O(L_m)` CARRIER ENVELOPE KILLED; COMBINED SOURCE-ACTION DISCRIMINATOR AUTHORIZED
```yaml
PRIMARY: ADMIT_H2A_4_1B_0_AND_SELECT_COMBINED_SOURCE_ACTION_DISCRIMINATOR
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 989fd1272e0591ec0eb426947126ecced0b22a6e
  REPORT_COMMIT: 989fd1272e0591ec0eb426947126ecced0b22a6e
  ACTUAL_PARENT: 551d0c48161a1accf96badf6ab79204a195b01a7
  CLAIMED_PARENT: 551d0c48
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT_2026-08-23.md
  REPORT_GIT_BLOB: 2a8408d7987f85507790374f4c655d96f55d8dd2
  REPORT_LINES_REPORTED: 253
  LEAN_SOURCE_CHANGED_BY_REPORT: false

PREFLIGHT_ADMISSION:
  OUTCOME_CODE: L73_L2_INPUT_INSUFFICIENT_FOR_ERROR_GRAPH_NORM
  STATUS: RATIFIED
  EXACT_DUAL_DEFECT_IDENTITY: RATIFIED
  L73_HILBERT_NORM_DOES_NOT_IMPLY_SHIFTED_ARCH_GRAPH_NORM: RATIFIED
  FACTOR_FOUR_TARGET_SOURCE_ACTION_IDENTITY_ABSENT: RATIFIED_AT_CURRENT_SOURCE_LEVEL
  CURRENT_SCHEDULE_RATE_FATAL: false
  ARISTOTLE_USED: false
  NUMERICS_USED: false

CORRECTIONS_TO_REPORT:
  GENERIC_MISSING_A:
    proposed_statement: >-
      exists Cgraph, for every PairIndex i and every v in E_m_N i,
      graphNorm(i,v)^2 <= Cgraph * L_m(i) * norm(v)^2
    status: KILLED_AS_FALSE
    scope: ABSTRACT
    verifier: PAPER_PLUS_SOURCE_FORMULA
    reason: >-
      PairIndex has independent m and N, but the proposed right-hand side
      remembers only m.  At fixed m and N tending to infinity, the unit single
      mode V_N has Fourier mass concentrated near t=N/L_m while the shifted
      archimedean weight grows logarithmically there.  Hence the graph norm is
      unbounded in N and cannot be bounded by Cgraph*L_m uniformly over all
      PairIndex values.
    card: C04_SAME_COORDINATES_TWO_LAWS
    weakest_repair: >-
      retain explicit N-dependence, for example a logarithmic carrier factor,
      or specialize to the precommitted selected Ferrers schedule N=m.

  SELECTED_SCHEDULE_GRAPH_ENVELOPE:
    status: PLAUSIBLE_NOT_PROVED
    exact_schedule: selectedFerrersPreAnchorIndex k has m=N=k+2
    expected_shape: >-
      graphNorm(index_k,v)^2 <= Cgraph * polylog(m_k) * norm(v)^2
      for v in the selected carrier
    warning: >-
      the existing theorem is modewise and contains 1+abs(n/L_m); a vector-level
      bound must preserve the common finite-span structure and must not pay an
      uncontrolled dimension factor by triangle inequality.

  BOUNDED_COMPONENT_LEDGER:
    W02_structure: RATIFIED_AS_BOUNDED_RANK_TWO_FORM
    PRIME_structure: RATIFIED_AS_BOUNDED_MULTIPLIER_FORM
    useful_cofinal_growth_rate: NOT_ESTABLISHED
    prior_prediction_P_H2A41B0_2: PARTIALLY_CONFIRMED_STRUCTURE_ONLY
    reason: >-
      abstract opNorm existence is not a rate.  The direct triangle estimate for
      the prime multiplier is of order sqrt(m)*log(m), which combined with the
      current O(lambda^-1/2) Hilbert error and the O(sqrt(L)) consumer weight
      does not tend to zero.  This kills the generic ambient-opNorm proof route,
      not the actual source-specific prime cancellation.

  SEPARATE_ERROR_AND_TARGET_DECAY:
    status: REJECTED_AS_NECESSARY_REPRESENTATION
    scope: ABSTRACT
    verifier: PAPER_COUNTEREXAMPLE
    card: C10_FUNCTIONAL_NOT_SURROGATE
    plant: >-
      On C^2 let R=diag(0,1), a=0, q=e0, e=-e1 and g=e0+e1.  Then q=e+g and
      (R-a)q=0, while norm((R-a)e)=norm((R-a)g)=1.  The exact combined defect
      vanishes although both separated action terms are nonzero.
    consequence: >-
      A_k+T_k is a sufficient triangle majorant, not the exact consumer and not
      a necessary route.  A separate target theorem may still be used if sourced,
      but it may not be assumed to be the unique or cheapest representation.

H2A_BOUNDARY_AFTER_ADJUDICATION:
  H2A_4_1A_EXACT_ACTION_SPLIT: CLOSED
  H2A_4_1B_0_REPRESENTATION_PREFLIGHT: CLOSED
  GENERIC_PAIRINDEX_O_L_GRAPH_ENVELOPE: KILLED
  SELECTED_SCHEDULE_GRAPH_ENVELOPE: OPEN_CANDIDATE
  GENERIC_PRIME_OPNORM_RATE: INSUFFICIENT
  TARGET_ACTION_IDENTITY: OPEN
  COMBINED_SELECTED_SOURCE_ACTION_RATE: OPEN_PRIMARY
  SELECTED_RESIDUAL_DECAY: OPEN
  SECTOR_FLOORS: OPEN
  POSITIVE_COFINAL_EFFECTIVE_FLOOR: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN
  REAL_ZEROS: OPEN

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_READ_ONLY
  CODE: H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_GIT_REV_PARSE_HEAD
  LEAN_WRITE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  NUMERICS_AUTHORIZED: false
  OUTPUT_PATH: docs/routeB_bus/H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR_2026-08-23.md
  PRIMARY_ROLE: >-
    Decide the exact source representation for the selected residual rate before
    any further Lean theorem.  Test the combined shifted CCM action on the exact
    selected row first; use target-only or separated graph envelopes only if an
    independent source identity makes them genuinely cheaper.
  CLOSES_IF_SUCCESSFUL:
    - H2A_4_1B_SOURCE_ACTION_REPRESENTATION_SELECTION
    - H2A_4_1B_MINIMAL_SOURCE_RATE_CONTRACT
  OPENS: []

PREFLIGHT_REQUIRED_TESTS:
  - name: SEPARATE_ACTION_DECAY_IS_NOT_NECESSARY_PLANT
    task: >-
      Record and verify the C^2 plant R=diag(0,1), a=0, q=e0, e=-e1,
      g=e0+e1.  Any representation claiming that both separated terms must
      decay before the combined residual can decay is rejected.

  - name: GENERIC_GRAPH_SCALE_PLANT
    task: >-
      At one fixed m and increasing N, take the unit single mode at n=N.
      Use the exact zero-extended mode Fourier formula and the exact shifted
      archimedean lower growth to prove that no constant Cgraph can give the
      report's generic Cgraph*L_m bound for all PairIndex values.  State the
      weakest N-aware replacement and its selected N=m specialization.

  - name: COMBINED_COEFFICIENT_LOCK
    task: >-
      Use the public H2A.4.1A vector identity to expose eE_k+gE_k as the same
      selected kTrial/source row with the exact sourceScale and exact sTrial
      normalizer.  No fitted scalar, no division by an unproved uniform floor,
      and no replacement of the exact Rayleigh shift.

  - name: STRUCTURED_CCM_ACTION_EXPANSION
    task: >-
      Expand the literal source matrix action on the selected row using
      ccmWeilTau_structured_offdiag and ccmWeilMatFinite_structured_offdiag,
      retaining the diagonal term and the exact ordered carrier.  Determine
      whether the resulting expression is a closed divided-difference/moment
      defect or merely a restatement of matrix multiplication.

  - name: TARGET_R2_DISCRIMINATOR
    task: >-
      On the explicit coefficients of selectedFerrersFactorFourTargetProjection,
      test for an exact commutator, moment, radical, or divided-difference
      identity that controls its shifted defect.  Inversion-evenness and trial
      transform convergence are forbidden surrogates.

  - name: PRIME_ERROR_DISCRIMINATOR
    task: >-
      Determine whether the full source-scaled L73 pointwise error yields a
      direct bound for the prime pairing/action after the finite von-Mangoldt
      sum is kept intact.  The ambient prime opNorm bound by itself is rejected
      because its available growth does not close the weighted consumer.

  - name: SELECTED_GRAPH_SHAPE
    task: >-
      If a separated graph route still survives, state it only on the exact
      precommitted selected schedule N=m and derive its vector-level constant
      without summing modewise norms.  Do not state the false generic theorem.

PREFLIGHT_OUTCOME_CODES_EXACTLY_ONE:
  - COMBINED_SOURCE_ACTION_RATE_CONTRACT_FOUND
  - TARGET_DIVIDED_DIFFERENCE_RATE_CONTRACT_FOUND
  - SEPARATE_SELECTED_ENVELOPE_CONTRACT_FOUND
  - SOURCE_ACTION_RATE_REPRESENTATION_UNMAPPED
  - SEPARATE_ACTION_ROUTE_KILLED_BY_SOURCE_LOWER_BOUND

CANDIDATE_REPRESENTATIONS:
  R1:
    CODE: COMBINED_STRUCTURED_CCM_ACTION_ON_SELECTED_ROW
    ROLE: PRIMARY
    KILL_POWER: 10
    COST: 4
    ADVANTAGE: >-
      exact consumer; preserves cancellation between error and target; same
      source row, carrier, scale, schedule and Rayleigh shift
    DISCRIMINATOR: source-derived weighted combined residual bound

  R2:
    CODE: TARGET_STRUCTURED_COMMUTATOR_DIVIDED_DIFFERENCE
    ROLE: RUNNER_UP
    KILL_POWER: 8
    COST: 5
    ADVANTAGE: >-
      could isolate the only genuinely new target mathematics while leaving
      the error side to existing L73 inputs
    DISCRIMINATOR: exact closed target identity with a legal rate

  R3:
    CODE: SELECTED_SCHEDULE_GRAPH_PLUS_DIRECT_PRIME_ERROR
    ROLE: HIGH_COST_RUNNER_UP
    KILL_POWER: 7
    COST: 8
    ADVANTAGE: >-
      repairs the false generic graph theorem by retaining the selected N=m
      schedule and source-specific prime cancellation
    DISCRIMINATOR: vector-level selected graph envelope plus direct prime rate

ZERO_CONSISTENT_RESULT:
  status: INCONCLUSIVE
  required_discriminator: exact_combined_or_target_source_action_identity

FORBIDDEN:
  - write_H2A_4_1B_1_Lean_before_representation_selection
  - state_generic_Cgraph_times_L_m_for_all_PairIndex
  - drop_the_independent_N_coordinate
  - pay_a_dimension_factor_by_modewise_triangle_inequality
  - treat_A_k_plus_T_k_as_the_exact_or_only_consumer
  - infer_target_defect_zero_from_inversion_evenness
  - infer_target_defect_zero_from_trial_transform_convergence
  - use_ambient_prime_opNorm_as_a_rate_without_a_closing_growth_bound
  - use_absolute_row_sums
  - substitute_ambient_associated_operator_A_m
  - claim_finite_Riesz_is_an_ambient_compression
  - add_action_decay_as_a_new_hypothesis
  - change_selected_shell_row_schedule_scale_or_exact_Rayleigh_shift
  - bundle_sector_floors_ground_Theorem510_or_real_zeros
  - paper_axiom
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

SUCCESS: H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR_CLASSIFIED
FAILURE: H2A_4_1B_SOURCE_ACTION_REPRESENTATION_STILL_UNMAPPED

NEXT_LOAD_BEARING_GAP: H2A_4_1B_SELECTED_FERRERS_COMBINED_SOURCE_ACTION_RATE
NEXT_CHEAPEST_DECISIVE_TEST: >-
  Run the exact source-action representation discriminator.  First fire the
  separate-term and generic-scale plants.  Then test the structured CCM action
  on the combined selected row before authorizing any graph-envelope theorem.

REGISTERED_PREDICTIONS:
  P_H2A41B1_1:
    claim: the_generic_all_PairIndex_Cgraph_times_L_m_statement_is_false
    probability: 0.99
  P_H2A41B1_2:
    claim: separate_error_and_target_action_decay_is_not_necessary_for_combined_residual_decay
    probability: 0.995
  P_H2A41B1_3:
    claim: the_target_commutator_structure_alone_does_not_close_to_a_rate_identity
    probability: 0.90
  P_H2A41B1_4:
    claim: the_generic_ambient_prime_opNorm_route_does_not_close_the_weighted_rate
    probability: 0.97
  LIKELIEST_FAILURE: TARGET_OR_PRIME_SOURCE_ACTION_IDENTITY_MISSING

PRIOR_PREDICTION_FATES:
  P_H2A41B0_1:
    probability: 0.97
    fate: CONFIRMED
    result: current_L73_L2_control_does_not_bound_shifted_arch_graph_norm
  P_H2A41B0_2:
    probability: 0.88
    fate: PARTIALLY_CONFIRMED
    result: bounded_W02_and_prime_forms_exist_but_useful_cofinal_growth_rates_do_not
  P_H2A41B0_3:
    probability: 0.95
    fate: CONFIRMED_AT_CURRENT_SOURCE_LEVEL
    result: projected_factor_four_target_has_no_existing_radical_or_source_action_identity
  RETROACTIVE_REPAIR: false

CLOSES:
  - H2A_4_1B_0_FORM_GRAPH_PREFLIGHT_CLASSIFICATION
  - GENERIC_PAIRINDEX_O_L_GRAPH_ENVELOPE_CANDIDATE
  - SEPARATE_ACTION_DECAY_AS_NECESSARY_REPRESENTATION
OPENS: []

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_AUTHORIZED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. What is admitted

The report's exact dual-defect identity is semantically correct.  The finite
Riesz operator and the finite source-Weil form use the same literal
`ccmWeilMatFinite` matrix, on the same ordered carrier and with the same
conjugate-first convention.  This closes the object/orientation audit, but it
supplies no estimate. `[FINITE_CELL][LEAN]`

The outcome

```text
L73_L2_INPUT_INSUFFICIENT_FOR_ERROR_GRAPH_NORM
```

is also correct.  The shifted archimedean form is the squared norm of the
logarithmically weighted Fourier image on its exact form domain.  H2A.3 controls
only the unweighted `H_m` norm of the physical error.  Since the Fourier weight
is unbounded, no continuity estimate follows from that input alone.
`[COFINAL_FAMILY][LEAN]`

The source audit is also correct that the current tree contains no theorem
making the projected factor-four target a radical vector, an eigenvector, or a
vector with a decaying shifted finite-Riesz defect.  The source literature calls
this object an educated guess for the ground state; inversion-evenness is not a
replacement for an action theorem. `[COFINAL_FAMILY][PAPER]`

### 2. Strongest attack: the proposed generic graph theorem is false

The report proposes a bound depending only on `L_m = log m`, while `PairIndex`
contains an independent truncation coordinate `N`.  Fix any admissible `m` and
let `N` grow.  The carrier then contains the unit mode `V_N`.

Its exact zero-extended Fourier image is a translated normalized sinc packet
centred at

\[
 t=N/L_m.
\]

A fixed fraction of its `L²` mass lies in an interval of width comparable to
`1/L_m` around that centre.  On that interval the exact shifted archimedean
weight grows as

\[
 1+\log(2+N/L_m)
\]

up to fixed additive constants.  Consequently

\[
 \|W_i\mathcal F(V_N)\|_2^2
 \ge c\log(2+N/L_m)-C,
\]

whereas the proposed right-hand side is the fixed number `Cgraph*L_m`.
Letting `N→∞` contradicts the claimed uniform bound. `[ABSTRACT][PAPER]`

This is a **C04** kill.  The proposed reformulation forgot the independent
carrier coordinate `N`; equality after projecting `PairIndex` to `m` is not
an equality in the category seen by the graph norm.

The weakest repair is either to retain an explicit `N`-dependent logarithmic
factor or to specialize to the precommitted selected Ferrers schedule.  On that
schedule

```text
m = N = k+2,
```

so the high-mode logarithm is only `O(log m)`.  Thus a selected-schedule
polylogarithmic graph bound remains plausible.  It is not supplied by the
existing modewise theorem, whose constant contains `1+|n/L_m|`; a proof must
use the common finite-span structure rather than sum modewise norms and lose a
dimension factor. `[COFINAL_FAMILY][CONDITIONAL]`

### 3. Second attack: separated decay is a sufficient surrogate, not the consumer

Let

\[
R=\operatorname{diag}(0,1),\quad a=0,\quad q=e_0,
\quad e=-e_1,\quad g=e_0+e_1.
\]

Then `q=e+g` and

\[
 (R-a)q=0,
\]

while

\[
 \|(R-a)e\|=\|(R-a)g\|=1.
\]

Therefore the exact combined defect may vanish by cancellation while the two
separated terms stay large.  The triangle budget `A_k+T_k` is legal as a
sufficient condition, but it is not the exact functional and it is not a
necessary route. `[ABSTRACT][PAPER]`

This is a **C10 functional/surrogate kill**: the consumer is the norm of the
combined shifted action, while the proposed next programme treats the sum of
two norms as though it were the only representation.

### 4. Bounded W02 and Prime forms do not yet give a usable rate

The W02 and Prime objects are correctly identified as bounded ambient forms.
That proves continuity, not a cofinal envelope.  In particular the direct
triangle bound for the prime multiplier is controlled by

\[
 2\sum_{r\le m}\frac{\Lambda(r)}{\sqrt r}
 \le C\sqrt m\log m.
\]

With `λ=√m`, the current Hilbert error is only `O(λ^{-1/2})`, and the final
consumer carries an additional `O(√L)` factor.  This available generic bound
therefore grows rather than decays.  Failure of this sufficient bound does not
prove the actual prime action is large; it proves that source-specific
cancellation must be retained. `[COFINAL_FAMILY][PAPER]`

### 5. Selected next representation

The next test must start from the exact combined source action

\[
 (R_k-a_k)(eE_k+gE_k),
\]

which H2A.4.1A identifies, after the exact scale and normalizer, with the shifted
finite-Riesz residual of the same selected `kTrial`.  The literal CCM matrix has
an exact structured off-diagonal divided-difference formula.  The cheapest
belief-changing question is whether applying that structured matrix to the
selected row produces a closed source defect with a rate, or only rewrites the
same matrix multiplication.

A target-only commutator/divided-difference identity is the runner-up.  A
selected-schedule graph theorem is retained only as a high-cost fallback,
because it still needs a direct prime-error estimate and a vector-level
archimedean bound.

## FINAL PROPOSAL

Run exactly one read-only source-action discriminator at the path named in the
header.  Fire the two plants before deriving any candidate estimate.  Select
one representation and one minimal source-rate contract; do not write Lean in
this transaction.

Registered expectation: the generic graph statement and necessity of separate
decay both fail, while the decisive remaining question is whether the structured
CCM action exposes a source cancellation for the target/prime terms.

## STRONGEST ATTACK

The combined-action route can collapse into a tautology: substituting the
structured off-diagonal formula may merely restate `M*q` with more notation.
The discriminator must therefore produce one of:

```text
an exact cancellation identity;
a one-sided source envelope with a closing weighted rate;
an explicit residual formula in already controlled L73 quantities.
```

If it produces none, return

```text
SOURCE_ACTION_RATE_REPRESENTATION_UNMAPPED
```

and do not formalize another algebraic receiver.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR

MODE:
  READ_ONLY
  NO_LEAN_EDIT
  NO_ARISTOTLE
  NO_NUMERICS

PIN:
  start from the current rh_clean head after this verdict and verify it with
  git rev-parse before reading.

OUTPUT:
  docs/routeB_bus/H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR_2026-08-23.md

REQUIRED:
  execute every PREFLIGHT_REQUIRED_TEST from the YAML header;
  return exactly one listed outcome code;
  give exact source paths, theorem names and formulas;
  preserve the selected row, schedule, scale, carrier and Rayleigh shift;
  do not add a hypothesis and call it a supplier.

SUCCESS:
  one exact source representation and one minimal theorem contract are selected.

FAILURE:
  H2A_4_1B_SOURCE_ACTION_REPRESENTATION_STILL_UNMAPPED
```

## META CLOSEOUT

**What became smaller?**

The open wall is no longer “find an operator norm for two arbitrary pieces.”
It is the exact selected combined source-action rate, with two concrete
runner-up representations.

**What was killed?**

- the generic all-`PairIndex` `Cgraph*L_m` carrier theorem;
- treating bounded-form existence as a useful cofinal rate;
- treating separated error/target decay as a necessary representation.

**What must not be tried again?**

Do not forget `N`, do not pay a dimension factor by summing modewise bounds,
and do not formalize another triangle receiver before testing the exact combined
source action.

**Current smallest named gap:**

```text
H2A_4_1B_SELECTED_FERRERS_COMBINED_SOURCE_ACTION_RATE
```

**Next cheapest decisive test:**

The read-only structured-CCM combined-action discriminator.

**Fate of prior registered predictions:**

Recorded in the header without retroactive repair.

```yaml
iteration:
  target: H2A.4.1B source-action representation
  status: PROGRESS
  failed_strategy: generic_all_PairIndex_graph_envelope_plus_separate_triangle_terms
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: H2A_4_1B_SELECTED_FERRERS_COMBINED_SOURCE_ACTION_RATE
  invariant_learned: retain_independent_N_and_combined_source_action_cancellation
  forbidden_future_move: formalize_generic_O_L_graph_bound_or_another_triangle_receiver
  next_decisive_test: structured_CCM_action_on_exact_selected_row
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```
