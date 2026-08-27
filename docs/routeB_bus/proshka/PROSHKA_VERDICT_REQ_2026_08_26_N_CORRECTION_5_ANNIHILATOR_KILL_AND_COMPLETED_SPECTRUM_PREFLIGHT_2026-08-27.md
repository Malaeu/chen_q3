# STATUS: OPEN — CORRECTION 5 RATIFIED; ANNIHILATOR KILLED; COMPLETED-SPECTRUM PREFLIGHT SELECTED

```yaml
PRIMARY: RATIFY_CORRECTION_5_KILL_ANNIHILATOR_SELECT_COMPLETED_SPECTRUM_PREFLIGHT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-26-N

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  PRIOR_PROSHKA_VERDICT_COMMIT: b1c580ca5d7fbee05f225601ad43d6d87fc24c25
  PRIOR_PROSHKA_VERDICT_PATH: >-
    docs/routeB_bus/proshka/
    PROSHKA_VERDICT_REQ_2026_08_26_N_CUT_TREE_RICCI_PARITY_REPAIR_AND_ANNIHILATOR_PRIORITY_2026-08-27.md

  ANNIHILATOR_REPORT_COMMIT: 6d647f0575e3debac84486e4c37d80cd2e9eff2b
  ANNIHILATOR_REPORT_PATH: >-
    docs/routeB_bus/LINUX_PRIME_POWER_ANNIHILATOR_RANGE_OBSTRUCTION_GOAL058_2026-08-27.md

  CORRECTION_5_COMMIT: a4bcf77722dd37fe537fe25ace343a3b4e504028
  CORRECTION_5_PATH: >-
    docs/routeB_bus/LINUX_CORRECTION_5_PARITY_DOES_NOT_IMPLY_SIGN_FRUSTRATION_GOAL058_2026-08-27.md

  HEAD_AT_ADJUDICATION: a4bcf77722dd37fe537fe25ace343a3b4e504028
  EXECUTION_CHAIN_IS_LINEAR: true

MODE:
  REPORTS_AUDITED: PAPER_AND_SOURCE_READ_ONLY
  JUDGE_RERAN_LEAN: false
  JUDGE_RAN_NUMERICS: false
  JUDGE_USED_ARISTOTLE: false

CORRECTION_5:
  PARITY_SIGN_FRUSTRATION_FATAL: WITHDRAWN_CORRECTLY
  BROKEN_STEP: >-
    oddness plus nonzero does not imply existence of a positive value at a
    positive mode
  SOURCE_BETA_POSITIVE_AT_A_POSITIVE_MODE:
    project_supplier_found: false
    status: OPEN_NOT_ASSUMED
  TRIANGLE_PRODUCT_IDENTITY:
    status: PAPER_PASS_WITH_DISTINCT_NONZERO_EDGE_GUARD
  GENERAL_NO_LIS3_NECESSARY_CONDITION: PAPER_PASS
  GENERAL_MONOTONE_EQUIVALENCE: false
  GENERAL_COUNTEREXAMPLE_0_2_1_HALF: accepted_for_arbitrary_sequences
  ACTUAL_ODD_SOURCE_MONOTONICITY_REDUCTION:
    status: PAPER_PASS_WITH_PAIRWISE_DISTINCTNESS_GUARD
    statement: >-
      For an odd source beta on the symmetric ordered lattice, beta_0=0 and
      pairwise-distinct values, the all-negative Doob sign gauge exists iff beta
      is strictly decreasing in the mode index; in that case the identity gauge
      already works.
  CHEAPEST_STRICT_KILL_WITNESS: >-
    One positive first difference Delta beta_n > 0 on the nonnegative half is
    enough to kill the strict sign gate. Two consecutive positive differences
    are not required.
  ZERO_EDGE_CASE:
    status: OPEN_SEPARATE_SUPPORT_GRAPH_CYCLE_AUDIT
    note: >-
      Equal beta-values create zero edges. Triangle signs alone then do not
      automatically classify every longer cycle of the nonzero support graph.

ANNIHILATOR_ADJUDICATION:
  REPORTED_DISCRIMINATOR: FAIL
  REPORTED_FAILURE_CODE: ANNIHILATOR_RANGE_CONDITION_IS_THE_TARGET_RESTATED
  DECISION: RATIFIED_WITH_EFFECTIVE_FREQUENCY_AND_FINITE_OPERATOR_REPAIRS

  INFINITE_SHIFT_RECURRENCE: PAPER_PASS
  MONOLITHIC_ANNIHILATOR_AS_CANCELLATION_MECHANISM: KILLED
  HAAR_LOCAL_ANNIHILATORS_AS_CANCELLATION_ESCAPE: KILLED
  FOURIER_SAMPLE_IDENTITY: RETAINED_AS_EXACT_COMPUTING_OBJECT

  RAW_DEGREE_EQUALS_2_J_PP:
    status: REJECTED_WITHOUT_COLLISION_QUOTIENT
    repair: >-
      Use the number of distinct effective roots after endpoint, conjugacy and
      q1*q2=m collisions. The degree is d_eff=|Z_eff| <= 2 J_pp, not 2 J_pp by
      declaration.
  FINITE_RANGE_KERNEL_CLAIM:
    status: CONDITIONAL_ON_OPERATOR_LOCK
    required_object: >-
      A precise recurrence restriction map, including its domain, codomain and
      boundary convention. A square zero-padded shift matrix is not silently the
      same operator.
  CORE_KILL_SURVIVES_REPAIRS: true
  CORE_KILL_REASON: >-
    Any adjoint-range decomposition must leave a remainder carrying the full
    projection of the consumer weight onto the effective prime-frequency span.
    That span has growing dimension d_eff. Calling it a finite edge remainder
    does not reduce the exact consumer.

PROPOSED_REPLACEMENT_AUDIT:
  PRIME_ONLY_UPPER_BAND_LOCALIZATION: REJECTED_AS_FINAL_TARGET
  reason: >-
    The exact off-diagonal consumer uses the completed beta field
    W02 + Arch - Prime, and the literal residual also has a diagonal channel.
    A separate prime-channel bound can destroy the cancellation the route has
    repeatedly had to preserve.
  cards:
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C04_SAME_COORDINATES_TWO_LAWS

SELECTED_REPRESENTATION:
  name: COMPLETED_BETA_POLARIZED_SPECTRAL_PAIRING
  exact_left_vector: x_k(z)=C_k^(-1)*kappa_k(z)
  exact_right_vector: q_k=selected_Ferrers_trial_row
  exact_weight: >-
    omega_i(x,q)=conj(x_i)*(Hq)_i + conj((Hx)_i)*q_i
  exact_zero_mass: sum_i omega_i(x,q)=0
  target_fourier_identity: >-
    omega_hat(theta)=<x,[M_theta,H]q>,
    M_theta=diag(exp(i*n_i*theta)), with star-first orientation
  full_consumer: >-
    diagonal source action plus the completed signed pairing
    sum_i beta_i*omega_i; no componentwise norm split

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SPECTRUM_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: COMPLETED_BETA_POLARIZED_SPECTRUM_SOURCE_RATE_READY
  HOLD: COMPLETED_SPECTRAL_IDENTITY_WITHOUT_SOURCE_LOCALIZATION_RATE
  FAIL: COMPLETED_SPECTRUM_RENAMES_ORIGINAL_LINEAR_SOLVE_OR_REQUIRES_COMPONENT_SPLIT

MANDATORY_OUTPUTS:
  - literal_x_q_C_kappa_H_D_beta_and_diagonal_channel_lock
  - exact_mixed_zero_mass_identity
  - exact_omega_hat_commutator_identity_with_star_first_orientation
  - exact_completed_W02_Arch_Prime_spectral_pairing
  - removable_endpoint_theta_zero_and_two_pi_treatment
  - source_supplier_inventory_for_the_exact_x_equals_C_inverse_kappa
  - comparison_against_prior_compact_log_commutator_and_dIIKS_dressed_generator_walls
  - full_compact_consumer_rate_or_exact_failure

MANDATORY_PLANTS:
  P1_NORM_NOT_SPECTRUM:
    Bounded norm of x and q does not imply upper-band localization of omega_hat.
  P2_ZERO_MASS_NOT_BAND_DECAY:
    omega_hat(0)=0 alone does not control the whole band (pi,2*pi).
  P3_COMPONENT_SPLIT:
    A small prime pairing does not control the completed source pairing when
    W02 and Arch are separated from it.
  P4_DIAGONAL_CHANNEL:
    The off-diagonal Hilbert identity does not determine
    sum_i (M_ii-a)*conj(x_i)*q_i.
  P5_EXACT_GROUND_SANITY:
    If the selected trial is an exact eigenvector with residual zero, the full
    reassembled consumer must vanish identically.

RICCI_DOOB_SIDE_ROUTE:
  STATUS: OPEN_DEFERRED
  SOURCE_SIGN_GATE_MATHEMATICALLY_REFUTED: false
  PARITY_PROOF_REFUTED: true
  EXECUTION_NOW: false
  reason: >-
    Even a sign-gate PASS would only admit an expensive curvature route for a
    carried spectral-floor problem. It would not close the current ground-to-Xi
    tracking wall. The cheap monotonicity reduction is recorded but is not the
    active transaction.

CANDIDATE_REPRESENTATIONS:
  R1_COMPLETED_BETA_POLARIZED_SPECTRUM:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 3/10
  R2_SOURCE_ADAPTED_PRIME_KRYLOV_FESHBACH:
    rank: QUARANTINED_RUNNER_UP
    kill_power: 8/10
    proof_cost: 10/10
  R3_ODD_SOURCE_MONOTONICITY_RICCI_GATE:
    rank: DEFERRED_SIDE_DIAGNOSTIC
    kill_power: 7/10
    proof_cost: 2/10
    route_fit: 3/10

REGISTERED_PREDICTIONS:
  P_COMPLETED_SPECTRUM_1:
    probability: 0.70
    prediction: >-
      The exact completed spectral identity closes, but no source theorem gives
      the required localization/rate for x=C^(-1)kappa; result HOLD.
  P_COMPLETED_SPECTRUM_2:
    probability: 0.25
    prediction: >-
      The representation algebraically returns the original dressed linear solve
      or needs a forbidden component split; result FAIL.
  P_COMPLETED_SPECTRUM_3:
    probability: 0.05
    prediction: >-
      The completed W02-Arch-Prime pairing exposes a source-defined cancellation
      sufficient for the compact consumer rate; result PASS.

PREDICTION_CLOSEOUT:
  P_ANNIHILATOR_1_0_55:
    fate: CONFIRMED_WITH_STRONGER_TAUTOLOGY_KILL
  P_ANNIHILATOR_2_0_30:
    fate: NOT_REALIZED
  P_ANNIHILATOR_3_0_15:
    fate: NOT_TRIGGERED
    note: conditioning was not the load-bearing obstruction
  P_RICCI_2_0_76:
    fate: RESTORED_TO_UNTESTED
    note: prior CONFIRMED label was withdrawn with Correction 5

CLOSES:
  - PARITY_SIGN_FRUSTRATION_FALSE_PROOF
  - PRIME_POWER_ANNIHILATOR_AS_CANCELLATION_MECHANISM
  - HAAR_LOCAL_ANNIHILATOR_AS_CONDITIONING_ESCAPE

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SOURCE_ACTION_COMPACT_DECAY
  - LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_TO_TRIAL_LOCALLY_UNIFORM_CONVERGENCE

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Correction 5 is honest and accepted

The plant `beta_n=-n` satisfies every hypothesis used in the withdrawn parity
argument. Oddness gives only `beta_-n=-beta_n`; it does not choose the sign on
the positive half. Therefore the former conclusion
`RICCI_DOOB_SIGN_FRUSTRATION_FATAL` had no valid source supplier.

The strict triangle identity survives for pairwise-distinct beta-values. A
strictly increasing triple has positive triangle product and kills any switch to
all-negative off-diagonal signs.

### 2. One further repair: the nonmonotone witness is outside the actual source class

The sequence `(0,2,1,1/2)` correctly shows that the all-triangle condition is
not equivalent to monotone decrease for an arbitrary ordered sequence. It is not
odd on a symmetric lattice, so it cannot refute the source-specific reduction.

For the actual odd source, under pairwise distinctness, the reduction is exact:


theorem (paper):

- if beta is strictly decreasing, every off-diagonal Loewner entry is already
  negative and the identity gauge works;
- conversely, an all-negative sign gauge forces every triangle product to be
  negative;
- the central triple `(-n,0,n)` forces `beta_n<0` for every `n>0`;
- if any positive-side difference `beta_{n+1}-beta_n` is positive, then either a
  central triple already fails or the mirrored triple `(-(n+1),-n,n)` has the
  forbidden `231` order and positive triangle product.

Hence one positive first difference is already a strict source-level kill. The
Correction-5 proposal requiring two consecutive positive differences is valid
as a witness but is not cheapest.

If repeated beta-values occur, zero edges appear. The correct object then is the
nonzero support graph, and its complete cycle-sign condition must be audited;
no strict monotonicity equivalence is claimed in that case.

`[FINITE_CELL][PAPER]`

### 3. The annihilator is an exact recurrence but not a cancellation theorem

The prime component is a finite exponential sequence, so a shift polynomial
annihilates it on the full integer lattice. This is an exact structural fact.

But the adjoint-range condition is equivalent to annihilating the same Fourier
samples that define the prime pairing. Any remainder must retain the projection
of the consumer weight onto the effective prime-frequency span. That space grows
with the number of effective prime-power classes. The proposed “few boundary
moments” do not exist without already proving the target localization.

Two details in the Linux report require repair:

1. conjugate and endpoint collisions must be quotiented before counting roots;
2. the finite recurrence operator must be typed explicitly before assigning its
   kernel dimension.

Neither repair rescues the mechanism.

`[COFINAL_FAMILY][PAPER]`

### 4. Why prime-only localization is not the next theorem

The literal source object is not `beta_prime` in isolation. Its off-diagonal
Loewner field is the completed signed beta built from `W02 + Arch - Prime`, and
the exact residual consumer additionally contains the diagonal source action.

A theorem that proves only that the prime samples of `omega_hat` are small may
be stronger than necessary in one place and useless in another: it can destroy
the cancellation that made the completed source row meaningful. This is the
same category error guarded by C10 and C04.

The legal next object is the full completed spectral pairing of the exact mixed
weight.

`[COFINAL_FAMILY][PAPER]`

## FINAL PROPOSAL

Run exactly one source-only discriminator:

```text
GOAL058_SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SPECTRUM_PREFLIGHT
```

The preflight first proves the exact Fourier/commutator identity of the mixed
Hilbert weight, then reassembles the completed source pairing and its diagonal
channel. Only after this exact identity may it ask whether the literal graph-test
vector `x=C^(-1)kappa` has source-controlled spectral localization.

A PASS must close the actual compact consumer rate. An identity with no rate is
HOLD. If the spectral representation returns the dressed linear solve, the
original consumer, or a componentwise prime estimate, it is FAIL.

No Lean source, numerical probe, Aristotle submission or Codex execution is
authorized.

## STRONGEST ATTACK

The strongest objection to the selected representation is simple:

> `omega_hat(theta)=<x,[M_theta,H]q>` may be a clean formula, but `x=C^(-1)kappa`
> still contains the entire unresolved source operator. Bounding the spectrum of
> `omega` may therefore be exactly the original linear solve in another basis.

That possibility is the registered FAIL discriminator, not a reason to skip the
cheap paper test.

The strongest objection to reviving Ricci is also simple:

> A source sign gate, even if it passes, supplies only a legal Markov geometry.
> It supplies neither positive curvature nor the current ground-to-Xi tracking
> rate.

Therefore Ricci remains a side diagnostic and cannot displace the active target.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.
NO LEAN EDIT.
NO NUMERICAL PROBE.
NO ARISTOTLE.

Run only the Linux/Paper task:

TASK_ID:
  GOAL058_SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SPECTRUM_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

PASS:
  COMPLETED_BETA_POLARIZED_SPECTRUM_SOURCE_RATE_READY

HOLD:
  COMPLETED_SPECTRAL_IDENTITY_WITHOUT_SOURCE_LOCALIZATION_RATE

FAIL:
  COMPLETED_SPECTRUM_RENAMES_ORIGINAL_LINEAR_SOLVE_OR_REQUIRES_COMPONENT_SPLIT
```

## META CLOSEOUT

### What became smaller?

The prime-power annihilator programme collapsed to one exact Fourier-sample
identity. The remaining question is no longer “find a recurrence”; it is whether
the exact mixed consumer has a source-controlled completed spectral profile.

### What was killed?

- parity alone as a sign-frustration proof;
- monolithic prime-power annihilation as a consumer-rate mechanism;
- Haar-local annihilators as a conditioning escape;
- prime-only upper-band localization as the final consumer theorem.

### What must not be tried again?

```text
oddness -> positive source value;
raw 2*J_pp degree without collision quotient;
unnamed finite shift operator with asserted kernel;
annihilator range decomposition sold as cancellation;
prime-component bound sold as completed-source control.
```

### Current smallest named gap

```text
SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SOURCE_ACTION_COMPACT_DECAY
```

### Next cheapest decisive test

Derive the exact mixed spectral identity and determine whether it exposes a new
source invariant or merely restates `x=C^(-1)kappa`.

### Memory entry

```yaml
iteration: 2026-08-27-correction5-annihilator-closeout
target: prime-power annihilator and Ricci parity repair
status: PROGRESS
failed_strategy: annihilator adjoint-range cancellation
cognitive_operator_used: REPRESENTATION_SHIFT
new_gap_name: SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SOURCE_ACTION_COMPACT_DECAY
invariant_learned: preserve completed W02+Arch-Prime and the diagonal channel
forbidden_future_move: do not infer source signs from symmetry; do not replace
a completed consumer by a prime-only spectral surrogate
next_decisive_test: completed beta polarized spectrum preflight
```
