# STATUS: FATAL — CENTRAL-WINDOW / CENTRAL-SCHUR CONTINUATION STOPPED; OWNER REPRESENTATION RERANK REQUIRED

```yaml
PRIMARY: RATIFY_CENTRAL_SAMPLING_AND_ENFORCE_STOP_RULE
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 655c9831cf22c11c0704bf6256e2eb1711fd4195
  REPORT_PARENT: 5405b7ed3fdb8c3d9e57b6578ea547a1cbf7e19d
  REPORT_PATH: docs/routeB_bus/LINUX_CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_PREFLIGHT_GOAL058_2026-08-28.md
  REPORT_BLOB: 591ed7497f6a92a48633ccfe50b8138c4ebcc8b6
  REPORT_LINES: 148
  REPORT_WAS_BRANCH_HEAD_AT_ADJUDICATION: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_PROBE_PERFORMED: false
  ARISTOTLE_USED: false
  CODEX_USED: false
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: HOLD
  REPORTED_CODE: CENTRAL_WINDOW_SAMPLING_EXACT_BUT_GRAPH_RESOLVENT_MASS_UNCONTROLLED
  DECISION: HOLD_RATIFIED_AND_STOP_RULE_ENFORCED

  P59_POLE_EVALUATION: LEAN_SOURCE_PASS
  CENTRAL_WINDOW_SAMPLING_INEQUALITY: PAPER_PASS_WITH_CARRIER_GUARD
  CENTRAL_MASS_THRESHOLD_REDUCTION: PAPER_PASS_COFINALLY
  POSDEF_INVERSE_LOCALIZATION_PLANT: PAPER_PASS

  SCHUR_FESHBACH_IDENTITY: PAPER_PASS_AFTER_FULL_CARRIER_BLOCK_REPAIR
  SCHUR_FESHBACH_STRICT_LEDGER_REDUCTION: REFUTED
  CENTRAL_SCHUR_EXCEPTION_TO_STOP_RULE: REJECTED

  CENTRAL_WINDOW_CAUCHY_OBSERVABILITY_PROGRAM: FATAL_BY_PRECOMMITTED_STOP_RULE
  SELECTED_FERRERS_GROUND_TRACKING_RATE_CORRIDOR: REMAINS_FROZEN
  ROUTE_B_FATAL: false
  ARITHMETIC_RATE_MATHEMATICALLY_REFUTED: false
  RH_CLAIMED: false

REPORT_REPAIRS:
  carrier_window:
    report_object: "J_m=floor(delta*L_m/(2*pi))"
    exact_object: "J_m^car=min(N_m,floor(delta*L_m/(2*pi)))"
    selected_schedule_note: >-
      Since N_m=m and L_m=log m on the selected schedule, J_m^car equals the
      reported floor eventually.  The report's formula is therefore cofinally
      correct, not an exact all-cell identity without this guard.

  schur_domain:
    report_phrase: "writing C in blocks on q-perp"
    replacement: >-
      Split the full coordinate carrier as B direct-sum B'.  The coordinate
      projections P_B and P_B' do not generally preserve q-perp, so q-perp itself
      is not the asserted coordinate direct sum.  The full positive-definite
      matrix C has an invertible principal B' block, and the standard block solve
      then yields the stated formula for P_B u with source Q Phi.

  small_block_claim:
    report_phrase: "two objects, both on an O(log m)-dimensional block"
    replacement: >-
      Both outputs live on the O(log m) central block, but both depend on the full
      complement through C_B'B'^{-1}.  Output dimension is not dependency size.
      The complement has not disappeared from the theorem.

  ledger_count:
    report_claim: "strictly smaller by replacing four inputs with two"
    verdict: REJECTED
    reason: >-
      Counting names is not a W9 comparison.  The effective-source lower envelope
      is a cancellation-sensitive full-resolvent statement, and the pair
      (upper Schur norm, lower effective source) is a stronger sufficient
      condition for the original central-mass lower bound, not a weaker theorem.

EXACT_RETAINED_ASSETS:
  pole_row:
    statement: "kappa_m(2*pi*j/L_m)=(-1)^j*L_m*e_j"
    scope: FINITE_CELL
    verifier: LEAN_SOURCE_PLUS_PAPER_OFF_DIAGONAL_REDUCTION

  sampling:
    statement: >-
      sup_{z in K0}|T_m,z(a_rho)| >=
      L_m/sqrt(2*J_m^car+1) * ||P_{J_m^car} u_m,rho||_2.
    scope: COFINAL_FAMILY
    verifier: PAPER

  threshold:
    statement: >-
      On the selected schedule a sufficient central-mass scale is
      ||P_{J_m}u_m,rho||_2 >= constant(delta) *
      m^{-sigma}*(log m)^{-2} infinitely often.
    scope: COFINAL_FAMILY
    verifier: PAPER

  exact_vector: "u_m,rho=C_m^{-1}Q_m Phi_m(a_rho)"
  exact_source: "Phi_m(a)=([S_a,H_m]+C_a)q_m"
  full_volterra_identity: PRESERVED
  smooth_oriented_source_TV_ceiling_6_over_pi: PRESERVED
  finite_real_zero_assets: PRESERVED
  W1_W5_N2_N4_assets: PRESERVED

SCHUR_FESHBACH_ASSET:
  status: EXACT_REPRESENTATION_ONLY
  full_carrier_split: "H=B direct-sum B'"
  schur: "S_B=C_BB-C_BB'*C_B'B'^{-1}*C_B'B"
  effective_source: "f_B=P_B QPhi-C_BB'*C_B'B'^{-1}*P_B' QPhi"
  identity: "P_B u=S_B^{-1}f_B"
  sufficient_bound: "||P_Bu|| >= ||f_B||/||S_B||"
  limitation: >-
    No source-independent lower envelope for f_B follows from positivity,
    central localization of QPhi, bounded source norm, or a bounded Schur norm.

FALSIFIER:
  name: BOUNDED_SCHUR_AND_CENTRAL_SOURCE_DO_NOT_BOUND_EFFECTIVE_SOURCE
  construction: >-
    On q-perp=C^2 take C=[[1,1/2],[1/2,1]] and split the first coordinate as B.
    Then C is Hermitian positive definite, S_B=3/4, and for
    s_epsilon=(1,2*(1-epsilon)) one has bounded ||s_epsilon||, central source
    component equal to 1, but f_B=epsilon and (C^{-1}s_epsilon)_B=4*epsilon/3.
    Adjoin an orthogonal q-line with Cq=q to obtain the literal trialGraph form.
  conclusion: >-
    Even a uniformly bounded central Schur complement and a nonzero raw central
    source permit arbitrary cancellation against the tail-return term.  A lower
    envelope for f_B requires a new exact source-correlation theorem; it is not
    supplied by the Schur identity.
  card: C10_FUNCTIONAL_NOT_SURROGATE
  scope: ABSTRACT
  verifier: PAPER

STOP_RULE:
  triggered: true
  closes_program:
    - FURTHER_CAUCHY_OBSERVABILITY_WRAPPERS
    - FURTHER_VOLTERRA_RATE_WRAPPERS
    - CENTRAL_COORDINATE_SCHUR_WRAPPER_WITHOUT_NEW_SOURCE_THEOREM
    - CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_AS_CURRENT_EXECUTION_PROGRAM
  forbids:
    - renaming_effective_source_as_a_new_supplier_without_a_source_theorem
    - counting_output_dimension_as_dependency_reduction
    - reusing_localization_of_Phi_as_localization_of_C_inverse_Phi
    - using_no_catalog_supplier_as_mathematical_evidence
    - Lean_formalization_of_the_block_identity_as_route_progress
  not_closes:
    - exact_signed_transfer_rate_as_a_mathematical_statement
    - Route_B
    - finite_ground_real_zero_engine
    - qualitative_same_family_convergence_routes

CLOSES:
  - CENTRAL_WINDOW_SAMPLING_INEQUALITY
  - GENERIC_LOCALIZATION_TRANSFER_THROUGH_POSDEF_INVERSE
  - CENTRAL_SCHUR_EXCEPTION_AS_A_STRICT_W9_REDUCTION
  - CENTRAL_WINDOW_OBSERVABILITY_WRAPPER_LOOP

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_GROUND_FAMILY_TO_XI_LOCALLY_UNIFORM
  - ABSTRACT_EXACT_SIGNED_TRANSFER_RATE_IF_A_NEW_SOURCE_THEOREM_APPEARS
  - ROUTE_B_ALTERNATIVE_REPRESENTATION_SELECTION

OWNER_RERANK:
  required_now: true
  execution_authorized_by_this_verdict: false

CANDIDATE_REPRESENTATIONS:
  R1_VITALI_CAUCHY_DEBRANGES_QUALITATIVE:
    rank: PRIMARY
    object: >-
      The same normalized finite ground transforms, but replace the
      consumer-strength rate by local boundedness plus convergence on a uniqueness
      set or all jets at one anchor.  Vitali then supplies local uniform
      convergence without a quantitative zero-transfer lower-envelope program.
    mandatory_guard: >-
      Local boundedness must come from real-zero/Cauchy/de Branges structure and
      may not assume the missing tracking rate under another name.
    kill_power: 9/10
    proof_cost: 7/10
    reentry_condition: GENUINELY_NEW_SOURCE_THEOREM_OR_OWNER_AUTHORIZED_ACQUISITION

  R2_SOURCE_ADAPTED_MOVING_KRYLOV_FESHBACH:
    rank: RUNNER_UP
    card: C03_MOVING_REPRESENTATION
    object: >-
      Precommit a moving subspace generated by the literal prime/source action,
      rather than the fixed central coordinate window, and test the exact signed
      consumer after a source-faithful Feshbach reduction.
    mandatory_guards:
      - precommit_subspace_before_tests
      - exact_same_family_carrier_and_normalization
      - explicit_rank_growth_law
      - independent_complement_coupling_consumer
      - displacement_rank_not_confused_with_spectral_rank
    kill_power: 9/10
    proof_cost: 9/10
    reentry_condition: OWNER_SCOPED_NEW_REPRESENTATION_GRANT

NEXT_TRANSACTION:
  AUTHORIZED: false
  TASK_ID: NONE
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false
  reason: >-
    The precommitted HOLD stop rule fired.  The proposed Schur exception is an
    exact algebraic rewriting but not a strict dependency reduction.  Further
    execution requires an owner-selected representation change or a genuinely new
    source theorem.

REGISTERED_PREDICTION_FATE:
  P_CENTRAL_WINDOW_1_0_62: CONFIRMED
  P_CENTRAL_WINDOW_2_0_25: NOT_REALIZED
  P_CENTRAL_WINDOW_3_0_13: NOT_REALIZED_EXCEPT_MINOR_CARRIER_GUARD

PRIOR_PREDICTION_FATE:
  P_COMPACT_OBS_1_0_55: CONFIRMED
  P_COMPACT_OBS_2_0_30: NOT_REALIZED
  P_COMPACT_OBS_3_0_15: NOT_REALIZED

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C03_MOVING_REPRESENTATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: ABANDON_ROUTE
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
| Pole evaluation | Accepted.  The banked removable-pole theorem fixes the diagonal value; the common numerator vanishes at all other lattice points. | `[FINITE_CELL][LEAN]` |
| Central sampling | Accepted after replacing `J_m` by `min(N_m,J_m)` for exact finite cells.  On the selected schedule the reported form holds eventually. | `[COFINAL_FAMILY][PAPER]` |
| Central threshold | Accepted as the sufficient cofinal scale dictated by the earlier zero-transfer ledger. | `[COFINAL_FAMILY][PAPER]` |
| Localization plant | Accepted.  Positive definiteness and a complement floor do not preserve coordinate localization through `C^{-1}`. | `[ABSTRACT][PAPER]` |
| Schur identity | Accepted only as a full-carrier block identity.  Coordinate projections generally do not split `q^perp`. | `[FINITE_CELL][PAPER]` |
| Schur candidate is a strict reduction | Rejected.  Its effective source contains the full complement inverse and can cancel arbitrarily even with bounded Schur norm and nonzero central source. | `[ABSTRACT][PAPER]` |
| Current central-window program | Closed `FATAL` by its precommitted stop rule. | `[COFINAL_FAMILY][PAPER]` |
| Route B | Not killed.  Exact finite, P59, Volterra and real-zero assets remain reusable after an owner-selected representation shift. | `[ABSTRACT][PAPER]` |

## 1. What the report actually closed

The lattice-pole calculation is real progress.  For the unscaled P59 kernel row,

\[
\kappa_m\left(\frac{2\pi j}{L_m}\right)=(-1)^jL_m e_j.
\]

Therefore any pole inside one fixed compact reads one coordinate of the literal
vector

\[
u_{m,\rho}=C_m^{-1}Q_m\Phi_m(a_\rho)
\]

without a conditioning argument.  For

\[
J_m^{\rm car}
=
\min\!\left(N_m,
\left\lfloor\frac{\delta L_m}{2\pi}\right\rfloor\right),
\]

we have

\[
\sup_{z\in K_0}|T_{m,z}(a_\rho)|
\ge
\frac{L_m}{\sqrt{2J_m^{\rm car}+1}}
\|P_{J_m^{\rm car}}u_{m,\rho}\|_2.
\]

This removes the abstract compact-observability constant.  It does not control
the coordinate mass of the vector being sampled.

## 2. Why the plant is decisive

The report's diagonal plant proves exactly the right negative statement:
central localization of `Q Phi` is not preserved by an arbitrary positive graph
inverse.  Thus no theorem using only positivity, a lower floor, or localization of
the source can supply the desired central mass.

The stronger two-block plant in this verdict removes the proposed escape route.
Take

\[
C=
\begin{pmatrix}
1&1/2\\
1/2&1
\end{pmatrix},
\qquad
s_\varepsilon=
\binom{1}{2(1-\varepsilon)}.
\]

The central Schur complement is the fixed number `3/4`; the direct central source
is exactly `1`; the full source norm stays bounded.  Nevertheless the effective
source is `epsilon`, and the central solution coordinate is `4 epsilon / 3`.
The tail-return term can therefore erase the central source to arbitrary order.

This is a **C10 functional-not-surrogate** kill.  Bounding the raw central source
is not bounding the effective source consumed by the block solve.

## 3. Why the Schur candidate does not pass W9

The exact formula

\[
P_Bu=S_B^{-1}f_B
\]

is useful algebra.  But the report evaluates progress by counting four old labels
versus two new labels.  That is not a dependency audit.

The new lower-envelope target

\[
\|f_B\|
=
\left\|
P_BQ\Phi-C_{BB'}C_{B'B'}^{-1}P_{B'}Q\Phi
\right\|
\]

contains the full complement resolvent and an uncontrolled subtraction.  Its
failure modes include the old complement-floor problem and the old signed-source
cancellation problem.  Moreover the pair

\[
\|S_B\|\le M_m,
\qquad
\|f_B\|\ge M_m\tau_m
\]

is only a sufficient condition for `||P_Bu|| >= tau_m`; it is not a weakened form
of the original target.  A failed sufficient condition would not classify the
central mass in either direction.

Hence the Schur identity is bankable, but formalizing or wrapping it now would
close no source supplier and would violate W9.

## 4. Stop-rule consequence

The report returned the exact precommitted HOLD code.  The allowed exception was
conditional on a **strictly smaller input ledger**.  That condition failed.

Therefore:

```text
no further Cauchy wrapper;
no further Volterra rate wrapper;
no central-coordinate Schur wrapper;
no Lean transaction for the block identity;
no numerical ladder on the same representation.
```

The correct next control-plane state is:

```text
OWNER_REPRESENTATION_RERANK.
```

The selected-Ferrers ground-tracking rate corridor remains frozen.  This does not
refute the exact signed rate and does not kill Route B.

## 5. Candidate reranks

### R1 — qualitative Vitali / Cauchy–de Branges

Change the quantifier, not the constant: seek local boundedness of the same
normalized ground transforms and convergence on a uniqueness set.  A genuine
Vitali/de Branges theorem could then upgrade to local uniform convergence without
proving the consumer-strength zero-transfer rate.

This is admissible only if local boundedness is supplied independently.  The raw
P59 envelope grows like `m^(sigma/2)*sqrt(log m)`, so writing “Montel” does not
remove the wall.

### R2 — moving source-adapted Krylov/Feshbach

If the owner keeps a Feshbach route, the subspace must move with the literal
source/prime action and be fixed before testing.  A fixed central coordinate block
is not source-adapted and permits the cancellation plant above.

This is a new representation, not a continuation of the stopped central-window
program.  It requires its own owner-scoped contract and falsifiers.

## STRONGEST ATTACK

The strongest objection to this closeout is:

> Perhaps the literal CCM source has an exact identity that prevents the
> two-block cancellation plant, so rejecting Schur now throws away the answer.

Correct response: such an identity would be a **genuinely new source theorem** and
would satisfy the explicit reentry condition.  The current report neither states
nor sources it.  The stop rule blocks speculative wrappers, not future evidence.

## CODEX DIRECTIVE

```text
NO EXECUTION AUTHORIZED.

Freeze the report and all current central-window / Volterra / Cauchy assets.
Do not formalize the Schur block identity as route progress.
Do not launch numerics on CENTRAL_SCHUR_COMPLEMENT_ENVELOPE_AND_EFFECTIVE_CENTRAL_SOURCE.

Reentry requires exactly one of:

1. OWNER_SELECTS_R1_QUALITATIVE_VITALI_REPRESENTATION, with a source-locked
   local-boundedness theorem for the same normalized finite ground family; or

2. OWNER_SELECTS_R2_MOVING_SOURCE_KRYLOV_FESHBACH, with a precommitted moving
   subspace, exact rank law, same-family carrier and an independent coupling
   consumer; or

3. NEW_SOURCE_THEOREM preventing cancellation in the literal effective source.
```

## META CLOSEOUT

**What became smaller?**

The abstract observability constant became the exact central coordinate mass of
one literal vector.  The inability to control that mass is now witnessed by an
explicit positive-definite plant.

**What was killed?**

- localization of `Phi` as a proxy for localization of `C^{-1}Phi`;
- counting Schur outputs as a strict dependency reduction;
- the central-coordinate Schur exception to the stop rule;
- the Cauchy/Volterra/observability wrapper loop.

**What must not be tried again?**

Do not introduce another equivalent scalar, block, or effective source unless it
comes with an independent source theorem that changes the input ledger.

**Current smallest named gap?**

```text
ROUTE_B_ALTERNATIVE_REPRESENTATION_SELECTION
```

Inside the stopped representation, the exact unresolved functional remains
`||P_B C^{-1}QPhi||`, but it is no longer an authorized work target.

**Next cheapest decisive test?**

Owner rerank between R1 and R2.  No mathematical execution precedes that choice.

**Prior prediction fate?**

- `P_CENTRAL_WINDOW_1 (0.62)`: confirmed.
- `P_CENTRAL_WINDOW_2 (0.25)`: not realized.
- `P_CENTRAL_WINDOW_3 (0.13)`: not realized except for the minor carrier guard.

**Memory entry**

```yaml
iteration:
  target: CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_LOWER_ENVELOPE
  status: FATAL_FOR_CURRENT_PROGRAM
  failed_strategy: FIXED_CENTRAL_COORDINATE_OBSERVABILITY_AND_SCHUR_WRAPPER
  cognitive_operator_used: ABANDON_ROUTE
  new_gap_name: ROUTE_B_ALTERNATIVE_REPRESENTATION_SELECTION
  invariant_learned: >-
    Output dimension is not dependency size; a Schur effective source retains the
    full complement inverse and can cancel even under uniformly bounded blocks.
  forbidden_future_move: >-
    Do not count renamed combined suppliers as a smaller ledger without an
    independent source theorem and a falsifier against tail-return cancellation.
  next_decisive_test: OWNER_RERANK_R1_OR_R2
```
