# STATUS: OPEN — P59 KERNEL–COMMUTATOR FAIL RATIFIED; HIGHER-ACTION WALL REPAIRED TO A TAUTOLOGY; POLARIZED NEAR-RADICAL GRAPH FUNCTIONAL SELECTED

```yaml
PRIMARY: RATIFY_P59_KERNEL_COMMUTATOR_FAIL_AND_SELECT_POLARIZED_NEAR_RADICAL_GRAPH_FUNCTIONAL
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-N
  ADJUDICATION_ROLE: READ_ONLY_PREFLIGHT_CLOSEOUT
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: e09e5858bb7300022ec4e2b48e2f3b5dd5d7bb95
  REPORT_PARENT: 6b408189c029975fbf073e780cb603073e305532
  REPORT_PATH: docs/routeB_bus/LINUX_P59_KERNEL_COMMUTATOR_TARGET_ACTION_PREFLIGHT_GOAL058_2026-08-27.md
  REPORT_GIT_BLOB: 59c78e78c4170ec3fab24d28c4b73765774beb7d
  REPORT_LINES: 143
  REPORT_ONLY_COMMIT: true
  HEAD_IS_REPORT_COMMIT_AT_AUDIT: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_PROBE_PERFORMED: false
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false

ADJUDICATION:
  discriminator_fail_confirmed: true
  failure_code_confirmed: GOAL058_P59_KERNEL_COMMUTATOR_LEAVES_FULL_SOURCE_ACTION_OR_PRIME_OSCILLATION_WALL
  p59_kernel_riesz_vector_identity: PAPER_PASS
  off_lattice_diagonal_resolvent_identity: PAPER_PASS
  full_CCM_rank_two_commutator_port: PAPER_PASS
  removable_pole_entire_extension: PAPER_PASS
  component_split_used: false
  combined_prime_cancellation_preserved: true
  report_rank_at_most_four_commutator: REPAIRED_TO_RANK_AT_MOST_TWO
  report_infinite_higher_action_recursion: REFUTED
  partial_self_consistency_as_rate_mechanism: KILLED_AS_TAUTOLOGY
  beta_column_and_diagonal_moments: REAL_BUT_NONDECISIVE
  ground_graph_representation: SURVIVES
  p59_kernel_commutator_target_action_representation: KILLED_AS_SOURCE_RATE_MECHANISM
  cofinal_compact_rate_in_current_corpus: ABSENT
  Lean_source_authorized_now: false

EXACT_REPAIR:
  matrix: M_k
  trial: q_k
  Rayleigh: a_k
  residual: r_k = (M_k - a_k I) q_k
  ground_eigenvalue: epsilon_k
  trial_projection: P_k = q_k q_k_star
  trial_complement: Q_k = I - P_k
  trial_graph_operator: C_k = Q_k (M_k - epsilon_k I) Q_k + P_k
  second_action_vector: s_k = (M_k - epsilon_k I) r_k
  commutator_identity: >-
    [M_k,C_k] = (r_k-s_k) q_k_star - q_k (r_k-s_k)_star
  action_collapse_identity: >-
    s_k = C_k r_k + norm(r_k)^2 q_k
  consequence: >-
    the apparent higher-action term is reducible to the original graph functional,
    the raw residual transform and explicit q/r overlaps; it does not generate a
    nonterminating derivative hierarchy
  falsifier: >-
    substitute the exact recombined source row before estimating; the proposed
    self-consistency equation reduces to Phi_k(z) = Phi_k(z), so no denominator
    1-lambda(z), contraction or compact rate is obtained

SURVIVING_GRAPH_OBJECT:
  exact_functional: >-
    Phi_k(z) = inner(C_k_inverse kappa_k(z), r_k)
  exact_transform_error: >-
    graphGround_k(z) - centeredPstar_k(z)
    = - centerFactor_k * Phi_k(z)
  status: EXACT_FINITE_IDENTITY_PAPER
  source_rate: OPEN

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_COMPACT_DECAY
  formula: >-
    for every compact K in the open centered strip,
    sup_{z in K} norm(centerFactor_k *
      inner(C_k_inverse kappa_k(z), r_k)) tends to zero
  required_family: one_precommitted_selected_Ferrers_tail

SELECTED_REPRESENTATION:
  name: GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_POST_W5
  mechanism: >-
    pair the exact source-action split against the single consumer vector
    v_k(z)=C_k_inverse kappa_k(z), replace the explicit factor-four target by
    its paper-proved global radical representative, and retain every window,
    projection, midpoint and point-defect term exactly; spend the subsequently
    proved W5/Sturm/N2 rates only after the exact global/window form crosswalk
  why_smaller: >-
    the old radical route asked for a dual supremum over all unit vectors;
    the graph route needs one source-defined z-dependent functional only
  component_split_forbidden: true
  global_radical_after_projection_forbidden: true

CLOSES:
  - P59_KERNEL_ORIENTATION_AMBIGUITY
  - P59_OFF_LATTICE_RESOLVENT_IDENTITY
  - P59_REMOVABLE_POLE_COVERAGE
  - P59_FULL_CCM_COMMUTATOR_FINITE_RANK_REDUCTION
  - P59_HIGHER_ACTION_NONTERMINATING_RECURSION_CLAIM
  - P59_SELF_CONSISTENCY_AS_A_RATE_MECHANISM
  - P59_BETA_AND_DIAGONAL_MOMENTS_AS_THE_NEXT_LOAD_BEARING_NODE

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_COMPACT_DECAY
  - GLOBAL_WEIL_TO_PROJECT_SOURCE_WEIL_EXACT_RESTRICTION_ON_THE_SHIFTED_FORM_DOMAIN
  - WINDOW_FORM_INVERSION_COVARIANCE
  - POLARIZED_SPECTRAL_REPRESENTATION_FOR_BV_CLASS
  - SELECTED_FERRERS_GROUND_COFINAL_CONVERGENCE_ASSEMBLY
  - EXACT_COMBINED_GAMMA_RETAINED_PRIME_RATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_POST_W5_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  DISCRIMINATOR:
    PASS: SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_SOURCE_READY
    FAIL: GOAL058_GLOBAL_WINDOW_FORM_CROSSWALK_OR_BV_PRIME_OSCILLATION_WALL
  REQUIRED_OUTPUT:
    - exact source-action identity for v_k(z)=C_k_inverse kappa_k(z)
    - exact source lock that E_star(4*explicitCCMLimitH) is in the global Weil radical
    - exact global-Weil to project source-Weil restriction on the required finite synthesis or shifted form domain
    - exact BV Poisson completion with the surviving center point defect and no category drift
    - exact window/projection defect decomposition for the factor-four target
    - compact envelope for v_k(z), including the complement-floor denominator and centering factor
    - spendability audit of the committed W5, Sturm and N2 rates against every displayed defect
    - one common precommitted cofinal tail and no second extraction
    - final compact rate ledger for Phi_k on every fixed closed substrip
    - one exact PASS or FAIL code with no anonymous C(z) majorants
  SUCCESS_CODE: SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_LEAN_READY
  FAILURE_CODE: GOAL058_GLOBAL_WINDOW_FORM_CROSSWALK_OR_BV_PRIME_OSCILLATION_WALL

FORBIDDEN:
  - split_W02_Arch_Prime_into_norm_majorants
  - infer_polarized_action_from_a_small_scalar_Rayleigh_value
  - infer_projected_radicality_from_global_radicality
  - relabel_L2_or_projection_tail_decay_as_source_action_decay
  - introduce_a_second_tail_or_subsequence
  - formalize_beta_column_or_diagonal_moments_while_the_full_consumer_is_open
  - continue_the_P59_self_consistency_recursion
  - use_global_Weil_positivity_or_RH
  - change_the_selected_row_schedule_target_scale_or_Rayleigh_shift

CANDIDATE_REPRESENTATIONS:
  R1_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_POST_W5:
    rank: PRIMARY
    target: >-
      direct compact decay of the exact scalar graph functional using the
      global radical of the explicit target plus explicit window/projection defects
    kill_power: 10/10
    proof_cost: 6/10
    route_fit: 10/10
  R2_TWO_MODE_TARGET_SUBSPACE_FESHBACH:
    rank: RUNNER_UP
    target: >-
      precommit the literal projected h0/h4 target subspace, keep the exact
      target action in its finite block and control only its coupling to the complement
    kill_power: 9/10
    proof_cost: 9/10
    route_fit: 8/10
  R3_EXACT_COMBINED_GAMMA_RETAINED_PRIME:
    rank: LAST_RESORT
    target: >-
      cancellation-preserving source estimate on Gamma_k=D_k r_k including
      retained-prime action and the W02 endpoint trace
    kill_power: 10/10
    proof_cost: 10/10
    route_fit: 9/10

REGISTERED_PREDICTIONS:
  P_P59_KERNEL_COMMUTATOR_1:
    prior_probability: 0.81
    fate: CONFIRMED
  P_TARGET_MOMENT_SOURCE_1:
    prior_probability: 0.60
    fate: CONFIRMED_WITH_ANATOMY_REPAIR
    note: >-
      two finite moments remain in the main block, but the reported
      nonterminating higher-action wall collapses; the overall mechanism still
      fails because the exact self-consistency is tautological
  P_GROUND_COFINAL_RATE_1:
    prior_probability: 0.76
    fate: LIVE_NOT_YET_TESTED
  P_P59_SELF_CONSISTENCY_1:
    probability: 0.94
    prediction: >-
      the exact rank-two commutator simplification makes the combined source-row
      self-consistency relation an identity rather than a contraction
  P_NEAR_RADICAL_POST_W5_1:
    probability: 0.68
    prediction: >-
      the exact single-functional formulation and the later W5/N2 suppliers
      close some defect ledgers, but the global/window form crosswalk or the
      polarized BV spectral pairing remains the final source wall

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Report source lock | The report commit is the direct child of the parent verdict, adds only the 143-line read-only report, and was `rh_clean` HEAD at audit. | `[ABSTRACT][PAPER]` |
| Exact P59 kernel vector | The conjugated, source-ordered, reflected and `L^{-1/2}`-scaled kernel gives the literal Riesz identity for the transform. | `[FINITE_CELL][PAPER]` |
| Full source commutator | The complete CCM matrix satisfies the rank-two mode commutator without splitting W02, Arch or Prime. | `[FINITE_CELL][LEAN]` |
| P59 main-block reduction | Away from the pole lattice the action on the kernel reduces to explicit lattice sums and the vectors `M1-a1`, `beta`, `1`; the entire pole kernel extends the identity through all included poles. | `[FINITE_CELL][PAPER]` |
| Reported higher-action wall | The claimed nonterminating hierarchy is false: `(M-epsilon)r = C r + ||r||^2 q`. | `[FINITE_CELL][PAPER]` |
| P59 self-consistency | After exact recombination of target and error into the selected source row, the proposed recursive equation is `Phi=Phi`; it supplies no contraction or rate. | `[FINITE_CELL][PAPER]` |
| Ground-graph identity | The exact graph-normalized ground transform remains a nonzero scalar multiple of the same real-zero ground transform and differs from the selected trial by the transform of `-C^{-1}r`. | `[FINITE_CELL][PAPER]` |
| Current compact source rate | No theorem in the current corpus proves compact decay of the exact graph functional. | `[COFINAL_FAMILY][PAPER]` |

## 1. Source lock

The report commit is exactly

```text
e09e5858bb7300022ec4e2b48e2f3b5dd5d7bb95
```

with parent

```text
6b408189c029975fbf073e780cb603073e305532.
```

It adds only the stated read-only preflight. No Lean source and no numerical artifact changed. `[ABSTRACT][PAPER]`

The reported discriminator failure is accepted:

```text
GOAL058_P59_KERNEL_COMMUTATOR_LEAVES_FULL_SOURCE_ACTION_OR_PRIME_OSCILLATION_WALL.
```

This is not a kill of the exact ground-graph transform identity. It is a kill of the selected attempt to manufacture its compact rate by repeatedly moving the full source action through the trial-line graph inverse. `[COFINAL_FAMILY][PAPER]`

## 2. What the report proved correctly

The exact Riesz vector is

\[
\kappa_{k,j}(z)=
\overline{L_k^{-1/2}
\operatorname{proposition59PoleKernel}(L_k,n_j,-z)}.
\]

With the project convention that the inner product is conjugate-linear in the first argument,

\[
T_k(w)(z)=\langle\kappa_k(z),w\rangle.
\]

Off the finite pole lattice this vector is a diagonal-mode resolvent of the all-ones vector. The full CCM commutator then reduces `(M-aI)kappa` to a finite-rank expression involving lattice sums, the beta column and `M1`. No W02/Arch/Prime component split enters. The removable-pole values provide the entire continuation needed for compacts crossing the lattice. `[FINITE_CELL][PAPER]`

These are valid reusable identities. They do not yet carry a cofinal estimate. `[COFINAL_FAMILY][PAPER]`

## 3. Strongest correction: the alleged higher-action hierarchy collapses

Fix one finite cell. Write

\[
M=M^*,\qquad \|q\|=1,
\qquad a=\langle q,Mq\rangle,
\qquad r=(M-aI)q.
\]

Let `epsilon` be the exact bottom eigenvalue and define

\[
P=qq^*,\qquad Q=I-P,
\qquad C=Q(M-\epsilon I)Q+P.
\]

Set

\[
s=(M-\epsilon I)r.
\]

Because `r` is orthogonal to `q`, direct matrix algebra gives

\[
[M,P]=rq^*-qr^*,
\]

and the report's rank-at-most-four formula simplifies to

\[
\boxed{
[M,C]=(r-s)q^*-q(r-s)^*.
}
\]

Thus the commutator has rank at most two, not four. `[FINITE_CELL][PAPER]`

Moreover,

\[
Cr=Q(M-\epsilon I)r
=s-\|r\|^2q,
\]

because

\[
\langle q,(M-\epsilon I)r\rangle=\|r\|^2.
\]

Hence

\[
\boxed{
(M-\epsilon I)r=Cr+\|r\|^2q.
}
\]

The report's wall term therefore does not create a new tower

\[
r,(M-\epsilon)r,(M-\epsilon)^2r,\ldots.
\]

It reduces exactly to the original graph functional, the raw residual transform and explicit overlaps with `q` and `r`. The diagnosis “nonterminating higher-action recursion” is refuted. `[FINITE_CELL][PAPER]`

## 4. Why this repair does not rescue the P59 self-consistency route

Let

\[
\Phi(z)=\langle C^{-1}\kappa(z),r\rangle.
\]

The selected source row satisfies `(M-aI)q=r` by definition. Therefore any exact moved-action identity applied after recombining the target and error channels into that same source row must return

\[
\langle C^{-1}\kappa,(M-aI)q\rangle
=
\langle C^{-1}\kappa,r\rangle
=
\Phi.
\]

After substituting the rank-two commutator and the collapse identity above, the proposed relation

```text
Phi = explicit + lambda(z) * Phi + B
```

has no strict residual coefficient to divide by. On the combined exact source object it reduces to

\[
\boxed{\Phi(z)=\Phi(z).}
\]

This is the cheapest decisive falsifier: substitute the exact recombined source row before taking any norm or asymptotic limit. The self-consistency is algebraic bookkeeping, not a contraction. `[FINITE_CELL][PAPER]` **[C10]**

Consequently, proving the new beta-column and diagonal moments would close only the main block of a mechanism whose complete consumer remains open. Formalizing those moments now would be a W9 violation: a bridge node with no load-bearing source progress. `[COFINAL_FAMILY][PAPER]`

## 5. Boundary of the kill

The following remains valid:

\[
d^{-1}\xi-q=-C^{-1}r,
\]

and therefore

\[
G_k^{\rm graph}(z)-P_k^{\rm trial}(z)
=-\operatorname{centerFactor}_k
\langle C_k^{-1}\kappa_k(z),r_k\rangle.
\]

The graph-normalized function remains a nonzero scalar multiple of the same finite Proposition-59 ground transform. Its zero set remains real under the already proved finite ground package. `[FINITE_CELL][PAPER]`

What is killed is only:

```text
P59 kernel commutator
→ finite moments
→ self-consistency
→ compact rate.
```

The exact functional itself is still the smallest consumer object. `[COFINAL_FAMILY][PAPER]`

A ground-line spectral graph was also tested as the obvious commuting repair. It commutes with `M`, but on the ground complement its inverse is exactly the inverse of `M-aI`; moving the action cancels it and returns the original projective transform difference. It is another identity, not a source-rate mechanism. `[FINITE_CELL][PAPER]`

## 6. Selected representation after the kill

The best remaining representation is not a norm of the residual. It is the polarized full-source pairing for the exact vector

\[
v_k(z)=C_k^{-1}\kappa_k(z).
\]

The exact source-action split gives, schematically,

\[
\langle v_k,(M_k-a_kI)y\rangle
=
W_{i_k}(S(v_k),S(y))-a_k\langle v_k,y\rangle.
\]

For the factor-four target, the unwindowed object

\[
E_\star(4\,\operatorname{explicitCCMLimitH})
\]

has already been source-locked on paper as an element of the radical of the global Weil form. Projection and window restriction do not preserve radicality, so all defects must remain explicit. `[ABSTRACT][PAPER]` **[C04][C10]**

An earlier preflight derived the exact BV Poisson completion

\[
E(f)(u)=E(\widehat f)(1/u)
+\tfrac12\widehat f(0)u^{-1/2}
-\tfrac12f(0)u^{1/2},
\]

with the production midpoint convention. For the selected zero-mass trial only the center-value defect survives. This is the correct explicit-shadow mechanism, not an `O`-term. `[ABSTRACT][PAPER]` **[C13]**

The crucial change since that earlier audit is that W5/Sturm first-order control and the source-scaled N2 projection-tail rate are now committed suppliers. The old audit asked for a uniform dual bound over every unit vector; the present graph functional asks only for the one source-defined vector `C^{-1}kappa(z)`. Therefore one post-W5 read-only source preflight is decision-changing rather than repetitive. `[COFINAL_FAMILY][PAPER]`

## 7. One next transaction

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_POST_W5_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY
```

It must answer one discriminator:

```text
SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_SOURCE_READY

vs

GOAL058_GLOBAL_WINDOW_FORM_CROSSWALK_OR_BV_PRIME_OSCILLATION_WALL.
```

The preflight must not re-derive generic graph algebra. It must source-lock and spend, or reject, the exact remaining suppliers:

1. global Weil radical membership of the factor-four limit target;
2. exact global-to-window/project source-form crosswalk on the required domain;
3. inversion covariance and BV polarized spectral representation;
4. explicit center, window and projection defects;
5. compact envelope of `C^{-1}kappa(z)` with the complement-floor cost visible;
6. W5/Sturm/N2 rates for each displayed defect;
7. one common precommitted tail;
8. the final compact rate for `Phi_k`.

No Lean source and no numerical probe is authorized by this verdict. `[COFINAL_FAMILY][PAPER]`

## STRONGEST ATTACK

The strongest objection is:

> The global radical theorem concerns an unwindowed Schwartz target, while the project consumer contains a finite projection in a shifted form domain. Why should a radical statement survive those changes?

It does not survive automatically. A two-dimensional plant already shows that projection can destroy radicality. The selected route is valid only if it carries the exact difference as window/projection/point defects and proves their polarized pairing against `C^{-1}kappa(z)` tends to zero. Any statement that simply replaces the finite target by the global radical object is killed by **C04** and **C10**. `[ABSTRACT][PAPER]`

If the global/window form crosswalk cannot be proved on the exact shifted domain, or if the BV polarized pairing still requires the unrestricted prime oscillation estimate, R1 fails. Then the route moves to the precommitted two-mode target-subspace Feshbach representation or, last, the exact combined-Gamma retained-prime wall. `[COFINAL_FAMILY][PAPER]`

## META CLOSEOUT

### What became smaller?

The report's open object

```text
full source action + rank-four commutator + higher-action recursion
```

became

```text
one scalar graph functional;
rank-two commutator;
no higher-action hierarchy;
one exact polarized radical/window-defect discriminator.
```

### What was killed?

```text
P59 self-consistency as a compact-rate mechanism;
nonterminating (M-epsilon)^j r hierarchy;
beta/diagonal moments as the next load-bearing node;
ground-line commuting graph as a source-rate shortcut.
```

### What must not be tried again?

```text
another commutator wrapper around C^{-1};
formalizing finite moments before the full consumer closes;
componentwise W02/Arch/Prime norms;
scalar near-radical values as polarized bounds;
projection-tail L2 decay relabeled as source-action decay.
```

### Current smallest named gap

```text
SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_COMPACT_DECAY.
```

### Next cheapest decisive test

Run the post-W5 read-only preflight on the exact vector

\[
v_k(z)=C_k^{-1}\kappa_k(z),
\]

and force every global/window/category/rate defect into one explicit compact ledger.

### Prediction closeout

```text
P_P59_KERNEL_COMMUTATOR_1, p=0.81:
  CONFIRMED.

P_TARGET_MOMENT_SOURCE_1, p=0.60:
  CONFIRMED_WITH_ANATOMY_REPAIR.
  Finite moments appeared, but the alleged higher-action wall collapsed and
  the overall mechanism failed by tautological self-consistency.

P_GROUND_COFINAL_RATE_1, p=0.76:
  LIVE_NOT_YET_TESTED.
```

No retroactive repair.

### Memory entry

```yaml
iteration:
  target: P59 kernel-commutator compact source rate
  status: OPEN
  failed_strategy: self-consistent action transfer through the trial-line graph inverse
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SELECTED_FERRERS_GRAPH_FUNCTIONAL_POLARIZED_NEAR_RADICAL_COMPACT_DECAY
  invariant_learned: preserve the exact full-source signed pairing and the single precommitted family
  forbidden_future_move: do not recurse source action through C_inverse or formalize nondecisive moments
  next_decisive_test: post-W5 polarized near-radical graph-functional preflight
```
