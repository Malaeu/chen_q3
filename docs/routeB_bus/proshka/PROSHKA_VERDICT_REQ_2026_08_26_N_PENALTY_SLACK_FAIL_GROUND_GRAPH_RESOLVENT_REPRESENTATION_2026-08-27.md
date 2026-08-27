# STATUS: OPEN — PENALTY-SLACK SOURCE FAIL RATIFIED; MODE-GRADED FLOOR NOT SELECTED; GROUND-GRAPH RESOLVENT FUNCTIONAL SELECTED

```yaml
PRIMARY: RATIFY_PENALTY_SLACK_FAIL_AND_SELECT_GROUND_GRAPH_RESOLVENT_FUNCTIONAL
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-N
  ADJUDICATION_ROLE: READ_ONLY_PREFLIGHT_CLOSEOUT
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false
  STALE_OPEN_ENTRY_OBSERVED: REQ-2026-08-21-P_HAS_PRIOR_VERDICT_AND_IS_NOT_REANSWERED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 1270eecec675cc0002557159caa062622877f901
  REPORT_PARENT: edfedd82e882e1437e3a30869708401b9c6871be
  REPORT_PATH: docs/routeB_bus/LINUX_PENALTY_SLACK_COMPACT_RATE_PREFLIGHT_GOAL058_2026-08-27.md
  REPORT_GIT_BLOB: 7ea176ca8060bc184ecbea2b3ede2d8d7673bd48
  REPORT_LINES: 126
  REPORT_ONLY_COMMIT: true
  HEAD_IS_REPORT_COMMIT_AT_AUDIT: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_PERFORMED: false
  NEW_NUMERICAL_PROBE_PERFORMED: false
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false

ADJUDICATION:
  discriminator_fail_confirmed: true
  failure_code_confirmed: GOAL058_PENALTY_SLACK_SELF_ENERGY_SOURCE_RATE_NOT_AVAILABLE
  penalty_slack_lower_envelope_I_version: PAPER_PASS
  penalty_slack_lower_envelope_Gram_version: PAPER_PASS
  Schur_minimal_slack_identity: PAPER_PASS
  compact_penalty_slack_threshold: PAPER_PASS
  source_defined_b_tau_g_s_on_selected_family: ABSENT
  cofinal_penalty_slack_rate_in_current_corpus: ABSENT
  report_claim_resolvent_gain_requires_mode_growing_floor: REFUTED_AS_UNIVERSAL
  report_REP_alpha_mode_graded_even_floor_selected: false
  report_REP_beta_combined_Gamma_selected: false
  selected_representation: GROUND_GRAPH_RESOLVENT_TRANSFORM_FUNCTIONAL
  Lean_source_authorized_now: false

PARITY_CORRECTION:
  selected_trial_exactly_reflection_even: NOT_PROVED
  penalty_engine_evenness_requires_Jq_eq_q: true
  penalty_certificate_as_automatic_odd_sector_floor: REJECTED_FOR_CURRENT_SELECTED_ROW
  odd_sector_floor_remains_separate_theorem_cargo: true

GROUND_GRAPH_REPRESENTATION:
  trial: q_k
  matrix: K_k
  Rayleigh: a_k
  residual: r_k = (K_k - a_k I) q_k
  ground: K_k xi_k = epsilon_k xi_k
  graph_coordinate: d_k = inner(q_k, xi_k)
  trial_projection: P_k = q_k q_k_star
  trial_complement: Q_k = I - P_k
  full_carrier_graph_operator: C_k = Q_k (K_k - epsilon_k I) Q_k + P_k
  exact_coefficient_identity: d_k_inverse xi_k - q_k = - C_k_inverse r_k
  exact_transform_error: >-
    graphNormalizedGround_k(z) - centeredPstar_k(z)
    = - centerFactor_k * sourceOrderedCCMRawTransform_k(C_k_inverse r_k)(z)
  overlap_requirement: d_k != 0
  overlap_supplier: existing_strict_residual_floor_ratio_less_than_one
  zero_set_preservation: nonzero_scalar_multiple_of_same_ground_transform

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_COMPACT_DECAY
  formula: >-
    for every compact K in the open centered strip,
    sup_{z in K} norm(
      centerFactor_k * sourceOrderedCCMRawTransform_k(C_k_inverse r_k)(z)
    ) tends to zero

CLOSES:
  - PENALTY_SLACK_AS_PRIMARY_SOURCE_REPRESENTATION
  - SOURCE_DEFINED_B_TAU_PARAMETER_REQUIREMENT
  - PROJECTIVE_CAUCHY_MAJORANT_AS_ONLY_TRACKING_REPRESENTATION
  - PENALTY_CERTIFICATE_AUTOMATIC_ODD_FLOOR_OVERCLAIM
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_COMPACT_DECAY
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
  TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  DISCRIMINATOR:
    PASS: SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_SOURCE_READY
    FAIL: GOAL058_GROUND_GRAPH_RESOLVENT_FUNCTIONAL_SOURCE_NOT_AVAILABLE
  REQUIRED_OUTPUT:
    - exact orientation of d_k = inner(q_k, xi_k) against the existing overlap inner(xi_k, q_k)
    - exact proof that ratio_less_than_one implies d_k_nonzero
    - exact full-carrier definition C_k = Q_k (K_k - epsilon_k I) Q_k + P_k
    - exact proof that the complement floor makes C_k positive definite and invertible
    - exact coefficient graph identity d_k_inverse xi_k - q_k = - C_k_inverse r_k
    - exact graph-normalized P59 transform and scalar transfer of real zeros
    - exact transform-error identity against centeredPstar
    - source audit of the literal scalar resolvent matrix element, preserving the combined prime cancellation
    - comparison against mode-graded self-energy and exact combined-Gamma routes
    - one Lean theorem signature and complete proof route if the representation is source-ready
  SUCCESS_CODE: SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_LEAN_READY
  FAILURE_CODE: GOAL058_GROUND_GRAPH_RESOLVENT_FUNCTIONAL_SOURCE_NOT_AVAILABLE

CANDIDATE_REPRESENTATIONS:
  R1_GROUND_GRAPH_RESOLVENT_TRANSFORM:
    rank: PRIMARY
    target: >-
      direct compact decay of the exact P59 transform of C_k_inverse r_k
    kill_power: 10/10
    proof_cost: 5/10
    route_fit: 10/10
  R2_MODE_GRADED_EVEN_SELF_ENERGY:
    rank: RUNNER_UP
    target: >-
      a coefficientwise growing even-sector floor and an inverse-weighted residual profile
      strong enough to force lambda_k^(2sigma) L_k s_k/g_k to zero
    kill_power: 9/10
    proof_cost: 8/10
    route_fit: 8/10
  R3_EXACT_COMBINED_GAMMA_RETAINED_PRIME:
    rank: LAST_RESORT
    target: >-
      cancellation-preserving source estimate directly on Gamma_k = D_k r_k,
      including retained-prime action and W02 endpoint trace
    kill_power: 10/10
    proof_cost: 10/10
    route_fit: 9/10

REGISTERED_PREDICTIONS:
  P_RAYLEIGH_EXCESS_GENERIC_PORT_1:
    prior_probability: 0.98
    fate: CONFIRMED
  P_RAYLEIGH_EXCESS_SOURCE_1:
    prior_probability: 0.62
    fate: CONFIRMED_AS_OPEN_SOURCE_GAP
  P_PENALTY_SLACK_IDENTITY_1:
    prior_probability: 0.99
    fate: CONFIRMED
  P_PENALTY_SLACK_SOURCE_1:
    prior_probability: 0.74
    fate: CONFIRMED
  P_GROUND_COFINAL_RATE_1:
    prior_probability: 0.76
    fate: LIVE_NOT_YET_TESTED
  P_GROUND_GRAPH_IDENTITY_1:
    probability: 0.98
    prediction: >-
      the exact coefficient and transform graph identities close on the existing
      selected ground witness with no new analytic hypothesis
  P_GROUND_GRAPH_SOURCE_1:
    probability: 0.67
    prediction: >-
      no ready compact-rate theorem exists, but the remaining source object is one
      direct resolvent-weighted P59 functional, strictly smaller than self-energy
  P_MODE_GRADED_EVEN_FLOOR_1:
    probability: 0.38
    prediction: >-
      the current odd-tail high-frequency proof does not directly upgrade to a
      coefficientwise growing even-sector floor without a new cross-mode theorem

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C07_PROBABILITY_WEIGHTED_ESTIMATE
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Source lock and surviving FAIL

The report commit is the direct child of the preceding Proshka verdict and adds only the 126-line read-only report. No Lean or numerical source changed. `[ABSTRACT][PAPER]`

The discriminator failure is correct:

```text
GOAL058_PENALTY_SLACK_SELF_ENERGY_SOURCE_RATE_NOT_AVAILABLE.
```

The repository has no selected-family definitions of `b_k`, `tau_k`, `g_k` or `s_k`, and no theorem giving the required cofinal penalty-slack rate. The report asked the capability shelf before making that negative claim. `[COFINAL_FAMILY][PAPER]`

### 2. What the report proved correctly

For a Hermitian matrix `K`, a unit trial `q`, Rayleigh value

\[
a=\langle q,Kq\rangle,
\]

and a certificate

\[
K-bI+\tau qq^*\succeq0,
\qquad b>a,
\]

define

\[
g=b-a,
\qquad
s=\tau-g.
\]

Testing on `q` gives `s >= 0`; testing on arbitrary unit vectors gives

\[
\epsilon\ge a-s.
\]

The same argument works in the positive-definite Gram metric. `[ABSTRACT][PAPER]`

In the block decomposition `C q + q^perp`, if the complementary block satisfies `B-bI > 0`, the exact Schur criterion gives

\[
s_{\min}=r^*(B-bI)^{-1}r.
\]

This is a genuine resolvent-weighted self-energy, not the raw residual norm. `[ABSTRACT][PAPER]` **[C04][C10]**

Together with the generic projective consumer, it yields the sufficient compact threshold

\[
\lambda_k^{2\sigma}L_k\frac{s_k}{g_k}\longrightarrow0,
\qquad 0\le\sigma<\frac12.
\]

That threshold is correct as a sufficient route. `[COFINAL_FAMILY][PAPER]`

The fixed-`m=13` Phase-2 values remain diagnostic only. They neither prove nor disprove a cofinal slack rate. `[FINITE_CELL][ARB_INTERVAL]`

### 3. First correction: a mode-growing floor is not logically necessary

The report says that resolvent gain exists only after proving a mode-growing complementary floor. That is too strong.

What is true is narrower:

> If the only permitted information is `B-bI >= c I` and `||r||`, then the crude bound degenerates to `s <= ||r||^2/c`.

But the exact resolvent can be much smaller because of spectral orientation and cancellation. A two-coordinate plant makes the distinction literal:

\[
C=I,
\qquad r=e_1,
\qquad h=e_2.
\]

Then

\[
r^*C^{-1}r=1,
\qquad
h^*C^{-1}r=0.
\]

Thus a direct consumer functional can vanish while the global self-energy remains order one. Proving self-energy decay is strictly stronger than proving the final transform error. `[ABSTRACT][PAPER]` **[C10]**

The repository itself already preserves an exact inverse-weighted odd-tail correction `R^* C^{-1} R`; it explicitly forbids replacing it by a scalar-floor raw-norm surrogate. The finite nested-Schur audit also found the exact correction substantially smaller than its constant-floor surrogate. These facts do not supply the selected even-sector rate, but they refute the universal claim that resolvent gain requires a coefficientwise growing floor. `[FINITE_CELL][LEAN]` `[FINITE_CELL][CONDITIONAL]`

### 4. Second correction: the current selected trial is not proved exactly even

The generic penalty theorem obtains an even ground only under the explicit hypothesis

\[
Jq=q.
\]

The selected Ferrers source layer does not provide this equality. It instead carries an exact odd-mass quantity and a physical reflection-defect identity, and its complement-floor receiver keeps the even-sector and odd-sector floors as separate hypotheses. `[FINITE_CELL][LEAN]`

Therefore the earlier claim that one selected rank-one penalty certificate automatically supplies the odd-sector floor is rejected. A penalty certificate may still supply a trial-complement floor and a simple ground, but parity selection requires the separately retained odd-sector theorem cargo. `[FINITE_CELL][PAPER]` **[C04]**

### 5. Selected representation: normalize the same ground by its trial coordinate

Let, on one literal selected cell,

\[
K=K^*,
\qquad
\|q\|=1,
\qquad
a=\langle q,Kq\rangle,
\qquad
r=(K-aI)q.
\]

Let `epsilon, xi` be the already selected unit bottom ground from the literal complement floor. Put

\[
d=\langle q,\xi\rangle.
\]

The existing strict residual/floor-ratio guard gives `d != 0`. Define

\[
P=qq^*,
\qquad
Q=I-P,
\]

and the full-carrier graph operator

\[
\mathcal C
=
Q(K-\epsilon I)Q+P.
\]

The complement floor at the Rayleigh shift and `epsilon <= a` imply that `C` is positive definite: it acts as the identity on the trial line and as a positive operator of floor at least `beta` on its orthogonal complement. Hence `C` is invertible. `[FINITE_CELL][PAPER]`

Decompose

\[
\xi=dq+w,
\qquad w\perp q.
\]

Projecting the ground equation onto `q^perp` gives

\[
Q(K-\epsilon I)Qw=-d\,r.
\]

Therefore

\[
\boxed{
d^{-1}\xi-q=-\mathcal C^{-1}r.
}
\]

This is an exact graph identity, not an inequality. `[ABSTRACT][PAPER]`

The existing tracked transform uses the orthogonal-projection scale `inner(xi,q)`. Dividing it by the nonzero number `|inner(q,xi)|^2` gives the graph-normalized transform, a nonzero scalar multiple of the same Proposition-59 ground transform. Its zeros remain real. `[FINITE_CELL][PAPER]`

By linearity of the literal source-ordered Proposition-59 transform,

\[
\boxed{
G_k^{\rm graph}(z)-P_k^{\rm trial}(z)
=
-\frac{\Xi(0)}{\operatorname{rawFplus}_k(0)}
T_k\!\left(\mathcal C_k^{-1}r_k\right)(z).
}
\]

The right side is exactly the final consumer error. It removes:

```text
b_k;
tau_k;
g_k;
s_k;
a separate inverse-overlap upper bound;
the global coefficient-norm Cauchy majorant.
```

It retains:

```text
the same selected matrix;
the same selected trial;
the same selected ground witness;
the same selected schedule;
the same source-ordered P59 transform;
the existing complement and odd-sector floors.
```

This is the smallest current source object. `[COFINAL_FAMILY][PAPER]` **[C10]**

### 6. Why REP-alpha is not the next transaction

A coefficientwise estimate

\[
\langle w,(B_k-b_k)w\rangle
\ge
\sum_n\phi_k(n)|w_n|^2,
\qquad \phi_k(n)\uparrow\infty,
\]

would be useful. It is also substantially stronger than the current consumer.

The existing odd-tail proof uses one high/low frequency split and a scalar low-band mass budget. It does not diagonalize the windowed archimedean form in the CCM mode basis and does not control arbitrary cross-mode interference. Retaining the pointwise logarithmic growth of the multiplier is therefore not, by itself, a coefficientwise growing matrix floor. A new cross-mode theorem would still be required. `[COFINAL_FAMILY][PAPER]` **[C04][C10]**

Moreover REP-alpha needs both a growing even floor and an inverse-weighted residual profile. Neither is supplied. It opens two analytic fronts before touching the exact final functional. It is retained only as a runner-up supplier mechanism.

### 7. Representation ordering

```text
PRIMARY:
  GROUND_GRAPH_RESOLVENT_TRANSFORM
  exact final functional;
  no penalty parameters;
  no global self-energy requirement.

RUNNER-UP:
  MODE_GRADED_EVEN_SELF_ENERGY
  useful only if a direct-functional estimate needs a positive majorant.

LAST RESORT:
  EXACT_COMBINED_GAMMA_RETAINED_PRIME
  maximum source fidelity, maximum proof cost.
```

## FINAL PROPOSAL

Do not formalize the penalty-slack wrappers now. Their source parameters are absent.

Do not launch the mode-growing even floor before checking whether the exact final transform functional already collapses under the source identities.

Run one read-only preflight on the graph-normalized ground transform. The decisive question is:

> After normalizing the same bottom ground by its nonzero trial coordinate, can the literal source identities control the single function
> \[
> z\mapsto
> \frac{\Xi(0)}{\operatorname{rawFplus}_k(0)}
> T_k(\mathcal C_k^{-1}r_k)(z)
> \]
> directly on compact substrips?

A positive answer authorizes one exact Lean graph identity and one source-rate theorem. A negative answer names the exact unresolved resolvent matrix element before escalating to REP-alpha or combined `Gamma`.

## STRONGEST ATTACK

The strongest objection is:

> `C_k^{-1}r_k` may simply hide the same prime-action wall as the raw residual.

That objection is live. The selected representation is not declared solved.

The preflight must fail it if every legal estimate reduces to one of:

```text
||r_k|| / beta;
self-energy s_k;
combined Gamma_k without a new cancellation identity.
```

The representation survives only if the exact P59 functional, the exact resolvent, or the exact source action provides a strictly smaller cancellation-preserving scalar object. A zero-consistent source computation without a theorem-level discriminator remains `INCONCLUSIVE`.

## CODEX DIRECTIVE

```text
NO LEAN SOURCE TRANSACTION AUTHORIZED.
NO NUMERICAL PROBE AUTHORIZED.

Run only:
  GOAL058_SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_PREFLIGHT

Mode:
  PAPER_AND_SOURCE_READ_ONLY

Read first:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1SelectedFerrersTrackedGroundTransform.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/
    CCMProposition59ComplexTrialComplementFloor.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/
    CCMProposition59ComplexTrialComplementSpectral.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/
    LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/
    D0PstarSourceWeilOddTailResidual.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1SelectedFerrersCommutatorResidualDefect.lean

Required:
  1. Lock the inner-product orientation of d = inner(q,xi).
  2. Prove the graph identity on paper in the literal carrier.
  3. Identify a full-carrier positive/invertible graph operator.
  4. Prove the exact P59 transform-error identity.
  5. Audit the direct resolvent matrix element against every existing source identity.
  6. Preserve combined prime cancellation and the one precommitted tail.
  7. Return one Lean signature and proof route only if the representation is source-ready.

Forbidden:
  - introduce b_k or tau_k;
  - replace the direct functional by a raw norm before source audit;
  - claim the selected trial is exactly even;
  - choose a second ground witness;
  - use finite interval diagnostics in a cofinal quantifier;
  - split the retained-prime term entrywise;
  - edit Lean;
  - run numerics;
  - claim ground-family convergence, route promotion, or RH.
```

## META CLOSEOUT

**What became smaller?**

The missing compact tracking rate is now one direct scalar entire-function error, not a global self-energy and not a raw coefficient norm.

**What was killed?**

```text
Temple rate-equivalence;
source-ready penalty slack;
mode-growing floor as logically necessary;
penalty certificate as automatic odd-floor supplier.
```

**What must not be tried again?**

Do not infer a coefficientwise mode floor from pointwise multiplier growth. Do not introduce post-hoc penalty parameters. Do not majorize the exact consumer before checking its cancellation.

**Current smallest named gap:**

```text
SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_COMPACT_DECAY
```

**Next cheapest decisive test:**

Source-lock the exact graph-normalized P59 error and determine whether it reduces to a genuinely smaller resolvent matrix element.

**Prediction fates:**

```text
P_RAYLEIGH_EXCESS_GENERIC_PORT_1: CONFIRMED.
P_RAYLEIGH_EXCESS_SOURCE_1: CONFIRMED AS OPEN.
P_PENALTY_SLACK_IDENTITY_1: CONFIRMED.
P_PENALTY_SLACK_SOURCE_1: CONFIRMED AS FAIL.
P_GROUND_COFINAL_RATE_1: LIVE.
```

**Memory entry:**

```yaml
iteration:
  target: selected_Ferrers_ground_compact_tracking_rate
  status: PROGRESS
  failed_strategy: penalty_slack_self_energy_as_source_ready_representation
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_COMPACT_DECAY
  invariant_learned: normalize the same ground by its trial coordinate before estimating; the exact transform error is a resolvent functional, not a projective norm
  forbidden_future_move: do_not_require_global_self_energy_decay_before_auditing_the_direct_P59_functional
  next_decisive_test: source_audit_the_graph_resolvent_P59_matrix_element
```
