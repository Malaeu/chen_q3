# STATUS: OPEN — COMPACT `Γ` RATE IS ABSENT; REP1 AND NAIVE REP2 ARE REJECTED; RAYLEIGH-EXCESS DUAL IS SELECTED
```yaml
PRIMARY: RATIFY_COMPACT_GAMMA_SOURCE_FAIL_AND_SELECT_RAYLEIGH_EXCESS_PREFLIGHT
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
  REPORT_COMMIT: 406d4988b2b13d96d1b715357aabcacc048f57f1
  REPORT_PARENT: 6a47f79cf29caffd24fa23a1ee8078883f819b0c
  REPORT_PATH: docs/routeB_bus/LINUX_COMPACT_LOG_COMMUTATOR_RATE_SOURCE_PREFLIGHT_GOAL058_2026-08-27.md
  REPORT_GIT_BLOB: e7b0e7bd907cdaa6a67396479548d210561314d3
  REPORT_LINES: 133
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
  failure_code_confirmed: GOAL058_COMPACT_LOG_COMMUTATOR_SOURCE_RATE_NOT_AVAILABLE
  compact_Gamma_rate_in_current_corpus: absent
  Gamma_preserved_as_combined_object: true
  centering_factor_port: PAPER_READY_ASSEMBLY_ONLY
  sourceOrdered_P59_compact_envelope: PAPER_READY_ASSEMBLY_ONLY
  compact_threshold_lambda_2sigma_L2_G: confirmed
  pointwise_n_minus_two_decay_is_necessary: false
  pointwise_n_minus_two_decay_is_one_sufficient_route: true
  REP1_second_order_W4_selected: false
  REP1_rejection: PRIOR_SOURCE_AUDIT_PROVES_DERIVATIVE_PROXIMITY_CONTROLS_ROW_NOT_RIESZ_RESIDUAL
  REP2_naive_q_line_Feshbach_selected: false
  REP2_rejection: Q_LINE_COUPLING_IS_EXACTLY_THE_RAW_RESIDUAL
  selected_representation: RAYLEIGH_EXCESS_LOWER_ENVELOPE
  selected_existing_catalog_gap: H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING
  Lean_source_authorized_now: false

CONFIRMED_CONSUMER_RATE:
  residual_commutator_route: >-
    for every fixed 0 <= sigma < 1/2,
    lambda_k^(2*sigma) * L_k^2 * G_k tends to zero
  notation:
    G_k: selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k
    L_k: L_m(selected index k)
    lambda_k: lambda_m(selected index k)

SELECTED_DUAL_RATE:
  exact_projective_bound: >-
    1 - |<xi_k,q_k>|^2 <= (a_k - epsilon_k) / beta
  compact_consumer_rate: >-
    for every fixed 0 <= sigma < 1/2,
    lambda_k^(2*sigma) * L_k * (a_k - epsilon_k) / beta tends to zero
  fixed_beta_specialization: >-
    lambda_k^(2*sigma) * L_k * (a_k - epsilon_k) tends to zero
  required_source_form: >-
    produce delta_k >= 0 with epsilon_k >= a_k - delta_k and
    lambda_k^(2*sigma) * L_k * delta_k / beta tending to zero

CLOSES:
  - SELECTED_FERRERS_CENTERING_FACTOR_COMPACT_BOUND_PAPER
  - SELECTED_FERRERS_SOURCEORDERED_P59_COMPACT_ENVELOPE_PAPER
  - SELECTED_FERRERS_COMPACT_LOG_COMMUTATOR_SOURCE_RATE_NOT_AVAILABLE
  - SECOND_ORDER_W4_AS_DIRECT_GAMMA_SOURCE_ROUTE_NOT_READY
  - Q_LINE_FESHBACH_AS_RAW_RESIDUAL_BYPASS_KILLED
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING
  - SELECTED_FERRERS_GROUND_COFINAL_CONVERGENCE_ASSEMBLY

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: DUALIZE
ROUTE_SCORE: 5

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_RAYLEIGH_EXCESS_COMPACT_RATE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  DISCRIMINATOR:
    PASS: SELECTED_FERRERS_RAYLEIGH_EXCESS_COMPACT_RATE_SOURCE_READY
    FAIL: H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING
  REQUIRED_OUTPUT:
    - exact same-tail selected ground eigenvalue epsilon_k and trial Rayleigh a_k
    - exact use of weighted_projective_defect_le_rayleigh_excess_div_gap
    - exact compact threshold lambda^(2*sigma)*L*(a-epsilon)/beta
    - shelf audit for a source lower envelope epsilon_k >= a_k - delta_k
    - audit of penalty, sector-floor, finite-certificate and Schur-complement suppliers
    - circularity audit excluding global Weil positivity, RH, and the desired convergence
    - comparison against the exact combined-Gamma prime-oscillation route
    - one Lean theorem signature and complete paper route if PASS
    - two repaired representations with kill-power/cost if FAIL
  SUCCESS_CODE: SELECTED_FERRERS_RAYLEIGH_EXCESS_COMPACT_RATE_LEAN_READY
  FAILURE_CODE: GOAL058_RAYLEIGH_EXCESS_LOWER_ENVELOPE_SOURCE_NOT_AVAILABLE

NEXT_AFTER_RATE_PREFLIGHT_PASS_ONLY:
  TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
  REQUIRED_CONCLUSION: >-
    one exact reindexed tracked-ground family has real zeros and tends locally
    uniformly to centeredXi on every compact of the open centered strip

CANDIDATE_REPRESENTATIONS:
  R1_RAYLEIGH_EXCESS_LOWER_ENVELOPE:
    rank: PRIMARY
    target: >-
      epsilon_k >= a_k - delta_k and
      lambda_k^(2*sigma)*L_k*delta_k/beta -> 0 for every sigma < 1/2
    kill_power: 10/10
    proof_cost: 7/10
    route_fit: 10/10
  R2_EXACT_COMBINED_GAMMA_PRIME_OSCILLATION:
    rank: RUNNER_UP
    target: >-
      cancellation-preserving source estimate directly on Gamma_k = D_k r_k,
      including the retained-prime action and W02 endpoint trace
    kill_power: 10/10
    proof_cost: 10/10
    route_fit: 9/10

REGISTERED_PREDICTIONS:
  P_CENTER_FACTOR_PORT_1:
    prior_probability: 0.97
    fate: CONFIRMED_PAPER_READY
  P_SOURCEORDERED_KERNEL_ENVELOPE_PORT_1:
    prior_probability: 0.92
    fate: CONFIRMED_WITH_DIRECT_P59_MECHANISM
  P_COMPACT_LOG_COMMUTATOR_SOURCE_1:
    prior_probability: 0.78
    fate: CONFIRMED
  P_GROUND_COFINAL_RATE_1:
    prior_probability: 0.76
    fate: LIVE_NOT_YET_TESTED
  PRIOR_R2_GENUINELY_DIFFERENT_CLASSIFICATION:
    source: verdict_6a47f79c
    fate: REFUTED_AS_STATED
    reason: standard q-line Feshbach coupling equals the raw residual exactly
  P_RAYLEIGH_EXCESS_GENERIC_PORT_1:
    probability: 0.98
    prediction: >-
      the existing generic weighted-Rayleigh and projective-evaluation cores
      yield the compact threshold without new analytic mathematics
  P_RAYLEIGH_EXCESS_SOURCE_1:
    probability: 0.62
    prediction: >-
      the first genuine source question is a lower envelope for the selected
      ground eigenvalue, not a derivative estimate for the source action

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C07_PROBABILITY_WEIGHTED_ESTIMATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Source lock and discriminator

The report commit is the unique direct child of the prior Proshka verdict and adds only the 133-line read-only preflight. No Lean source or numerical artifact changed. `[ABSTRACT][PAPER]`

The discriminator failure is correct. The current corpus does not prove

\[
\lambda_k^{2\sigma}L_k^2\|\Gamma_k\|^2\longrightarrow0,
\qquad 0\le\sigma<\tfrac12,
\]

for the literal combined commutator defect

\[
\Gamma_k=D_kr_k.
\]

The new Sturm files do not mention the finite CCM residual objects, and W4/W5 control a first-order exterior projection tail rather than the interior source-action defect. Therefore no existing theorem can be relabeled as the consumer-strength compact `Gamma` rate. `[COFINAL_FAMILY][PAPER]` **[C10]**

### 2. The two cheap ports survive

The exact zero-mode identity and the inverse-log center floor give an eventual uniform upper bound on

\[
\left\|\frac{\Xi(0)}{\operatorname{rawFplus}_k(0)}\right\|.
\]

No new analytic input is required. `[COFINAL_FAMILY][PAPER]`

The direct Proposition-59 kernel calculation also survives. The common sine numerator cancels the nearest apparent pole before the lattice square-sum is estimated. After the explicit `L^{-1/2}` factor in `sourceOrderedCCMKernelL2`, the closed-substrip envelope has size

\[
C_\sigma\lambda_k^\sigma\sqrt{L_k}.
\]

This is paper-ready assembly, not yet a public Lean theorem. `[COFINAL_FAMILY][PAPER]`

Together with the center-anchored inequality

\[
E_k\le \frac{L_k}{c_*}G_k,
\]

the exact compact residual route requires

\[
\lambda_k^{2\sigma}L_k^2G_k\to0.
\]

The report reproduces this threshold correctly. `[COFINAL_FAMILY][PAPER]`

### 3. The report overstates the role of second-order pointwise decay

A bound

\[
|r_{k,n}|\le B_k n^{-2}
\]

is one sufficient mechanism for controlling

\[
G_k=\sum_n n^2|r_{k,n}|^2.
\]

It is not a necessary consequence of the compact consumer. The consumer needs one weighted `l2` scalar rate for the combined `Gamma`; it does not require a uniform pointwise second-order Fourier theorem. Proving the pointwise theorem is strictly stronger and may destroy cancellation. `[COFINAL_FAMILY][PAPER]`

### 4. REP1 is not selected

The project already ran a source-locked preflight on the strongest derivative-proximity contract. Its outcome was

```text
DERIVATIVE_PROXIMITY_CONTROLS_ROW_NOT_RIESZ_RESIDUAL.
```

Even after granting mode-weighted control of the physical E-star error, that route controls the selected row and the shifted-arch channel only. The exact W02 endpoint trace, the target action, scalar bounds, and especially the retained-prime oscillatory action remain open. Extending W4 by one derivative does not remove those source-action obligations.

Worse, defining a sufficiently regular “residual function” already requires control of the source action producing that residual. Thus REP1 risks assuming the derivative regularity of `M q - a q` in order to prove the rate of `M q - a q`. That is not a completed source route. `[COFINAL_FAMILY][PAPER]` **[C04][C10]**

The exact combined `Gamma` must remain the consumer. Component estimates are still legal as kill bounds, never as a replacement for its cancellation.

### 5. Naive REP2 is not a bypass

Let `q` be unit, let

\[
a=\langle q,Kq\rangle,
\qquad
P=qq^*,
\qquad
Q=I-P.
\]

In the block decomposition

\[
\mathbb Cq\oplus q^\perp,
\]

the off-diagonal Feshbach coupling is

\[
QKq=Kq-PKq=Kq-aq=r.
\]

Hence the standard one-line Schur/Feshbach graph has block form

\[
K=\begin{pmatrix}a&r^*\\r&B\end{pmatrix}.
\]

Its coupling budget is exactly the raw residual norm. Calling the same vector “coupling” rather than “residual” does not create a different representation. The previous verdict's classification of this naive q-line graph as a genuine bypass is therefore refuted as stated. `[ABSTRACT][PAPER]` **[C04][C10]**

A larger source-defined retained subspace could produce a genuinely different Feshbach problem, but no such subspace or independent coupling supplier was specified in the report.

### 6. Selected representation: Rayleigh excess

The repository already proves the generic inequality

\[
\operatorname{gap}\,(1-w_{\rm ground})\le\operatorname{RayleighExcess},
\]

and its divided form. For the selected finite Hermitian cell this becomes

\[
1-|\langle\xi_k,q_k\rangle|^2
\le
\frac{a_k-\epsilon_k}{\beta},
\]

where `epsilon_k` is the exact bottom eigenvalue, `a_k` is the selected trial Rayleigh value, and the admitted complement-floor package supplies the positive ground gap `beta`.

The already proved phase-alignment transfer bounds the coefficient-row error by the square root of this projective defect. Combining it with the paper-ready centering and Proposition-59 envelope gives

\[
\sup_{|\operatorname{Im}z|\le\sigma}
|G_k^{\rm ground}(z)-P_k^{\rm trial}(z)|^2
\le
C_{\sigma,\beta}
\lambda_k^{2\sigma}L_k
\frac{a_k-\epsilon_k}{\beta}.
\]

Therefore a sufficient source target is

\[
\boxed{
\lambda_k^{2\sigma}L_k
\frac{a_k-\epsilon_k}{\beta}\longrightarrow0
\quad(0\le\sigma<\tfrac12).
}
\]

Since the current selected tail uses one fixed positive `beta`, this saves one logarithmic factor and avoids differentiating the source action. It is a genuinely different dual object: a lower envelope for the ground eigenvalue rather than an upper envelope for the residual norm. `[COFINAL_FAMILY][PAPER]`

The exact source obligation can be written as

\[
\epsilon_k\ge a_k-\delta_k,
\qquad
\lambda_k^{2\sigma}L_k\delta_k/\beta\to0.
\]

A certificate of

\[
K_k-(a_k-\delta_k)I\succeq0
\]

would supply it directly. Penalty, sector-floor, finite-certificate, and Schur-complement machinery are plausible sources, but none is assumed here.

### 7. Circularity firewall

A lower-envelope proof is invalid if it imports:

```text
global Weil positivity on the target class;
absence of off-critical zeros;
the desired ground-family convergence;
W_k -> 0;
RH or an RH-equivalent spectral statement.
```

It remains potentially noncircular if it is built from exact finite source matrices, source-locked parity decomposition, explicit coercive floors, interval certificates, or a finite Schur complement with an independent tail theorem.

## FINAL PROPOSAL

Do not formalize the two cheap ports yet. They are no longer analytic gaps, but a standalone wrapper would not move the source frontier.

Do not launch second-order W4 on the residual function. The earlier source-action audit already shows that derivative proximity does not control the retained-prime action, and the pointwise `n^-2` target is stronger than the consumer requires.

Do not launch a one-line Feshbach graph over the trial vector. Its coupling is the raw residual exactly.

Run one read-only source preflight on the already catalogued **Rayleigh-excess projective defect** route. The decisive question is now:

> Can the selected finite source matrices provide a consumer-strength lower envelope for their true bottom eigenvalue without importing the desired convergence or global Weil positivity?

A paper-complete positive answer authorizes one Lean assembly. A negative answer returns the route to the exact combined-`Gamma` prime-oscillation wall.

## STRONGEST ATTACK

The strongest objection to the selected representation is:

> A lower bound on the true bottom eigenvalue may be exactly as hard as the global positivity theorem that the route was meant to avoid.

This objection is live. The preflight must prove that its lower envelope comes from an independently verifiable finite/source certificate and not from the conclusion in disguise. If every candidate lower envelope requires global Weil positivity or the desired limit, the Rayleigh-excess representation is killed and the retained-prime oscillation wall becomes the honest primary front.

## CODEX DIRECTIVE

```text
NO LEAN SOURCE TRANSACTION AUTHORIZED.
NO NUMERICAL PROBE AUTHORIZED.

Run only:
  GOAL058_SELECTED_FERRERS_RAYLEIGH_EXCESS_COMPACT_RATE_PREFLIGHT

Mode:
  PAPER_AND_SOURCE_READ_ONLY

Read first:
  q3.lean.aristotle/Q3/Proofs/RouteB/WeightedRayleighProjectiveDefect.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/WeightedProjectiveEvaluationTransfer.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementSpectral.lean
  docs/FINITE_CERTIFICATE_PRINCIPLE.md
  docs/routeB_bus/H2A_4_1B_3C_1_3_SELECTED_FERRERS_ESTAR_TO_GAMMA_SOURCE_ACTION_CROSSWALK_PREFLIGHT_2026-08-23.md

Required:
  - ask the capability shelf before naming a lower-envelope supplier;
  - keep epsilon_k, a_k, beta and the selected schedule on one exact family;
  - derive the compact rate with every lambda/L/beta factor;
  - audit every candidate for circularity;
  - compare lower-envelope cost against the retained-prime Gamma route.

Forbidden:
  - rename residual as Feshbach coupling;
  - infer a bottom lower envelope from a finite upper Rayleigh value;
  - use global Weil positivity or RH;
  - use numerics in a cofinal quantifier;
  - edit Lean;
  - reopen W5 or N2/N3/N4;
  - claim cofinal ground convergence, route promotion, or RH.
```

## META CLOSEOUT

**What became smaller?**

The open compact-tracking wall is no longer “derive a second derivative estimate.” It is one dual scalar question:

```text
selected trial Rayleigh value
minus true selected bottom eigenvalue
at the compact-consumer rate.
```

**What was killed?**

```text
weighted residual -> raw residual;
pointwise n^-2 decay as a necessary target;
second-order W4 as a paper-ready Gamma source;
q-line Feshbach as a distinct raw-residual bypass.
```

**What must not be tried again?**

Do not differentiate a source-action residual before proving the source action has the required regularity. Do not rename the same q-line coupling. Do not formalize assembly wrappers while the sole analytic source rate is absent.

**Current smallest named gap:**

```text
H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING
```

**Next cheapest decisive test:**

Find or kill a source lower envelope

\[
\epsilon_k\ge a_k-\delta_k
\]

with

\[
\lambda_k^{2\sigma}L_k\delta_k/\beta\to0.
\]

**Prediction fates:**

```text
P_CENTER_FACTOR_PORT_1: CONFIRMED.
P_SOURCEORDERED_KERNEL_ENVELOPE_PORT_1: CONFIRMED.
P_COMPACT_LOG_COMMUTATOR_SOURCE_1: CONFIRMED.
P_GROUND_COFINAL_RATE_1: LIVE.
prior naive-R2 distinctness claim: REFUTED AS STATED.
```

**Memory entry:**

```yaml
iteration:
  target: selected_Ferrers_compact_ground_tracking_source_rate
  status: PROGRESS
  failed_strategy: second_order_W4_and_q_line_Feshbach
  cognitive_operator_used: DUALIZE
  new_gap_name: H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING
  invariant_learned: projective tracking may be sourced either by residual norm or Rayleigh excess, but the compact evaluation growth must be paid before the limit
  forbidden_future_move: do_not_rename_q_line_residual_as_Feshbach_coupling
  next_decisive_test: source_lock_a_consumer_strength_ground_eigenvalue_lower_envelope
```
