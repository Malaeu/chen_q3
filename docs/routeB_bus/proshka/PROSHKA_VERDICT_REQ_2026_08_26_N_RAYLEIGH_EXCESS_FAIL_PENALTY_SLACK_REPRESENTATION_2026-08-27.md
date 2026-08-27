# STATUS: OPEN — LOWER-ENVELOPE FAIL RATIFIED; TEMPLE “RATE-EQUIVALENCE” KILLED; PENALTY-SLACK SELF-ENERGY SELECTED

```yaml
PRIMARY: RATIFY_LOWER_ENVELOPE_FAIL_AND_SELECT_PENALTY_SLACK_SELF_ENERGY
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
  REPORT_COMMIT: d78a18ea5bd13c47db643a98d0673c21e086ff1b
  REPORT_PARENT: 809b776bd628c39a5e99dc54e9720a4e7a4bd0a0
  REPORT_PATH: docs/routeB_bus/LINUX_RAYLEIGH_EXCESS_COMPACT_RATE_PREFLIGHT_GOAL058_2026-08-27.md
  REPORT_GIT_BLOB: 5e098eca13ff35e771aad26c90492d52b2af9e67
  REPORT_LINES: 136
  REPORT_ONLY_COMMIT: true
  HEAD_IS_REPORT_COMMIT_AT_AUDIT: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_PROBE_PERFORMED: false
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_MATRIX_NUMERICS: false
  JUDGE_DERIVED_SCALAR_ARITHMETIC_FROM_EXISTING_INTERVAL_DATA: true

ADJUDICATION:
  discriminator_fail_confirmed: true
  failure_code_confirmed: GOAL058_RAYLEIGH_EXCESS_LOWER_ENVELOPE_SOURCE_NOT_AVAILABLE
  generic_Rayleigh_projective_port: PAPER_READY
  same_tail_object_lock: PASS
  Temple_small_residual_implies_small_excess: true
  Temple_small_excess_implies_small_residual: false
  report_rate_equivalence_claim: REFUTED
  Rayleigh_excess_representation_killed: false
  report_REP_A_broad_fixed_block_Schur_selected: false
  report_REP_B_combined_Gamma_selected: false
  selected_representation: PENALTY_SLACK_FESHBACH_SELF_ENERGY
  Lean_source_authorized_now: false

PENALTY_SLACK_REPRESENTATION:
  certificate: "K_k - b_k I + tau_k q_k q_k* >= 0"
  rayleigh: "a_k = <q_k,K_k q_k>"
  certified_gap: "g_k = b_k - a_k > 0"
  slack: "s_k = tau_k - g_k"
  exact_lower_envelope: "epsilon_k >= a_k - s_k"
  exact_projective_bound: "1 - |<xi_k,q_k>|^2 <= s_k/g_k"
  compact_consumer_rate: >-
    for every fixed 0 <= sigma < 1/2,
    lambda_k^(2*sigma) * L_k * s_k/g_k tends to zero
  Schur_identity_when_complement_is_strict: >-
    inf_tau s_k = r_k^*(B_k-b_k I)^(-1) r_k
    in the decomposition C q_k plus q_k-perp

EXISTING_FINITE_DIAGNOSTIC:
  script: docs/routeB_bus/phase2_scripts/ccm_beta_n_profile.py
  data: docs/routeB_bus/phase2_results/ccm_fixed_q_beta_n_profile.json
  fixed_parameters:
    m: 13
    q: exact_zero_padding_from_E_120
    N_ladder: [120, 160, 200, 240]
  exact_script_identity: "tau_required = beta_cert - a + schur_term"
  derived_slack_midpoints:
    N120: approximately_1.2361351493e-59
    N160: approximately_1.5966206887e-59
    N200: approximately_1.8659817648e-59
    N240: approximately_1.9012540078e-59
  scope: FINITE_CELL
  verifier: ARB_INTERVAL
  proof_role: DIAGNOSTIC_NOT_COFINAL_SUPPLIER

CLOSES:
  - TEMPLE_RATE_EQUIVALENCE_OVERCLAIM
  - PENALTY_SLACK_LOWER_ENVELOPE_IDENTITY_PAPER
  - Q_LINE_SCHUR_SELF_ENERGY_DISTINGUISHED_FROM_RAW_RESIDUAL_NORM
  - EXISTING_TAU_REQUIRED_FINITE_DIAGNOSTIC_LOCATED
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_PENALTY_CERTIFICATE
  - SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE
  - SELECTED_FERRERS_GROUND_COFINAL_CONVERGENCE_ASSEMBLY
  - EXACT_COMBINED_GAMMA_RETAINED_PRIME_RATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  DISCRIMINATOR:
    PASS: SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE_SOURCE_READY
    FAIL: PENALTY_SLACK_SELF_ENERGY_SOURCE_RATE_NOT_AVAILABLE
  REQUIRED_OUTPUT:
    - exact penalty-slack lower-envelope theorem and generalized-G version
    - exact selected-family b_k, tau_k, g_k and s_k objects on one schedule
    - exact Schur/Feshbach identity for minimal slack
    - compact threshold lambda^(2sigma)*L*s/g for every sigma < 1/2
    - audit of the existing fixed-m tau_required instrument without promoting it
    - audit whether existing even-tail, sector-floor, Sturm, W5, or source-action facts bound the self-energy rather than the raw residual
    - one source-defined cancellation-preserving supplier route if PASS
    - two repaired representations with kill-power/cost if FAIL
  SUCCESS_CODE: SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE_LEAN_READY
  FAILURE_CODE: GOAL058_PENALTY_SLACK_SELF_ENERGY_SOURCE_RATE_NOT_AVAILABLE

NEXT_AFTER_SOURCE_PREFLIGHT_PASS_ONLY:
  TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
  REQUIRED_CONCLUSION: >-
    one exact reindexed tracked-ground family has real zeros and tends locally
    uniformly to centeredXi on every compact of the open centered strip

CANDIDATE_REPRESENTATIONS:
  R1_PENALTY_SLACK_FESHBACH_SELF_ENERGY:
    rank: PRIMARY
    target: >-
      construct cofinal rank-one penalty certificates with
      lambda^(2sigma)*L*(tau-(b-a))/(b-a) -> 0
    kill_power: 10/10
    proof_cost: 8/10
    route_fit: 10/10
  R2_EXACT_COMBINED_GAMMA_RETAINED_PRIME:
    rank: RUNNER_UP
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
    fate: CONFIRMED_AS_OPEN_SOURCE_GAP_NOT_AS_RESIDUAL_EQUIVALENCE
  P_GROUND_COFINAL_RATE_1:
    prior_probability: 0.76
    fate: LIVE_NOT_YET_TESTED
  P_PENALTY_SLACK_IDENTITY_1:
    probability: 0.99
    prediction: >-
      the generic penalty certificate yields epsilon >= a-s and projective
      defect <= s/g with no new analytic hypothesis
  P_PENALTY_SLACK_SOURCE_1:
    probability: 0.74
    prediction: >-
      no cofinal slack-rate theorem is currently in the corpus, but the source
      gap compresses to one even-sector resolvent self-energy rather than the
      full raw residual or differentiated Gamma

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

### 1. Source lock and the part of the FAIL that survives

The report commit is the direct child of the prior Proshka verdict and adds only the 136-line read-only report. No Lean or numerical source changed. `[ABSTRACT][PAPER]`

The discriminator result survives:

```text
GOAL058_RAYLEIGH_EXCESS_LOWER_ENVELOPE_SOURCE_NOT_AVAILABLE.
```

The current theorem catalog does not contain a cofinal source theorem proving

\[
\epsilon_k\ge a_k-\delta_k
\]

at the compact-consumer rate. The generic weighted-Rayleigh/projective-defect port is ready, but its source scalar remains open. `[COFINAL_FAMILY][PAPER]`

The exact same-family lock also survives: `epsilon_k`, `a_k`, the finite source matrix and the selected schedule refer to one literal family. `[COFINAL_FAMILY][LEAN]`

### 2. Fatal correction: Temple does not make excess and residual rate-equivalent

The report uses

\[
\alpha(\mathrm{gap}-\alpha)\le \eta^2
\]

and calls this a two-sided rate comparison between Rayleigh excess `alpha` and residual variance `eta^2`. That direction is wrong for the claimed conclusion. It is a **lower bound on residual variance**, not an upper bound obtained from excess.

A planted family kills the equivalence. For `M >= 2`, take spectral levels

\[
(0,1,M)
\]

with ground index at level zero and probability weights

\[
(1-M^{-2},0,M^{-2}).
\]

The true complementary gap is exactly `1`, while

\[
\alpha=M^{-1}\to0,
\qquad
\eta^2=1-M^{-2}\to1.
\]

Thus small Rayleigh excess does **not** force a small raw residual, even under a fixed positive gap. `[ABSTRACT][PAPER]` **[C07][C10]**

The valid one-way statement is:

```text
small residual + controlled gap -> small excess.
```

The reverse requires an independent upper spectral-moment envelope and is absent here. Therefore the Rayleigh-excess dual remains a genuinely weaker consumer and is not returned automatically to the killed `E_k` wall. `[ABSTRACT][PAPER]`

### 3. The exact smaller object is penalty slack

Let `K` be Hermitian, `q` a unit vector, and

\[
a=\langle q,Kq\rangle.
\]

Assume a rank-one penalty certificate

\[
K-bI+\tau qq^*\succeq0,
\qquad b>a.
\]

Define

\[
g=b-a>0,
\qquad
s=\tau-g.
\]

First, testing the certificate on `q` gives

\[
s=a-b+\tau\ge0.
\]

Second, for every unit `x`,

\[
\langle x,Kx\rangle
\ge b-\tau|\langle q,x\rangle|^2
\ge b-\tau
=a-s.
\]

Hence the true bottom eigenvalue obeys

\[
\boxed{\epsilon\ge a-s.}
\]

The existing penalty theorem independently supplies a simple even ground and a true gap at least

\[
\boxed{g=b-a.}
\]

Combining this lower envelope with the weighted projective-defect core gives

\[
\boxed{
1-|\langle\xi,q\rangle|^2
\le \frac{a-\epsilon}{g}
\le \frac{s}{g}.
}
\]

After the already paper-ready centering and Proposition-59 compact envelope, the exact source target becomes

\[
\boxed{
\lambda_k^{2\sigma}L_k\frac{s_k}{g_k}\to0,
\qquad 0\le\sigma<\frac12.
}
\]

This one certificate can also provide the complement floor and the odd-sector floor, because every vector orthogonal to the even probe `q` sees `K-aI >= gI`. It therefore has better `CLOSES/OPENS` economics than a standalone lower-envelope theorem. `[ABSTRACT][PAPER]`

### 4. Why this is a genuine Feshbach representation, not the killed raw coupling rename

In the decomposition

\[
\mathbb Cq\oplus q^\perp,
\qquad
K=\begin{pmatrix}a&r^*\\r&B\end{pmatrix},
\]

the off-diagonal vector is indeed the raw residual `r`. The previous kill remains correct if one merely estimates the coupling by `||r||`.

But for `B-bI > 0`, the Schur complement says the smallest admissible penalty is

\[
\tau_{\min}
=g+r^*(B-bI)^{-1}r.
\]

Therefore the minimal slack is

\[
\boxed{
s_{\min}=r^*(B-bI)^{-1}r.
}
\]

This is a **resolvent-smoothed self-energy**, not the raw residual norm. High complement modes are suppressed by the inverse operator. It can tend to zero while `||r||` does not. Calling these two functionals equivalent would repeat the same C04/C10 error in a different direction. `[ABSTRACT][PAPER]` **[C04][C10]**

Broad fixed-block Schur is therefore not selected as the theorem target. It remains one possible supplier mechanism for this exact scalar self-energy.

### 5. The repository already contains a finite instrument for the selected scalar

The precommitted Phase-2 script at fixed `m = 13` rotates the exact probe to the first coordinate, forms the `q^perp` compression, and computes

```text
tau_required = beta_cert - a + schur_term.
```

Thus its stored `schur_term` is exactly the finite penalty slack. The retained interval profile uses the fixed zero-padded probe over

```text
N = 120, 160, 200, 240.
```

Subtracting the stored certified gap from `tau_required` gives midpoint diagnostics approximately

```text
1.2361e-59, 1.5966e-59, 1.8660e-59, 1.9013e-59.
```

This is valuable evidence that the correct scalar was already instrumented. It is not a cofinal theorem: `m` is fixed, the probe is the Phase-1 fixed vector, and no `m -> infinity` rate is supplied. `[FINITE_CELL][ARB_INTERVAL]`

The original certificate used `tau = 1`, which is sufficient but destroys the lower-envelope information. Future source work must retain the minimal or near-minimal `tau`, not merely exhibit an arbitrary large penalty. `[FINITE_CELL][PAPER]`

### 6. Representation decision

The report's broad REP-A asks for an entire fixed-block positivity architecture before naming the scalar actually consumed. That is stronger than necessary.

The selected primary is:

```text
PENALTY_SLACK_FESHBACH_SELF_ENERGY.
```

Its source theorem may still be supplied by an even-tail/fixed-block Schur certificate, but every estimate must terminate in `s_k`, not in full positivity or `||r_k||`.

The exact combined-`Gamma` retained-prime route remains the runner-up. It is not launched while the cheaper resolvent-smoothed consumer remains untested.

## FINAL PROPOSAL

Do not return the Rayleigh-excess route to the raw residual wall. The report's key equivalence claim is false.

Do not formalize the generic port yet. The source scalar is still missing.

Run one source-only preflight on the exact penalty slack

\[
s_k=\tau_k-(b_k-a_k),
\]

or equivalently on the Schur self-energy

\[
r_k^*(B_k-b_kI)^{-1}r_k.
\]

The decisive question is:

> Can the selected Ferrers source family produce cofinal rank-one penalty certificates whose **slack**, after every compact-growth factor is paid, tends to zero?

A paper-complete positive answer authorizes one Lean assembly that simultaneously supplies simple-even ground, complement/odd floors and projective tracking. A negative answer promotes the exact combined-`Gamma` retained-prime wall.

## STRONGEST ATTACK

The strongest objection is still valid:

> The self-energy contains the prime action and may have no consumer-strength source rate.

The existing `m=13` profile does not answer this. Its slack does not decay along the fixed-`m` `N`-ladder, and that ladder is not the selected cofinal schedule. The next preflight must preserve the combined prime cancellation and must not infer a cofinal rate from these four finite cells. `[COFINAL_FAMILY][PAPER]`

A second attack is post-hoc optimization. Choosing `b_k`, `tau_k`, the retained block or the probe after inspecting each matrix can produce unrelated finite witnesses. The selected schedule, probe family and certificate parametrization must be source-defined before rate tests. **[C09]**

## CODEX DIRECTIVE

```text
NO LEAN SOURCE TRANSACTION AUTHORIZED.
NO NEW NUMERICAL PROBE AUTHORIZED.

Run only:
  GOAL058_SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE_PREFLIGHT

Mode:
  PAPER_AND_SOURCE_READ_ONLY

Read first:
  q3.lean.aristotle/Q3/Proofs/RouteB/H2aPenaltyCoercivity.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/WeightedRayleighProjectiveDefect.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
  docs/routeB_bus/phase2_scripts/ccm_beta_n_profile.py
  docs/routeB_bus/phase2_results/ccm_fixed_q_beta_n_profile.json

Required:
  1. Ask the shelf for penalty slack, tau_required, rank-one penalty,
     Schur self-energy and resolvent-smoothed residual before naming a supplier.
  2. Prove on paper the exact penalty-slack lower envelope, including the
     generalized-Gram version used by H2aPenalty.
  3. Give the exact selected-family definitions of b_k, tau_k, g_k and s_k,
     or report which one is not source-defined.
  4. Derive the Schur identity for minimal slack in the literal q/q-perp carrier.
  5. Pay the full compact threshold lambda^(2sigma)*L*s/g.
  6. Audit whether current sector-floor, even-tail, Sturm, W5 or source-action
     facts control the self-energy without replacing it by ||r||^2.
  7. Treat the fixed-m Phase-2 profile only as a calibration/falsifier.

Forbidden:
  - claim Temple gives residual/excess rate equivalence;
  - replace Schur self-energy by raw residual norm;
  - use tau=1 when a near-minimal penalty is the consumer;
  - choose a new probe, block or schedule post hoc;
  - split retained-prime terms entrywise before cancellation;
  - use finite interval data in the cofinal quantifier;
  - edit Lean;
  - run new numerics;
  - claim ground-family convergence, route promotion or RH.

Return exactly one:
  SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE_SOURCE_READY
  GOAL058_PENALTY_SLACK_SELF_ENERGY_SOURCE_RATE_NOT_AVAILABLE
```

## META CLOSEOUT

**What became smaller?**

The lower-envelope wall is no longer an arbitrary PSD theorem. It is one scalar:

\[
\boxed{s_k=\tau_k-(b_k-a_k)=r_k^*(B_k-b_kI)^{-1}r_k.}
\]

**What was killed?**

```text
Temple excess/residual rate equivalence;
broad fixed-block positivity as the immediate theorem target;
raw q-line coupling norm as the only Feshbach functional.
```

**What must not be tried again?**

Do not use the reverse Temple inequality as an upper residual estimate. Do not discard the inverse complement operator. Do not certify with an arbitrary large `tau` and then claim a sharp lower envelope.

**Current smallest named gap:**

```text
SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE.
```

**Next cheapest decisive test:**

Source-lock `s_k` on the selected Ferrers schedule and determine whether its compact-weighted rate follows from an existing cancellation-preserving supplier.

**Prediction fates:**

```text
P_RAYLEIGH_EXCESS_GENERIC_PORT_1: CONFIRMED.
P_RAYLEIGH_EXCESS_SOURCE_1: CONFIRMED AS AN OPEN SOURCE GAP,
  REFUTED AS A RESIDUAL-EQUIVALENCE CLAIM.
P_GROUND_COFINAL_RATE_1: LIVE.
```

**Memory entry:**

```yaml
iteration:
  target: selected_Ferrers_Rayleigh_excess_source_rate
  status: PROGRESS
  failed_strategy: Temple_equivalence_and_broad_fixed_block_Schur
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SELECTED_FERRERS_PENALTY_SLACK_COMPACT_RATE
  invariant_learned: the compact consumer needs projective spectral mass, and rank-one penalty slack is a resolvent-smoothed self-energy rather than raw residual variance
  forbidden_future_move: do_not_use_reverse_Temple_as_residual_upper_bound_or_drop_the_resolvent
  next_decisive_test: source_lock_and_rate_a_near_minimal_penalty_slack_on_one_precommitted_schedule
```
