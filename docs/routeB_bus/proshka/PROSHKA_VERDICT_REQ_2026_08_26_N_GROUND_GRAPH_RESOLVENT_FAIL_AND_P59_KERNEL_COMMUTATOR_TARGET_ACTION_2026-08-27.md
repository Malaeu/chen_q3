# STATUS: OPEN — GROUND-GRAPH SOURCE FAIL RATIFIED; REPRESENTATION SURVIVES; P59 KERNEL–COMMUTATOR TARGET-ACTION PREFLIGHT SELECTED

```yaml
PRIMARY: RATIFY_GROUND_GRAPH_SOURCE_FAIL_AND_SELECT_P59_KERNEL_COMMUTATOR_TARGET_ACTION
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
  REPORT_COMMIT: f0a3132e4d41c2670eb8e71188902f1e49a69b43
  REPORT_PARENT: 4a576dd53258289bbe09b24b89195048cfc52443
  REPORT_PATH: docs/routeB_bus/LINUX_GROUND_GRAPH_RESOLVENT_TRANSFORM_PREFLIGHT_GOAL058_2026-08-27.md
  REPORT_GIT_BLOB: 170d1a1da063096418ee791f7d2efefe4f3512b4
  REPORT_LINES: 123
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
  failure_code_confirmed: GOAL058_GROUND_GRAPH_RESOLVENT_FUNCTIONAL_SOURCE_NOT_AVAILABLE
  representation_killed: false
  overlap_orientation: PAPER_PASS
  overlap_nonzero_supplier: LEAN_EXISTING
  graph_operator_positive_definite: PAPER_PASS
  graph_coefficient_identity: PAPER_PASS
  graph_normalized_transform_identity: PAPER_PASS
  graph_normalized_real_zero_transfer: PAPER_PASS
  cofinal_compact_rate_in_current_corpus: ABSENT
  exact_remaining_source_object: TARGET_ACTION_RESOLVENT_PAIRING
  report_suggested_target_tail_file_as_direct_supplier: REJECTED_WRONG_CATEGORY
  Lean_source_authorized_now: false

GROUND_GRAPH_OBJECT:
  selected_matrix: K_k
  selected_trial: q_k
  selected_Rayleigh: a_k
  selected_residual: r_k = (K_k - a_k I) q_k
  selected_ground: K_k xi_k = epsilon_k xi_k
  trial_coordinate: d_k = inner(q_k, xi_k)
  trial_projection: P_k = q_k q_k_star
  trial_complement: Q_k = I - P_k
  graph_operator: C_k = Q_k (K_k - epsilon_k I) Q_k + P_k
  graph_floor: min(1, beta)
  exact_coefficient_identity: d_k_inverse xi_k - q_k = - C_k_inverse r_k
  exact_transform_identity: >-
    graphGround_k(z) - centeredPstar_k(z)
    = - centerFactor_k * T_k(C_k_inverse r_k)(z)

MANDATORY_ORIENTATION_REPAIR:
  status: REQUIRED
  exact_kernel_vector: >-
    define kappa_k(z) with the conjugated scaled pole-kernel entries so that
    T_k(w)(z) = inner(kappa_k(z), w) in the project's conjugate-first convention
  forbidden_shorthand: h_k(z)_is_the_vector_of_pole_kernel_values_without_conjugation_or_scale
  lattice_guard: >-
    the diagonal-resolvent formula is first an off-lattice identity; included
    removable poles must be handled separately and then glued by the exact
    entire pole-kernel theorem

TARGET_ACTION_GAP:
  name: SELECTED_FERRERS_GROUND_GRAPH_TARGET_ACTION_COMPACT_RATE
  scalar: >-
    Psi_k(z) = inner(
      C_k_inverse kappa_k(z),
      P_Nk (R_k - a_k I) gE_k)
  target_vector: gE_k = selectedFerrersFactorFourTargetProjection P k
  required_conclusion: >-
    for every compact K in the open centered strip,
    sup_{z in K} norm(centerFactor_k * Psi_k(z)) tends to zero

ERROR_CHANNEL_BOUNDARY:
  object: >-
    inner(C_k_inverse kappa_k(z), P_Nk (R_k - a_k I) eE_k)
  status: CONDITIONAL_ASSEMBLY_NOT_A_NEW_PRIMARY_SOURCE_WALL
  note: >-
    the E-star error has Hilbert/window rates, but those rates are not themselves
    a finite-Riesz action theorem. They become spendable only after action is
    moved to the exact kernel/resolvent vector and the resulting compact envelope
    is proved. Do not relabel the existing L2 rate as action decay.

SELECTED_REPRESENTATION:
  name: P59_KERNEL_COMMUTATOR_TARGET_ACTION
  mechanism: >-
    express the off-lattice Proposition-59 Riesz kernel as a diagonal-mode
    resolvent, move the full source action to that kernel, and use the exact
    rank-two commutator of the complete CCM source matrix to reduce the target
    action to finitely many source moments plus explicit removable-pole and
    window/projection defects
  preserves_combined_prime_cancellation: true
  component_split_forbidden: true

CLOSES:
  - GROUND_GRAPH_OVERLAP_ORIENTATION_AMBIGUITY
  - GROUND_GRAPH_OPERATOR_POSITIVITY_PAPER
  - GROUND_GRAPH_COEFFICIENT_IDENTITY_PAPER
  - GROUND_GRAPH_TRANSFORM_ERROR_IDENTITY_PAPER
  - PENALTY_SLACK_AS_REQUIRED_TRACKING_SOURCE
  - GLOBAL_SELF_ENERGY_AS_REQUIRED_TRACKING_SOURCE

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_GRAPH_TARGET_ACTION_COMPACT_RATE
  - SELECTED_FERRERS_GROUND_GRAPH_ERROR_CHANNEL_COMPACT_ASSEMBLY
  - SELECTED_FERRERS_GROUND_COFINAL_CONVERGENCE_ASSEMBLY
  - EXACT_COMBINED_GAMMA_RETAINED_PRIME_RATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - REPRESENTATION_PROGRESS
  - FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: DUALIZE
ROUTE_SCORE: 5

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  DISCRIMINATOR:
    PASS: SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_SOURCE_READY
    FAIL: GOAL058_P59_KERNEL_COMMUTATOR_LEAVES_FULL_SOURCE_ACTION_OR_PRIME_OSCILLATION_WALL
  SUCCESS_CODE: SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_LEAN_READY
  FAILURE_CODE: GOAL058_P59_KERNEL_COMMUTATOR_LEAVES_FULL_SOURCE_ACTION_OR_PRIME_OSCILLATION_WALL

NEXT_AFTER_SOURCE_PREFLIGHT_PASS_ONLY:
  TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_ASSEMBLY
  REQUIRED_CONCLUSION: >-
    one exact graph-normalized tracked-ground family has real zeros and differs
    locally uniformly from the selected trial family by a term tending to zero
    on the already precommitted common cofinal tail

CANDIDATE_REPRESENTATIONS:
  R1_P59_KERNEL_COMMUTATOR_TARGET_ACTION:
    rank: PRIMARY
    target: >-
      an exact finite-rank formula and compact rate for the scalar pairing of
      the full source action on gE_k against the graph-resolvent-smoothed P59 kernel
    kill_power: 10/10
    proof_cost: 5/10
    route_fit: 10/10
  R2_FULL_SOURCE_RADICAL_PLUS_WINDOW_DEFECT:
    rank: RUNNER_UP
    target: >-
      prove exact full-source radical membership of the unwindowed factor-four
      target and then carry every window, projection, seam and finite-carrier defect
    kill_power: 10/10
    proof_cost: 8/10
    route_fit: 7/10
  R3_EXACT_COMBINED_GAMMA_RETAINED_PRIME:
    rank: LAST_RESORT
    target: >-
      cancellation-preserving source estimate on Gamma_k = D_k r_k including
      retained-prime action and W02 endpoint trace
    kill_power: 10/10
    proof_cost: 10/10
    route_fit: 9/10

REGISTERED_PREDICTIONS:
  P_GROUND_GRAPH_IDENTITY_1:
    prior_probability: 0.98
    fate: CONFIRMED
  P_GROUND_GRAPH_SOURCE_1:
    prior_probability: 0.67
    fate: CONFIRMED
  P_MODE_GRADED_EVEN_FLOOR_1:
    prior_probability: 0.38
    fate: NOT_TESTED
  P_GROUND_COFINAL_RATE_1:
    prior_probability: 0.76
    fate: LIVE_NOT_YET_TESTED
  P_P59_KERNEL_COMMUTATOR_1:
    probability: 0.81
    prediction: >-
      off the finite pole lattice, the exact P59 kernel is a diagonal-mode
      resolvent vector and the full CCM rank-two commutator reduces its source
      action to finitely many scalar moments without splitting Arch, W02 and Prime
  P_TARGET_MOMENT_SOURCE_1:
    probability: 0.60
    prediction: >-
      the reduction leaves at most one genuinely new target moment or window
      defect; if it leaves an unrestricted full-source pairing, R1 fails and the
      route returns to the radical/window-defect or combined-Gamma alternatives

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
| Report source lock | The report commit is the direct child of the prior verdict, adds only the 123-line read-only report, and was `rh_clean` HEAD at audit. | `[ABSTRACT][PAPER]` |
| Overlap orientation | The existing overlap is \(\langle\xi,q\rangle\); the graph coordinate is \(d=\langle q,\xi\rangle=\overline{\langle\xi,q\rangle}\). Nonvanishing is equivalent. | `[FINITE_CELL][PAPER]` |
| Overlap nonvanishing | `selectedCCMGroundOverlap_ne_zero_of_ratio_lt_one` already supplies it under the strict ratio guard. | `[FINITE_CELL][LEAN]` |
| Graph operator | \(C=Q(K-\epsilon I)Q+P\) has floor \(\min(1,\beta)>0\), hence is invertible. | `[FINITE_CELL][PAPER]` |
| Coefficient graph identity | \(d^{-1}\xi-q=-C^{-1}r\) follows exactly from the projected ground equation and residual orthogonality. | `[FINITE_CELL][PAPER]` |
| Transform identity | The graph-normalized ground transform differs from the selected trial transform by the exact source-ordered P59 transform of \(-C^{-1}r\). | `[FINITE_CELL][PAPER]` |
| Current source rate | No theorem in the current corpus proves compact decay of this exact resolvent-weighted P59 functional. | `[COFINAL_FAMILY][PAPER]` |
| Representation | The representation is strictly weaker than self-energy or global residual control and therefore survives. | `[ABSTRACT][PAPER]` |

## 1. Source lock and the surviving FAIL

The discriminator result is ratified:

```text
GOAL058_GROUND_GRAPH_RESOLVENT_FUNCTIONAL_SOURCE_NOT_AVAILABLE.
```

The report closed every finite-dimensional graph identity requested by the parent verdict, but it found no cofinal source theorem for

\[
\frac{\Xi(0)}{\operatorname{rawFplus}_k(0)}
T_k(C_k^{-1}r_k).
\]

Failure of that source search does not kill the representation. The scalar functional can vanish because of the orientation of the kernel against the residual even when \(\|r_k\|\), \(\langle r_k,C_k^{-1}r_k\rangle\), or \(\|D_kr_k\|\) do not vanish. `[COFINAL_FAMILY][PAPER]`

## 2. Finite graph layer: admitted on paper

Let \(q\) be the literal selected unit trial, \(a=\langle q,Kq\rangle\), \(r=(K-aI)q\), and let \(\xi\) be the exact unit bottom ground at eigenvalue \(\epsilon\). Put

\[
P=qq^*,\qquad Q=I-P,
\qquad C=Q(K-\epsilon I)Q+P.
\]

The literal complement-floor theorem at shift \(a\) gives

\[
\langle w,(K-aI)w\rangle\ge\beta\|w\|^2
\qquad(w\perp q).
\]

Since \(\epsilon\le a\),

\[
\langle w,(K-\epsilon I)w\rangle
\ge\beta\|w\|^2.
\]

Thus \(C\) is the identity on the trial line and has floor \(\beta\) on its complement. It is Hermitian positive definite with floor \(\min(1,\beta)\). `[FINITE_CELL][PAPER]`

Set

\[
d=\langle q,\xi\rangle,\qquad \xi=dq+w,\quad w\perp q.
\]

The strict residual/floor ratio gives \(d\neq0\). Projecting \((K-\epsilon I)\xi=0\) to \(q^\perp\), and using \(Q(K-\epsilon I)q=Qr=r\), gives

\[
Cw=-dr.
\]

Therefore

\[
\boxed{d^{-1}\xi-q=-C^{-1}r.}
\]

The graph-normalized ground function is obtained from the already tracked ground function by a nonzero scalar. Hence it has the same real zero set. Linearity of the exact source-ordered Proposition-59 transform gives

\[
\boxed{
G_k^{\rm graph}(z)-P_k^{\rm trial}(z)
=-\frac{\Xi(0)}{\operatorname{rawFplus}_k(0)}
T_k(C_k^{-1}r_k)(z).
}
\]

No second ground witness, inverse-overlap majorant, penalty parameter, self-energy, or raw residual norm enters this identity. `[FINITE_CELL][PAPER]`

## 3. Mandatory kernel-orientation repair

The report's phrase “the vector of pole-kernel values” is insufficient for a Lean-facing identity.

The project inner product is conjugate-linear in the first argument, while

\[
T_k(w)(z)
=rac1{\sqrt{L_k}}
\sum_j w_j\,K_{k,j}(z)
\]

is linear in \(w\). Therefore the exact Riesz vector must contain the conjugated scaled kernel entries. The next preflight must define \(\kappa_k(z)\) so that

\[
T_k(w)(z)=\langle\kappa_k(z),w\rangle
\]

literally, with the source-order label, the production argument reflection, the \(L_k^{-1/2}\) factor and all conjugations visible. `[FINITE_CELL][PAPER]`

A second boundary is equally load-bearing. Away from the finite P59 pole lattice, \(\kappa_k(z)\) is a diagonal-mode resolvent vector. At an included pole the displayed Cauchy denominator is not legal; the entire `proposition59PoleKernel` uses a removable value. Thus any commutator computation must be proved off lattice and then extended through the included poles by the exact removable-pole theorem or by an entire-function identity. A compact may cross those points. Ignoring them is a domain hole. `[FINITE_CELL][PAPER]`

## 4. Strongest attack on the report's proposed next probe

The file

```text
G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
```

proves a support-category theorem: it splits the full E-star error into a main window error and the noncompact target tail, and bounds that tail in the window Hilbert norm. It does **not** compute

\[
P_N(R-aI)gE
\]

and does not connect a Hilbert tail bound to finite source-Riesz action. Treating it as the direct target-action supplier would repeat the exact C04/C10 error already killed for the L73 error channel. `[COFINAL_FAMILY][PAPER]` **[C04][C10]**

The older full-source dual/radical audit also established that the repository contains no theorem placing the unwindowed factor-four target in the radical of the full source Weil form. Its projection plant proves that even a genuine global radical vector need not remain radical after projection. Therefore the next transaction must not repeat a broad search for “target is radical” and must not infer radicality from Fourier invariance, Mellin identification or inversion symmetry. `[ABSTRACT][PAPER]` **[C04][C13]**

## 5. Why the P59 kernel–commutator representation is selected

The full finite source matrix has the exact structured law

\[
(n_j-n_\ell)M_{j\ell}=\beta_j-\beta_\ell,
\]

which is the rank-two commutator identity

\[
DM-MD=\beta\,\mathbf1^*-\mathbf1\,\beta^*.
\]

This theorem is proved for the complete source matrix, including W02, Arch and Prime. It therefore preserves the cancellation that every component-majorant route loses. `[FINITE_CELL][LEAN]`

Away from the P59 pole lattice, the Riesz kernel has Cauchy form and should satisfy an exact diagonal-resolvent equation of the shape

\[
(D-\zeta_k(z)I)\kappa_k(z)=c_k(z)\mathbf1,
\]

with signs and constants determined from the production mode labels and argument reflection. Moving \(M-aI\) from the target vector to this kernel and applying the rank-two commutator can reduce the target-action scalar to finitely many moments against \(\mathbf1\), \(\beta\), and any remaining explicit row such as \(M\mathbf1\). This is the cheapest representation that attacks the exact consumer functional rather than a global norm. `[FINITE_CELL][CONDITIONAL]`

A PASS requires more than writing that formal identity. Every resulting moment must already have a source theorem or receive a new explicit compact-rate estimate. If one unrestricted full-source pairing remains, the representation has not reduced the wall and must return FAIL without further algebraic wrappers.

## 6. Status of the error channel

The Riesz split also produces

\[
\left\langle C_k^{-1}\kappa_k(z),
P_{N_k}(R_k-a_kI)eE_k\right\rangle.
\]

The E-star error has source-locked pointwise and Hilbert/window rates. Those rates are not, by themselves, action decay. The selected kernel–commutator preflight must move the action to the exact kernel/resolvent vector and derive a compact envelope. If that envelope times the existing error rate tends to zero, the error channel is assembly. If not, it becomes a second source wall and the preflight must say so. `[COFINAL_FAMILY][PAPER]`

Thus the report is correct that the target-action channel is the only newly named analytic object. It is not correct to treat the error channel as already proved merely because `eE_k` is small in `H_m`.

## 7. CODEX / Linux directive

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

NO:
  Lean edits;
  numerical probes;
  Aristotle;
  componentwise W02/Arch/Prime norm split;
  raw residual or self-energy substitution;
  post-hoc schedule or second tail;
  global-radical inference from Mellin/Fourier labels.

READ_FIRST:
  docs/routeB_bus/LINUX_GROUND_GRAPH_RESOLVENT_TRANSFORM_PREFLIGHT_GOAL058_2026-08-27.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
  docs/routeB_bus/H2A_4_1B_3C_1_5_SELECTED_FERRERS_FULL_SOURCE_DUAL_RADICAL_PREFLIGHT_2026-08-23.md

REQUIRED OUTPUT:
  1. Exact definition of the P59 Riesz kernel vector kappa_k(z), including
     conjugation, source ordering, -z orientation and L_k^(-1/2).
  2. Exact identity T_k(w)(z) = inner(kappa_k(z), w).
  3. Exact off-lattice diagonal-resolvent equation for kappa_k(z), with the
     dimensionless spectral parameter written explicitly.
  4. Exact full-matrix commutator equation in the same complex carrier.
  5. Exact formula for (M_k-a_k I) kappa_k(z), without component splitting.
  6. Exact reduction of the target-action pairing to a finite list of target
     moments and explicit window/projection/removable-pole defects.
  7. Shelf and source audit for every resulting moment. No anonymous C(z).
  8. Separate treatment of included lattice poles and proof that the compact
     statement survives compacts crossing them.
  9. Full center-factor and cofinal-rate ledger on the existing common tail.
 10. The corresponding error-channel compact envelope using the same kernel.
 11. Exactly one discriminator result:

     PASS:
       SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_SOURCE_READY

     FAIL:
       GOAL058_P59_KERNEL_COMMUTATOR_LEAVES_FULL_SOURCE_ACTION_OR_PRIME_OSCILLATION_WALL

PASS BOUNDARY:
  The target action is an exact finite-rank/moment expression and every term
  has a source-derived compact rate strong enough for the final consumer.

FAIL BOUNDARY:
  An unrestricted full-source pairing, uncontrolled M_k*1 moment, retained-prime
  oscillation, or equivalent raw residual/source-action term survives.
```

Lean is not authorized by this verdict. The graph identities should be formalized only after this preflight selects an exact source contract, so one node can close the graph identity and its load-bearing target-action supplier together rather than add another bridge with no source progress.

## STRONGEST ATTACK

The strongest objection to R1 is that the P59 Cauchy kernel may convert the commutator into a formula containing

\[
M_k\mathbf1
\]

or another target moment for which no source rate exists. Then the apparent finite-rank reduction merely relocates the full source-action wall. The pass criterion forbids hiding that term behind a fitted bound, an unnamed operator norm, or a component split.

The second objection is the removable-pole lattice. An off-lattice formula is not a compact theorem. If the extension across included poles creates growing derivative values or loses uniformity, R1 fails at the actual consumer topology even though the meromorphic algebra is correct.

If either attack lands, the repaired route is R2: exact global radical plus explicit window/projection defect. If no exact radical theorem can be acquired, the route returns to R3, the combined-\(\Gamma\) retained-prime wall.

## FINAL PROPOSAL

Keep the ground-graph representation. It has compressed the convergence problem from a global coefficient norm to the exact analytic functional consumed by the roof.

Do not write the finite graph theorem yet. Do not re-run the penalty-slack, Rayleigh-excess, mode-graded-floor or raw-\(\Gamma\) routes.

Run one source-only algebraic preflight on the **P59 kernel against the full CCM commutator**. Its purpose is binary:

```text
finite-rank target moments with adequate rates
versus
full source action / retained-prime wall in disguise.
```

This test has the best kill-power per cost and preserves every source-locked object, normalization, carrier, schedule and cancellation.

## META CLOSEOUT

**What became smaller?**

```text
ground-to-trial compact convergence
→ exact graph transform of C_k^(-1) r_k
→ one target-action resolvent pairing
→ candidate finite-rank P59-kernel commutator formula.
```

**What was killed?**

```text
penalty slack as a required tracking scalar;
global self-energy as a required consumer;
raw residual norm as the only tracking representation;
target E-star tail bound as a finite-Riesz action theorem;
Mellin/Fourier invariance as a radical certificate.
```

**What must not be tried again?**

```text
L2-small ⇒ source-action-small;
componentwise W02/Arch/Prime majorants relabeled as the combined consumer;
global radical silently preserved by projection;
off-lattice P59 algebra presented as a compact theorem;
formalizing another bridge before identifying the source rate.
```

**Current smallest named gap:**

```text
SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_COMPACT_RATE
```

**Next cheapest decisive test:**

Derive the exact off-lattice P59 diagonal-resolvent identity, apply the full source commutator, and inventory every surviving target moment before any estimate or Lean edit.

**Prediction fates:**

```text
P_GROUND_GRAPH_IDENTITY_1: CONFIRMED.
P_GROUND_GRAPH_SOURCE_1: CONFIRMED.
P_MODE_GRADED_EVEN_FLOOR_1: NOT TESTED.
P_GROUND_COFINAL_RATE_1: LIVE.
```

**Memory entry:**

```yaml
iteration:
  target: SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_COMPACT_DECAY
  status: OPEN
  failed_strategy: READY_MADE_SOURCE_RATE_SEARCH
  cognitive_operator_used: DUALIZE
  new_gap_name: SELECTED_FERRERS_P59_KERNEL_COMMUTATOR_TARGET_ACTION_COMPACT_RATE
  invariant_learned: >-
    preserve the complete source matrix and move action to the exact P59 Riesz
    kernel before estimating; the target E-star tail and the finite Riesz action
    live in different categories
  forbidden_future_move: >-
    do not infer finite source-action decay from Hilbert tail decay or from
    Fourier/Mellin labels
  next_decisive_test: >-
    exact P59 diagonal-resolvent plus full CCM rank-two commutator reduction
```
