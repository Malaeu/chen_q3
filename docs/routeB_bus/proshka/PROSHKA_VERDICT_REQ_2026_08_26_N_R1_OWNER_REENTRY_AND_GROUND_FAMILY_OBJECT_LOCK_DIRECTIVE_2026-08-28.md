# STATUS: OPEN — OWNER R1 REENTRY ACCEPTED; SAME-GROUND-FAMILY OBJECT-LOCK PREFLIGHT AUTHORIZED

```yaml
PRIMARY: ACCEPT_OWNER_R1_AND_AUTHORIZE_GROUND_FAMILY_VITALI_OBJECT_LOCK
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  OWNER_DECISION_COMMIT: 0b01efb175b5dd2e805425d288caf24a0cad00d3
  OWNER_DECISION_PATH: docs/routeB_bus/LINUX_OWNER_RERANK_R1_VITALI_OPENING_AUDIT_GOAL058_2026-08-28.md
  PRIOR_STOP_VERDICT: 9759aa5c7db001a883a6c0fde1ebb98af999da41
  PRIOR_STOP_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_N_CENTRAL_WINDOW_STOP_RULE_AND_OWNER_RERANK_2026-08-28.md
  OWNER_DECISION_WAS_PRECOMMITTED_BEFORE_WORK: true
  LEAN_OR_NUMERICAL_WORK_AFTER_DECISION: false

REENTRY:
  OWNER_AUTHORIZED_ACQUISITION: SATISFIED
  R1_SELECTED: true
  OWNER_REPRESENTATION_RERANK: CLOSED
  EXECUTION_REOPENED_ONLY_FOR_THIS_PREFLIGHT: true

ADJUDICATION:
  GENERIC_MONTEL_APPARATUS: LEAN_BANKED
  GENERIC_NONZERO_ANCHOR_APPARATUS: LEAN_BANKED
  SAME_PARENT_SUBSEQUENCE_REFINEMENT: LEAN_BANKED

  D0PostAnchorMontel_object: SELECTED_TRIAL_CENTERED_PSTAR_FAMILY
  D0CriticalMomentCanonicalCluster_object: SELECTED_TRIAL_CENTERED_PSTAR_FAMILY
  D0CriticalMomentMontelGate_object: SELECTED_TRIAL_CENTERED_PSTAR_FAMILY
  D0AnchorFloor_object: SELECTED_TRIAL_RAWFPLUS_FAMILY

  REAL_ZERO_OBJECT: SELECTED_FERRERS_TRACKED_GROUND_TRANSFORM
  SAME_WITNESS_REAL_ZERO_THEOREM: LEAN_BANKED
  TRIAL_AND_GROUND_ARE_DEFINITIONALLY_THE_SAME_FAMILY: false
  TRIAL_MONTEL_WRAPPER_DIRECTLY_SUPPLIES_R1: false
  TRIAL_CENTRAL_FLOOR_DIRECTLY_SUPPLIES_GROUND_ANCHOR: false
  TRIAL_CRITICAL_MOMENT_RATIO_DIRECTLY_SUPPLIES_GROUND_NORMALITY: false

  OPENING_REPORT_TWO_HYPOTHESES_REMAIN: NOT_RATIFIED_AS_STATED
  reason: >-
    The two named hypotheses are hypotheses for the selected trial family.
    R1 was authorized for the same normalized finite ground transforms that
    carry the real-zero theorem.  A same-object adapter has not been supplied.

R1_EXACT_OBLIGATIONS:
  R1_0_GROUND_FAMILY_OBJECT_LOCK:
    status: OPEN_FIRST_GATE
    requirement: >-
      Fix one literal cofinal family of finite ground transforms, its scalar or
      gauge normalization, its source carrier, sector-floor inputs and selected
      schedule.  The family must be exactly the family carrying ZerosRealOn.

  R1_A_GROUND_FAMILY_LOCAL_NORMALITY:
    status: OPEN
    requirement: >-
      Prove compact-local boundedness on the centered critical strip for the
      post-normalized ground family itself.  The proof may use P59/Cauchy,
      real-zero, Cartwright, Herglotz or de Branges structure, but not the dead
      residual/graph-resolvent tracking rate under another name.

  R1_B_GROUND_FAMILY_NONZERO_TIGHTNESS:
    status: OPEN
    requirement: >-
      Supply a fixed compact-open continuous normalization witness: a fixed
      nonzero point anchor, a fixed finite jet, or another fixed continuous
      functional whose value is nonzero along the whole selected family.
      Eta normalization on a growing coefficient carrier is not automatically
      such a witness.

  R1_C_GROUND_CLUSTER_IDENTIFICATION:
    status: OPEN
    requirement: >-
      Identify every nonzero locally uniform ground-family cluster with
      centeredXi times a nonzero scalar and zero-free gauge, using convergence on
      a source-locked uniqueness set, fixed jets, logarithmic derivatives or a
      weak spectral-measure theorem for the same family.

EXACT_PRIMARY_CANDIDATE:
  family: selectedFerrersTrackedGroundTransform
  why: >-
    It is a named finite ground transform for which the repository already proves
    both the same-witness real-zero theorem and the exact source provenance.
  forbidden_use: >-
    Its banked pointwise tracking estimate may not be used to prove R1_A or R1_C;
    that would reopen the rate corridor closed by the stop rule.

FALLBACK_CANDIDATE:
  family: ETA_NORMALIZED_REAL_GROUND_PROPOSITION59_TRANSFORM
  admissible_only_if: >-
    The preflight proves an exact source-defined normalization and a fixed
    compact-open nonzero witness without choosing an anchor after seeing cells.

CLOSES:
  - OWNER_REPRESENTATION_RERANK
  - OWNER_AUTHORIZED_ACQUISITION_GATE
  - TRIAL_MONTEL_WRAPPER_AS_DIRECT_GROUND_R1_SUPPLIER

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - R1_SAME_GROUND_FAMILY_LOCAL_BOUNDEDNESS
  - R1_SAME_GROUND_FAMILY_NONZERO_TIGHTNESS
  - R1_SAME_GROUND_FAMILY_CLUSTER_IDENTIFICATION

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_R1_SAME_GROUND_FAMILY_VITALI_OBJECT_LOCK_PREFLIGHT
  MODE: PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false
  NEW_MATHEMATICAL_OBJECT_AUTHORIZED: false

NEXT_TRANSACTION_PHASES:
  PHASE_0_LITERAL_OBJECT_AND_ANCHOR_LOCK:
    mandatory_first: true
    outputs:
      - exact definition of the finite ground family F_k
      - exact theorem giving ZerosRealOn for that same F_k
      - exact scalar/gauge normalization
      - exact selected cofinal schedule and all floor assumptions
      - exact formula for F_k(0) and the first source-available fixed jets
      - audit whether eta normalization induces a fixed compact-open continuous functional
      - one planted family showing that a moving coefficient normalization can escape every compact
    hard_stop: >-
      If no fixed point, fixed jet or compact-tight normalization functional is
      source-ready, do not proceed to a generic Montel wrapper.  Return the exact
      missing tightness theorem.

  PHASE_1_MONTEL_SOURCE_ACQUISITION:
    run_only_after_phase_0_pass: true
    primary_sources_only: true
    source_families:
      - de_Branges_space_normal_families
      - Cartwright_class_real_zero_entire_functions
      - Herglotz_log_derivative_compactness
      - weak_spectral_measure_to_Cauchy_transform_compactness
    required_for_each_source:
      - exact theorem statement
      - exact assumptions and topology
      - bibliographic pin
      - parameter and normalization crosswalk to F_k
      - proof that no missing tracking rate is imported

  PHASE_2_UNIQUENESS_AND_CLUSTER_IDENTIFICATION_AUDIT:
    outputs:
      - exact uniqueness set, fixed jet sequence or spectral measure
      - source theorem giving its convergence for the same ground family
      - exact identity-theorem or transform adapter to centeredXi
      - classification of D0CriticalMomentCanonicalCluster and D0CriticalMomentMontelGate as trial-family cluster-existence assets only

  PHASE_3_SELECT_ONE_THEOREM_SIZED_NEXT_NODE:
    outputs:
      - one existing catalog name or one source-justified minimal theorem statement
      - exact CLOSES and OPENS ledger
      - proof cost and kill-power estimate
      - no Lean authorization; return to the judge

MANDATORY_SHELF_QUERIES:
  - selectedFerrersTrackedGroundTransform
  - ground transform locally bounded
  - ground transform anchor
  - eta normalized transform
  - de Branges
  - Cartwright
  - Herglotz
  - uniqueness set
  - critical moment ratio
  - cluster identification

MANDATORY_PLANTS:
  P_R1_REAL_ZERO_ANCHOR_NOT_NORMALITY:
    statement: >-
      F_n(z)=cos(n z) has only real zeros and F_n(0)=1, but is not locally
      bounded on any compact containing a nonreal point.  Real zeros plus one
      anchor do not supply Montel normality.
    purpose: kill_generic_real_zero_shortcut

  P_R1_MOVING_NORMALIZATION_ESCAPE:
    statement: >-
      A normalization functional whose support or evaluation point moves to
      infinity can stay equal to one while the functions converge locally to
      zero.  Eta normalization on growing coefficient carriers therefore needs a
      compact-tightness adapter before it can certify a nonzero Montel limit.
    purpose: kill_moving_anchor_shortcut

  P_R1_TWO_FAMILY_SPLICE:
    statement: >-
      One family may have real zeros and another may be locally bounded and
      converge to centeredXi.  Without an exact same-family theorem, the two
      facts do not compose through Hurwitz.
    cards:
      - C04_SAME_COORDINATES_TWO_LAWS
      - C10_FUNCTIONAL_NOT_SURROGATE

DISCRIMINATOR:
  PASS:
    code: R1_SAME_GROUND_FAMILY_NORMALITY_AND_UNIQUENESS_SOURCE_READY
    requirement: >-
      One literal ground family, one fixed normalization, a primary-source
      compact-normality theorem, and a same-family uniqueness/cluster theorem
      all survive the plants with exact adapters.

  HOLD:
    code: R1_GROUND_FAMILY_OBJECT_LOCKED_BUT_NORMALITY_OR_CLUSTER_ID_UNSUPPLIED
    requirement: >-
      The literal family and normalization are fixed, but at least one theorem
      source or adapter remains absent.  Return at least two candidate
      re-representations and no execution directive.

  FAIL:
    code: R1_REQUIRES_WRONG_FAMILY_OR_DEAD_TRACKING_RATE
    requirement: >-
      Every attempted local-boundedness or cluster-identification route either
      applies only to centeredPstar/trial transforms, or assumes the stopped
      residual/graph-resolvent rate, or lacks a compact-tight nonzero
      normalization.

STOP_RULE:
  - do_not_write_a_Montel_wrapper_before_the_literal_ground_family_is_locked
  - do_not_use_D0AnchorFloor_as_a_ground_anchor_without_an_exact_adapter
  - do_not_use_CenteredTrialCriticalMomentRatio_as_ground_normality
  - do_not_reopen_residual_floor_or_C_inverse_rate_estimates
  - do_not_choose_an_anchor_or_subsequence_after_inspecting_cells
  - do_not_treat_catalog_silence_as_mathematical_evidence
  - one_HOLD_after_the_source_acquisition_preflight_returns_to_owner_or_judge

CANDIDATE_REPRESENTATIONS:
  R1A_DIRECT_GROUND_DEBRANGES_NORMALITY:
    rank: PRIMARY
    object: >-
      Put the exact finite ground P59 transforms in a source-matched de Branges or
      Cartwright class and obtain normality plus cluster rigidity directly.
    kill_power: 10/10
    proof_cost: 6/10

  R1B_GROUND_LOG_DERIVATIVE_HERglotz:
    rank: RUNNER_UP
    object: >-
      Divide out the explicit lattice factor, use the logarithmic derivative of
      the real-rooted ground polynomial/transform as a Herglotz function, prove
      compactness of the associated positive spectral measures, and recover the
      limit by one anchored primitive.
    kill_power: 9/10
    proof_cost: 7/10

  R1C_FIXED_JET_UNIQUENESS:
    rank: THIRD
    object: >-
      Prove convergence of all fixed jets at one source-locked anchor for the
      exact ground family, then combine local normality with the identity theorem.
    kill_power: 8/10
    proof_cost: 6/10

REGISTERED_PREDICTIONS:
  P_R1_OBJECT_1:
    probability: 0.90
    prediction: >-
      The opening audit's two hypotheses belong to the trial centeredPstar family
      and do not directly discharge R1 for the real-zero ground family.

  P_R1_ANCHOR_1:
    probability: 0.68
    prediction: >-
      Eta normalization does not by itself produce a fixed compact-open point or
      jet anchor for the ground transforms; a tightness theorem or a new exact
      source normalization will be required.

  P_R1_NORMALITY_1:
    probability: 0.46
    prediction: >-
      A primary de Branges/Cartwright/Herglotz theorem will provide a viable
      normality shape, but its source assumptions will leave one nontrivial
      adapter for the literal selected ground family.

  P_R1_IDENTIFICATION_1:
    probability: 0.22
    prediction: >-
      Existing critical-moment Montel files already identify the ground cluster
      with centeredXi without importing tracking.

PRIOR_PREDICTION_FATE:
  P_CENTRAL_WINDOW_1_0_62: CONFIRMED
  P_CENTRAL_WINDOW_2_0_25: NOT_REALIZED
  P_CENTRAL_WINDOW_3_0_13: NOT_REALIZED_EXCEPT_CARRIER_GUARD_REPAIR

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
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
| Owner R1 choice | Accepted. It satisfies the explicit acquisition reentry condition and closes the owner-rerank control gate. | `[ABSTRACT][PAPER]` |
| Generic Montel machinery | Preserved as a kernel-green asset: compact-local bounded holomorphic families admit same-parent subsequential clusters, and a fixed nonzero anchor prevents the zero limit. | `[ABSTRACT][LEAN]` |
| Existing D0 Montel wrappers | They are wrappers for the selected trial `centeredPstar` family built from `kTrial`. They do not directly apply to the finite ground transform carrying real zeros. | `[COFINAL_FAMILY][LEAN]` |
| Existing critical-moment ratio | It is a scale-free trial-family normality contract. It is not a theorem about the ground transform. | `[COFINAL_FAMILY][LEAN]` |
| Existing D0 anchor floor | It gives a trial `rawFplus` central floor from unprojected trial mass. It is not a ground-transform anchor theorem. | `[COFINAL_FAMILY][LEAN]` |
| Same-witness ground asset | `selectedFerrersTrackedGroundTransform` is the primary literal R1 candidate because the repository proves its real-zero property for the same selected ground witness. | `[FINITE_CELL][LEAN]` |
| R1 source count | Not two. After the object lock, R1 needs ground-family local normality, compact-tight nonvanishing, and cluster identification. | `[COFINAL_FAMILY][PAPER]` |

## FINAL PROPOSAL

Run exactly one source-read-only R1 transaction. Start with the literal ground-family and anchor lock. Do not begin from `D0PostAnchorMontel`, because that silently selects the trial family. Only after Phase 0 establishes one fixed ground family and one compact-tight nonzero normalization may the transaction acquire a primary-source normality theorem and audit uniqueness-set identification.

The first decisive question is not:

```text
Can Montel extract a subsequence?
```

That machinery is already proved.

It is:

```text
Which exact real-zero ground family is normalized in a way that cannot escape every compact, and what source theorem makes that same family normal?
```

## STRONGEST ATTACK

The strongest mathematical attack is the elementary family

\[
F_n(z)=\cos(nz).
\]

Every `F_n` has only real zeros and satisfies `F_n(0)=1`, but on any compact containing `iy` with `y != 0`,

\[
|F_n(iy)|=\cosh(n|y|)\to\infty.
\]

Thus real-rootedness plus a point anchor does not imply local boundedness. R1 needs a real structural theorem, not a renamed compactness wish.

The strongest object attack is simpler: the current Montel wrappers normalize `centeredPstar`, while the real-zero theorem belongs to a finite ground transform. Combining them without an exact adapter repeats the same-family error that the route was built to prevent. This is a direct **C04/C10** kill.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.

AUTHORIZED BODY:
  Linux/paper/source-acquisition body only.

TASK_ID:
  GOAL058_R1_SAME_GROUND_FAMILY_VITALI_OBJECT_LOCK_PREFLIGHT

READ_FIRST:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersGroundProposition59RealZeros.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PostAnchorMontel.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/MontelCenteredCriticalStrip.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0AnchorFloor.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0CriticalMomentCanonicalCluster.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0CriticalMomentMontelGate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean

DO:
  1. Execute Phase 0 first and stop on failure.
  2. Ask the shelf using all mandatory queries before naming a supplier.
  3. If Phase 0 passes, acquire exact primary theorem statements only.
  4. Return one report with the precommitted PASS/HOLD/FAIL code.

DO_NOT:
  edit Lean;
  run numerics;
  submit Aristotle;
  invoke Codex;
  introduce a new approximation family;
  use the stopped tracking-rate estimate;
  treat a trial-family theorem as a ground-family theorem.
```

## META CLOSEOUT

**What became smaller?**

`OWNER_REPRESENTATION_RERANK` is closed. R1 is no longer a vague option: its first gate is the literal ground-family normalization/normality object lock.

**What was killed?**

The claim that the two trial-family hypotheses in the opening audit are already the two remaining R1 inputs.

**What must not be tried again?**

Splicing real zeros from the ground family with Montel compactness or cluster data from `centeredPstar` without an exact same-family theorem.

**Current smallest named gap?**

```text
R1_SAME_GROUND_FAMILY_COMPACT_TIGHT_NORMALITY_AND_CLUSTER_IDENTIFICATION
```

**Next cheapest decisive test?**

Evaluate the exact ground-family anchor and fixed jets, and determine whether eta normalization yields a fixed compact-open continuous nonzero functional. This source calculation precedes literature search and all formalization.

**Fate of prior predictions?**

The central-window prediction ledger remains closed without repair. New R1 predictions are registered before this preflight.

**Memory entry**

```yaml
iteration:
  target: OWNER_REPRESENTATION_RERANK
  status: PROGRESS
  failed_strategy: CENTRAL_WINDOW_CAUCHY_OBSERVABILITY
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: R1_SAME_GROUND_FAMILY_COMPACT_TIGHT_NORMALITY_AND_CLUSTER_IDENTIFICATION
  invariant_learned: Montel_and_real_zero_must_use_the_same_literal_family
  forbidden_future_move: trial_Montel_plus_ground_real_zeros_without_adapter
  next_decisive_test: literal_ground_family_anchor_and_fixed_jet_lock
```
