# STATUS: CONDITIONAL — CONTROL V9 RATIFIED AS AT-MOST-ONCE; G5 FLOOR CANCELS, SOURCE LEAKAGE REMAINS OPEN
```yaml
PRIMARY: RATIFY_REQ_2026_08_21_P_WITH_G5_REPRESENTATION_SHIFT
PRIMARY_COUNT: 3

REQUEST:
  ID: REQ-2026-08-21-P
  STATUS_AT_REVIEW: OPEN
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_GIT_BLOB: 3dcffca1fb51a42608b91bbd91dda17a3cd30f0d

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: aecdc6800b9dc97265e05898988b2a7207448a56
  CONTROL_V9_COMMIT: d92960a02ef6e845d574d4cba02e4ee4c2293104
  CONTROL_PATH: docs/CODEX_CONTROL.md
  CONTROL_GIT_BLOB: 43dfaa28cf495f1c60eb4c196e22aa4842205ff0
  RUNTIME_PATH: orchestrator/three_body_loop.py
  RUNTIME_GIT_BLOB: 0258b6a94d2ca12b5d22e97fbaea4c8f7791b27b
  CONTROL_TASK_PATH: docs/Codex/TASK_2026-08-21_codex_control_v9_three_body_lease_and_semantic_quarantine.md
  CONTROL_TASK_GIT_BLOB: fdf743081ceff497a3c63cbc13e25abc3663d953
  QUARANTINE_STATE_PATH: orchestrator/state/SEMANTIC_QUARANTINE.json
  QUARANTINE_STATE_GIT_BLOB: 689c73002d181f97014b013910147d6763e12e92
  ACTIVE_LEASE_AT_REVIEW: null

CONTROL_REVIEW:
  JUDGE_RERAN_TEST_SUITE: false
  SOURCE_AND_PLANT_CODE_AUDITED: true
  IMPLEMENTER_VALIDATION_LEDGER_PRESENT: true
  CONTROL_V9_DESIGN: RATIFIED
  REQ_O_HOLD: SATISFIED_BY_CONTROL_V9
  OWNER_MAY_ISSUE_BOUNDED_LEASE: true
  VERDICT_ITSELF_ACTIVATES_LEASE: false

POINT_1_LAUNCH_SEMANTICS:
  EXACTLY_ONCE_TRIGGER: REJECTED_AS_UNATTAINABLE_ACROSS_UNCOOPERATIVE_CRASH_BOUNDARY
  AT_MOST_ONCE_LAUNCH: RATIFIED
  DURABLE_EVENT_STATES:
    - RESERVED
    - STARTED
    - FAILED_BEFORE_LAUNCH
  REQUESTED_RUNNING_COMPLETED_FAILED_IN_TRIGGER_LEDGER: REJECTED_WRONG_STATE_MACHINE
  COMPLETION_BELONGS_TO_TASK_RESULT_OR_QUARANTINE_LEDGER: true
  DUPLICATE_RUN_NONCE: NOOP
  PRELAUNCH_FAILURE_REQUIRES_NEW_EXTERNALLY_AUTHORIZED_NONCE: true
  AUTOMATIC_RETRY_OF_AMBIGUOUS_EVENT: forbidden
  LOST_TRIGGER_ON_AMBIGUITY: ACCEPTED_FAIL_CLOSED_COST

POINT_2_SEMANTIC_ADMISSION:
  CLOSED_STRUCTURED_ATTESTATION: RATIFIED
  EXTERNAL_LINUX_ISSUER: required
  CODEX_SELF_ADMISSION: forbidden
  BINDS:
    - task_path_and_blob
    - source_commit_and_blob
    - theorem_ids
    - admitted_scope
    - terminal_consumer
    - closes_and_opens
    - normalization
    - domain
    - quantifiers
    - canonical_hypothesis_provenance_digest
  OPERATIONAL_ADMISSION_IS_A_PROOF_OF_TRUTH: false
  ROLE: FAIL_CLOSED_ACCOUNTABILITY_AND_DOWNSTREAM_PERMISSION
  OLD_PLANT_NAME: UNINHABITED_ANTECEDENT_REPLAY
  OLD_PLANT: FALSIFIED_AS_RECEIPT_TAUTOLOGICAL
  NEW_PLANT_NAME: MALFORMED_INHABITANT_OR_PLANT_REPLAY
  NEW_PLANT: RATIFIED_AS_THE_ACTUAL_SCHEMA_FALSIFIER

POINT_3_G5:
  TARGET: CenteredTrialCriticalMomentRatio
  EXACT_EQUIVALENCE:
    theorem: centeredTrialCriticalMomentRatio_iff_uniform_leakage
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0CenteredMomentRatioLeakageEquivalence.lean
    blob: 2307e8c386bbd1ad566fe432c72096d62f51527b
    status: LEAN_PROVED_RESTATEMENT
  SELECTED_CENTRAL_FLOOR_AS_G5_INPUT: REMOVED
  SELECTED_ANCHOR_RATIO_DATA_AS_G5_INPUT: REMOVED
  POINTWISE_CENTRAL_NONVANISHING: STILL_REQUIRED_BY_CentralIndex
  UNIFORM_ANCHOR_FLOOR_ELSEWHERE: NOT_DISCHARGED
  UNIFORM_SOURCE_LEAKAGE_BOUND: OPEN
  GENERIC_NORMALIZED_TRIGONOMETRIC_ROW_THEOREM: KILLED_BY_CONSTANT_MODE
  SOURCE_SPECIFIC_PROLATE_ROW_THEOREM: OPEN_REPAIRABLE
  EDGE_VS_CENTER_ARGUMENT: KILLED_NO_LOCATION_INFORMATION
  SCALAR_RENORMALIZATION_AS_REPAIR: KILLED_BY_SCALE_INVARIANCE
  WINDOW_CUT_AS_REPAIR: FORBIDDEN_WITHOUT_SOURCE_AND_CONSUMER_CROSSWALK

G5_EXACT_NORMAL_FORM:
  L: log_m
  P_i: "sum_{n=-N}^N (-1)^n (c_n/c_0) exp(2*pi*i*n*t/L)"
  ZERO_COEFFICIENT: 1
  LEAKAGE: "(1/L) * integral_{-L/2}^{L/2} |P_i(t)| exp(sigma*|t|) dt"
  LOWER_BOUND: "1 <= leakage"
  LOWER_BOUND_IMPLIES_DIVERGENCE: false

G5_PRIMARY_REPRESENTATION:
  CODE: SOURCE_ENVELOPE_PLUS_DIAGONAL_GALERKIN
  INPUT_A: uniform_weighted_L1_ratio_for_the_unprojected_E_star_source
  INPUT_B: fixed_m_weighted_L1_convergence_of_Fourier_projection
  INPUT_C: exact_zero_mode_preservation_under_projection
  OUTPUT: one_precommitted_PairCofinal_path_satisfying_CenteredTrialCriticalMomentRatio
  KILL_POWER: 9/10
  PROOF_COST: 6/10

G5_SECONDARY_REPRESENTATION:
  CODE: DIRECT_COMPACT_STRIP_BOUND
  TARGET: SelectedLocallyBoundedOnCenteredCriticalStrip
  EXISTING_CONSUMER: exists_refined_montelAnchorGate_of_strip_bounds
  ROLE: bypass_weighted_L1_if_the_stronger_moment_functional_is_false
  KILL_POWER: 10/10
  PROOF_COST: 7/10

G5_DISCRIMINATOR:
  NAME: SOURCE_VS_PROJECTION_WEIGHTED_SPLIT
  SOURCE_TERM: "integral |E_star(h_m)(exp t)| exp(sigma|t|) / |zero_mode|"
  PROJECTION_TERM: "integral |P_{m,N}g_m-g_m| exp(sigma|t|) / |zero_mode|"
  PASS: source_term_uniform_and_one_diagonal_makes_projection_term_bounded
  KILL_G5_MOMENT_REPRESENTATION: source_term_has_a_proved_cofinal_lower_envelope_tending_to_infinity
  ZERO_CONSISTENT_NUMERICS: INCONCLUSIVE_WITHOUT_THIS_SPLIT

REGISTERED_PREDICTIONS:
  P_P_G5_1:
    statement: the unprojected canonical prolate source has a uniform weighted L1 ratio for every fixed sigma below one half
    probability: 0.75
    fate: PENDING
  P_P_G5_2:
    statement: one diagonal N(m) can absorb weighted Galerkin error without a uniform N-versus-m rate theorem
    probability: 0.82
    fate: PENDING
  P_P_G5_3:
    statement: the first genuine failure, if any, is an endpoint/source-envelope failure near sigma approaching one half, not a central-normalization failure
    probability: 0.70
    fate: PENDING

PRIOR_PREDICTIONS_FATE:
  P_O_1: REFUTED_IN_ORIGINAL_FORM_REPAIRED_PLANT_NOT_RETROACTIVELY_RELABELED
  P_O_2: CONFIRMED_AT_SOURCE_AND_PLANT_LEVEL
  P_O_3: CONFIRMED_AT_CONTROL_SCHEMA_LEVEL_OPERATIONAL_TRAFFIC_NOT_YET_SCORED
  P_O_4: CONFIRMED_IMPLEMENTATION_DEFECTS_WERE_LIFECYCLE_LOCK_AND_CLI_WIRING
  P_BATCH_G5_COUNT: CONFIRMED_TWO_ROPES
  P_BATCH_G5_CHARACTER: REFUTED_PAIRCOFINAL_PLUS_ONE_UNIFORM_RATIO

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Control v9: the corrected launch contract is admissible

The request is right that a literal **exactly-once execution** guarantee cannot
be obtained across a crash boundary when the launched program does not
participate in one atomic transaction with the trigger ledger.  Persisting the
nonce before spawn can lose the event; spawning first can duplicate the event
after a crash.  The implementation chooses the safe side:

```text
reserve durably
→ hold one writer flock across fork and child runtime
→ bind one exact session/task/phase/head/run/nonce
→ never launch the same run/nonce twice
→ require a new external nonce after a proved pre-launch failure.
```

This is an honest **at-most-once launch** contract.  It can lose work in an
ambiguous crash window, but it cannot silently duplicate a writer.  That is the
correct trade for this repository. `[ABSTRACT][PAPER]`

The exact event states in Control v9 are better typed than the four labels in
the request:

```text
RESERVED
STARTED
FAILED_BEFORE_LAUNCH
```

`STARTED` records that the launch crossed the non-retry boundary.  It does not
claim that the mathematical task completed successfully.  Completion belongs
to the task/result/quarantine state machine, not to the trigger ledger.  Mixing
those two state machines would recreate a C04 error: equal-looking status words
for different laws. `[ABSTRACT][PAPER] [C04]`

The source implementation checks the exact session instead of `--last`, pins
`HEAD`, branch, task blob, phase hash and control version, reserves under an
exclusive `flock`, transfers the lock descriptor to the child, and uses a
`CHILD_READY_TO_EXEC` marker plus PID/start-time/boot-ID identity for recovery.
A duplicate run/nonce returns `DUPLICATE_TRIGGER_NOOP`.  The crash-after-spawn
plants exercise the ambiguous boundary. `[ABSTRACT][PAPER]`

The at-most-once contract is therefore ratified.  The cost is explicit:
ambiguous or proven pre-launch failure may require manual review and a new
externally authorized nonce.  Automatic retry under the same nonce remains
forbidden.

### 2. Control v9 may now support a bounded autonomy lease

REQ-O's hold is satisfied by the v9 transaction.  The active policy now
separates:

```text
SOURCE_WRITTEN
→ KERNEL_GREEN
→ SEMANTICALLY_ADMITTED(scope = ...).
```

The autonomy lease is externally resolved and bound to one control version,
branch, worktree, writer body, phase, exact task blob, allowed paths, activation
commit, expiry and positive node budget.  Policy ancestors, `CURRENT.md`, Git
internals, route promotion, `PX_RH_CLAIM`, force push and direct judge transport
remain outside the lease.  The tracked state is currently empty and has
`active_lease: null`. `[ABSTRACT][PAPER] [C12]`

This verdict does not manufacture an active lease.  It permits the owner/Linux
authority to issue one bounded lease under Control v9.  The lease must still be
resolved externally and must match the tracked state byte-for-field.

### 3. Semantic admission: structured receipt accepted, magical truth stamp rejected

The repaired admission record binds more than the requested seven semantic
items.  It binds exact task and source blobs, theorem IDs, admitted scope,
terminal consumer, `CLOSES`, `OPENS`, normalization, domain, quantifiers and a
canonical digest of every load-bearing hypothesis.  Each hypothesis carries a
closed source/supplier/open-obligation variant and a committed production
inhabitant or reachability plant.  Codex cannot self-resolve the Linux receipt.
`[ABSTRACT][PAPER] [C09] [C10]`

This is the correct operational gate.  It is not a mathematical proof that the
independent auditor thought correctly.  It makes the trust boundary explicit,
binds the auditor to the exact object, and blocks downstream consumption when
that judgement is absent or malformed.

The old plant name `UNINHABITED_ANTECEDENT_REPLAY` overstated what its first
implementation tested.  The original plant was falsified as receipt-tautological:
it could fail merely because the receipt was absent.  The repaired
`MALFORMED_INHABITANT_OR_PLANT_REPLAY` supplies an otherwise field-bound receipt,
then replaces the structured inhabitant/plant object with free text and requires
rejection.  That is the actual schema falsifier.  The original prediction stays
recorded as refuted; the new plant is not a retroactive repair of its score.

### 4. G5: the denominator cancellation is exact

For the exact source row,

\[
q_i(t)=L^{-1/2}\sum_{n=-N}^{N}(-1)^n c_n
       e^{2\pi i n t/L},
\qquad
F_i(0)=\sqrt L\,c_0.
\]

At a `CentralIndex`, \(c_0\ne0\).  Define

\[
P_i(t)=\sum_{n=-N}^{N}(-1)^n\frac{c_n}{c_0}
       e^{2\pi i n t/L}.
\]

Then the exact leakage quotient is

\[
\boxed{
\operatorname{Leak}_{i,\sigma}
 =\frac1L\int_{-L/2}^{L/2}|P_i(t)|e^{\sigma|t|}\,dt.
}
\]

The Lean theorem
`centeredTrialCriticalMomentRatio_iff_uniform_leakage` proves that the named G5
contract is exactly uniform boundedness of this quotient along the same path.
No uniform lower floor for `rawFplus(0)` is an input to this implication; it
cancels. `[COFINAL_FAMILY][LEAN]`

The boundary is precise:

```text
pointwise nonzero denominator:
  still required to inhabit CentralIndex and define the normalization;

uniform positive denominator floor:
  not required by G5;

uniform floor needed by another consumer:
  not proved or removed by this result.
```

### 5. The edge-growth argument does not kill the target

The zero Fourier coefficient of \(P_i\) is one, hence

\[
1=\left|\frac1L\int P_i(t)\,dt\right|
 \le \frac1L\int|P_i(t)|\,dt
 \le \operatorname{Leak}_{i,\sigma}.
\]

This proves only a lower bound.  It contains no location information.  It does
not force a fixed fraction of the mass into the endpoint region where
\(e^{\sigma|t|}\) is large.  Treating total mass as endpoint mass is exactly the
C01 failure. `[ABSTRACT][PAPER] [C01]`

There are finite trigonometric-polynomial families with zero coefficient one
and mass increasingly concentrated near the center.  Period-\(L\) Fejér kernels
with degree growing sufficiently faster than the endpoint weight are an
explicit abstract falsifier of the claimed incompatibility.  Thus

```text
center normalization
+
large endpoint weight
```

does not logically imply divergence. `[ABSTRACT][PAPER]`

The opposite generic theorem is also false.  The constant mode \(P_i\equiv1\)
has

\[
\frac1L\int_{-L/2}^{L/2}e^{\sigma|t|}\,dt
\asymp \frac{e^{\sigma L/2}}L,
\]

so arbitrary normalized rows fail.  This is already planted in the G5 source.
Therefore the only honest target is source-specific localization of the
canonical prolate row. `[ABSTRACT][LEAN]`

The binary64 probe on \(m=13,\ldots,257\), \(N=120\) reports approximately

```text
R(0.10): 1.017
R(0.25): 1.045
R(0.40): 1.073
R(0.45): 1.083
```

with tiny sampled \(N\)-sensitivity.  This supports repairability but occupies
no cofinal quantifier. `[FINITE_CELL][CONDITIONAL]`

### 6. The correct representation split

The useful object is not the normalized polynomial alone.  Split the exact
finite density into:

```text
unprojected source density from E_star(prolateCombination)
+
Galerkin projection error.
```

For fixed \(m\), the exponential weight is bounded on the finite window, so
ordinary \(L^2\) projection convergence implies weighted \(L^1\) convergence by
Cauchy--Schwarz.  A uniform \(N\)-versus-\(m\) rate is not logically required if
one is free to choose one precommitted diagonal path: enumerate rational
\(\sigma<1/2\), and at stage \(k\) choose \(N_k\) large enough for the first
\(k\) weighted requirements.  Monotonicity in \(\sigma\) extends the result to
every fixed real \(\sigma<1/2\). `[COFINAL_FAMILY][CONDITIONAL] [C09]`

What remains genuinely analytic is the source term:

\[
\sup_k
\frac{
 \int |E_\star(h_{m_k})(e^t)|e^{\sigma|t|}\,dt
}{|\text{zero mode of }E_\star(h_{m_k})|}
<\infty.
\]

The threshold \(\sigma<1/2\) strongly suggests the intended two-sided
multiplicative envelope \(e^{-|t|/2}\), but that envelope is not yet a theorem
for the exact project source.  This is now the smallest analytic content of G5.
`[COFINAL_FAMILY][CONDITIONAL]`

### 7. Do not cut the window or change the scalar normalization

Changing the scalar normalization cannot improve the leakage quotient: numerator
and denominator have the same homogeneity, and the quotient is scale invariant.
That repair is algebraically dead.

Cutting the window changes the source transform and its consumers.  It is a
C04/C10 object substitution unless an exact crosswalk preserves the selected
family, anchor, zero set, paper limit and one cofinal schedule.  No such repair
is authorized. `[COFINAL_FAMILY][CONDITIONAL] [C04] [C10]`

If the weighted-moment representation is eventually killed, the roof still has
a weaker direct interface.  `exists_refined_montelAnchorGate_of_strip_bounds`
consumes `SelectedLocallyBoundedOnCenteredCriticalStrip` directly.  A source-
specific compact-strip estimate can therefore replace the stronger weighted
\(L^1\) functional without changing the roof theorem.  That is the mandatory
runner-up representation, not a post-hoc window cut.

## FINAL PROPOSAL

### Operational decision

Freeze Control v9 as the active control text.  Do not rename its launch contract
to exactly-once.  Do not add `COMPLETED` to the trigger ledger.  The owner/Linux
authority may now issue a bounded `CODEX_AUTONOMY_LEASE_V1`; this verdict does not
activate one automatically.

### Mathematical decision

Keep `UNIFORM_CENTERED_CRITICAL_MOMENT_RATIO` open.  Remove
`SelectedCentralFloor` and `SelectedAnchorRatioData` only from this G5 input
ledger.  Do not infer that those objects are unnecessary elsewhere.

Registered primary route:

```text
exact source density
→ uniform source weighted envelope
→ fixed-m Galerkin weighted convergence
→ one precommitted diagonal PairCofinal path
→ CenteredTrialCriticalMomentRatio.
```

Registered fallback:

```text
direct SelectedLocallyBoundedOnCenteredCriticalStrip
→ existing strip-Montel consumer.
```

Likeliest failure point: the exact source endpoint envelope near
\(\sigma\uparrow1/2\), not the cancelled central floor.

## STRONGEST ATTACK

### Against the operational verdict

At-most-once can lose a legitimate wake event.  Correct.  That is not a hidden
bug; it is the safety price.  An ambiguous event is never retried under the same
nonce.  A human or external authority must inspect the ledger and issue a new
nonce.  If uninterrupted progress is valued above duplicate-writer exclusion,
this contract is the wrong one; this repository has already chosen the opposite
priority.

The structured semantic receipt also cannot prove that the Linux auditor is
infallible.  Correct.  It creates source-bound accountability and an independent
permission boundary; it does not replace mathematical review.

### Against the G5 verdict

The canonical source row might still place enough mass near the moving endpoints
to make the weighted ratio diverge.  Existing finite probes do not rule this
out.  The route survives only if the source/projection discriminator closes.

The weakest repaired statement if the source term diverges is not a shorter
window and not a fitted scalar.  It is direct compact-strip local boundedness,
which is exactly what the Montel consumer requires.

## CODEX DIRECTIVE

```text
TASK: G5_SOURCE_PROJECTION_LEAKAGE_SPLIT

One theorem transaction only.
Do not edit docs/CODEX_CONTROL.md, AGENTS.md, CURRENT.md, the queue, or Q3.Main.
Do not claim the uniform source estimate.

Preferred new file:
  Q3/Proofs/RouteB/D0CenteredSourceProjectionLeakageSplit.lean

Source objects:
  ProlateCanonicalSourceData
  E_star
  gTrial_m
  P_m_N
  kTrial_m_N
  c_n
  centeredTrialDensity
  centeredMomentLeakage

Prove an exact source-facing decomposition with no new analytic axiom:

1. Define the centered log-coordinate representative of the unprojected
   E_star(prolateCombination) source on [-L/2,L/2].

2. Prove that the zero Fourier coefficient is preserved by P_m_N and that the
   positive kTrial normalization cancels from the leakage ratio.

3. Define the weighted source ratio and weighted projection-error ratio.

4. Prove the pointwise inequality

     centeredMomentLeakage
       <= sourceWeightedRatio + projectionWeightedErrorRatio.

5. State no uniform bound and no cofinal limit in this transaction.

Forbidden shortcuts:
  - no new sorry/admit/axiom/opaque supplier;
  - no free coefficient row replacing ProlateCanonicalSourceData;
  - no uniform central floor premise;
  - no window cut;
  - no scalar renormalization repair;
  - no numerical estimate as proof;
  - no second cofinal schedule.

Validation:
  cd q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/D0CenteredSourceProjectionLeakageSplit.lean
  lake build Q3.Proofs.RouteB.D0CenteredSourceProjectionLeakageSplit
  cd ..
  scripts/q3_check.sh \
    Q3/Proofs/RouteB/D0CenteredSourceProjectionLeakageSplit.lean

Expected axiom profile:
  [propext, Classical.choice, Quot.sound]

Success code:
  G5_SOURCE_PROJECTION_LEAKAGE_SPLIT_LEAN

Failure codes:
  G5_SOURCE_DENSITY_OBJECT_CROSSWALK_GAP
  G5_ZERO_MODE_PROJECTION_IDENTITY_GAP
  G5_WEIGHTED_PROJECTION_SPLIT_GAP

On failure, return the exact smallest missing identity and stop.  Do not open a
new analytic premise merely to make the receiver compile.
```

## META CLOSEOUT

**What became smaller?**

```text
Control ambiguity:
  exactly-once fantasy
  → exact at-most-once launch contract.

G5:
  moment bound + uniform anchor floor
  → one source-specific scale-free leakage bound.
```

**What was killed?**

- exactly-once execution language across the uncooperative crash boundary;
- `RUNNING/COMPLETED` as trigger-ledger states;
- the old receipt-tautological plant interpretation;
- a uniform anchor floor as a G5 premise;
- the claim that average mass one forces endpoint mass;
- a generic theorem for arbitrary normalized trigonometric rows;
- scalar renormalization as a repair;
- unsourced window cutting.

**What must not be tried again?**

Do not infer edge mass from total mass.  Do not rerun the generic constant-mode
route.  Do not reopen Control v9 semantics without a new falsifier.  Do not call
a structured semantic receipt a proof of mathematical truth.

**Current smallest named gap:**

```text
UNIFORM_CENTERED_CRITICAL_MOMENT_RATIO
```

with internal discriminator:

```text
SOURCE_VS_PROJECTION_WEIGHTED_SPLIT.
```

**Next cheapest decisive test:**

Prove the exact source/projection split, then attack the unprojected source
envelope before attempting any cofinal numerical expansion.

**Fate of prior predictions:**

Recorded in the machine block.  In particular, `P_O_1` remains refuted in its
original form; the renamed plant does not rewrite history.

```yaml
iteration:
  target: REQ-2026-08-21-P operational repair and G5 hidden-kill audit
  status: PROGRESS
  failed_strategy: exactly_once_trigger_plus_total_mass_edge_inference
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: UNIFORM_CENTERED_CRITICAL_MOMENT_RATIO
  invariant_learned: trigger completion and task completion are different state machines; G5 is scale invariant and source-localization dependent
  forbidden_future_move: infer endpoint mass from average mass or repair a homogeneous ratio by scalar normalization
  next_decisive_test: G5_SOURCE_PROJECTION_LEAKAGE_SPLIT
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
