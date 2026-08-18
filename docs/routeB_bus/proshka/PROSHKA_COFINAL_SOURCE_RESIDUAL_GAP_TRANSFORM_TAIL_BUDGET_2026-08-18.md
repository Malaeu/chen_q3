# STATUS: CONDITIONAL — COFINAL RESIDUAL/GAP TRANSFORM-TAIL SOURCE WRITTEN; KERNEL GATE PENDING

```yaml
PRIMARY: COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_SOURCE_WRITTEN
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PARENT_HEAD: 648f240f8f01d05a19e666da1941dba2a1be28ec
  COMMIT: THIS_COMMIT
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/CofinalSourceResidualGapTransformTailBudget.lean
  LEAN_BLOB: cd910e8485b6ce816b51080b42c8c0c0af1aa75c

PUBLIC_SURFACE:
  DEFINITION: Q3.RouteB.sourceUnitRayleighResidual
  THEOREM: Q3.RouteB.cofinalSourceResidualGapTransformTailBudget

KERNEL_VALIDATION: PENDING
SOURCE_WRITTEN: true
LEAN_PROVED: false
EXPECTED_AXIOMS: [propext, Classical.choice, Quot.sound]

LOOPHOLE_REPAIR:
  FREE_ERROR_FAMILIES: false
  FREE_DECOMPOSITION_HYPOTHESIS: false
  RESIDUAL_COMPUTED_FROM_NAMED_OPERATOR: true
  PROJECTED_TRIAL_COMPUTED_FROM_NAMED_PROJECTION: true
  NORMALIZER_EXPLICIT_AND_NONZERO: true
  TAIL_IS_LITERAL_NAMED_TRANSFORM_DIFFERENCE: true

OPEN_SUPPLIERS:
  - PROJECTIVE_RESIDUAL_GAP_INEQUALITY
  - COMPACT_EVALUATION_ENVELOPE_AND_COFINAL_RATE
  - LITERAL_PROJECTED_TRIAL_TO_TARGET_TAIL
  - EXACT_CCM_OBJECT_CROSSWALK

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED: [C04, C09, C10]

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

REGISTERED_PREDICTIONS:
  P_CRGTTB_1:
    statement: source compiles without edits
    probability: 0.68
  P_CRGTTB_2:
    statement: green source has exactly the standard axiom triple
    probability: 0.95
  LIKELIEST_FIRST_FAILURE: CONTINUOUS_LINEAR_MAP_OR_SQRT_API_MISMATCH

SUCCESS_CODE_AFTER_GATE: COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_LEAN
STOP_CODE_NOW: COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_KERNEL_PENDING
NEXT_LOAD_BEARING_GAP: LITERAL_CCM_COFINAL_RESIDUAL_FLOOR_ENVELOPE_AND_TRANSFORM_TAIL

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

The repaired `SameFamilyGroundTrialCompositionCore` is kernel-proved, but its
Linux gate exposed a semantic loophole: free error functions plus `hdecomp`
allowed the desired conclusion to be passed back as a premise.

The new source removes that loophole.  It names one operator, one finite
projection, one ground family, one source-trial family, one normalizer, one
continuous evaluation map, one target family, one filter, and one domain.  It
computes

```text
q_i = finiteProjection_i(sourceTrial_i)
r_i = sourceOperator_i(q_i) - <q_i,sourceOperator_i(q_i)> q_i
```

and derives the tracking term internally from the phase-aligned ground vector.
The tail premise is the literal difference between the normalized projected
trial transform and the named target transform.  No independent
`trackingError`, `projectionTail`, `normalizationError`, or `hdecomp` binder
remains. `[COFINAL_FAMILY][CONDITIONAL]`

The theorem composes the legal chain

```text
residual / positive gap
-> projective defect
-> phase-aligned coefficient distance
-> compact transform tracking
+ literal transform tail
-> locally uniform ground-to-trial tracking.
```

It does not prove the three quantitative suppliers.

## FINAL PROPOSAL

Run the kernel gate on the exact blob.  A green result closes the typed
source-facing composition theorem only.  The next mathematics is the literal
CCM cofinal supplier producing the residual/floor envelope, P59 compact
evaluation envelope, and projection/normalization tail on one precommitted
family.

## STRONGEST ATTACK

**C10:** the hard estimates remain premises.  Correct; this theorem prevents
error-as-conclusion circularity, not the need to prove those estimates.

**C04:** abstract maps can still be instantiated with the wrong objects.
Correct; the production CCM crosswalk remains mandatory.

**C09:** a schedule could still be selected post hoc outside this theorem.
Correct; source precommit remains a separate gate.

## CODEX DIRECTIVE

```text
TASK: kernel-check the committed source unchanged.

WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/CofinalSourceResidualGapTransformTailBudget.lean
  lake build Q3.Proofs.RouteB.CofinalSourceResidualGapTransformTailBudget

WORKDIR: <repo root>
  bash scripts/q3_check.sh Q3/Proofs/RouteB/CofinalSourceResidualGapTransformTailBudget.lean

AXIOM GATE:
  #print axioms Q3.RouteB.cofinalSourceResidualGapTransformTailBudget
  require exactly [propext, Classical.choice, Quot.sound]

SUCCESS: COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_LEAN
FAILURE: COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_KERNEL_OR_API_MISMATCH

On failure report the exact line, stdout, axiom profile, and smallest API-only
repair.  Do not weaken the statement or source-object graph.
```

## META CLOSEOUT

**What became smaller?** Free error families and the assumed decomposition are
gone; three named supplier classes remain.

**What was killed?** The instantiation
`trackingError := ground - trial`, `tail := 0`, `normalization := 0`.

**What must not be tried again?** Source-lock-as-proof, free error ledgers, or
merged working directories for Lean and `q3_check`.

**Current smallest named gap:**
`LITERAL_CCM_COFINAL_RESIDUAL_FLOOR_ENVELOPE_AND_TRANSFORM_TAIL`.

**Fate of prior predictions:** `P-SF1` and committed-source `P-SF2` are refuted;
the free-error firewall claim is refuted by the Linux gate.  No retroactive
repair.

```yaml
iteration:
  target: CofinalSourceResidualGapTransformTailBudget
  status: OPEN
  failed_strategy: free errors plus assumed decomposition
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: LITERAL_CCM_COFINAL_RESIDUAL_FLOOR_ENVELOPE_AND_TRANSFORM_TAIL
  invariant_learned: every error is computed from named source objects
  forbidden_future_move: pass desired convergence back as an error premise
  next_decisive_test: exact Linux kernel gate
```

## VERIFICATION HANDOFF

```yaml
BRANCH: rh_clean
PARENT: 648f240f8f01d05a19e666da1941dba2a1be28ec
COMMIT: THIS_COMMIT
FILES_WRITTEN:
  - q3.lean.aristotle/Q3/Proofs/RouteB/CofinalSourceResidualGapTransformTailBudget.lean
  - docs/routeB_bus/proshka/PROSHKA_COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_2026-08-18.md
LEAN_BLOB: cd910e8485b6ce816b51080b42c8c0c0af1aa75c
EXPECTED_AXIOMS: [propext, Classical.choice, Quot.sound]
STATUS_ON_GREEN_GATE: SOURCE_WRITTEN_TO_LEAN_PROVED_FOR_THIS_THEOREM_ONLY
UNCHANGED: literal CCM suppliers OPEN; CHALLENGER_NOT_RH; BUS_010 VOID
```
