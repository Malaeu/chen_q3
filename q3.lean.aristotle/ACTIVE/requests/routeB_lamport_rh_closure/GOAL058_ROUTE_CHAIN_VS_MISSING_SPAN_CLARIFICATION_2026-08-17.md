# STATUS: OPEN — ROUTE MAP COMPLETE; SAME-FAMILY SPAN UNPROVED
```yaml
PRIMARY: GOAL058_ROUTE_CHAIN_COMPLETE_BUT_SPAN_PLACEHOLDER
PRIMARY_COUNT: 1

FINAL_CLOSURE:
  ZERO_ESCAPE_HURWITZ: VALID
  REQUIRED_INPUT: SAME_NORMALIZED_COFINAL_FAMILY
  RH_CLAIMED: false

LEFT_BANK:
  FINITE_GROUND_REAL_ZERO_ENGINE: CONDITIONAL_ON_G1_GROUND_PACKAGE
  TRIAL_OBJECT_SOURCE_LOCK: ACTIVE_G3_PROGRESS
  CENTER_SIGN_AND_FOURIER_PHASE: USEFUL_NORMALIZATION_SUPPLIERS

RIGHT_BANK:
  CCM_LEMMA_7_3_TRIAL_TO_XI: PAPER_PROVED
  PROJECT_OBJECT_NORMALIZATION_CROSSWALK: OPEN

MISSING_SPAN:
  THEOREM: FiniteGroundTransformToCCMTrialLocallyUniform
  CONTRACT_STATUS: PLACEHOLDER
  TRUE_GAP_AND_RESIDUAL: PROSE_ONLY
  EXACT_GROUND_EQUALS_TRIAL: KILLED
  ROLE: MAIN_LOAD_BEARING_APPROXIMATION_BRIDGE

REPAIRED_LOGICAL_CHAIN:
  - G0_EXACT_OBJECT_COORDINATE_NORMALIZATION_LOCK
  - G1_COFINAL_SIMPLE_EVEN_GROUND_PACKAGE
  - G2_GROUND_TRANSFORM_REAL_ZEROS
  - G3_FINITE_GROUND_TO_CCM_TRIAL_LOCALLY_UNIFORM
  - G4_CCM_TRIAL_TO_XI
  - G5_ZERO_ESCAPE_HURWITZ
  - RH

SPAN_DECOMPOSITION:
  - PROJECTED_TRIAL_RESIDUAL_UPPER_BOUND
  - TRUE_GROUND_COMPLEMENT_FLOOR_OR_GAP_LOWER_BOUND
  - RESIDUAL_OVER_GAP_TO_PROJECTIVE_GROUND_TRACKING
  - COEFFICIENT_TRACKING_TO_COMPACT_TRANSFORM_BOUND
  - PROJECTION_TAIL_AND_NORMALIZATION_ERROR_TO_ZERO
  - ONE_PRECOMMITTED_COFINAL_SCHEDULE

MINIMAL_TARGET:
  NAME: GroundStateToTrialSameFamilyBridge
  FORMULA: >-
    for every compact K in the open strip,
    C_K(m_j,N_j) * norm(r_j) / Delta_j
    + Tail_j(K) + NormalizationError_j(K) tends to zero

SCHEDULE_GUARD:
  REQUIREMENT: N_j / log(m_j) tends to infinity
  PURPOSE: external sine-lattice zeros leave every fixed compact

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

The previously drawn chain was a complete dependency graph, not a theorem-complete proof.
The valid final implication is:

```text
same finite functions have only real zeros
+ the same normalized functions converge locally uniformly to Xi
→ ZeroEscape / Rouché / Hurwitz
→ RH.
```

The current suppliers do not yet inhabit one family:

```text
actual finite CCM ground transforms:
  real-zero property, conditional on a simple-even ground package;

CCM prolate trial transforms:
  convergence to Xi, paper-proved by Lemma 7.3;

missing:
  actual ground transforms track those trial transforms
  along one normalization and one cofinal schedule.
```

Therefore the theorem

```text
FiniteGroundTransformToCCMTrialLocallyUniform
```

is the missing bridge span. Its name existing in a contract does not count as a proof.

The killed shortcut remains killed:

```text
exact ground = trial.
```

The repair is quantitative, not definitional. Let `q_j` be the projected source trial,
`xi_j` the actual finite ground vector, `a_j` the Rayleigh value of `q_j`,
`r_j = (K_j - a_j I) q_j`, and `Delta_j` the true ground-to-complement gap or floor.
A lawful bridge must prove a compact-transform estimate controlled by

```text
C_K(m_j,N_j) * ||r_j|| / Delta_j
+ projection tail
+ normalization error.
```

All terms must tend to zero along one precommitted cofinal schedule.

The current Ferrers center/sign/Fourier work is not wasted. It source-locks the trial,
its phase, scale, zero orientation and nondegenerate normalization. Those are left-bank
foundations. They do not by themselves produce the actual ground vector, a true gap,
a residual bound, or the span theorem.

## FINAL PROPOSAL

Finish the already small `center_pos_of_no_interior_zero` node, then stop expanding the
left-bank supplier tree and freeze the exact span API.

The span must be built in this order:

```text
1. CofinalFiniteSimpleEvenGroundPackage
   actual ground xi_j + true complement floor Delta_j.

2. ProjectedTrialResidualOverGapToGroundTracking
   dist_projective(xi_j, q_j) <= controlled ||r_j|| / Delta_j.

3. GroundCoefficientTrackingToTransformLocallyUniform
   coefficient/projective tracking gives a sup norm bound on every compact K.

4. ProjectedTrialTransformToCCMTrialLocallyUniform
   projection tail and normalization errors vanish.

5. FiniteGroundTransformToCCMTrialLocallyUniform
   compose 2–4 on the same source family and schedule.
```

Registered prediction:

```text
The dominant mathematics is not the final Hurwitz theorem and not the Ferrers sign.
It is the cofinal true-gap/residual estimate required by steps 1–2.
```

## STRONGEST ATTACK

A reviewer can currently say:

```text
You proved real zeros for family A.
You proved convergence to Xi for family B.
You have not proved A approaches B.
Therefore the two theorems do not compose.
```

This attack is fatal to the present RH closure and must not be answered by
`morally the same`, `up to scalar`, numerical overlap, or exact equality.
Only the same-family locally uniform tracking theorem answers it.

## CODEX DIRECTIVE

```text
CODEX_STATUS: UNAVAILABLE

NO LEAN EXECUTION FROM THIS CLARIFICATION.

NEXT THEOREM-SHAPE TASK WHEN CODEX RETURNS:
  materialize the exact interface for
  FiniteGroundTransformToCCMTrialLocallyUniform
  without proving it by assumption.

Required fields:
  - one precommitted cofinal schedule (m_j,N_j);
  - N_j / log(m_j) -> infinity;
  - actual ground vector xi_j;
  - source projected trial q_j;
  - true complement floor/gap Delta_j;
  - residual r_j;
  - compact transform evaluation constant C_K;
  - projection tail;
  - normalization error;
  - exact same-family object and coordinate crosswalk.

Forbidden:
  - exact ground equals trial;
  - numerical finite-gap extrapolation as a cofinal theorem;
  - trial-to-Xi convergence applied to the ground without tracking;
  - real-zero property transferred from the ground to the trial;
  - changing family, normalization or subsequence between suppliers.
```

## META CLOSEOUT

**What became smaller?**

The apparent contradiction was reduced to one distinction:

```text
complete route map != complete proof.
```

The missing proof content is one macro-bridge with a precise quantitative error ledger.

**What was killed?**

The interpretation that the previously drawn chain meant every arrow was already proved.

**What must not be tried again?**

Do not compose real-zero facts and convergence facts from different families.
Do not revive exact ground equals trial.

**Current smallest named gap:**

```text
GroundStateToTrialSameFamilyBridge
```

with quantitative core:

```text
C_K * ||r_j|| / Delta_j + Tail_j(K) + NormalizationError_j(K) -> 0.
```

**Next cheapest decisive test:**

Audit the current G1 outputs and determine whether they already provide a true complement
floor for the same projected trial. If not, name the exact missing cofinal floor theorem.

**Fate of prior prediction:**

```text
ZeroEscape is the final lever:
  CONFIRMED.

The remaining work was only left-bank source locking:
  REFUTED.

The main remaining wall is same-family ground-to-trial tracking:
  CONFIRMED.
```

```yaml
iteration:
  target: reconcile full Route B chain with missing span
  status: PROGRESS
  failed_strategy: treat dependency graph as theorem-complete proof
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GroundStateToTrialSameFamilyBridge
  invariant_learned: real-zero and convergence properties must inhabit one normalized cofinal family
  forbidden_future_move: compose distinct ground and trial families without quantitative tracking
  next_decisive_test: audit true cofinal complement floor and residual suppliers
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
