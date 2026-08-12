# STATUS: OPEN — M1B WEAK RATIFIED; ISOLATED REPORT COMMIT AUTHORIZED; PARITY-WEIGHTED REPAIR SELECTED BEFORE FESHBACH
```yaml
PRIMARY: COMMIT_M1B_WEAK_REPORT_BUNDLE
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_HEAD: 8c3aec96
  BASE_HEAD_SOURCE: OWNER_REPORTED
  STRICT_STARTUP: P9_STRICT_PASS
  JUDGE_REHASHED_UNTRACKED_ARTIFACTS: false

M1B:
  STATUS: WEAK
  CLASSIFICATION_RATIFIED: true
  SQRT_U_RAYLEIGH: 0.007974761644
  U_RAYLEIGH: 6.359682328e-5
  SOURCE_RESIDUAL_NU: 4.851502174e-30
  PERSISTED_Q_PARITY_DEFECT: 3.438401150e-30
  DELTA_EVEN_USED: false
  DENOMINATOR_USED: ISOLATION_GAP
  MATVEC_AGREEMENT: 1.32e-131
  PLANTS: 5_OF_5_PASS
  INDEPENDENT_VALIDATOR: PASS
  SCOPE: FINITE_CELL
  VERIFIER: CONDITIONAL

COMPARISON:
  OBSERVED_PROJECTIVE_DEFECT: 4.691882549929e-9
  OBSERVED_PROJECTIVE_DISTANCE: 6.849731783018e-5
  U_OVER_OBSERVED_DEFECT: 13554.64946
  SQRT_U_OVER_OBSERVED_DISTANCE: 116.42444

PREDICTION_FATE:
  P058_M1R_1_DISTANCE_BELOW_1E3: REFUTED
  P058_M1R_2_EXACT_PARITY_PERMITS_EVEN_GAP: NOT_ESTABLISHED
  P058_M1R_3_TWO_SOURCE_MATVECS_AGREE: CONFIRMED
  P058_M1R_4_FESHBACH_SHARPER_IF_WEAK: UNTESTED_SELECTED_AS_BACKUP

COMMIT:
  AUTHORIZED: true
  TYPE: ISOLATED_REPORT_BUNDLE
  EXACT_FILE_COUNT: 4
  LEAN_SOURCE_CHANGES: false
  ROUTE_STATE_CHANGES: false
  BUS_CHANGES: false
  PROTOCOL_CHANGES: false
  PUSH_TO_ORIGIN_RH_CLEAN: true
  MESSAGE: "[MacOS][rh_clean][RouteB] Record Goal 058 M1B weak residual-gap control cell"

NEXT_REPRESENTATIONS:
  SELECTED_FIRST:
    ID: G3_M1C_PARITY_WEIGHTED_SECTOR_BOUND_PREFLIGHT
    KILL_POWER: 5
    COST: 1
    EXECUTION_AUTHORIZED_NOW: false
    REASON: tiny odd component can be budgeted explicitly without post-hoc symmetrizing q
  BACKUP:
    ID: G3_M1D_TRIAL_LINE_FESHBACH_PREFLIGHT
    KILL_POWER: 5
    COST: 3
    EXECUTION_AUTHORIZED_NOW: false
    TRIGGER: M1C_REMAINS_WEAK_OR_INVALID

G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C07_PROBABILITY_WEIGHTED_ESTIMATE
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

## ROUTE MAP

| Route | Exact statement | Kill-power | Cost | Status |
|---|---|---:|---:|---|
| **M1B scalar isolation-gap bound** | \(d_{\rm proj}\le \alpha/\Delta_{\rm iso}\) | 4/5 | 1/5 | **WEAK, CLOSED AS MEASUREMENT** |
| **M1C parity-weighted sector bound** | Budget the actual odd mass, then use the next-even gap only on the even complement. | 5/5 | 1/5 | **SELECTED NEXT AFTER COMMIT** |
| **M1D trial-line Feshbach** | Decompose \(\mathbb Cq\oplus q^\perp\); certify complement floor and coupling. | 5/5 | 3/5 | Backup |
| Larger \(m,N\) grid | Repeat observed overlaps without improving the theorem-facing mechanism. | 2/5 | 3/5 | Rejected now |

The result is not negative evidence against ground-to-trial tracking.

It is evidence that the **single scalar isolation denominator** loses too much geometry.

`[FINITE_CELL][CONDITIONAL]`

## EXACT INTERPRETATION OF M1B

The registered classification was:

```text
STRONG:
  certified distance <= 1e-3

WEAK:
  1e-3 < certified distance <= 1e-1
```

The result

\[
0.007974761644
\]

is therefore unambiguously **WEAK**.

The observed distance is

\[
6.849731783018\times10^{-5}.
\]

The certified radius is approximately

\[
116.42444
\]

times larger.

The squared bound is approximately

\[
13554.64946
\]

times the observed projective defect.

This does not invalidate the bound. It identifies its loss.

`[FINITE_CELL][CONDITIONAL]`

The source residual

\[
\nu=4.851502174\times10^{-30}
\]

is extremely small. However, a small residual without a usable source-faithful separation does not itself imply tracking. The route has already separated a small Rayleigh value, a small residual, and a ground-tracking theorem as different objects.

`[ABSTRACT][PAPER]`

## WHY FULL FESHBACH IS NOT THE CHEAPEST NEXT TEST

The persisted vector is not exactly even at the numerical representation level:

\[
\operatorname{parityDefect}(q)
=
3.438401150\times10^{-30}.
\]

Therefore M1B correctly refused to use \(\Delta_{\rm even}\).

But this does not force use of the smaller global isolation gap.

Let:

\[
q_+ = \frac{q+Jq}{2},
\qquad
q_- = \frac{q-Jq}{2}.
\]

Assume:

1. \(KJ=JK\);
2. the global ground vector \(\xi_0\) is even;
3. the next-even gap satisfies
   \[
   \Delta_+>0.
   \]

Then:

\[
1-|\langle \xi_0,q\rangle|^2
=
\|q_-\|^2
+
\|P_{H_+\cap\xi_0^\perp}q_+\|^2.
\]

The even-complement term obeys:

\[
\|P_{H_+\cap\xi_0^\perp}q_+\|^2
\le
\frac{a-\epsilon_0}{\Delta_+}.
\]

Hence:

\[
\boxed{
d_{\rm proj}
\le
\|q_-\|^2
+
\frac{a-\epsilon_0}{\Delta_+}.
}
\]

This theorem does not replace \(q\).

It does not symmetrize \(q\).

It charges the measured odd component explicitly, then uses the larger even-sector gap only where that gap is legal.

This is a **C07 scale-resolved repair** and respects **C09 precommit**.

`[FINITE_CELL][CONDITIONAL]`

An independent residual form is also available:

\[
\boxed{
d_{\rm proj}
\le
\|q_-\|^2
+
\left(
\frac{\|P_+(K-aI)q\|}
     {\epsilon_1^+-a}
\right)^2
}
\]

when the denominator has a positive lower enclosure.

The next preflight must use both formulas.

## REQUIRED SEMANTIC GUARD

The reported `parity defect` must be defined exactly.

The next report must distinguish:

```text
||Jq-q||
||q_-||
||q_-||^2
```

because:

\[
q_-=\frac{q-Jq}{2}.
\]

No threshold may be applied until this unit is locked.

A source theorem proving exact parity would be stronger, but it is not required for the parity-weighted inequality.

Post-hoc replacement

\[
q\mapsto\frac{q+Jq}{\|q+Jq\|}
\]

is forbidden unless a source theorem proves that this is the intended source trial.

## FINAL PROPOSAL

### Immediate owner action

Commit the four M1B artifacts.

Do not delete them.

A correctly planted **WEAK** result is a scientific output. Deleting it would erase:

- the first persisted exact source matvec;
- the independent matvec agreement;
- the envelope-direction plants;
- the exact reason the scalar denominator is insufficient.

### Next mathematical action after the new HEAD exists

Run:

\[
\boxed{
\texttt{G3\_M1C\_PARITY\_WEIGHTED\_SECTOR\_BOUND\_PREFLIGHT}
}
\]

on the same control cell.

Do not run a ladder.

Do not run full Feshbach yet.

### Registered M1C prediction

```yaml
P058_M1C_1:
  prediction: the parity-weighted even-sector bound restores STRONG classification
  threshold: sqrt(min_valid_upper) <= 1e-3
  confidence: 0.70

P058_M1C_2:
  prediction: the persisted parity defect is a representation/precision effect, not a substantive odd source component
  confidence: 0.80

P058_M1C_3:
  prediction: if M1C remains WEAK, trial-line Feshbach materially improves the bound
  confidence: 0.70
```

No threshold changes after the run.

## STRONGEST ATTACK

The strongest objection is:

> You saw that exact parity failed and then invented a way to use the even gap anyway.

The repair is legal only because it does **not** assert that \(q\) is even.

It proves a different inequality:

\[
\text{total defect}
=
\text{odd mass}
+
\text{even-complement defect}.
\]

The odd mass is paid directly.

Only the even-complement defect uses \(\Delta_+\).

If the implementation silently drops \(\|q_-\|^2\), replaces \(q\) by \(q_+\), or computes the gap in a different carrier, the result is killed by **C04/C09/C10**.

A second objection:

> The tiny parity defect may be below the input-data floor and therefore meaningless.

Correct. The M1C report must publish the source precision and interval enclosure for the odd mass. A decimal midpoint without an upper enclosure cannot occupy the odd-mass budget.

## CODEX DIRECTIVE

```text
TARGET:
  COMMIT_M1B_WEAK_REPORT_BUNDLE

AUTHORIZATION:
  explicit commit report authorization granted

BASE:
  HEAD = 8c3aec96
  branch = rh_clean

PRECONDITIONS:
  - worktree contains only the four expected untracked M1B files
    or any unrelated owner files remain unstaged
  - P9_STRICT_PASS
  - route status CHECK: OK

STAGE EXACTLY:

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_REPORT_2026-08-12.md

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_DATA_2026-08-12.json

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    exact_residual_gap_ground_to_trial_one_control_cell.py

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    validate_exact_residual_gap_ground_to_trial_one_control_cell.py

DO NOT STAGE:
  Lean files
  route state
  Bus files
  protocol
  manifests
  databases
  unrelated untracked files

VALIDATE:
  git diff --cached --check
  staged file count = 4
  staged paths equal the exact list above
  rerun the validator
  confirm all five plants retain their expected stop codes
  confirm report says:
    M1B = WEAK
    G1 = OPEN
    G3 = OPEN
    no route promotion
    no RH claim

COMMIT MESSAGE:
  [MacOS][rh_clean][RouteB] Record Goal 058 M1B weak residual-gap control cell

PUSH:
  origin rh_clean

AFTER PUSH:
  rerun strict startup
  rerun route status check
  require clean tree
  report the new full HEAD

SUCCESS:
  M1B_WEAK_REPORT_BUNDLE_COMMITTED

FAILURE:
  M1B_COMMIT_SCOPE_DRIFT
  M1B_VALIDATOR_REGRESSION
  M1B_PLANT_REGRESSION
  M1B_POST_COMMIT_TREE_NOT_CLEAN

STOP AFTER COMMIT.

Do not execute M1C or Feshbach in the same transaction.
```

## META CLOSEOUT

### What became smaller?

The vague statement

```text
the residual/gap route is weak
```

became:

```text
the scalar full-isolation denominator is weak;
the unresolved cheap repair is an exact odd-mass budget
plus an even-complement gap.
```

### What was killed?

- The prediction that M1B would certify distance below \(10^{-3}\).
- Using the next-even gap while silently assuming exact parity.
- Starting a larger \(m,N\) grid from a weak one-cell mechanism.
- Immediate full Feshbach before testing the cheaper sector decomposition.

### What must not be tried again?

Do not call a tiny decimal parity residual “exact parity”.

Do not symmetrize the precommitted source trial after seeing the spectrum.

Do not use observed ground overlap as a theorem-facing bound.

### Current smallest named gap

\[
\boxed{
\texttt{ParityWeightedEvenSectorGroundTrackingBound}
}
\]

### Next cheapest decisive test

Compute certified:

\[
U_{\rm sector}
=
\|q_-\|_U^2
+
\min\left(
\frac{\alpha_U}{\Delta_{+,L}},
\left(\frac{\nu_{+,U}}{s_{+,L}}\right)^2
\right)
\]

on `(13,120)`.

### Fate of prior predictions

```text
P058_M1R_1:
  REFUTED.

P058_M1R_2:
  NOT ESTABLISHED.
  Exact parity was not proved for the persisted vector.

P058_M1R_3:
  CONFIRMED.

P058_M1R_4:
  UNSCORED.
  Feshbach remains selected only if the cheaper M1C repair fails.
```

### Memory entry

```yaml
iteration:
  target: M1B_exact_residual_gap_control_cell
  status: PROGRESS
  failed_strategy: one_scalar_isolation_gap_for_a_nearly_even_trial
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: ParityWeightedEvenSectorGroundTrackingBound
  invariant_learned: approximate parity must be paid as odd mass; it does not authorize an even-sector denominator for the whole vector
  forbidden_future_move: posthoc_symmetrize_source_trial_or_drop_odd_mass
  next_decisive_test: parity_weighted_sector_bound_at_m13_N120
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
