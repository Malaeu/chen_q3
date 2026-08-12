# STATUS: OPEN — M1B COMMIT RATIFIED; M1C PARITY-SECTOR PREFLIGHT AUTHORIZED
```yaml
PRIMARY: RUN_G3_M1C_PARITY_SECTOR_BOUND_PREFLIGHT
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: c17a115713a856666533a069fe3c4d2ae5afa527
  ORIGIN_HEAD_EQUALS_HEAD: OWNER_REPORTED
  TREE_CLEAN: OWNER_REPORTED
  STRICT_STARTUP: P9_STRICT_PASS
  ROUTE_CHECK: OK

M1B_TRANSACTION:
  code: M1B_WEAK_REPORT_BUNDLE_COMMITTED
  validator: PASS
  plants: 5_OF_5_PASS
  classification: WEAK
  scope: FINITE_CELL
  verifier: CONDITIONAL
  reopen_M1B: false

M1C:
  target: G3_M1C_PARITY_SECTOR_BOUND_PREFLIGHT
  execution_authorized: true
  mode: READ_COMPUTE_REPORT
  control_cell: [13, 120]
  lean_production_edit: false
  route_state_edit: false
  bus_edit: false
  commit_authorized: false

MAIN_IDEA:
  total_projective_defect:
    - actual_odd_mass
    - even_complement_defect
  even_gap_applies_only_to: even_complement
  persisted_q_replaced_or_symmetrized: false

REQUIRED_BOUNDS:
  rayleigh:
    U_sector_rayleigh: omega_upper + alpha_plus_upper / delta_even_lower
  residual:
    U_sector_residual: omega_upper + (nu_plus_upper / separation_plus_lower)^2
  final:
    U_sector: min_of_valid_bounds

CLASSIFICATION:
  STRONG: sqrt_U_sector_le_1e_minus_3
  WEAK: 1e_minus_3_lt_sqrt_U_sector_le_1e_minus_1
  UNUSABLE: sqrt_U_sector_gt_1e_minus_1
  INVALID: missing_exact_sector_or_positive_lower_envelope

NEXT_IF_STRONG:
  target: G3_M2_PRECOMMITTED_RESIDUAL_GAP_LADDER
  authorized_now: false

NEXT_IF_WEAK_OR_UNUSABLE:
  target: G3_M1D_TRIAL_LINE_FESHBACH_PREFLIGHT
  authorized_now: false

G1: OPEN
G3: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
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

| Route | Computing object | Kill-power | Cost | Status |
|---|---|---:|---:|---|
| **M1C parity-sector bound** | \(q=q_++q_-\), exact odd-mass budget, even complement gap | 5/5 | 1/5 | **SELECTED** |
| **M1D trial-line Feshbach** | \(\mathbb Cq\oplus q^\perp\), complement floor and coupling | 5/5 | 3/5 | Backup |
| Larger cell ladder | Repeats a weak scalar mechanism | 2/5 | 3/5 | Forbidden now |
| Post-hoc symmetrized trial | Changes the precommitted source witness | 0/5 | — | Killed |

`M1B` is frozen. Its report is useful precisely because it shows that the full isolation gap loses too much geometry while the source residual remains extremely small.

`[FINITE_CELL][CONDITIONAL]`

## MATHEMATICAL TARGET

Let \(J\) be the exact reflection involution and let \(KJ=JK\).

For the persisted normalized source trial \(q\), define

\[
q_+ := \frac{q+Jq}{2},
\qquad
q_- := \frac{q-Jq}{2}.
\]

Do not replace \(q\) by \(q_+\).

Let \(\xi_0\) be the global finite ground vector. Before using the even sector, certify

\[
\epsilon_0^+ < \epsilon_0^-,
\]

so the global ground state is even.

Then orthogonality of the parity sectors gives

\[
1-|\langle \xi_0,q\rangle|^2
=
\|q_-\|^2
+
\|P_{H_+\cap\xi_0^\perp}q_+\|^2.
\]

Define

\[
\omega := \|q_-\|^2.
\]

Let

\[
\Delta_+ := \epsilon_1^+-\epsilon_0^+.
\]

Define the even-sector Rayleigh excess without charging the odd sector:

\[
\alpha_+
:=
\langle q_+,Kq_+\rangle
-
\epsilon_0^+\|q_+\|^2.
\]

Then

\[
\boxed{
d_{\rm proj}
\le
\omega+\frac{\alpha_+}{\Delta_+}.
}
\]

For the independent residual judge, let

\[
a_+
:=
\frac{\langle q_+,Kq_+\rangle}{\|q_+\|^2},
\]

\[
r_+:=(K-a_+I)q_+,
\qquad
\nu_+:=\|r_+\|.
\]

If

\[
s_+:=\epsilon_1^+-a_+>0,
\]

then

\[
\boxed{
d_{\rm proj}
\le
\omega+\left(\frac{\nu_+}{s_+}\right)^2.
}
\]

Both formulas preserve the original source witness.

`[ABSTRACT][PAPER]`

## PHASE ZERO — PARITY UNIT LOCK

The previous report contains a number called a parity defect.

Before any use, classify it exactly as one of:

```text
norm_Jq_sub_q:
  ||Jq-q||

odd_norm:
  ||q_-||

odd_mass:
  ||q_-||²
```

Use

\[
q_-=(q-Jq)/2
\]

to convert between these quantities.

A midpoint decimal is not a certificate. Produce an upper enclosure for \(\omega\).

Also distinguish:

```text
source parity theorem:
  exact mathematical statement about the intended trial;

persisted parity residual:
  numerical representation error of the stored vector.
```

If an exact source theorem proves the trial is even, report it. Do not silently replace the persisted data.

## REGISTERED PREDICTIONS

```yaml
P058_M1C_1:
  prediction: parity-sector bound is STRONG
  threshold: sqrt_U_sector_le_1e_minus_3
  confidence: 0.70

P058_M1C_2:
  prediction: certified odd-mass contribution is negligible relative to 1e_minus_6
  confidence: 0.95

P058_M1C_3:
  prediction: even-sector separation explains most of the improvement over M1B
  confidence: 0.80

P058_M1C_4:
  prediction: if M1C remains WEAK, trial-line Feshbach gives a materially sharper theorem-facing bound
  confidence: 0.70
```

Do not alter thresholds or predictions after seeing the result.

## FINAL PROPOSAL

Run one bounded preflight at `(13,120)`.

Reuse the persisted M1B source matrix and source trial.

Do not create a larger grid.

Do not edit Lean.

Do not commit the report without a separate owner authorization.

A **STRONG** M1C result justifies a later, separately precommitted \(m,N\)-ladder for the parity-sector quantities.

A **WEAK** or **UNUSABLE** result selects the trial-line **Schur/Feshbach** representation.

## STRONGEST ATTACK

The repair can be faked in three ways.

### 1. Dropping the odd mass

Using \(\Delta_+\) for all of \(q\) is invalid.

The exact odd budget \(\omega\) must remain in the bound.

### 2. Replacing the witness

The map

\[
q\mapsto\frac{q+Jq}{\|q+Jq\|}
\]

changes the persisted witness unless a source theorem identifies this vector with the intended source trial.

That is a **C09** failure.

### 3. Assuming the global ground is even

Commutation \(KJ=JK\) only decomposes the space.

It does not by itself prove that the lowest global eigenvalue lies in the even sector.

The ordering

\[
\epsilon_0^+<\epsilon_0^-
\]

requires a certified enclosure.

## CODEX DIRECTIVE

```text
TARGET:
  G3_M1C_PARITY_SECTOR_BOUND_PREFLIGHT

PIN:
  repo = /Users/emalam/GitHub/rh_lean_01_2026
  branch = rh_clean
  HEAD = origin/rh_clean =
    c17a115713a856666533a069fe3c4d2ae5afa527

ABORT:
  if HEAD differs;
  if tree is dirty before work;
  if P9_STRICT_PASS fails;
  if Route B status is not CHECK: OK.

MODE:
  bounded read/compute/report transaction;
  no production Lean edit;
  no protocol edit;
  no Bus edit;
  no Route B state edit;
  no commit.

INPUTS:
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_REPORT_2026-08-12.md

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_DATA_2026-08-12.json

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    exact_residual_gap_ground_to_trial_one_control_cell.py

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    validate_exact_residual_gap_ground_to_trial_one_control_cell.py

TASK 1 — LOCK PARITY SEMANTICS:
  Identify the exact meaning of the persisted parity-defect field.

  Compute certified enclosures for:
    ||Jq-q||
    ||q_-||
    omega = ||q_-||²

  Verify:
    q_plus + q_minus = q
    <q_plus,q_minus> = 0
    ||q||² = ||q_plus||² + ||q_minus||²

  Verify exact source identities:
    J*J = I
    KJ = JK

  Locate any existing source theorem asserting exact evenness
  of the intended projected trial.
  Report it, but do not mutate q.

TASK 2 — CERTIFY SECTOR ORDER:
  Compute certified enclosures for:
    epsilon0_even
    epsilon1_even
    epsilon0_odd

  Require:
    epsilon0_even_upper < epsilon0_odd_lower
    epsilon0_even_upper < epsilon1_even_lower

  Derive:
    Delta_even_lower =
      epsilon1_even_lower - epsilon0_even_upper

TASK 3 — RAYLEIGH SECTOR BOUND:
  Compute:
    alpha_plus =
      <q_plus,K q_plus>
      - epsilon0_even * ||q_plus||²

  Use directed enclosures:
    U_sector_rayleigh =
      omega_upper
      + alpha_plus_upper / Delta_even_lower

TASK 4 — RESIDUAL SECTOR BOUND:
  Compute:
    a_plus =
      <q_plus,K q_plus> / ||q_plus||²

    r_plus =
      K q_plus - a_plus q_plus

    nu_plus =
      ||r_plus||

    separation_plus_lower =
      epsilon1_even_lower - a_plus_upper

  If separation_plus_lower > 0:
    U_sector_residual =
      omega_upper
      + (nu_plus_upper / separation_plus_lower)^2
  else:
    mark this judge invalid;
    do not force a result.

TASK 5 — CLASSIFY:
  U_sector =
    minimum of valid upper bounds

  STRONG:
    sqrt(U_sector) <= 1e-3

  WEAK:
    1e-3 < sqrt(U_sector) <= 1e-1

  UNUSABLE:
    sqrt(U_sector) > 1e-1

  INVALID:
    no valid positive lower separation
    or source/parity mismatch.

  Compare with:
    M1B sqrt(U_rayleigh)
    observed projective distance

  Ground-vector overlap remains validator-only.

MANDATORY PLANTS:

  P-M1C-1_DROP_ODD_MASS:
    delete omega.
    Required:
      M1C_ODD_MASS_DROPPED

  P-M1C-2_POSTHOC_SYMMETRIZE:
    replace q by normalized q_plus.
    Required:
      M1C_SOURCE_TRIAL_REPLACED

  P-M1C-3_UNCERTIFIED_GROUND_PARITY:
    use the even gap without proving
      epsilon0_even < epsilon0_odd.
    Required:
      M1C_GLOBAL_GROUND_SECTOR_UNJUSTIFIED

  P-M1C-4_PARITY_UNIT_CONFUSION:
    treat ||Jq-q|| as ||q_-||².
    Required:
      M1C_PARITY_DEFECT_UNIT_MISMATCH

  P-M1C-5_MIDPOINT_AS_ENVELOPE:
    use a decimal midpoint as omega_upper.
    Required:
      M1C_ODD_MASS_UPPER_ENVELOPE_MISSING

  P-M1C-6_GROUND_ORACLE:
    use the computed ground vector to alter q_plus,
    a_plus, or the sector decomposition.
    Required:
      M1C_GROUND_ORACLE_SURROGATE

VALIDATION:
  - precision ladder at the same levels as M1B;
  - direct and independent source matvec agreement;
  - independent sector-eigenvalue validator;
  - all six plants produce exact stop codes;
  - route status remains CHECK: OK;
  - final tree remains clean except the two new untracked reports.

OUTPUTS:
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_DATA_2026-08-12.json

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md

SUCCESS:
  M1C_PARITY_SECTOR_CONTROL_CELL_CLASSIFIED

FAILURE:
  M1C_PARITY_SEMANTICS_UNRESOLVED
  M1C_SOURCE_PARITY_OBJECT_MISMATCH
  M1C_GLOBAL_GROUND_SECTOR_UNJUSTIFIED
  M1C_EVEN_GAP_LOWER_ENVELOPE_MISSING
  M1C_SECTOR_BOUND_INCONSISTENT
  M1C_VALIDATOR_OR_PRECISION_DISAGREEMENT

STOP:
  after writing and validating the two reports.

Do not:
  run Feshbach;
  run a cell ladder;
  commit;
  edit Lean;
  claim G1 or G3 closure;
  promote Route B;
  claim RH.
```

## META CLOSEOUT

### What became smaller?

`M1B` showed that one scalar isolation gap is too coarse.

The next unknown is now exactly:

\[
\boxed{
\texttt{ParityWeightedEvenSectorGroundTrackingBound}.
}
\]

### What was killed?

- Reopening M1B.
- Launching a larger grid with the weak denominator.
- Immediate full Feshbach.
- Silent symmetrization of the source trial.

### What must not be tried again?

Do not interpret approximate parity as exact parity.

Do not apply an even-sector gap to the odd component.

Do not use the ground vector to construct the witness being tested.

### Current smallest named gap

\[
\boxed{
\texttt{M1CParitySectorControlCell}.
}
\]

### Next cheapest decisive test

Evaluate the certified odd mass and the two even-sector upper bounds on `(13,120)`.

### Fate of prior predictions

```text
P058_M1R_1:
  REFUTED.

P058_M1R_2:
  NOT ESTABLISHED.

P058_M1R_3:
  CONFIRMED.

P058_M1R_4:
  STILL UNTESTED.
  Feshbach remains the backup, not the immediate move.
```

### Memory entry

```yaml
iteration:
  target: post_commit_M1B_weak
  status: OPEN
  failed_strategy: full_isolation_gap_for_nearly_even_trial
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: M1CParitySectorControlCell
  invariant_learned: the exact odd mass must be paid before the even-sector gap can be used
  forbidden_future_move: silently_symmetrize_q_or_drop_the_odd_sector
  next_decisive_test: parity_sector_bound_at_m13_N120
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
