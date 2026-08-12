# STATUS: OPEN — G2b CLOSED; SELECT G3 M1 EXACT RESIDUAL/GAP CONTROL-CELL AUDIT
```yaml
PRIMARY: RUN_G3_M1_EXACT_RESIDUAL_GAP_CONTROL_CELL
PRIMARY_COUNT: 1

PIN:
  HEAD: 8c3aec96
  TREE_CLEAN: true
  P9_STRICT_PASS: true
  PIN_SOURCE: OWNER_REPORTED_AND_STRICT_STARTUP_VALIDATED
  JUDGE_REHASHED_CURRENT_HEAD: false

ROUTE:
  STATE: CHALLENGER_NOT_RH
  CHECK: OK
  BUS_010: VOID
  ROUTE_PROMOTION: false
  RH_CLAIM: false

GOAL_058:
  STATUS: OPEN
  G2B:
    status: PROVED
    theorem: P59_GROUND_LAGRANGE_ZEROSET_BRIDGE_PROVED
    supplier: Proposition59GroundLagrangeZeroSetBridge_normalized
  G1:
    status: OPEN
    gap: COFINAL_FINITE_SIMPLE_EVEN_GROUND_PACKAGE
  G3:
    status: OPEN
    gap: FINITE_GROUND_TRANSFORM_TO_CCM_TRIAL_LOCALLY_UNIFORM

M1_CONTROL_CELL:
  m: 13
  N: 120
  projective_defect: 4.691882549929e-9
  projective_distance: 6.849731783018e-5
  independent_validator: PASS
  residual: NOT_MEASURED
  gap: NOT_MEASURED
  blocker: NO_PERSISTED_MFIN_MATVEC
  scope: FINITE_CELL
  verifier: NUMERIC_CROSSCHECK

DECISION:
  selected_front: G3
  selected_child: G3_M1B_EXACT_RESIDUAL_GAP_CONTROL_CELL
  G1: HOLD_AS_PARALLEL_FRONT_NOT_ABANDONED
  reason:
    - generic phase/projective/evaluation receivers already exist
    - observed projective closeness is diagnostic only
    - residual and true spectral separation are the missing theorem-facing inputs
    - the same run also measures the finite isolation data relevant to G1

TARGET:
  name: EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL
  cell: [13, 120]
  mode: READ_COMPUTE_REPORT
  Lean_edit: false
  route_state_edit: false

REQUIRED_OBJECTS:
  K: exact source-locked ccmWeilMatFinite(13,120)
  q: precommitted normalized projected CCM source trial
  xi0: lowest finite ground vector, crosscheck only
  J: exact reflection/parity involution
  mode_order: source-locked

REQUIRED_SCALARS:
  rayleigh_a: q_star_K_q
  residual_nu: norm(Kq - a*q)
  rayleigh_excess_alpha: a - epsilon0
  gap_even: epsilon1_even - epsilon0_even
  gap_odd: epsilon0_odd - epsilon0_even
  gap_isolation: min(gap_even, gap_odd)
  residual_separation: epsilon1_even - a

REQUIRED_BOUNDS:
  rayleigh_projective_upper: alpha_upper / gap_track_lower
  residual_projective_upper: (nu_upper / separation_lower)^2
  gap_track_rule:
    exact_even_q_and_KJ_eq_JK: use gap_even
    otherwise: use gap_isolation

PRECOMMIT_CLASSIFICATION:
  STRONG:
    sqrt(min(valid_upper_bounds)) <= 1e-3
  WEAK:
    1e-3 < sqrt(min(valid_upper_bounds)) <= 1e-1
  UNUSABLE:
    sqrt(min(valid_upper_bounds)) > 1e-1
  INVALID:
    no_positive_lower_gap_or_source_mismatch

SUCCESS: M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED
STOP: M1_SOURCE_MFIN_MATVEC_OR_GAP_CERTIFICATE_MISSING

NEXT_IF_STRONG:
  name: G3_RESIDUAL_GAP_PRECOMMITTED_LADDER
  authorization: NOT_GRANTED_BY_THIS_VERDICT

NEXT_IF_WEAK_OR_UNUSABLE:
  name: G3_TRIAL_LINE_FESHBACH_GRAPH_PREFLIGHT
  authorization: NOT_GRANTED_BY_THIS_VERDICT

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C07_PROBABILITY_WEIGHTED_ESTIMATE
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

| Route | Exact role | Kill-power | Cost | Decision |
|---|---|---:|---:|---|
| **R1 — residual / true-gap control cell** | Explain the measured ground–trial overlap from the exact source matrix and the precommitted trial. | 5/5 | 1/5 | **SELECTED** |
| **R2 — trial-line Schur/Feshbach graph** | Prove complement coercivity and small coupling around the source trial line. It can supply overlap and isolation together. | 5/5 | 3/5 | Backup if R1 is weak |
| **R3 — direct projective-distance ladder** | Measure overlap at more cells without a source mechanism. | 2/5 | 2/5 | Rejected now |
| **R4 — cofinal penalty package** | Attack G1 directly through simple-even finite certificates. | 5/5 | 4/5 | Hold until R1 classifies the shared spectral geometry |

The constructor infrastructure has done its current job.

Do not add another constructor layer now.

Use `lean-env-dump` and `comparator-lite` only to locate and verify the exact existing consumers.

## WHY THIS IS NEXT

The P59 theorem closes the finite zero-set transport once a finite ground package exists.

It does not construct that package.

The M1 control cell supplies a small observed projective defect:

\[
d_{\rm obs}
=
1-\left|\langle \xi_0,q\rangle\right|^2
=
4.691882549929\cdot10^{-9}.
\]

Its square root is the reported projective distance:

\[
\sqrt{d_{\rm obs}}
=
6.849731783018\cdot10^{-5}.
\]

This agreement checks the reported convention.

It does not explain why the vectors are close.

The existing generic H3 receiver uses a complementary spectral gap to bound projective defect by Rayleigh excess.

Therefore the first missing source data are:

\[
a=\langle Kq,q\rangle,
\qquad
r=(K-aI)q,
\qquad
\alpha=a-\epsilon_0,
\qquad
\Delta.
\]

The current report explicitly lacks the source matrix-vector product needed for these quantities.

## EXACT MATHEMATICAL AUDIT

Let:

\[
K=\operatorname{ccmWeilMatFinite}(13,120).
\]

Let \(q\) be the source projected trial.

Normalize it before reading the spectrum:

\[
\|q\|_2=1.
\]

Define:

\[
a=q^*Kq,
\qquad
r=Kq-aq,
\qquad
\nu=\|r\|_2.
\]

Use exact parity decomposition.

Let:

\[
\epsilon_0^+
\]

be the bottom even eigenvalue.

Let:

\[
\epsilon_1^+
\]

be the next even eigenvalue.

Let:

\[
\epsilon_0^-
\]

be the bottom odd eigenvalue.

Define:

\[
\Delta_{\rm even}
=
\epsilon_1^+-\epsilon_0^+,
\]

\[
\Delta_{\rm odd}
=
\epsilon_0^--\epsilon_0^+,
\]

\[
\Delta_{\rm iso}
=
\min(\Delta_{\rm even},\Delta_{\rm odd}).
\]

The full finite simple-even isolation input uses \(\Delta_{\rm iso}\).

The ground-to-trial estimate may use \(\Delta_{\rm even}\) only after proving:

\[
Jq=q,
\qquad
JK=KJ.
\]

Otherwise it must use the full complement gap.

### Rayleigh-excess bound

Let:

\[
\alpha=a-\epsilon_0^+.
\]

Then the existing spectral-weight argument has the form:

\[
d_{\rm proj}
\le
\frac{\alpha}{\Delta_{\rm track}}.
\]

For interval data use:

\[
\alpha_U=a_U-\epsilon_{0,L}^+,
\]

\[
\Delta_{{\rm even},L}
=
\epsilon_{1,L}^+-\epsilon_{0,U}^+.
\]

### Independent residual bound

If:

\[
s_L=\epsilon_{1,L}^+-a_U>0,
\]

then:

\[
d_{\rm proj}
\le
\frac{\nu_U^2}{s_L^2}.
\]

This is an independent judge.

The two bounds need not have the same sharpness.

They must refer to the same \(K\), \(q\), mode order, and normalization.

## REGISTERED PREDICTIONS

```yaml
P058_M1R_1:
  prediction: the source residual/gap mechanism certifies projective distance below 1e-3
  confidence: 0.75

P058_M1R_2:
  prediction: exact parity permits the tracking denominator to use the next-even gap
  confidence: 0.90

P058_M1R_3:
  prediction: direct dense matvec and independent source-component matvec agree within the certified enclosure
  confidence: 0.95

P058_M1R_4:
  prediction: if the residual/gap bound is weak, a trial-line Feshbach graph is materially sharper
  confidence: 0.65
```

Do not change these thresholds after seeing the result.

## FINAL PROPOSAL

Run one bounded child under Goal 058:

\[
\boxed{
\texttt{G3\_M1B\_EXACT\_RESIDUAL\_GAP\_CONTROL\_CELL}
}
\]

Do not start a new global proof branch.

Do not start a cofinal grid.

Do not formalize a new generic residual theorem.

The generic phase, Rayleigh/projective, and compact-evaluation machinery already exists.

The transaction must provide the missing source instantiation at `(13,120)`.

A **STRONG** result authorizes a later precommitted \(N\)- and \(m\)-ladder proposal.

It does not itself prove G1, G3, or a cofinal statement.

A **WEAK** or **UNUSABLE** result selects the Schur/Feshbach representation before any larger computation.

## STRONGEST ATTACK

The observed projective distance could be real and still be useless for proof.

A numerical eigensolver directly compares \(q\) with the computed ground vector.

That comparison already knows the answer.

It does not provide a source-side reason for the closeness.

The route needs a bound constructed from:

\[
K,
\quad
q,
\quad
\|Kq-aq\|,
\quad
\text{and a certified spectral separation}.
\]

Using the computed ground vector to define or improve \(q\) is a **C09** failure.

Using a next-even gap without exact parity invariance is a **C04** category error.

Using a fitted overlap as a substitute for a residual theorem is a **C10** surrogate error.

A small denominator can destroy the estimate. This is the **C07** attack.

## CODEX DIRECTIVE

```text
TARGET:
  G3_M1B_EXACT_RESIDUAL_GAP_CONTROL_CELL

PARENT:
  Goal 058

MODE:
  bounded compute + report
  no Lean production edit
  no route-state edit
  no Bus goal
  no route promotion

PIN:
  HEAD = origin/rh_clean = 8c3aec96
  require clean tree
  require P9_STRICT_PASS before work

CONTROL CELL:
  m = 13
  N = 120

INPUTS:
  - exact matrix object used by ccmWeilMatFinite 13 120
  - the exact source projected trial coefficient vector used in the M1 report
  - exact mode order
  - exact reflection involution
  - the independently computed ground vector only for comparison

TASK 1 — PERSIST THE SOURCE MATVEC:
  Persist enough source data to reproduce:
    K q
  without using the ground vector.

  Produce two implementations:
    A. direct dense matrix-vector multiplication;
    B. independent multiplication assembled from source matrix components.

  Require agreement under precision doubling.

TASK 2 — COMPUTE THE THEOREM-FACING DATA:
  q := source trial normalized to ||q||_2 = 1
  a := q* K q
  r := K q - a q
  nu := ||r||_2

  Compute certified enclosures for:
    epsilon0_even
    epsilon1_even
    epsilon0_odd

  Derive lower enclosures:
    Delta_even
    Delta_odd
    Delta_iso

  Derive:
    alpha = a - epsilon0_even
    separation = epsilon1_even - a

TASK 3 — APPLY TWO INDEPENDENT BOUNDS:
  Rayleigh:
    U_rayleigh = alpha_upper / Delta_track_lower

  Residual:
    U_residual = (nu_upper / separation_lower)^2

  Use Delta_even only if exact checks establish:
    Jq = q
    JK = KJ

  Otherwise use Delta_iso where required.

TASK 4 — COMPARE WITH THE EXISTING M1 OBSERVATION:
  observed projective defect:
    4.691882549929e-9

  observed projective distance:
    6.849731783018e-5

  Report:
    bound / observed-defect ratio
    square-root bound
    precision stability
    solver independence
    exact object hashes

MANDATORY PLANTS:

  P-M1R-1_POSTHOC_Q:
    replace q by the computed ground vector.
    Required rejection:
      M1_SOURCE_TRIAL_PRECOMMIT_VIOLATION

  P-M1R-2_MODE_ORDER:
    reverse or shift the source mode order in only one matvec implementation.
    Required rejection:
      M1_SOURCE_MFIN_MODE_ORDER_MISMATCH

  P-M1R-3_PARITY_DENOMINATOR:
    use Delta_even after disabling Jq=q or JK=KJ.
    Required rejection:
      M1_TRACKING_GAP_PARITY_UNJUSTIFIED

  P-M1R-4_INTERVAL_DIRECTION:
    use a gap upper bound as denominator lower bound,
    or use a residual lower bound as an upper certificate.
    Required rejection:
      M1_RESIDUAL_GAP_ENVELOPE_DIRECTION_ERROR

  P-M1R-5_GROUND_ORACLE:
    construct Kq from the eigendecomposition instead of the source matrix.
    Required rejection:
      M1_MATVEC_GROUND_ORACLE_SURROGATE

VALIDATION:
  - strict startup
  - source hash report
  - precision ladder, at least three levels
  - independent matvec comparison
  - independent eigensolver or eigenpair-residual validator
  - exact parity checks
  - verify sqrt(projective_defect) equals the reported distance
  - git diff --check
  - clean final tree unless owner explicitly authorizes report commit

OUTPUTS:
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_DATA_2026-08-12.json

  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_REPORT_2026-08-12.md

SUCCESS:
  M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED

FAILURE:
  M1_SOURCE_MFIN_MATVEC_MISSING
  M1_SOURCE_TRIAL_OBJECT_MISMATCH
  M1_GAP_CERTIFICATE_MISSING
  M1_PARITY_CROSSWALK_MISSING
  M1_RESIDUAL_GAP_BOUND_INCONSISTENT
  M1_PRECISION_OR_VALIDATOR_DISAGREEMENT

FORBIDDEN:
  - no fitted normalization
  - no q chosen after spectrum inspection
  - no float64 route verdict
  - no cofinal claim
  - no G1 closure claim
  - no G3 closure claim
  - no RH claim
  - no Route B promotion
  - no new generic Lean theorem
```

## META CLOSEOUT

### What became smaller?

Before this iteration, G3 had an observed overlap but no theorem-facing cause.

The gap is now:

\[
\boxed{
\texttt{PersistedSourceMatvec}
+
\texttt{CertifiedResidual}
+
\texttt{CertifiedComplementGap}
}
\]

at one exact control cell.

### What was killed?

The next action is not:

- another P59 theorem;
- another constructor layer;
- a larger projective-distance grid;
- direct cofinal extrapolation from one cell;
- a post-hoc optimized trial.

### What must not be tried again?

Do not treat numerical projective overlap as a proof of ground-to-trial tracking.

Do not replace the true spectral denominator by a prolate proxy.

Do not use only the next-even gap without exact parity.

### Current smallest named gap

\[
\boxed{
\texttt{M1SourceResidualGapControlCell}
}
\]

### Next cheapest decisive test

Persist and validate the exact source matrix-vector product at `(13,120)`.

### Fate of prior registered predictions

```text
P-GS1 / P59 lattice zero-set transfer:
  CONFIRMED by the proved normalized supplier.

P-C3 control-cell projective residual:
  CONFIRMED as calibration evidence.

Residual/gap mechanism:
  UNSCORED because the required source data were not measured.
```

### Memory entry

```yaml
iteration:
  target: Goal058_after_P59_and_M1_control_cell
  status: OPEN
  failed_strategy: infer_tracking_from_observed_projective_overlap
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: M1SourceResidualGapControlCell
  invariant_learned: the source trial must be fixed before the spectrum and the tracking denominator must match the exact parity sector
  forbidden_future_move: use computed ground overlap or prolate proxy as the cofinal tracking proof
  next_decisive_test: persist Kq and certify residual plus even/odd complement gaps at m13_N120
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
