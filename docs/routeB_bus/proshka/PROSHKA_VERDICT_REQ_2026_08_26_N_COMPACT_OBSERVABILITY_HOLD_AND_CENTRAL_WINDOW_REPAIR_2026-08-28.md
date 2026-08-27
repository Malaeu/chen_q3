# STATUS: OPEN — FINITE-CELL OBSERVABILITY RATIFIED; COFINAL WINDOW CLAIMS REPAIRED; CENTRAL GRAPH-RESOLVENT MASS IS THE NEXT GAP

```yaml
PRIMARY: RATIFY_FINITE_OBSERVABILITY_AND_REPAIR_COFINAL_WINDOW_CLAIMS
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  CORRECTION_COMMIT: 94a01da5244b7a7675c7e79bdde0e1c946e447c2
  CORRECTION_PATH: docs/routeB_bus/LINUX_CORRECTION_13_NONZERO_IS_NOT_A_RATE_GOAL058_2026-08-28.md
  CORRECTION_BLOB: d8eac31af5382a95af13b53b07eb148845776d73
  REPORT_COMMIT: 4c6956a93e8619cbd93ee8990a6397ec67921b3d
  REPORT_PATH: docs/routeB_bus/LINUX_ZERO_TRANSFER_COMPACT_OBSERVABILITY_PREFLIGHT_GOAL058_2026-08-28.md
  REPORT_BLOB: daef5df2d6f7fab2561d0e3f2c33c3f012fe9558
  REPORT_LINES: 166
  REPORT_WAS_BRANCH_HEAD_AT_ADJUDICATION: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_PROBE_PERFORMED: false
  ARISTOTLE_USED: false
  CODEX_USED: false
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: HOLD
  REPORTED_CODE: ZERO_TRANSFER_EXACT_WITHOUT_QUANTITATIVE_COMPACT_OBSERVABILITY
  DECISION: HOLD_REPAIRED

  CORRECTION_13: RATIFIED
  EXACT_NONANNIHILATION_IS_A_RATE: false
  GRAPH_SOLVE_SUPPLIES_LOWER_BOUND: false
  GLOBAL_SPAN_IS_COMPACT_OBSERVABILITY: false
  NO_SUPPLIER_FOUND_IS_EVIDENCE: false

  FINITE_CELL_OBSERVABILITY_POSITIVITY: PAPER_PASS_WITH_SOURCE_ASSUMPTIONS
  WINDOWED_CAUCHY_TRANSFORM_REPRESENTATION: PAPER_PASS
  SELECTED_SCHEDULE_WINDOW_SITE_COUNT_O_LOG_M: PAPER_PASS

  GENERIC_WORST_DIRECTION_UPPER_BOUND: NOT_ESTABLISHED
  OBS_M_K_TENDS_TO_ZERO: NOT_ESTABLISHED
  REASON_GENERIC_BOUND_FAILS: >-
    The report estimates a localized Cauchy coefficient vector but the observation
    infimum is parametrized by unit v with transformed vector u=C^{-1}v on q-perp.
    Selecting u=e_j requires v=C e_j and the missing normalization ||C e_j||;
    selecting v=e_j leaves C^{-1}e_j uncontrolled.  The graph operator cannot be
    dropped from a cofinal upper or lower envelope.

  SELECTED_Q_LOW_MODE_LOCALIZATION_FROM_ODD_MASS: REFUTED_AS_OBJECT_MISMATCH
  SELECTED_PHI_LOW_MODE_LOCALIZATION: NOT_PROVED
  GRAPH_RESOLVENT_PRESERVES_LOCALIZATION: NOT_PROVED
  ACTUAL_SPECIFIC_CAUCHY_VECTOR: "u_m,rho = C_m^(-1) Q_m Phi_m(a_rho)"

  GROWING_QUARTET_CRITERION_SECTION_5: NOT_RATIFIED_DOMAIN_MISMATCH
  MAXIMAL_REAL_PART_ALMOST_PERIODICITY_SECTION_6: HEURISTIC_QUARANTINED

  ARITHMETIC_GATE_CLOSED_NEGATIVE: false
  TRACKING_CORRIDOR_THAWED: false
  OWNER_REPRESENTATION_RERANK_NOW: PREMATURE_BEFORE_ONE_CENTRAL_WINDOW_GATE

EXACT_RETAINED_OBJECTS:
  q_m: literal selected Ferrers finite CCM row
  Q_m: "I - q_m q_m*"
  C_m: "Q_m (K_m-eps_m I) Q_m + q_m q_m*"
  Phi_m_a: "([S_a,H_m]+C_a) q_m"
  u_m_rho: "C_m^(-1) Q_m Phi_m(a_rho)"
  transfer: "T_m,z(a_rho)=<kappa_m(z),u_m,rho>"
  critical_threshold: "m^(-sigma) * (log m)^(-3/2)"

FINITE_CELL_RESULT:
  statement: >-
    For a fixed finite cell and a compact K with an accumulation point, the map
    v |-> sup_{z in K}|<C^(-1)Q kappa(z),v>| is strictly positive on every
    nonzero v in q-perp; on the unit sphere it has a positive attained minimum.
  required_source_facts:
    - q_is_unit
    - C_is_invertible_and_preserves_q_perp
    - proposition59_kernel_rows_are_linearly_independent
    - K_has_an_accumulation_point
  scope: FINITE_CELL
  verifier: PAPER

CENTRAL_WINDOW_REPRESENTATION:
  fixed_compact: >-
    Choose once a compact K0 inside the tracking strip containing a real interval
    [-delta,delta] and having nonempty interior.
  lattice_indices: "J_m=floor(delta*log(m)/(2*pi))"
  exact_sampling_target: >-
    At z_{m,j}=2*pi*j/log(m), |j|<=J_m, the P59 row is a nonzero source scalar
    times e_j.  Hence the transfer supremum controls the central coordinates of
    u_m,rho exactly.
  expected_inequality: >-
    sup_{z in K0}|T_m,z(a_rho)| >= log(m) * max_{|j|<=J_m}|u_m,rho(j)|,
    up to the already source-locked P59 normalization and sign.
  l2_form: >-
    sup_{z in K0}|T_m,z(a_rho)| >=
      log(m)/sqrt(2*J_m+1) * ||P_{J_m}u_m,rho||_2.
  threshold_reduction: >-
    A sufficient lower envelope becomes a lower bound on the central O(log m)
    mode mass of u_m,rho at approximately m^(-sigma)*(log m)^(-2).
  status: PRECOMMITTED_PAPER_TARGET_NOT_YET_SOURCE_LOCKED

CLOSES:
  - FINITE_CELL_OBSERVABILITY_POSITIVITY
  - ZERO_TRANSFER_WINDOWED_CAUCHY_REPRESENTATION
  - EXACT_NONANNIHILATION_AS_AUTOMATIC_RATE
  - ODD_MASS_AS_LOW_MODE_LOCALIZATION_SURROGATE

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - QPROJECTED_P59_KERNEL_COMPACT_RATE
  - SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
  - SelectedPhysicalFourierEnergyControl
  - CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_LOWER_ENVELOPE
  - GROWING_QUARTET_SOURCE_CATEGORY_CRITERION
  - MAXIMAL_REAL_PART_ZERO_ISOLATION
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_TRANSACTION_REQUIRED_OUTPUTS:
  - source-locked signs and scalar in the P59 lattice-pole evaluation
  - exact fixed-compact central-window sampling inequality
  - exact definition u_m,rho=C_m^(-1)Q_m Phi_m(a_rho)
  - exact threshold for ||P_{J_m}u_m,rho||_2
  - shelf audit for suppliers controlling u_m,rho, not q_m or Phi_m separately
  - a positive-definite plant showing central localization of Phi need not survive C^(-1)
  - one source-adapted Schur/Feshbach candidate if no direct mass theorem exists
  - no use of selectedFerrersFiniteCCMOddMass as a mode-localization theorem
  - no quartet or cross-zero conclusion in this transaction

NEXT_DISCRIMINATOR:
  PASS: CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_LOWER_ENVELOPE_READY
  HOLD: CENTRAL_WINDOW_SAMPLING_EXACT_BUT_GRAPH_RESOLVENT_MASS_UNCONTROLLED
  FAIL: SOURCE_SPECIFIC_CENTRAL_GRAPH_RESOLVENT_MASS_IS_BELOW_REQUIRED_SCALE

STOP_RULE:
  on_hold: >-
    Do not launch another Cauchy/Volterra/observability wrapper.  Return to the
    owner for representation rerank unless a source-adapted Schur/Feshbach theorem
    has a strictly smaller input ledger.
  on_fail: >-
    Refute the proposed zero-free-strength closeout for this representation; do
    not infer that the exact tracking rate is false.

CANDIDATE_REPRESENTATIONS:
  R1_CENTRAL_LATTICE_POLE_SAMPLING:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 2/10
    object: >-
      Replace the abstract observability infimum by the exact central coordinates
      of u=C^(-1)QPhi read at P59 lattice points that lie inside one fixed compact.
  R2_SOURCE_ADAPTED_CENTRAL_TAIL_SCHUR:
    rank: RUNNER_UP
    kill_power: 9/10
    proof_cost: 6/10
    object: >-
      Split the graph equation C u=QPhi into the central O(log m) block and its
      complement; use a source-defined Schur/Feshbach identity to prove that the
      central block cannot be smaller than the required threshold.

REGISTERED_PREDICTIONS:
  P_CENTRAL_WINDOW_1:
    probability: 0.62
    prediction: >-
      The pole-sampling identity closes exactly, but the shelf has no theorem on
      the central mass of C^(-1)QPhi; the result is HOLD and triggers owner rerank.
  P_CENTRAL_WINDOW_2:
    probability: 0.25
    prediction: >-
      The graph equation plus a source center anchor yields a usable central-window
      lower envelope through a Schur/Feshbach block estimate.
  P_CENTRAL_WINDOW_3:
    probability: 0.13
    prediction: >-
      A P59 sign, normalization, compact, or source-category mismatch requires
      repair before the central-window reduction is exact.

PRIOR_PREDICTION_FATE:
  P_COMPACT_OBS_1_0_55: CONFIRMED
  P_COMPACT_OBS_2_0_30: NOT_REALIZED
  P_COMPACT_OBS_3_0_15: NOT_REALIZED

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 4

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Correction 13 | Ratified.  Exact nonannihilation is not a quantitative rate; a positive graph operator supplies an upper bound for its inverse from a floor, not a lower bound; whole-plane span is not compact observability. | `[COFINAL_FAMILY][PAPER]` |
| Finite-cell compact observability | Accepted after retaining the actual graph block structure.  Analytic uniqueness and finite-dimensional compactness give a positive constant at each fixed cell. | `[FINITE_CELL][PAPER]` |
| Cauchy representation | Accepted.  The literal transfer is the P59 discrete Cauchy transform of `u=C^{-1}QPhi`, evaluated on the rescaled compact window. | `[FINITE_CELL][PAPER]` |
| Fixed-window site count | Accepted for the selected schedule `m=N=k+2`: a fixed spectral compact contains only `O(log m)` lattice sites among `2m+1`. | `[COFINAL_FAMILY][PAPER]` |
| Generic `Obs_{m,K}->0` | Not proved.  The report estimates a localized post-adjoint vector without paying the graph operator needed to make it arise from a unit observation input. | `[COFINAL_FAMILY][PAPER]` |
| Odd mass supplies low-mode localization | Refuted as a C04 object mismatch.  The repository defines odd mass as the norm of the reflection-odd part; it does not measure high-mode mass. | `[COFINAL_FAMILY][LEAN]` |
| `Phi` is centrally localized at consumer strength | Not proved.  Even a central source vector may be delocalized by a positive definite inverse; the exact vector in the Cauchy transform is `C^{-1}QPhi`. | `[COFINAL_FAMILY][PAPER]` |
| Growing-quartet criterion | Not ratified.  The report moves between a real spectral slice and a compact with complex interior.  The exact real/complex source category must be fixed before declaring the real-linear annihilator. | `[COFINAL_FAMILY][PAPER]` |
| Maximal-real-part almost-periodicity | Quarantined as heuristic.  Attainment of the supremum, finiteness of the leading set, slow variation of coefficients and noncancellation on the integer schedule were not proved. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. What Block 2 actually closed

The finite result is real.  For a fixed cell, define

\[
\mathcal O_{m,K}(v)
=
\sup_{z\in K}
\left|
\left\langle C_m^{-1}Q_m\kappa_m(z),v\right\rangle
\right|,
\qquad v\perp q_m.
\]

When `K` has an accumulation point, vanishing of this scalar entire function on
`K` forces it to vanish identically.  The P59 kernel rows are linearly independent,
and the graph operator preserves the decomposition

\[
\mathbb Cq_m\oplus q_m^\perp.
\]

Thus a nonzero `v` cannot have zero observation.  Continuity on the compact unit
sphere then gives

\[
\operatorname{Obs}_{m,K}>0
\]

for every fixed finite cell.  This statement has no cofinal lower envelope.

The exact representation is also useful.  With

\[
u=Q_mC_m^{-1}v,
\qquad
w=\frac{L_mz}{2},
\]

the observation is, up to the already fixed source convention,

\[
L_m\sin w
\sum_j\frac{\overline{u_j}}{w-j\pi}.
\]

This is a genuine representation gain: the abstract functional is now one finite
Cauchy transform.

## 2. The report's generic upper envelope drops the graph operator

The report substitutes a high-mode coordinate vector into the Cauchy transform
and concludes that the worst observation is of order

\[
L_m m^{\sigma_K/2-1}.
\]

That vector is not automatically an admissible unit input `v` to the observation
map.  There are two possible substitutions, and both retain a missing factor.

If one chooses `v=e_j`, then the Cauchy coefficient vector is

\[
u=C_m^{-1}e_j,
\]

which need not be localized at `j`.

If one chooses `u=e_j`, then the corresponding unit input is

\[
v=\frac{C_me_j}{\|C_me_j\|},
\]

and the observation contains the omitted denominator `||C_m e_j||`.

The complement floor gives one-sided control on `C_m^{-1}`.  It does not erase
this factor.  Therefore neither

\[
\operatorname{Obs}_{m,K}\to0
\]

nor the absence of a cofinal lower envelope follows from section 2a.

This is a **C10 functional-not-surrogate** failure: a convenient Cauchy direction
was estimated instead of the unit direction consumed by the observation map.

## 3. Odd mass is not mode localization

The repository defines

\[
q_m^{\rm odd}(j)=\frac{q_m(j)-q_m(-j)}2,
\qquad
\eta_m=\sum_j|q_m^{\rm odd}(j)|^2.
\]

Thus `selectedFerrersFiniteCCMOddMass` measures reflection parity contamination.
It says nothing about how much mass lies in

\[
|j|\le c\log m.
\]

Using it as the source of central mode localization is a **C04
same-coordinates-two-laws** error.

There is a second separation.  The transfer is not the Cauchy transform of `q_m`
or even of `Phi_m(a)` directly.  It is the transform of

\[
\boxed{
 u_{m,\rho}=C_m^{-1}Q_m\Phi_m(a_\rho).
}
\]

A positive definite inverse can rotate and delocalize a vector.  For example, on
a two-coordinate block the positive matrix

\[
C^{-1}=\begin{pmatrix}1&M\\M&M^2+1\end{pmatrix}
\]

has determinant one and maps the central coordinate `e_1` to `(1,M)`.  Central
localization of the source therefore does not imply central localization of the
graph solution.

## 4. The pole trick survives with the correct compact quantifier

Correction 13 correctly rejected the use of every pole in the whole spectral
plane as a compact lower envelope.  But the selected schedule has

\[
N=m=k+2,
\qquad
L_m=\log m,
\]

so the lattice spacing is `2*pi/L_m`.  A fixed compact containing a real interval
`[-delta,delta]` eventually contains

\[
J_m\asymp\frac{\delta L_m}{2\pi}
\]

actual P59 lattice points.

At these points the removable kernel row is a nonzero scalar multiple of one
coordinate vector.  Consequently the same fixed compact gives an exact lower
bound of the shape

\[
\sup_{z\in K_0}|T_{m,z}(a_\rho)|
\ge
L_m\max_{|j|\le J_m}|u_{m,\rho}(j)|
\ge
\frac{L_m}{\sqrt{2J_m+1}}
\|P_{J_m}u_{m,\rho}\|_2,
\]

subject only to locking the production sign and scalar.  This does not prove the
needed rate.  It moves the missing statement to one explicit central-window mass
of the literal graph-resolvent vector.

This is the selected **C01 sign/mass localization** move: retain where the vector
is observed instead of replacing it by a global norm.

## 5. Quartet and cross-zero claims remain outside the proof ledger

The report's growing-pair formula is written for a real spectral slice, while its
compact observability argument uses a compact with complex accumulation.  The
annihilation criteria in these two categories need not be copied across without
an explicit adapter.  Section 5 is therefore not used.

Section 6 additionally assumes, without proof, that the maximal real part is
attained by a finite leading set, that the transfer coefficients vary slowly, and
that an almost-periodic argument survives restriction to the selected integer
schedule.  Those ideas may generate a later falsifier.  They do not occupy a
ledger claim now.

## FINAL PROPOSAL

Run exactly one cheap source preflight on the central-window identity.  Do not
attempt another global observability theorem.

The primary representation is

\[
\boxed{
  P_{J_m}C_m^{-1}Q_m\Phi_m(a_\rho).
}
\]

The preflight first locks the exact P59 scalar and threshold.  It then asks whether
an existing source theorem controls this vector.  If not, it may formulate one
source-adapted Schur/Feshbach block estimate.  If that estimate has no smaller
input ledger than the original tracking rate, the owner reranks the representation.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The new central-window mass theorem may simply be the original signed tracking
> rate rewritten after one exact sampling identity.

That objection is currently live.  The next preflight must compare the complete
input ledger.  A new name, a Cauchy transform, or a Schur complement is not
progress unless it removes at least one of:

```text
prime discrepancy;
graph inverse growth;
selected-row mode localization;
maximal-zero cancellation.
```

If it removes none, W9 fires and the representation returns to the owner.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.
NO LEAN EDIT.
NO NUMERICAL PROBE.
NO ARISTOTLE.

PAPER-ONLY TASK:
  GOAL058_SELECTED_FERRERS_CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_PREFLIGHT

DELIVER:
  1. Exact P59 lattice-pole scalar and sign on the production row.
  2. Exact fixed-compact central-window sampling inequality.
  3. Exact threshold for the central L2 mass of
       C^(-1) Q Phi(a_rho).
  4. Shelf audit on that exact vector.
  5. One delocalizing positive-definite plant.
  6. At most one source-adapted Schur/Feshbach candidate.
  7. Input-ledger comparison with the original tracking rate.

FORBIDDEN:
  odd mass as mode localization;
  localization of Phi substituted for localization of C^(-1)QPhi;
  generic observability infimum;
  whole-plane poles used as a fixed-compact argument;
  quartet or all-zero cancellation claims;
  absence of a supplier used as evidence.
```

## META CLOSEOUT

**What became smaller?**

The unknown moved from an abstract compact observability constant to the central
`O(log m)`-mode mass of one explicit graph-resolvent vector.

**What was killed?**

- exact nonannihilation as a rate;
- the report's generic worst-direction envelope;
- odd mass as central localization;
- the current quartet and almost-periodic claims as proof inputs.

**What must not be tried again?**

Do not estimate `q`, `Phi`, or a convenient Cauchy coefficient vector and relabel
that estimate as control of `C^{-1}QPhi`.

**Current smallest named gap:**

```text
CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_LOWER_ENVELOPE
```

**Next cheapest decisive test:**

The exact lattice-pole sampling crosswalk and input-ledger comparison above.

**Prediction fate:**

`P_COMPACT_OBS_1` is confirmed: finite positivity closes and the cofinal constant
remains uncontrolled.  The two stronger branches were not realized.

**Memory entry:**

```yaml
iteration:
  target: ZERO_TRANSFER_COMPACT_OBSERVABILITY
  status: OPEN
  failed_strategy: GENERIC_OBSERVABILITY_AND_SOURCE_LOCALIZATION_SURROGATE
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_LOWER_ENVELOPE
  invariant_learned: THE_CAUCHY_VECTOR_IS_C_INVERSE_Q_PHI_NOT_Q_OR_PHI
  forbidden_future_move: ODD_MASS_OR_SOURCE_LOCALIZATION_AS_GRAPH_SOLUTION_LOCALIZATION
  next_decisive_test: FIXED_COMPACT_P59_POLE_SAMPLING_AND_CENTRAL_MASS_LEDGER
```
