# STATUS: OPEN — CORRECTIONS 10–11 RATIFIED; RAW P59 NORM CLOSED; THE MINIMAL CONSUMER IS Q-PROJECTED

```yaml
PRIMARY: RATIFY_CORRECTIONS_10_11_AND_REPAIR_TO_QPROJECTED_TWO_CHANNEL_CONSUMER
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD_READ: 9ddfaacdb51632832017bd86ea67a23f97dd8e00

  CORRECTION_10:
    COMMIT: 36eda20be9a9086526ca723cca6f938ce38a7403
    PATH: docs/routeB_bus/LINUX_CORRECTION_10_ENERGY_IS_UNPROJECTED_GOAL058_2026-08-28.md
    GIT_BLOB: 79a5b1659fe57bd0ef014ca62e0c8287de8d3ded

  GRAPH_ENVELOPE_REPORT:
    COMMIT: 7cd5f9a54f5b3d1efc510952ef3ffc388e259bdd
    PATH: docs/routeB_bus/LINUX_GRAPH_TEST_VECTOR_L2_ENVELOPE_PREFLIGHT_GOAL058_2026-08-28.md
    GIT_BLOB: 4cc3055ad26ea59cf06c0b28426e918027b4ffd8

  CORRECTION_11:
    COMMIT: 293994c15cd96490683e38a818ce633e1028251f
    PATH: docs/routeB_bus/LINUX_CORRECTION_11_HALF_FACTOR_AND_KERNEL_NOT_ODD_GOAL058_2026-08-28.md
    GIT_BLOB: b65f4b83cc5ad64acd4ef9828d7b795e74885aec

  LITERAL_CONSUMER_REPORT:
    COMMIT: 39773de88f2cb620fe75033103b76a629c081889
    PATH: docs/routeB_bus/LINUX_LITERAL_CONSUMER_TWO_CHANNEL_PREFLIGHT_GOAL058_2026-08-28.md
    GIT_BLOB: 638ac71f32197e13d17a0faaa97eaac5196e6753

MODE:
  REPORTS: PAPER_AND_SOURCE_READ_ONLY
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  CORRECTION_10: RATIFIED
  CORRECTION_11: RATIFIED_ALL_FOUR_WITHDRAWALS

  P59_FULL_LATTICE_RAW_KERNEL_NORM:
    status: PAPER_PASS
    formula: >-
      sum_{n in Z} |proposition59PoleKernel(L,n,z)|^2
      = L^2 * sinh(L*Im(z))/(L*Im(z)), with continuous value L^2 at Im(z)=0.
    finite_carrier_use: VALID_UPPER_BOUND
    exact_consumer_norm: false
    reason: >-
      The literal residual consumer sees the q-orthogonal projection Q*kappa,
      not the whole raw kernel row.

  GENERIC_GRAPH_COERCIVITY:
    status: PAPER_PASS
    full_space_bound: >-
      ||C^(-1) kappa|| <= ||kappa||/min(beta,1).
    minimal_consumer_bound: >-
      ||Q C^(-1) kappa|| = ||C^(-1) Q kappa|| <= ||Q kappa||/beta.
    complement_floor_still_required: true

  LITERAL_TWO_CHANNEL_IDENTITY:
    status: PAPER_PASS_AFTER_HALF_FACTOR_REPAIR
    nonminimal_formula: >-
      Psi = D_x + (1/2) Phi(G_x),
      D_x = sum_i (M_ii-a) conj(x_i) q_i,
      x=C^(-1)kappa.
    minimal_formula: >-
      Let y=Qx=C^(-1)Qkappa.  Then
      Psi=<y,(M-aI)q>=<y,Mq>
      because <q,r>=0 and <y,q>=0.  Hence
      Psi = D_perp + (1/2) Phi(G_y),
      D_perp = sum_i M_ii conj(y_i) q_i.

  FULL_VOLTERRA_REFLECTION_ODD: REFUTED
  ABSORPTION_INTO_THE_SAME_ODD_REFLECTION_FUNCTIONAL: KILLED
  ALL_SOURCE_SPECIFIC_DIAGONAL_CANCELLATION: NOT_KILLED
  DIAGONAL_CAN_NEVER_BE_ABSORBED: REJECTED_AS_TOO_STRONG

  COMPENSATED_PRIMITIVE_FROM_RESIDUE_ALONE: REFUTED
  GRAPH_ENVELOPE_IS_THE_ONLY_BINDING_GAP: REFUTED

EXACT_QPROJECTED_REPAIRS:
  RESIDUAL:
    r: "(M-aI)q"
    orthogonality: "<q,r>=0"
  PROJECTIONS:
    P: "q q*"
    Q: "I-P"
    graph_operator: "C=Q(M-eps I)Q+P"
    block_laws:
      - "CP=PC=P"
      - "CQ=QC=Q(M-eps I)Q"
      - "C^(-1)P=P"
      - "C^(-1)Q=Q C^(-1)"
  MINIMAL_LEFT_VECTOR:
    x: "C^(-1)kappa"
    y: "Qx=C^(-1)Qkappa"
  EXACT_CANCELLATIONS:
    - "<x,r>=<y,r>"
    - "<y,(M-aI)q>=<y,Mq>"
    - "every n-independent diagonal term c*I pairs to zero"
    - "the Rayleigh shift -aI disappears"
    - "the n-independent CCM archimedean prefactor disappears"
    - "the constant subtraction ccmQKernel(L,n,n,0)=2 in the WR integrand disappears after summation"

REPORT_CLOSEOUT:
  GRAPH_ENVELOPE_REPORT:
    reported_code: GRAPH_INVERSE_BOUND_REDUCED_TO_FLOOR_SOURCE_ALONE
    decision: HOLD_RATIFIED_WITH_QPROJECTION_REPAIR
    closes:
      - P59_RAW_FULL_LATTICE_KERNEL_NORM
    does_not_close:
      - QPROJECTED_P59_KERNEL_NORM_RATE
      - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
      - GRAPH_CONSUMER_COMPACT_RATE

  LITERAL_CONSUMER_REPORT:
    reported_code: DIAGONAL_OR_NORMALIZED_FINITE_ROW_ADAPTER_STILL_OPEN
    decision: HOLD_RATIFIED_WITH_PERMANENCE_CLAIM_REPAIR
    closes:
      - ONE_ODD_REFLECTION_FUNCTIONAL_SHORTCUT
      - MISSING_HALF_FACTOR
      - FULL_KERNEL_REFLECTION_ODD_CLAIM
    does_not_prove:
      - NO_SELECTED_FAMILY_DIAGONAL_CANCELLATION
      - NO_USEFUL_SYMMETRIC_SHADOW_REPRESENTATION
      - DIRECT_DIAGONAL_BOUND_IS_THE_ONLY_ROUTE

CLOSES:
  - CORRECTION_10_ENERGY_OBJECT_RETRACTION
  - CORRECTION_11_FOUR_CLAIM_RETRACTION
  - P59_RAW_FULL_LATTICE_KERNEL_NORM_PAPER_IDENTITY
  - FULL_VOLTERRA_REFLECTION_ODD_SHORTCUT
  - NON_QPROJECTED_LITERAL_CONSUMER_AS_MINIMAL_OBJECT

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - QPROJECTED_P59_KERNEL_COMPACT_RATE
  - SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
  - SelectedPhysicalFourierEnergyControl
  - COMPENSATED_ENDPOINT_REMAINDER_PRIMITIVE
  - COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND
  - LITERAL_CCM_QPROJECTED_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_QPROJECTED_DIAGONAL_SOURCE_ACTION_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: QPROJECTED_DIAGONAL_COMPLETED_SOURCE_RATE_READY
  HOLD: QPROJECTED_DIAGONAL_IDENTITY_WITHOUT_SOURCE_RATE
  FAIL: QPROJECTED_DIAGONAL_REIMPORTS_PRIME_DISCREPANCY_OR_FULL_ACTION_WALL

CANDIDATE_REPRESENTATIONS:
  R1_QPROJECTED_COSINE_COMPLETED_SOURCE:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 2/10
    object: >-
      Use y=Q C^(-1)kappa, b_n=conj(y_n)q_n and sum b_n=0.  Rewrite the
      literal diagonal W02/Arch/Prime action as one endpoint-vanishing cosine
      or Volterra shadow against the completed source before any inequality.
  R2_QPROJECTED_FULL_VOLTERRA_SYMMETRIC_ANTISYMMETRIC_SPLIT:
    rank: RUNNER_UP
    kill_power: 9/10
    proof_cost: 4/10
    object: >-
      Decompose the full q-projected Volterra kernel and the completed source
      simultaneously into reflection-symmetric and reflection-antisymmetric
      channels.  Keep the explicit shadow; do not claim it vanishes.

REGISTERED_PREDICTIONS:
  P_QPROJECTED_DIAGONAL_1:
    probability: 0.76
    prediction: >-
      Q-projection kills the Rayleigh and constant diagonal pieces exactly and
      yields an endpoint-vanishing cosine functional, but its cofinal source rate
      remains open; HOLD.
  P_QPROJECTED_DIAGONAL_2:
    probability: 0.18
    prediction: >-
      The completed-source main terms cancel strongly enough to give a usable
      direct compact rate for the diagonal shadow.
  P_QPROJECTED_DIAGONAL_3:
    probability: 0.06
    prediction: >-
      A sign, scale or star-first correction is needed before the completed
      diagonal identity is exact.

PRIOR_PREDICTION_FATE:
  P_GRAPH_ENVELOPE_1_0_65: CONFIRMED_WITH_QPROJECTION_REPAIR
  P_GRAPH_ENVELOPE_2_0_25: NOT_REALIZED
  P_GRAPH_ENVELOPE_3_0_10: NOT_REALIZED
  P_LITERAL_REPAIR_1_0_82: CONFIRMED_FOR_TWO_CHANNEL_IDENTITY_NOT_FOR_PERMANENT_NO_CANCELLATION
  P_LITERAL_REPAIR_2_0_15: NOT_REALIZED_AS_ABSORPTION
  P_LITERAL_REPAIR_3_0_03: NOT_REALIZED

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C07_PROBABILITY_WEIGHTED_ESTIMATE
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
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
| Correction 10: the existing physical-energy contract is on the unprojected trial, not the normalized finite row | Ratified. | `[COFINAL_FAMILY][PAPER]` |
| Correction 11: restore the factor `1/2` | Ratified. | `[FINITE_CELL][PAPER]` |
| Correction 11: full Volterra kernel is not generally reflection-odd | Ratified. | `[FINITE_CELL][PAPER]` |
| Correction 11: endpoint residue alone does not prove the compensated primitive exists | Ratified. | `[COFINAL_FAMILY][PAPER]` |
| Correction 11: the graph envelope is not the sole open input | Ratified. | `[COFINAL_FAMILY][PAPER]` |
| Full-lattice raw P59 row has the displayed exact norm | Accepted on paper; finite carrier is bounded by the full lattice. | `[ABSTRACT][PAPER]` |
| The exact consumer requires the whole vector `x=C⁻¹κ` | Rejected.  Residual orthogonality removes its `q`-parallel component. | `[FINITE_CELL][PAPER]` |
| The raw P59 norm is the sharp consumer kernel norm | Rejected.  The sharp object is `Qκ`. | `[FINITE_CELL][PAPER]` |
| The literal consumer has two channels | Accepted after Q-projection and the factor `1/2`. | `[FINITE_CELL][PAPER]` |
| Aperiodicity proves the diagonal can never enjoy any selected-family cancellation | Rejected.  It kills only absorption into the unchanged odd reflection functional. | `[COFINAL_FAMILY][PAPER]` |
| The next object should be a direct absolute bound on the old diagonal term | Rejected as premature.  First remove the exact `q`-parallel and constant source pieces. | `[COFINAL_FAMILY][PAPER]` |

## 1. Corrections 10 and 11

All withdrawals are accepted.

Correction 10 catches a genuine C04 object mismatch.  The existing contract
`SelectedPhysicalFourierEnergyControl` is evaluated on the full unprojected
`gTrial_m`.  The literal finite row is the coefficient row of

\[
kTrial_{m,N}=s_{m,N}P_NgTrial_m.
\]

Therefore the exact finite mode-energy identity applies to `kTrial_m_N`; the
full-object contract gives only the projection-and-normalizer inequality

\[
\|Nq\|_2
\le
|s_{m,N}|\frac{L}{2\pi}
\sqrt{\operatorname{physicalFourierEnergy}(gTrial_m)}.
\]

The normalizer has a selected-Ferrers supplier under the frozen W5 inputs.  The
full physical-energy contract remains open.  `[COFINAL_FAMILY][PAPER]`

Correction 11 also survives intact:

- the reflected functional contributes one half of the original off-diagonal
  integral;
- only the periodic sine test is reflection-odd;
- subtracting the endpoint logarithm does not prove convergence of the
  compensated remainder;
- no single current input may be called the only binding gap.

`[COFINAL_FAMILY][PAPER]`

## 2. The P59 norm identity

For

\[
w=\frac{Lz}{2}=u+iv,
\qquad
\kappa_n(z)=L\frac{\sin w}{w-n\pi},
\]

the standard cotangent partial-fraction identity gives

\[
\sum_{n\in\mathbb Z}
\frac{1}{(u-n\pi)^2+v^2}
=
\frac{\sinh(2v)}{v(\cosh(2v)-\cos(2u))}.
\]

Together with

\[
|\sin(u+iv)|^2
=
\frac{\cosh(2v)-\cos(2u)}2,
\]
this yields

\[
\boxed{
\sum_{n\in\mathbb Z}|\kappa_n(z)|^2
=
L^2\frac{\sinh(L\operatorname{Im}z)}
{L\operatorname{Im}z}
}
\]

with the continuous value \(L^2\) on the real axis.  Restriction to
\(|n|\le N\) gives a rigorous upper bound.  `[ABSTRACT][PAPER]`

This closes the **raw full-lattice kernel norm** as a paper input.  It does not
identify the sharp vector used by the residual functional.

## 3. The missing Q-projection

Let

\[
P=qq^*,\qquad Q=I-P,
\]

\[
C=Q(M-\varepsilon I)Q+P,
\qquad
r=(M-aI)q,
\qquad
a=q^*Mq.
\]

The selected row is unit-normalized.  Hence

\[
q^*r=q^*Mq-aq^*q=0.
\]

Moreover the graph operator is block diagonal relative to

\[
\mathbb Cq\oplus q^\perp:
\]

\[
CP=PC=P,
\qquad
CQ=QC=Q(M-\varepsilon I)Q.
\]

When \(C\) is invertible,

\[
C^{-1}P=P,
\qquad
C^{-1}Q=QC^{-1}.
\]

Put

\[
x=C^{-1}\kappa,
\qquad
y=Qx=C^{-1}Q\kappa.
\]

Then the exact consumer satisfies

\[
\boxed{
\langle x,r\rangle=\langle y,r\rangle.
}
\]

This is already foreshadowed by the earlier ground-graph audit, which states
that residual orthogonality kills the \(q\)-component of the inverse-kernel
vector.  The two new reports did not propagate that fact into their final
objects.

The complement floor gives the sharper bound

\[
\boxed{
\|y\|_2
\le
\frac{\|Q\kappa\|_2}{\beta},
}
\]

whereas the report's full-space estimate is

\[
\|x\|_2
\le
\frac{\|\kappa\|_2}{\min(\beta,1)}.
\]

The latter remains a valid sufficient bound.  It is not the minimal computing
object.  `[FINITE_CELL][PAPER]`

## 4. The repaired two-channel identity

Since \(y\perp q\),

\[
\langle y,(M-aI)q\rangle
=
\langle y,Mq\rangle.
\]

Thus the literal consumer is more sharply written as

\[
\boxed{
\Psi_k(z)
=
D_k^\perp(z)
+
\frac12\Phi_k(G_{y_k,z}),
}
\]

where

\[
D_k^\perp(z)
=
\sum_i(M_k)_{ii}\overline{y_{k,i}(z)}q_{k,i},
\]

and the polarized Hilbert weight and sine test are built from \(y_k\), not the
unprojected \(x_k\).

This exact replacement has three immediate consequences.

1. The Rayleigh term `-a` disappears.
2. Every diagonal source term independent of the mode index disappears because
   \[
   \sum_i\overline{y_i}q_i=0.
   \]
3. In the literal CCM archimedean diagonal, both the Euler/log prefactor and the
   constant subtraction `ccmQKernel(L,n,n,0)=2` are mode-independent and hence
   cancel before any estimate.

These are exact cancellations, not bounds.  Any direct diagonal preflight that
starts from the old \(D_x\) pays terms the consumer does not contain.

## 5. What the aperiodicity plant actually kills

The full polarized Volterra kernel contains

\[
K(w)=\sum_n(\alpha_n+\beta_nw)e^{2\pi inw}.
\]

Unless the trigonometric polynomial

\[
\sum_n\beta_ne^{2\pi inw}
\]
vanishes identically, \(K\) is not periodic and cannot be the same
reflection-odd test used for the off-diagonal channel.  This kills the claim
that the **unchanged odd reflection functional alone** represents the entire
consumer.

It does not prove that the selected-family diagonal shadow has no exact
cancellation, no useful completed-source representation, or no coupled
symmetric/antisymmetric estimate.  Those are different statements.  The phrase
"the diagonal can never be absorbed" is therefore too broad.

The correct durable conclusion is:

```text
The diagonal shadow cannot be deleted.
It must be carried explicitly.
Its best representation and rate remain open.
```

This is precisely the C13 discipline: write the shadow exactly before deciding
how expensive it is.

## 6. Exact next transaction

The next preflight must use the Q-projected vector and the literal diagonal
branch before applying inequalities.

Define

\[
b_n(z)=\overline{y_n(z)}q_n,
\qquad
B_z(t)=\sum_n b_n(z)\cos(nt).
\]

Then

\[
\sum_n b_n(z)=0,
\qquad
B_z(0)=B_z(2\pi)=0.
\]

The source diagonal branch contains

\[
2\left(1-\frac{t}{2\pi}\right)\cos(nt)
\]

for the prime and archimedean terms.  The W02 diagonal also has an exact
Laplace-cosine representation because

\[
\int_0^\infty t e^{-at}\cos(nt)\,dt
=
\frac{a^2-n^2}{(a^2+n^2)^2},
\qquad a=\frac{L}{4\pi}.
\]

Therefore the diagonal is not an arbitrary coordinate sum.  It is a completed
source pairing against one endpoint-vanishing cosine/Volterra shadow.  The
preflight must derive the exact signs, folds and correction terms, then decide
whether the resulting functional is small.

### Required output

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_QPROJECTED_DIAGONAL_SOURCE_ACTION_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

OBJECTS:
  q_k
  P_k = q_k q_k^*
  Q_k = I-P_k
  C_k
  kappa_k(z)
  y_k(z)=Q_k C_k^(-1) kappa_k(z)
  b_{k,n}(z)=conj(y_{k,n}(z))q_{k,n}

MUST DERIVE:
  1. Psi=<y,(M-aI)q>=<y,Mq>.
  2. ||y|| <= ||Qkappa||/beta.
  3. Exact cancellation of all mode-independent diagonal terms.
  4. Exact W02/Arch/Prime diagonal shadow with one sign convention.
  5. Endpoint vanishing of the shadow test.
  6. Exact relation to the full polarized Volterra kernel.
  7. A consumer-strength compact rate, or the exact source wall preventing it.

FORBIDDEN:
  old non-Q-projected x as the final consumer vector;
  carrying the Rayleigh term after y⊥q is known;
  componentwise absolute bounds before the completed diagonal identity;
  treating the full Volterra kernel as reflection-odd;
  treating aperiodicity as proof that no source-specific cancellation exists;
  numerics;
  Lean edits;
  Aristotle;
  Codex.
```

### Plants

```text
P1_CONSTANT_DIAGONAL:
  M_diag=cI.
  The Q-projected diagonal channel must vanish exactly.

P2_NONCONSTANT_DIAGONAL:
  A two- or three-mode diagonal with y⊥q but nonzero
  sum M_ii conj(y_i)q_i.
  Prevents the false claim that Q-projection kills the whole diagonal.

P3_QPARALLEL_CONTAMINATION:
  Compare x with y=Qx.
  Any surviving -a or constant diagonal term in the y formula is a bug.

P4_REFLECTION_SHADOW:
  A finite beta-row for which w*sum beta_n e^(2piinw) is aperiodic.
  Must kill the one-odd-functional shortcut without killing the explicit shadow.
```

## STRONGEST ATTACK

The strongest attack on report `39773de8` is its word **permanently**.
Aperiodicity proves that the full kernel is not the old periodic odd test.  It
does not prove that the selected-family diagonal source action lacks an exact
cancellation or a useful symmetric shadow.  A universal non-existence statement
would require a source-specific falsifier, which the report does not provide.

The strongest attack on report `7cd5f9a5` is object minimality.  Its raw kernel
norm is correct, but the residual functional kills the \(q\)-parallel component.
The theorem-facing inverse vector is therefore \(C^{-1}Q\kappa\), not
\(C^{-1}\kappa\).  Ignoring this projection can lose exact cancellation and
introduce the artificial denominator `min(beta,1)` instead of the complement
constant `beta`.

Neither attack kills the corridor.  Both make the next object smaller.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.
NO LEAN EDIT.
NO NUMERICAL PROBE.
NO ARISTOTLE.

Run only the paper/source task:

  GOAL058_SELECTED_FERRERS_QPROJECTED_DIAGONAL_SOURCE_ACTION_PREFLIGHT

Return exactly one discriminator:

PASS:
  QPROJECTED_DIAGONAL_COMPLETED_SOURCE_RATE_READY

HOLD:
  QPROJECTED_DIAGONAL_IDENTITY_WITHOUT_SOURCE_RATE

FAIL:
  QPROJECTED_DIAGONAL_REIMPORTS_PRIME_DISCREPANCY_OR_FULL_ACTION_WALL
```

## META CLOSEOUT

**What became smaller?**

```text
x=C^(-1)kappa
→ y=Qx=C^(-1)Qkappa;

D_x=sum(M_ii-a)conj(x_i)q_i
→ D_perp=sum M_ii conj(y_i)q_i.
```

The raw P59 row norm is explicit, the Rayleigh term is gone, and constant
source-diagonal terms are removed before estimation.

**What was killed?**

```text
full physical energy = finite normalized-row energy;
missing factor 1/2;
full Volterra kernel is reflection-odd;
residue alone proves the compensated primitive;
graph envelope is the sole gap;
one unchanged odd reflection functional represents the whole consumer.
```

**What must not be tried again?**

```text
Do not quote a formula without naming its argument.
Do not drop constants when changing functional normalization.
Do not call the non-Q-projected inverse vector the minimal consumer.
Do not infer universal absence of cancellation from aperiodicity.
```

**Current smallest named gap**

```text
LITERAL_CCM_QPROJECTED_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND
```

**Next cheapest decisive test**

Derive the exact Q-projected cosine/Volterra diagonal shadow and test whether its
completed-source main terms cancel before any inequality.

**Prediction fate**

```text
P_GRAPH_ENVELOPE_1:
  confirmed, but the minimal vector is Q-projected.

P_LITERAL_REPAIR_1:
  confirmed for the two-channel identity;
  not confirmed for the stronger permanent-no-cancellation wording.

P_LITERAL_REPAIR_2:
  not realized as deletion of the diagonal;
  the explicit shadow remains a potentially useful representation.
```

**Memory entry**

```yaml
iteration:
  target: completed reflection/Duhamel literal consumer
  status: PROGRESS
  failed_strategy: one odd reflection functional for the full consumer
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: LITERAL_CCM_QPROJECTED_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND
  invariant_learned: residual orthogonality must be propagated into every downstream representation
  forbidden_future_move: estimate x when the consumer only sees Qx
  next_decisive_test: exact completed-source formula for the Q-projected diagonal shadow
```
