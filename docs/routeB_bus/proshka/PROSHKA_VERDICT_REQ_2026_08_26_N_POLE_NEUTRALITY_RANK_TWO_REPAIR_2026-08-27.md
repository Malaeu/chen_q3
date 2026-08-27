# STATUS: FATAL FOR SINGLE-HYPERPLANE POLE REMOVAL — LITERAL RANK-TWO W02 ROUTE REMAINS OPEN

```yaml
PRIMARY: KILL_SINGLE_CAUCHY_HYPERPLANE_AS_LITERAL_W02_REMOVAL
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_REPORT_COMMIT: d2c044f7fac8c5c6a22fe6e5917a548ab0f37b8e
  BASE_REPORT_PATH: docs/routeB_bus/LINUX_LITERAL_POLE_NEUTRALITY_CROSSWALK_PREFLIGHT_GOAL058_2026-08-27.md
  BASE_REPORT_BLOB: 9ce995e1f876e99767a668e8a222a686b1828e03
  PARENT_VERDICT_COMMIT: d980277562b08f325922d2e5599b6e8a71dc1d1e
  HEAD_AT_AUDIT: d2c044f7fac8c5c6a22fe6e5917a548ab0f37b8e

ADJUDICATION:
  REPORTED_DISCRIMINATOR: HOLD
  REPORTED_CODE: POLE_FUNCTIONAL_EXPLICIT_BUT_COFINAL_SIZE_UNCONTROLLED
  DECISION: CROSSWALK_ACCEPTED_SINGLE_HYPERPLANE_REMOVAL_KILLED

  CAUCHY_FUNCTIONAL_TO_W02_CENTER_COLUMN: PAPER_PASS
  BUILT_IN_ZERO_INTEGRAL_EQUALS_CAUCHY_FUNCTIONAL: REJECTED_C04
  PHYSICAL_EVENNESS_IMPLIES_FINITE_ROW_EVENNESS: REJECTED_C04
  LITERAL_SELECTED_ROW_EXACT_REFLECTION_EVEN: NOT_PROVED
  LITERAL_SELECTED_ROW_ODD_MASS_DECAYS: LEAN_PROVED

  FULL_W02_OPERATOR_RANK: AT_MOST_TWO
  ONE_CAUCHY_MOMENT_KILLS_FULL_W02_ON_FULL_CARRIER: REFUTED_BY_EXACT_PLANT
  GROSKIN_EVEN_SECTOR_COROLLARY_APPLIES_TO_LITERAL_ROW: NOT_ESTABLISHED
  SELECTED_ROW_SCALAR_CAUCHY_MOMENT_ZERO_OR_NONZERO: UNDECIDED

  WHOLE_ROUTE_FATAL: false
  COMPLETED_ONE_MEASURE_VOLTERRA_ROUTE: OPEN
  POLARIZED_VOLTERRA_HILBERT_IDENTITY: RATIFIED_PAPER

EXACT_W02_REPAIR:
  denominator: d_n = L^2 + 16*pi^2*n^2
  even_vector: u_n = L / d_n
  odd_vector: v_n = 4*pi*n / d_n
  scalar: kappa_L = 32*L*sinh(L/4)^2
  entry_formula: W02_nm = kappa_L * (u_n*u_m - v_n*v_m)
  mixed_formula: x_star_W02_q = kappa_L*(conj(U(x))*U(q) - conj(V(x))*V(q))
  cauchy_functional: P(q) = sum_n q_n/(n^2 + (L/(4*pi))^2) = (16*pi^2/L)*U(q)
  consequence: P(q)=0 kills U(q), not V(q)
  full_annihilation_requires:
    - U(q)=0
    - V(q)=0

KILL_PLANT:
  carrier_modes: [-1, 0, 1]
  q: [1, 0, -1]
  result:
    U(q): 0
    V(q): nonzero
    P(q): 0
    W02_q: nonzero
    q_star_W02_q: strictly_negative
  code: SINGLE_CAUCHY_HYPERPLANE_DOES_NOT_ANNIHILATE_RANK_TWO_W02

MINIMAL_GAP_REPAIR:
  old_name_rejected: MODE_INDEX_DECAY_OF_THE_SELECTED_FERRERS_ROW
  new_name: SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_CONSUMER_CONTROL
  reason: >-
    The literal W02 action is determined by two endpoint moments. Full pointwise
    decay of every coefficient is a sufficient surrogate, not the minimal object.

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_FUNCTIONAL_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: LITERAL_SELECTED_W02_TWO_ENDPOINT_CONSUMER_RATE_READY
  HOLD: W02_RANK_TWO_IDENTITY_WITHOUT_ENDPOINT_RATE
  FAIL: W02_ENDPOINT_CONTROL_REIMPORTS_BOUNDARY_OR_FULL_MODE_WALL

CANDIDATE_REPRESENTATIONS:
  R1_LITERAL_TWO_ENDPOINT_MOMENTS:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 2/10
    object: >-
      Evaluate the two already-banked physical endpoint functionals on the exact
      selected kTrial and on x=C^{-1}kappa; preserve their exact mixed rank-two pairing.
  R2_EVEN_ODD_W02_SPLIT_WITH_EXPLICIT_ODD_DEFECT:
    rank: RUNNER_UP
    kill_power: 9/10
    proof_cost: 3/10
    object: >-
      Apply the Cauchy hyperplane only to the exact reflection-even part and carry
      the reflection-odd W02 channel explicitly through the proved odd-mass ledger.
  R3_COMPLETED_MEASURE_VOLTERRA:
    rank: FALLBACK_MAINLINE
    kill_power: 9/10
    proof_cost: 5/10
    object: >-
      Do not remove W02. Keep W02, Arch and Prime inside the single completed signed
      measure and attack the literal polarized Volterra test function.

REGISTERED_PREDICTIONS:
  P_W02_ENDPOINT_1:
    probability: 0.70
    prediction: >-
      The exact two-endpoint formula closes, but neither endpoint moment has the
      consumer-strength cofinal rate; result HOLD.
  P_W02_ENDPOINT_2:
    probability: 0.24
    prediction: >-
      Existing odd-mass and projection-tail suppliers control only the odd endpoint
      defect or only an interior-strip quantity, leaving the second boundary channel open.
  P_W02_ENDPOINT_3:
    probability: 0.06
    prediction: >-
      A source identity or exact endpoint crosswalk controls both endpoint moments
      at consumer strength without changing the selected family.

PRIOR_PREDICTION_FATE:
  P_POLE_NEUTRAL_1_0_76:
    fate: NOT_DECIDED_AS_SCALAR_EQUALITY
    note: >-
      The literal scalar Cauchy moment may or may not vanish. The stronger claim that
      its vanishing removes the literal W02 block is refuted.
  P_POLE_NEUTRAL_2_0_19:
    fate: NOT_TESTED
  P_POLE_NEUTRAL_3_0_05:
    fate: REFUTED_AS_SOURCE_IDENTITY
    note: >-
      The built-in unweighted integral identity is a different functional. Accidental
      equality of the Cauchy moment remains logically possible but is not source-forced.
  P_VOLTHILBERT_LEAN_1_0_88:
    fate: NOT_TESTED

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CLOSES:
  - GROSKIN_CAUCHY_FUNCTIONAL_TO_LITERAL_W02_CENTER_COLUMN_CROSSWALK
  - SINGLE_CAUCHY_HYPERPLANE_FULL_W02_REMOVAL_LEGALITY
  - PHYSICAL_EVENNESS_TO_FINITE_ROW_EVENNESS_SHORTCUT

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_CONSUMER_CONTROL
  - WEIGHTED_MODE_MOMENT_BOUND_FOR_GRAPH_RESOLVENT_VECTOR
  - COMPLETED_MEASURE_POLARIZED_VOLTERRA_CONSUMER_RATE
  - GROUND_TRACKING_COMPACT_RATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Groskin's Cauchy functional equals a nonzero scalar times pairing with the literal W02 center column | Accepted. | `[FINITE_CELL][PAPER]` |
| The selected construction already annihilates that functional because its physical integral is zero | Rejected: the unweighted physical integral and the Cauchy-weighted finite coefficient functional are different objects. | `[COFINAL_FAMILY][PAPER]` |
| Physical evenness of `h0,h4` makes the finite selected row exactly reflection-even | Rejected as an inference. The row is formed after `E_star`, projection and normalization; the repository defines its odd part and proves only cofinal odd-mass decay. | `[COFINAL_FAMILY][LEAN]` |
| One Cauchy hyperplane annihilates the literal full W02 block | Refuted by exact rank-two algebra and a three-mode plant. | `[FINITE_CELL][PAPER]` |
| The scalar Cauchy moment of the actual selected row is zero | Undecided. | `[COFINAL_FAMILY][CONDITIONAL]` |
| Full coefficientwise mode-index decay is the minimal missing object | Rejected. The literal W02 consumer depends on two endpoint moments. | `[COFINAL_FAMILY][PAPER]` |

## 1. What survives from `d2c044f7`

The report correctly identifies the scalar functional

\[
\mathcal P_L(q)
=
\sum_{n=-N}^{N}
\frac{q_n}{n^2+\beta^2},
\qquad
\beta=\frac{L}{4\pi},
\]

and correctly proves that it is a nonzero scalar multiple of

\[
\sum_n q_n\,\operatorname{ccmW02Entry}(L,n,0).
\]

This is a useful literal source crosswalk. `[FINITE_CELL][PAPER]`

The report is also correct that the selected physical combination is built to
annihilate the unweighted integral

\[
\int \operatorname{prolateCombination}=0,
\]

not the Cauchy-weighted coefficient functional. No same-family theorem currently
identifies these two functionals. `[COFINAL_FAMILY][PAPER]` **[C04]**

## 2. The missing rank-two channel

The literal source entry is

\[
W^{02}_{nm}
=
32L\sinh^2(L/4)
\frac{L^2-16\pi^2nm}
{(L^2+16\pi^2n^2)(L^2+16\pi^2m^2)}.
\]

Set

\[
d_n=L^2+16\pi^2n^2,
\qquad
u_n=\frac{L}{d_n},
\qquad
\upsilon_n=\frac{4\pi n}{d_n},
\qquad
\kappa_L=32L\sinh^2(L/4).
\]

Then exactly

\[
\boxed{
W^{02}_{nm}=\kappa_L(\nu_n\nu_m-\upsilon_n\upsilon_m).
}
\]

For complex rows `x,q`, with star-first convention,

\[
\boxed{
\langle x,W^{02}q\rangle
=
\kappa_L
\bigl(
\overline{U(x)}U(q)
-
\overline{V(x)}V(q)
\bigr),
}
\]

where

\[
U(q)=\sum_n\nu_nq_n,
\qquad
V(q)=\sum_n\upsilon_nq_n.
\]

The repository already contains this structure in invariant form: W02 is the
rank-two endpoint sesquilinear form built from two bounded endpoint functionals,
and that ambient form is proved to equal the literal finite CCM W02 matrix on
finite synthesis. `[FINITE_CELL][LEAN]`

Meanwhile

\[
\mathcal P_L(q)=\frac{16\pi^2}{L}U(q).
\]

Therefore the Groskin hyperplane kills `U(q)` only. It kills the full literal W02
action only when the second channel `V(q)` also vanishes. Exact reflection-evenness
would force this because `upsilon_n` is odd. But exact reflection-evenness of the
selected finite row is not supplied. `[COFINAL_FAMILY][PAPER]`

## 3. Exact falsifier

On the three modes `{-1,0,1}`, take

\[
q_{-1}=1,
\qquad q_0=0,
\qquad q_1=-1.
\]

Because `nu` is even,

\[
U(q)=0,
\qquad
\mathcal P_L(q)=0.
\]

Because `upsilon` is odd,

\[
V(q)=-2\upsilon_1\ne0.
\]

Consequently

\[
W^{02}q\ne0,
\qquad
q^*W^{02}q=-\kappa_L|V(q)|^2<0.
\]

Thus

\[
\boxed{
\mathcal P_L(q)=0
\not\Longrightarrow
W^{02}q=0
}
\]

on the literal full carrier. This is an exact kill, not a failed sufficient
estimate. `[FINITE_CELL][PAPER]` **[C10]**

## 4. Why physical evenness does not repair it

The literal selected coefficient row is not obtained by taking Fourier
coefficients of `prolateCombination` directly. The source chain is

```text
prolateCombination
→ E_star(prolateCombination)
→ multiplicative-window L2 object
→ finite orthogonal projection
→ unit normalization
→ coefficients q_n = <V_n,kTrial>.
```

The repository therefore defines a separate reflection-odd part of the selected
row and proves its mass tends to zero; it does not replace that theorem by an exact
identity `q_{-n}=q_n`. The implication

```text
physical h is even
→ selected finite CCM row is exactly reflection-even
```

crosses `E_star`, the log-window and projection without an intertwining theorem.
It is not legal. `[COFINAL_FAMILY][LEAN]` **[C04]**

The positive-index reduction

\[
\frac{q_0}{\beta^2}
+2\sum_{n\ge1}\frac{q_n}{n^2+\beta^2}=0
\]

must therefore be read as conditional on exact row evenness, not as a proved
identity for the literal selected row.

## 5. Why the old missing input is not minimal

A pointwise bound `|q_n| <= f(n)` could decide the scalar Cauchy moment. It is not
the minimal object controlling the W02 consumer.

The exact consumer depends only on two numbers:

\[
U(q),\qquad V(q),
\]

or equivalently the two already-defined physical endpoint moments. The correct
next question is therefore whether these two literal moments vanish or are small
enough after multiplication by their exact consumer-side partners.

The existing odd-mass theorem may control `V(q)` only after its full W02 prefactor
is retained. A bare statement `odd mass -> 0` is insufficient because the W02
operator scale grows with the source window. Failure of the resulting crude bound
will not prove that the signed endpoint contribution is large; it will only kill
that sufficient majorant.

The closed-substrip trial-to-Xi theorem does not bypass this audit: the two endpoint
moments live at the boundary `|Im z|=1/2`, while the proved convergence requires a
strict margin `sigma<1/2`, and its boundary plant shows that this margin is
load-bearing. `[COFINAL_FAMILY][LEAN]`

## FINAL PROPOSAL

Run exactly one paper/source audit:

```text
GOAL058_SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_FUNCTIONAL_PREFLIGHT
```

It must:

1. instantiate the existing `sourceW02PhysicalEndpointPlusFunctional` and
   `sourceW02PhysicalEndpointMinusFunctional` on the exact selected `kTrial`;
2. retain the exact mixed consumer
   `conj(endpointMinus x)*endpointPlus q + conj(endpointPlus x)*endpointMinus q`;
3. derive the exact even/odd decomposition of both moments without assuming the
   selected row is even;
4. audit whether the proved odd-mass decay, projection-tail decay, normalization
   bounds or a source Müntz identity controls either endpoint at consumer strength;
5. keep every W02 prefactor and the compact dependence of
   `x=C^{-1}kappa(z)`;
6. return PASS only from a complete rate ledger for both channels.

If the endpoint route fails, return immediately to the already-ratified completed
one-measure Volterra representation. Do not request full mode-index decay unless
the two endpoint functionals are first proved not directly accessible.

## STRONGEST ATTACK

The endpoint formulation may only rename the same boundary wall: both functionals
are boundary Mellin values, while current trial-to-Xi convergence stops on closed
substrips strictly inside `|Im z|<1/2`. If so, the two-endpoint audit must return
`W02_ENDPOINT_CONTROL_REIMPORTS_BOUNDARY_OR_FULL_MODE_WALL`, not another sequence
of wrappers.

A second attack is scale: the proved selected odd mass tends to zero, but the W02
prefactor grows. The audit must multiply them before claiming any decay.

## CODEX DIRECTIVE

```text
NO LEAN, NUMERICS, ARISTOTLE, OR CODEX EXECUTION.

Run only the paper-and-source preflight named in NEXT_TRANSACTION.
Do not formalize the Volterra bridge yet; its semantic admission remains valid,
but the cheapest decision-changing test is the literal two-endpoint W02 audit.
```

## META CLOSEOUT

**What became smaller?**

The vague pole-neutral question became an exact rank-two pair of source endpoint
moments.

**What was killed?**

```text
unweighted zero integral = Cauchy pole neutrality;
physical evenness = finite row evenness;
one Cauchy hyperplane removes the full literal W02 block;
mode-index decay as the minimal W02 object.
```

**What must not be tried again?**

Do not project the selected row into Groskin's hyperplane. Do not invoke the
even-sector corollary before proving exact selected-row evenness. Do not drop the
second W02 endpoint channel.

**Current smallest named gap**

```text
SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_CONSUMER_CONTROL
```

**Next cheapest decisive test**

Exact paper/source audit of the two endpoint moments on the literal selected row.

**Memory entry**

```yaml
iteration:
  target: literal pole-neutrality of the selected Ferrers row
  status: FATAL_FOR_SINGLE_HYPERPLANE_REMOVAL
  failed_strategy: one Cauchy hyperplane plus inferred exact evenness
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_CONSUMER_CONTROL
  invariant_learned: W02 is rank two on the literal full carrier
  forbidden_future_move: invoke even-sector pole annihilation without exact row evenness
  next_decisive_test: literal two-endpoint source preflight
```
