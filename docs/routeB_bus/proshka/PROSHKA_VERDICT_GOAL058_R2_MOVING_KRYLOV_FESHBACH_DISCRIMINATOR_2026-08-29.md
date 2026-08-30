# STATUS: FATAL — KILL_R2_MOVING_KRYLOV_FESHBACH
```yaml
PRIMARY: KILL_R2_MOVING_KRYLOV_FESHBACH
OPERATIVE_CLASS: KILL_R2_MOVING_KRYLOV_FESHBACH
PRIMARY_COUNT: 1
DOCUMENT_ROLE: GOAL058_R2_ADMISSIBILITY_DISCRIMINATOR

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-08-29-R2K
  BOUNDARY_ID: GOAL058_R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: cf32b9b0e15a779cc77de4b10712a668d2c8e01b
  AUTHORITATIVE_ATTACHMENT:
    NAME: PROSHKA_REQUEST_GOAL058_R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR_2026-08-29.txt
    BYTES: 5398
    LINES: 111
    SHA256: 04d0b471f6f8c59b3176d12e257df7cf3e5d90e45afc199b290379467ef30dd3
    GIT_BLOB: 067dd092faf722d7db193c160c2f1324285217b2
    FINAL_LF: true
  REQUEST_INTRODUCING_COMMIT: 02e60cc4177e9ec45b3571dfd082253d20f12f92
  ACTIVATION_COMMIT: 2661fe430cc04e45908e7d0d63b4c111db52a926
  TASK_GIT_BLOB: 97c1adfd2ccd1dbffde6a6ca21a5bf3fe716ce3b

SOURCE_LIST_FINDING:
  CODE: TASK_FILE_POSTDATES_SOURCE_BASE
  SOURCE_FILES_AT_SOURCE_BASE: REVIEWED_IN_FULL
  TASK_FILE_AT_SOURCE_BASE: ABSENT
  TASK_FILE_REVIEWED_AT_ACTIVATION_COMMIT: true
  BLOCKS_MATHEMATICAL_ADJUDICATION: false
  REASON: >-
    The byte-exact attachment is the controlling request, and every mathematical
    source object named by it was audited at the locked source commit. The later
    task file supplies execution constraints only; it does not alter K_i, q_i,
    a_i, r_i, or the proposed carrier.

SOURCE_AUDIT:
  RESIDUAL_SOURCE:
    PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean
    GIT_BLOB: af21711d6e3181076aadd6e7bab7f85f4e0ca757
  ONE_LINE_FESHBACH:
    PATH: q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean
    GIT_BLOB: 3315e77881d4d719f63461bbda1f57474938936a
  SOURCE_PREFLIGHT:
    PATH: q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean
    GIT_BLOB: 41a073e251614e409fde7ecc25d478df909db0f8
  JUDGE_RERAN_LEAN_KERNEL: false
  REQUEST_REPORTED_KERNEL_GREEN_PREFIX_ACCEPTED_AS_INPUT: true

PRODUCTION_OBJECT:
  MATRIX: K_i = D0Pstar.sourceCCMFiniteMatrix i
  SOURCE_ROW: q_i = D0Pstar.sourceCCMComplexRow S i
  RAYLEIGH: a_i = D0Pstar.sourceCCMFiniteRayleigh S i
  RESIDUAL: r_i = K_i *v q_i - a_i • q_i
  EXACT_INPUTS:
    - star q_i dot q_i = 1
    - K_i is Hermitian
    - star q_i dot r_i = 0
    - one-line complement coupling equals r_i

QUESTION_1_ADMISSIBILITY:
  R_EQ_ZERO_BRANCH:
    exact_eigenvector: true
    ends_krylov_expansion: true
    proves_bottom_ground: false
    proves_simple_ground: false
    proves_route_tracking: false
  R_NE_ZERO_BRANCH:
    CARRIER: U_i = span_C {q_i, r_i / norm(r_i)}
    EXACT_DIMENSION: 2
    DIMENSION_SOURCE: unit q_i plus orthogonality plus r_i nonzero
    NUMERICAL_RANK_TEST_USED: false
    LEGITIMATE_KRYLOV_REALIZATION: true
    MERELY_RAW_RESIDUAL_RENAMED: false
    ROUTE_ADMISSIBLE: false
  DECISION: >-
    U_i is the honest second Krylov space. It advances one algebraic step beyond
    the killed line carrier. That fact is not enough: its outgoing coupling is
    exactly the next Lanczos residual, and no production theorem makes that
    residual smaller for the literal CCM matrix family.

EXACT_LANCZOS_LEDGER:
  DEFINITIONS:
    beta_i: norm(r_i)
    e0_i: q_i
    e1_i: r_i / beta_i
    alpha_i: star e1_i dot (K_i *v e1_i)
    c_i: (I - P_i) *v (K_i *v e1_i)
  IDENTITIES:
    - K_i *v e0_i = a_i • e0_i + beta_i • e1_i
    - alpha_i is real
    - K_i *v e1_i = beta_i • e0_i + alpha_i • e1_i + c_i
    - c_i is orthogonal to U_i
    - compressed_2x2_block = [[a_i, beta_i], [beta_i, alpha_i]]
    - complement_coupling_has_rank_at_most_one
    - complement_coupling_operator_norm = norm(c_i)
  CLASSIFICATION: c_i_IS_EXACT_SECOND_LANCZOS_RESIDUAL

QUESTION_2_INDEPENDENT_COUPLING_CONSUMER:
  EXACT_SOURCE_THEOREM_CONTROLLING_c_i: NONE_FOUND
  EXACT_DOWNSTREAM_CONSUMER_AVOIDING_OLD_DEBT: NONE_FOUND
  AUDITED_MECHANISMS:
    CCM_SOURCE_RECURRENCE:
      controls_c_i: false
      finding: no source theorem gives a recurrence for repeated application of literal K_i
    LITERAL_CCM_BANDEDNESS:
      controls_c_i: false
      finding: no theorem makes the production CCM Weil matrix banded in this carrier
    COMMUTATOR:
      controls_c_i: false
      finding: >-
        The committed scalar commutator observable has zero real part for the
        generic Hermitian/real-diagonal setup and has a planted nonzero-residual
        witness. It cannot bound either r_i or c_i.
    REFLECTION:
      controls_c_i: false
      finding: reflection can keep q_i, r_i, and c_i in the even sector but supplies no norm decay
    SELECTED_FERRERS_OR_PROLATE_RECURRENCE:
      controls_c_i: false
      finding: >-
        Those recurrences belong to the prolate/Ferrers operator and packet
        coefficients, not to repeated action of the dense literal CCM Weil
        matrix K_i. Importing them here would change the source object.
    EVENTUAL_COMPLEMENT_FLOOR:
      controls_c_i: false
      finding: >-
        A two-vector Schur/Feshbach formula contains
        c_i^* (K_i|U_i_perp - z)^(-1) c_i. Requiring a complement floor or
        bounded inverse therefore reimports the exact debt that the stopped
        representation failed to control.

ARBITRARY_TAIL_PLANT:
  SPACE: C^3 with orthonormal basis e0,e1,e2
  PARAMETERS: a, alpha, tau real; M nonnegative
  q: e0
  K_M: "[[a,1,0],[1,alpha,M],[0,M,tau]]"
  CHECKS:
    - K_M is Hermitian
    - rayleigh(q) = a
    - residual(q) = e1
    - q and residual(q) are orthonormal
    - U = span {e0,e1}
    - c = M * e2
    - norm(c) = M
  RESULT: >-
    M is arbitrary. Hermiticity, q-unit normalization, q-orthogonality of the
    first residual, and exact rank two impose no upper bound on the next
    coupling.

FIXED_RANK_PLANT:
  FAMILY: Hermitian tridiagonal Jacobi chains
  CONSTRUCTION: >-
    Precommit nonzero beta_1,...,beta_R so that the Krylov space has exact rank
    R, then choose the next coefficient beta_(R+1)=M arbitrarily.
  RESULT: >-
    Every fixed finite Krylov rank merely exposes another uncontrolled Lanczos
    residual unless a source theorem controls the next coefficient or closes an
    invariant subspace.
  POST_HOC_RANK_FROM_NUMERICS: forbidden
  RANK_LAW_AS_BINDER: forbidden
  REQUIRED_RANK_EVIDENCE: exact Krylov determinant, minimal-polynomial theorem, or invariant-subspace theorem

CLASS_DECISION:
  TWO_VECTOR_TRY:
    status: REJECTED_NO_INDEPENDENT_COUPLING_CONTROL
  ALTERNATIVE_MOVING_CARRIER_REPAIR:
    status: REJECTED_NOT_FULLY_SPECIFIED
    reason: >-
      No different source-preserving carrier with an exact rank-growth law and
      an independent production consumer survived the audit. Minting a
      conditional receiver would only move the same floor/resolvent debt.
  SELECTED:
    status: KILL
    code: KILL_R2_MOVING_KRYLOV_FESHBACH

KILL_GROUNDS:
  - code: SECOND_LANCZOS_RESIDUAL_UNCONTROLLED
    card: C03_MOVING_REPRESENTATION
    detail: the moving carrier is genuine, but its newly exposed coupling has no smaller source ledger
  - code: ARBITRARY_COMPLEMENT_ACTION_PLANT
    card: C10_FUNCTIONAL_NOT_SURROGATE
    detail: available structural inputs permit arbitrary norm(c_i)
  - code: PROLATE_RECURRENCE_IS_WRONG_OPERATOR
    card: C04_SAME_COORDINATES_TWO_LAWS
    detail: a banded recurrence for the source packet cannot be transferred to the literal CCM Weil matrix without a theorem
  - code: POST_HOC_KRYLOV_RANK_FORBIDDEN
    card: C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    detail: choosing rank after numerical inspection proves no cofinal rank law
  - code: COMPLEMENT_INVERSE_DEBT_REAPPEARS
    card: C10_FUNCTIONAL_NOT_SURROGATE
    detail: the Schur term still consumes the uncontrolled complement inverse or floor

KILL_BOUNDARY:
  KILLS:
    - R2 as the presently admissible repair for Goal058 ground-to-trial tracking
    - a theorem inferred only from Hermiticity, q-unit, q-perp-r, and finite Krylov rank
    - any conditional receiver whose new hypothesis is the old eventual complement floor
  DOES_NOT_KILL:
    - the algebraic fact that U_i is an exact two-dimensional Krylov space
    - the r_i=0 exact-eigenvector branch
    - a future source-specific theorem controlling the literal CCM Lanczos coefficients
    - all possible infinite or adaptively source-certified Krylov methods
    - the underlying Goal058 same-family route
  LOGIC_GUARD: failure of this sufficient representation does not prove failure of ground-to-trial tracking

WEAKEST_REOPENING_CONDITION:
  - >-
    An independently proved theorem for the literal source family giving either
    c_i=0 eventually or a cofinal quantitative bound on norm(c_i) strong enough
    for a named downstream consumer.
  - >-
    The consumer must not assume the dead tracking rate, an eventual complement
    floor, or the same uncontrolled inverse.
  - >-
    Any rank growth must be precommitted and proved from the source operator,
    with a bound on the outgoing Lanczos coefficient after that rank.

CLOSES:
  - R2_MOVING_KRYLOV_ADMISSIBILITY_DISCRIMINATOR
REMAINS_OPEN:
  - GOAL058_GROUND_TO_TRIAL_SAME_FAMILY_BRIDGE
CURRENT_SMALLEST_NAMED_GAP: GOAL058_GROUND_TO_TRIAL_SAME_FAMILY_BRIDGE
NEXT_CONTROL_ACTION: OWNER_RERANK_AFTER_R2_KILL

PREDICTION_LEDGER:
  P_R2_1_EXACT_RANK_TWO:
    fate: CONFIRMED
  P_R2_2_c_IS_SECOND_LANCZOS_RESIDUAL:
    fate: CONFIRMED
  P_R2_3_CURRENT_SOURCE_THEOREM_CONTROLS_c:
    predicted: false
    fate: CONFIRMED_BY_SOURCE_AUDIT
  P_R2_4_PROLATE_RECURRENCE_TRANSFERS_TO_LITERAL_CCM:
    predicted: false
    fate: CONFIRMED_WRONG_OBJECT
  RETROACTIVE_REPAIR: false

CLAIM_LEDGER:
  - claim: source residual identities and one-line coupling declarations are present
    scope: FINITE_CELL
    verifier: LEAN
  - claim: U_i has exact dimension two when r_i is nonzero
    scope: FINITE_CELL
    verifier: PAPER
  - claim: c_i is the second Lanczos residual
    scope: FINITE_CELL
    verifier: PAPER
  - claim: the arbitrary-tail plant defeats structural control of c_i
    scope: ABSTRACT
    verifier: PAPER
  - claim: no current production theorem or independent consumer controls c_i
    scope: COFINAL_FAMILY
    verifier: PAPER
  - claim: R2 is inadmissible at the locked source state
    scope: COFINAL_FAMILY
    verifier: PAPER

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 5

LEAN_EDIT_AUTHORIZED: false
LEAN_SOURCE_EDITED: false
DOWNSTREAM_SHIFTED_FORM_OR_W5_AUTHORIZED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Node | Verdict | Exact boundary | Tags |
|---|---|---|---|
| `r_i = 0` | **Exact eigenvector branch** | The Krylov expansion terminates, but bottomness, simplicity and the route consumer do not follow from residual zero alone. | `[FINITE_CELL][LEAN]` |
| `r_i ≠ 0`, `U_i = span{q_i,r_i/‖r_i‖}` | **Algebraically valid** | Unit norm and orthogonality give exact rank two without numerical rank detection. | `[FINITE_CELL][PAPER]` |
| Compressed block on `U_i` | **Exact** | It is the first two-step Lanczos block `[[a_i,β_i],[β_i,α_i]]`. | `[FINITE_CELL][PAPER]` |
| Outgoing coupling `c_i` | **Uncontrolled** | It is the second Lanczos residual. The literal CCM shelf supplies no bound, closure, or smaller cofinal ledger. | `[COFINAL_FAMILY][PAPER]` |
| Reflection | **Sector-only** | It preserves evenness but does not make the coupling small. | `[FINITE_CELL][LEAN]` |
| Commutator observable | **Not a norm consumer** | Its real part vanishes structurally and a committed plant keeps the residual nonzero. | `[ABSTRACT][LEAN]` |
| Prolate/Ferrers recurrence | **Wrong object for this use** | It controls another operator and cannot be imported as bandedness of `K_i`. | `[ABSTRACT][PAPER]` |
| Higher fixed Krylov rank | **No repair without a source law** | A Jacobi-chain plant places an arbitrary coefficient at the next boundary for every fixed rank. | `[ABSTRACT][PAPER]` |

## QUESTION 1 — ADMISSIBILITY

The proposed carrier is mathematically legitimate. Put

\[
\beta_i=\|r_i\|,
\qquad e_{0,i}=q_i,
\qquad e_{1,i}=r_i/\beta_i.
\]

For `r_i ≠ 0`, the committed unit and orthogonality facts imply that
`e_{0,i},e_{1,i}` are orthonormal. Hence `dim U_i = 2` exactly.

Hermiticity gives

\[
K_ie_{0,i}=a_ie_{0,i}+\beta_ie_{1,i},
\]

and, with

\[
\alpha_i=\langle e_{1,i},K_ie_{1,i}\rangle\in\mathbb R,
\]

\[
K_ie_{1,i}=\beta_ie_{0,i}+\alpha_ie_{1,i}+c_i.
\]

Thus this is not merely the original residual written as a block. It is one honest Lanczos step beyond the killed line carrier. The problem is sharper: the step exposes `c_i`, the **second Lanczos residual**, and nothing in the current source layer makes it smaller.

The exact coupling from `U_i` to `U_i^⊥` has rank at most one and operator norm `‖c_i‖`. Therefore the two-vector carrier reduces the coupling's rank, not its uncontrolled size.

## QUESTION 2 — INDEPENDENT COUPLING CONSUMER

No exact source theorem and no exact downstream consumer satisfying the request exists at the locked source state.

The closest Schur/Feshbach expression is

\[
\langle c_i,(K_i|_{U_i^\perp}-z)^{-1}c_i\rangle.
\]

This is useful only after controlling both `c_i` and the complement resolvent. Assuming the eventual complement floor merely recreates the stopped program's debt. It is not an independent consumer.

The shelf mechanisms fail for distinct reasons:

- **CCM recurrence/bandedness:** no theorem gives a finite recurrence for repeated action of the literal dense Weil matrix `K_i`.
- **Commutator:** the committed scalar observable is structurally zero in real part and does not dominate a residual norm.
- **Reflection:** it places `c_i` in the even sector but supplies no magnitude estimate.
- **Selected Ferrers/prolate theory:** it controls the differential/Jacobi packet operator, not `K_i`. The object switch is forbidden.

The three-dimensional plant is decisive. With

\[
q=e_0,
\qquad
K_M=
\begin{pmatrix}
 a&1&0\\
 1&\alpha&M\\
 0&M&\tau
\end{pmatrix},
\]

we have `r=e_1`, so `q` and `r` are orthonormal, while

\[
c=Me_2.
\]

The next coupling is arbitrarily large. Therefore the available structural hypotheses do not imply a smaller coupling ledger.

## QUESTION 3 — FIRST THEOREM OR KILL

The operative result is:

```text
KILL_R2_MOVING_KRYLOV_FESHBACH
```

No Lean theorem is authorized. A conditional receiver would have no independent production supplier and would reopen the same complement-floor/inverse obligation under a new name.

## STRONGEST ATTACK

**Objection:** the actual CCM matrices may have hidden arithmetic structure that makes `c_i` small even though the abstract plant permits arbitrary `c_i`.

**Answer:** correct. The plant does not prove that the actual `c_i` is large. It proves that the currently committed structural facts cannot control it. The source audit then finds no additional theorem exploiting literal CCM arithmetic to do so. This is enough to kill the proposed representation as the current admissible R2 transaction, but not enough to assert that no future source-specific Lanczos estimate can exist.

This boundary is why the verdict kills a route architecture, not the mathematical possibility of ground-to-trial tracking.

## FINAL PROPOSAL

Freeze the following result:

```text
The two-vector space is the exact first nontrivial Krylov carrier.
Its outgoing coupling is the exact second Lanczos residual.
No current literal-CCM theorem bounds that residual.
No current consumer uses it without reimporting the dead complement inverse/floor.
Therefore R2 does not advance the load-bearing ledger.
```

Do not increase Krylov rank, run numerics to select a rank, or formalize a receiver. Return control to the owner rerank with the original same-family tracking gap still open.

## META CLOSEOUT

**What became smaller?**

The vague question “does a moving Krylov space help?” is compressed to one exact missing object:

\[
\left\|(I-P_i)K_i\frac{r_i}{\|r_i\|}\right\|.
\]

**What was killed?**

- two-vector R2 as a source-supported repair;
- fixed-rank escalation without a rank/coupling theorem;
- prolate recurrence as a surrogate for literal CCM bandedness;
- a conditional Feshbach receiver that assumes the old floor.

**What must not be tried again?**

Do not select Krylov rank after inspecting numerical couplings. Do not call sector preservation a norm estimate. Do not move a recurrence between different operators.

**Current smallest named gap:**

```text
GOAL058_GROUND_TO_TRIAL_SAME_FAMILY_BRIDGE
```

**Next cheapest decisive test:**

Owner rerank. R2 may be reopened only after a source-specific theorem for the literal CCM family controls the outgoing Lanczos coupling with a named independent consumer.

**Memory entry:**

```yaml
iteration:
  target: GOAL058_R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR
  status: FATAL
  failed_strategy: finite moving Krylov carrier without source coupling law
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: LITERAL_CCM_SECOND_LANCZOS_RESIDUAL_CONTROL
  invariant_learned: exact Krylov rank does not imply small outgoing coupling
  forbidden_future_move: post-hoc rank selection or prolate-to-CCM recurrence transfer
  next_decisive_test: owner rerank or independent literal-CCM coupling theorem
```

## VERIFICATION HANDOFF

This verdict changes documentation only.

```text
LEAN SOURCE EDITED: no
LEAN KERNEL RUN: no
EXPECTED AXIOM PROFILE: not applicable
ROUTE STATE EDITED: no
QUARANTINE STATE EDITED: no
```
