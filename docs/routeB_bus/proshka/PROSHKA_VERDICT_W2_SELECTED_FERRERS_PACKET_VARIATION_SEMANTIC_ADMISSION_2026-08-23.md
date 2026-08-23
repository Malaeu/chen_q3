# STATUS: PROVED — W2 SELECTED FERRERS PACKET VARIATION IS SEMANTICALLY ADMITTED

```yaml
PRIMARY: SEMANTICALLY_ADMIT_W2_SELECTED_FERRERS_PACKET_VARIATION
PRIMARY_COUNT: 1

ANSWERS_TASK:
  H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  TRANSACTION_COMMIT: 9a1f0017d63e90bb21ac44ad0b64e171ec679843
  TRANSACTION_PARENT: 460b017a4effe3755b4b8b99f45689575dd46564
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
  LEAN_BLOB: 0c57204461353f16ed91f1240173c90f94ad1b4d
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_2026-08-23.md
  SOURCE_RECORD_BLOB: 49c4451b35b39894dd1742bae67974eb564ba899

KERNEL_GATE_REPORTED:
  lake_env_lean: EXIT_0
  lake_build: PASS_7817_JOBS
  q3_check: EXIT_0
  warnings: ZERO
  sorryAx: ABSENT
  AXIOM_PROFILES:
    selectedFerrersLemma73SourcePacket_boundedVariationOn:
      [propext, Classical.choice, Quot.sound]
    strict_compact_derivative_bound_does_not_supply_closed_endpoint_bound_plant:
      [propext, Classical.choice, Quot.sound]

JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN: PROVED
  exact_source_packet: PRESERVED
  production_full_endpoint_values: PRESERVED
  variation_domain_Set_univ: PRESERVED
  midpoint_substitution: ABSENT
  endpoint_jumps_paid_explicitly: true
  cofinal_rate_claimed: false

PUBLIC_SURFACE:
  selectedFerrersLemma73SourcePacket:
    status: ADMITTED
  selectedFerrersLemma73SourcePacket_boundedVariationOn:
    status: ADMITTED
    conclusion: BoundedVariationOn_packet_Set_univ

CLOSES:
  - W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE
OPENS: []

NEXT_LOAD_BEARING_GAP:
  W3_DIRICHLET_JORDAN_SINE_HARMONIC_AND_MIDPOINT_SOURCE_LOCK

NEXT_TRANSACTION:
  TASK_ID: H2A_4_1B_3C_1_12_W3_ABEL_SOURCE_AND_API_LOCK_PREFLIGHT
  MODE: READ_ONLY_MATH_AND_API_PREFLIGHT
  EXECUTION_AUTHORIZED_UNDER_STANDING_NIGHT_GRANT: true
  LEAN_EDIT: false
  ARISTOTLE: false
  NUMERICS: false

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

PRIOR_PREDICTION_FATES:
  P_W2_1_0_88: CONFIRMED
  P_W2_2_0_81: CONFIRMED
  P_W2_3_0_72: CONFIRMED
  LIKELIEST_FAILURE: REFUTED_AS_BLOCKER
  RETROACTIVE_REPAIR: false

SCOPE: ABSTRACT
VERIFIER: LEAN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Node | Verdict | Exact boundary | Tags |
|---|---|---|---|
| **W1 actual-Fourier crosswalk** | **PROVED** | The synthesized `L²` image equals almost everywhere the ordinary Fourier integral of the additive log-window zero extension. | `[ABSTRACT][LEAN]` |
| **W2 selected packet variation** | **PROVED** | The exact source-scaled selected Ferrers packet, with production full endpoint values, has bounded variation on `Set.univ`. | `[ABSTRACT][LEAN]` |
| **W3 Abel `L²` lock** | **OPEN** | Exact midpoint/full-endpoint crosswalk plus Dirichlet–Jordan and universal sine-harmonic control must be source/API locked before a Lean transaction. | `[ABSTRACT][CONDITIONAL]` |
| **W4 fixed-`k` root energy** | **OPEN AFTER W3** | Finite-jump Fourier decay and logarithmically weighted shifted-form energy. | `[ABSTRACT][CONDITIONAL]` |
| **W5 cofinal rate** | **OPEN LATER** | W2 is qualitative and universal in `k`; it supplies no cofinal variation or root-energy rate. | `[COFINAL_FAMILY][CONDITIONAL]` |

## SEMANTIC AUDIT

### 1. The theorem proves the exact requested object

The public packet is definitionally the source-scaled production combination:

```lean
selectedFerrersLemma73SourceScale k *
  prolateCombination (selectedFerrersPreAnchorPair k)
```

No neighboring window, witness class, normalization, or midpoint representative is introduced.

`[ABSTRACT][LEAN]`

### 2. The closed-endpoint derivative problem is solved, not bypassed

The proof derives the polynomial bound

\[
|P_n'(x)|\le n(n+1),\qquad x\in[-1,1],
\]

from the exact Legendre flux identity and the closed bound `|P_n| ≤ 1`. It does not substitute `r=1` into the old strict-subinterval majorant containing `(1-r²)⁻¹`.

The mandatory plant proves that the old interior factor diverges along `r_k=1-(k+2)⁻¹`. Therefore the source distinguishes the valid closed-window argument from the invalid shortcut.

`[ABSTRACT][LEAN]`

### 3. The derivative series carries the required weighted summability

The proof uses the source `tail_splice` through the already checked polynomially weighted recurrence theorem at weight two:

\[
\sum_q (q+1)^2|a_q|<\infty.
\]

This is the correct budget for the degree-quadratic Legendre derivative bound. The weaker unweighted absolute summability is not substituted.

`[ABSTRACT][LEAN]`

### 4. Physical scaling and normalization are retained

The closed dimensionless Lipschitz estimate is transported through:

```text
physical scale sqrt(m);
L² normalization;
mode-zero/mode-four combination;
I0 and I4;
normalizing denominator;
exact complex selected source scale.
```

The proof treats a degenerate denominator in Lean without adding an unproved positivity premise. On the production source family the stronger pair facts remain available, but no hidden hypothesis is introduced into W2.

`[ABSTRACT][LEAN]`

### 5. The two endpoint jumps are paid explicitly

The whole line is decomposed as:

```text
Iic(-lambda)
union Icc(-lambda,lambda)
union Ici(lambda).
```

The middle interval is Lipschitz and hence of bounded variation. Each zero tail contributes at most one endpoint jump through a separate `eVariationOn.union` ledger.

The proof does not assume the production endpoint values vanish and does not replace them by half-values. This is the exact C04/C10 boundary required by the later Abel construction.

`[ABSTRACT][LEAN]` **[C04][C10]**

### 6. Scope is qualitative, not cofinal quantitative

The theorem is universal in `k`, but it asserts only finite variation for each exact packet. It does not provide a uniform total-variation constant, an Abel envelope rate, a shifted-form root-energy rate, or a cofinal limit.

Therefore W2 closes one regularity supplier and nothing beyond it.

`[COFINAL_FAMILY][PAPER]`

## FINAL PROPOSAL

Freeze the W2 source and source record. Do not reopen the Legendre endpoint estimate or replace the production packet by a midpoint object.

The next transaction is a read-only source/API lock for W3. It must decide the exact theorem packets before any Lean edit:

```text
1. production full-endpoint packet -> midpoint representative:
     equality a.e./in L1/L2, but not pointwise at ±lambda;

2. Dirichlet–Jordan convergence for the exact bounded-variation midpoint class;

3. universal sine-harmonic primitive bound:
     sup_{N,y} |sum_{n=1}^N sin(2*pi*n*y)/n| <= C_sin;

4. Abel partial-sum envelope with the reflected factor u^(-1/2):
     |E_r^vee(f)(u)| <= C * lambda^(3/2) * W_k
     on [lambda^(-1),lambda];

5. one fixed-k L2 dominated-convergence consumer.
```

W4 finite-jump decay and root energy remain a separate later transaction.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The source proves variation of a convenient midpoint representative, not the production full-endpoint packet.

The objection fails. The public theorem is about the production packet itself. The proof retains the closed-window endpoint values and pays both jumps explicitly. No midpoint definition appears in the public surface.

The second objection is:

> Interior analyticity plus endpoint continuity was silently relabeled as bounded variation.

The objection also fails. W2 derives a uniform closed-window derivative bound from weighted coefficient summability, obtains a Lipschitz estimate, and then constructs the whole-line variation ledger. The earlier analytic-continuity shortcut is not used.

The remaining W3 warning is different: Dirichlet–Jordan must act on the midpoint convention, and transport to production objects is only through a.e./`L¹`/`L²` equality. That future category change is not part of W2.

## CODEX DIRECTIVE — STANDING-NIGHT-GRANT READ-ONLY PREFLIGHT

```text
TASK_ID:
  H2A_4_1B_3C_1_12_W3_ABEL_SOURCE_AND_API_LOCK_PREFLIGHT

MODE:
  READ_ONLY_MATH_AND_API_PREFLIGHT
  NO LEAN EDIT
  NO NUMERICS
  NO ARISTOTLE
  ONE REPORT

READ_FIRST:
  docs/CODEX_CONTROL.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  docs/routeB_bus/H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT_2026-08-23.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_W2_SELECTED_FERRERS_PACKET_VARIATION_SEMANTIC_ADMISSION_2026-08-23.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean

SEARCH_PINNED_MATHLIB_AND_PROJECT_FOR:
  BoundedVariationOn Fourier series convergence midpoint
  Dirichlet Jordan
  conjugate Dirichlet kernel primitive
  partial sums sine over n uniformly bounded
  Abel summation Fourier coefficients
  Stieltjes integration bounded variation
  ae equality indicator endpoint finite set

OBJECT_LOCK:
  source packet:
    selectedFerrersLemma73SourcePacket k
  endpoint convention:
    PRODUCTION_FULL_ENDPOINT
  W3 analysis object:
    explicitly defined MIDPOINT representative
  permitted crosswalk:
    a.e. equality and L1/L2 equality only
  forbidden:
    pointwise equality at the two endpoints

REQUIRED_OUTPUT:
  A. Exact pinned declaration names and types if the classical suppliers exist.
  B. If absent, minimal source-faithful theorem statements and proof routes.
  C. Exact midpoint/full-endpoint crosswalk contract.
  D. Exact sine-harmonic bound, including normalization `2*pi`.
  E. Exact reflected Abel envelope including `u^(-1/2)` and hence the
     `lambda^(3/2)` scale.
  F. One smallest Lean transaction selected from the resulting dependency map.

MANDATORY_PLANTS:
  P_W3_1_FULL_ENDPOINT_NE_MIDPOINT_POINTWISE:
    nonzero endpoint value; expected unequal at endpoint, equal a.e.

  P_W3_2_CONDITIONAL_SERIES_NE_TSUM:
    alternating harmonic series; expected Abel/conditional value differs from
    an unjustified `tsum` interpretation.

  P_W3_3_BV_WITHOUT_COEFFICIENT_NORMALIZATION:
    verify that every Fourier sign and `2*pi` convention is source-derived,
    not recalled.

PASS:
  W3 source/API dependencies are exact and source-locked;
  no theorem name is taken from memory;
  midpoint/full-endpoint categories are separated;
  the `u^(-1/2)` factor survives the ledger;
  one theorem-sized next Lean target is emitted.

FAILURE_CODES:
  W3_DIRICHLET_JORDAN_SOURCE_MISSING
  W3_SINE_HARMONIC_NORMALIZATION_GAP
  W3_MIDPOINT_PRODUCTION_OBJECT_CONFLATION
  W3_REFLECTED_U_MINUS_HALF_FACTOR_DROPPED
  W3_PINNED_API_ABSENT_REPRESENTATION_SHIFT_REQUIRED

REPORT_PATH:
  docs/routeB_bus/H2A_4_1B_3C_1_12_W3_ABEL_SOURCE_AND_API_LOCK_PREFLIGHT_2026-08-23.md
```

## META CLOSEOUT

**What became smaller?**

The W2 regularity question is completely removed. The Abel chain now starts from a precise source/API acquisition problem rather than an unproved variation assumption.

**What was killed?**

```text
interior derivative bound evaluated at the endpoint;
unweighted coefficient summability as a derivative budget;
endpoint values assumed zero;
midpoint representative substituted for production packet;
qualitative BV relabeled as a cofinal rate.
```

**What must not be tried again?**

Do not reopen W2, differentiate the existing `C⁰` rate, or start W4 root-energy estimates before W3 fixes the exact Abel limit object.

**Current smallest named gap:**

```text
W3_DIRICHLET_JORDAN_SINE_HARMONIC_AND_MIDPOINT_SOURCE_LOCK.
```

**Next cheapest decisive test:**

Search the pinned source tree for the two classical suppliers and freeze the exact midpoint/full-endpoint crosswalk before writing Lean.

```yaml
iteration:
  target: W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE
  status: PROGRESS
  failed_strategy: INTERIOR_ANALYTICITY_AS_GLOBAL_VARIATION
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: W3_DIRICHLET_JORDAN_SINE_HARMONIC_AND_MIDPOINT_SOURCE_LOCK
  invariant_learned: production full endpoint values and midpoint analysis representatives are equal only a.e.
  forbidden_future_move: do_not_use_midpoint_pointwise_identity_or_drop_reflected_u_minus_half
  next_decisive_test: pinned_source_and_api_search_for_W3
  progress_class: PROOF_PROGRESS
  route_score: 5
```
