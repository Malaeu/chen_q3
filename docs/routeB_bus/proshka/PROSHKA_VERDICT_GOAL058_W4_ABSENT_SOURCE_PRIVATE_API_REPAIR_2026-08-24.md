# STATUS: CONDITIONAL — TRY_W4_CREATE_FROZEN_FILE_WITH_PRIVATE_LOCAL_RECONSTRUCTION
```yaml
PRIMARY: TRY_W4_CREATE_FROZEN_FILE_WITH_PRIVATE_LOCAL_RECONSTRUCTION
OPERATIVE_CLASS: TRY_W4_CREATE_FROZEN_FILE_WITH_PRIVATE_LOCAL_RECONSTRUCTION
PRIMARY_COUNT: 1
DOCUMENT_ROLE: INDEPENDENT_SOURCE_API_FORK_VERDICT

TASK:
  ID: GOAL058_SELECTED_FERRERS_V_W_FIXED_K_PHASE_CLOSE
  PATH: docs/Codex/TASK_2026-08-24_goal058_selected_ferrers_phase_closure.md
  PIN: edac6cb0f86c00ec182265d0e21312ceb9a2a92b
  TASK_BLOB: aea0977448788da679992865f73ff985949ae16a

PRIOR_REPAIR:
  VERDICT_COMMIT: 461f259e1526dfb30ce423c39d26d0cae21e49c5
  VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR_2026-08-24.md
  VERDICT_BLOB: 76d70ddef8c5770fa7c2e05ab6b9fefdf64c26a0
  DECISION: TRY_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
  MATHEMATICAL_REPAIR: PRESERVED

SOURCE_EXISTENCE_AUDIT:
  AUTHORIZED_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
  AT_INITIAL_AUTHORIZATION_1fd5e432: ABSENT_404
  AT_LEDGER_REPAIR_461f259e: ABSENT_404
  AT_CURRENT_PIN_edac6cb0: ABSENT_404
  REPOSITORY_CODE_SEARCH: DOC_REFERENCES_ONLY
  CONSEQUENCE: RESUME_EXISTING_FILE_REJECTED
  REPORTED_LOCAL_KERNEL_RECEIPT: UNMATERIALIZED_NOT_A_REPOSITORY_THEOREM

SOURCE_LOCK:
  W2_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
  W2_BLOB: 0c57204461353f16ed91f1240173c90f94ad1b4d
  W3_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
  W3_BLOB: a064544af242608b8d09b94931412d1bccd5c392
  W2_PRIVATE_BLUEPRINTS:
    - selected_weighted_summable
    - firstDerivativeTerm_abs_le_closed
    - firstDerivativeSeries_abs_le_closed
    - lipschitz_pairs_closed_of_open
    - ferrersSeries_lipschitz_closed
    - normalizedPhysicalMode_lipschitz_on_window
    - selectedPacket_lipschitz_on_window
  W2_PRIVATE_DECLARATIONS_IMPORTABLE: false

FORK_DECISION:
  SELECTED: LOCAL_PRIVATE_RECONSTRUCTION_IN_AUTHORIZED_W4_FILE
  REJECTED: NARROW_PUBLIC_PACKET_LIPSCHITZ_SUPPLIER
  HISTORICAL_W2_EDIT: forbidden
  NEW_PUBLIC_HELPER_API: forbidden
  NEW_INTERMEDIATE_LEAN_FILE: forbidden
  REASON:
    - the initial authorization already freezes local reconstruction from public lower-level suppliers
    - a separate supplier must reconstruct the same private W2 chain and therefore removes no mathematical work
    - a separate supplier adds one public theorem, one file, one kernel transaction, and one new DAG edge without a second identified consumer
    - the repaired W4 public surface explicitly requires no new public theorem

EXECUTION:
  TASK_ID: H2A_4_1B_3C_1_13A_W4_CREATE_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
  MODE: CODEX_CREATE_NEW_FILE_FROM_FROZEN_PACKET
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
  LEAN_MODULE: Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2
    - Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
  ARISTOTLE: false

PUBLIC_SURFACE:
  DEFINITIONS:
    - selectedFerrersAbelLogRepresentative
    - selectedFerrersAbelLogZeroExtension
    - selectedFerrersAbelLogSeamFreeOn
    - selectedFerrersAbelLogDerivativeBudget
    - selectedFerrersAbelLogJumpBudget
  THEOREMS:
    - selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    - selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    - selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
    - selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    - selectedFerrersAbelLogZeroExtension_fourier_decay
  ADDITIONAL_PUBLIC_DECLARATIONS: forbidden

PRIVATE_RECONSTRUCTION_POLICY:
  visibility: private
  required_role:
    - weighted coefficient summability for the two selected regular-even solutions
    - closed dimensionless derivative-series bound
    - closed-window Lipschitz transport for normalized physical modes
    - exact complex selected-packet closed-window Lipschitz bound
  source_engine:
    - mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed
    - mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
    - Mode4FerrersRegularEvenProlateSolution.ferrersSeries_hasDerivAt_firstDerivativeSeries
    - selectedFerrersPreAnchorSeparation
    - selectedFerrersPreAnchorPair_spec
    - selectedFerrersPreAnchorSolution0
    - selectedFerrersPreAnchorSolution4
  private_names_may_be_cosmetic: true
  theorem_shapes_may_not_be_weakened: true

CLOSES:
  - W4_ABSENT_SOURCE_EXECUTION_MODE_AMBIGUITY
  - W4_PRIVATE_API_FORK
OPENS:
  - W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
NEXT_LOAD_BEARING_GAP: W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN

EXPECTED_AXIOM_PROFILE:
  - propext
  - Classical.choice
  - Quot.sound

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ARSENAL_MANDATE:
  ACCEPTED: true
  SIDECAR_EXECUTION_TRIGGERED: false
ARSENAL_CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
W5_COFINAL_RATE: OUTSIDE_TRANSACTION
DOWNSTREAM_W4_ASSEMBLY: NOT_AUTHORIZED
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. The source status is not `RESUME`

The authorized W4 path is absent at the initial authorization commit, at the
endpoint-ledger repair commit, and at the current phase pin. Repository code
search finds the module name only in task, answer, and verdict documents. Thus
the execution verb in the repair verdict is corrected from

```text
CODEX_RESUME_EXISTING_ONE_LEAN_NODE
```

to

```text
CODEX_CREATE_NEW_FILE_FROM_FROZEN_PACKET.
```

This correction changes no mathematical statement. It prevents an uncommitted
local compile report from being treated as a repository theorem.
`[ABSTRACT][PAPER]`

### 2. The W2 implementation is a blueprint, not an imported API

The W2 source is kernel-green and contains the needed weighted-summability and
closed-window Lipschitz proof. But the load-bearing declarations are `private`.
The W2 source record freezes only the production packet and its whole-line
bounded-variation theorem as the intended public deliverable. Therefore W4 may
reuse the mathematics and public lower-level theorem engines; it may not cite
W2 private declarations across modules. `[ABSTRACT][LEAN]`

### 3. Selected repair: reconstruct privately in the authorized W4 file

This is the smaller source-preserving repair.

A narrow public supplier would still have to reproduce the same private proof
chain because importing W2 cannot expose private names. It would merely move
the duplication into an extra file and then add one public theorem and one
kernel transaction. No second consumer of that new API is source-locked. The
extra supplier therefore has no reduction in proof cost and expands the route
surface.

The authorized W4 file already has a larger load-bearing consumer: exact
piecewise AC, exact complex derivative integrability, the full endpoint/seam
ledger, hand-written piecewise integration by parts, and fixed-`k` Fourier
decay. Reconstructing the packet Lipschitz certificate privately inside that
file keeps the public theorem packet unchanged and preserves the exact source
object. `[ABSTRACT][PAPER]`

This is a C04 firewall: a documented path and a local compile receipt are not
the same category as a committed Lean declaration. It is also a C10 firewall:
the reconstruction must target the exact production packet, not a continuous,
midpoint, real-valued, or mollified surrogate.

## FROZEN PUBLIC SURFACE

The new file must contain exactly the following public definitions and theorem
heads. Cosmetic formatting is allowed. The source object, quantifiers,
representatives, ranges, and Fourier normalization are frozen.

```lean
noncomputable def selectedFerrersAbelLogRepresentative
    (k : ℕ) : ℝ → ℂ :=
  fun x =>
    selectedFerrersAbelLimit k
      (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k))

noncomputable def selectedFerrersAbelLogZeroExtension
    (k : ℕ) : ℝ → ℂ :=
  Set.indicator
    (Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k)))
    (selectedFerrersAbelLogRepresentative k)

def selectedFerrersAbelLogSeamFreeOn
    (k : ℕ) (a b : ℝ) : Prop :=
  Set.uIcc a b ⊆
      Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k)) ∧
    ∀ n : ℕ+, ∀ x ∈ Set.uIcc a b,
      (((n : ℕ) : ℝ) *
          (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k))) ≠
        lambda_m (selectedFerrersPreAnchorIndex k)

noncomputable def selectedFerrersAbelLogDerivativeBudget
    (k : ℕ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
    ‖deriv (selectedFerrersAbelLogRepresentative k) x‖

noncomputable def selectedFerrersAbelLogJumpBudget
    (k : ℕ) : ℝ :=
  ‖selectedFerrersAbelLogRepresentative k 0‖ +
  ‖selectedFerrersAbelLogRepresentative k
      (L_m (selectedFerrersPreAnchorIndex k))‖ +
  ∑ n ∈ Finset.Icc 2 (k + 2),
    ‖((Real.sqrt
        (lambda_m (selectedFerrersPreAnchorIndex k) / (n : ℝ)) : ℝ) : ℂ) *
      selectedFerrersLemma73SourcePacket k
        (lambda_m (selectedFerrersPreAnchorIndex k))‖

theorem selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    (k : ℕ) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersLemma73SourcePacket k)
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda

theorem
    selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersAbelLogRepresentative k) a b

theorem
    selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    IntervalIntegrable
      (deriv (selectedFerrersAbelLogRepresentative k)) volume a b

theorem selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      (selectedFerrersAbelLogDerivativeBudget k +
        selectedFerrersAbelLogJumpBudget k) /
      (2 * Real.pi * |t|)

theorem selectedFerrersAbelLogZeroExtension_fourier_decay
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ,
        ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
          C / (1 + |t|)
```

The lower one-sided representative remains exactly

\[
g_k(0+)=g_k(0)-
\sqrt{\lambda_k^{-1}}\,h_k(\lambda_k).
\]

The proof must first spend this right-hand value in the sharp private
piecewise-IBP estimate. Only afterward may triangle inequality replace it by
`‖g_k(0)‖` plus the exact final `n=k+2` summand of the public jump budget.

## PRIVATE RECONSTRUCTION CONTRACT

The W4 file may recreate any number of `private` supporting lemmas. It must not
add a public weighted-summability, physical-mode Lipschitz, or packet-Lipschitz
theorem.

The reconstruction must start from public source declarations, in particular:

```text
mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed
mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
Mode4FerrersRegularEvenProlateSolution.ferrersSeries_hasDerivAt_firstDerivativeSeries
selectedFerrersPreAnchorSeparation
selectedFerrersPreAnchorPair_spec
selectedFerrersPreAnchorSolution0
selectedFerrersPreAnchorSolution4
```

The following W2 names are proof blueprints only and must never appear as
cross-module dependencies:

```text
selected_weighted_summable
firstDerivativeTerm_abs_le_closed
firstDerivativeSeries_abs_le_closed
lipschitz_pairs_closed_of_open
ferrersSeries_lipschitz_closed
normalizedPhysicalMode_lipschitz_on_window
selectedPacket_lipschitz_on_window
```

The W4 SOURCE RECORD must cite W2 blob
`0c57204461353f16ed91f1240173c90f94ad1b4d` as a blueprint and enumerate every
locally reconstructed helper. It must not claim that a private W2 theorem was
imported.

## REJECTED ALTERNATIVE

Do not create:

```text
G6N1SelectedFerrersPacketClosedWindowLipschitz.lean
```

or any equivalent public-supplier module during this transaction.

A separate supplier becomes admissible only after a second exact consumer is
identified or local reconstruction is proved impossible because a required
lower-level theorem is not public. That failure must be reported before any API
expansion; it may not be repaired post hoc in the same commit.

## VALIDATION GATE

### WORKDIR: `q3.lean.aristotle`

```bash
lake env lean \
  Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

```bash
lake build \
  Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
```

### WORKDIR: repository root

```bash
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

Every printed public declaration and every mandatory plant must have exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Success:

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIRED_AND_FIXED_K_FOURIER_DECAY_KERNEL_GREEN
```

Failure codes:

```text
W4_ABSENT_SOURCE_LOCAL_RECONSTRUCTION_GAP
W4_PRIVATE_W2_BLUEPRINT_USED_AS_IMPORTED_API
W4_PUBLIC_SURFACE_EXPANSION
W4_ZERO_ENDPOINT_RIGHT_REPRESENTATIVE_GAP
W4_REPAIRED_JUMP_BUDGET_GAP
W4_PIECEWISE_IBP_OR_DERIVATIVE_INTEGRABILITY_GAP
W4_KERNEL_OR_AXIOM_PROFILE_GAP
```

A failure of local reconstruction does not authorize editing W2, minting a
supplier, weakening the exact packet, or starting the shifted-form-domain
assembly.

## FINAL PROPOSAL

Create the authorized W4 source **from scratch** at the original path. Keep all
W2 reconstruction private. Preserve the prior endpoint-ledger repair and the
frozen public surface. Run one kernel transaction. Only after a separate
semantic-admission verdict may the phase proceed to
`W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY`.

### Registered predictions before the source test

```text
P_W4_SOURCE_FORK_1:
  p = 0.68
  The private local reconstruction reaches the frozen packet-AC theorem without
  adding a public supplier.

P_W4_SOURCE_FORK_2:
  p = 0.80
  The first failure, if any, is a Lean normal-form or complex-AC/IBP API shape,
  not a counterexample to exact packet Lipschitzness.

P_W4_SOURCE_FORK_3:
  p = 0.96
  A green source has exactly the standard axiom triple on every printed item.
```

## STRONGEST ATTACK

The strongest objection is duplication: reconstructing W2's private proof
chain inside W4 creates two implementations of the same packet-Lipschitz fact.

The objection is valid but not fatal. Privacy means there is no importable W2
fact to reuse; a new supplier would duplicate the same mathematics anyway. The
selected repair contains the duplication inside one load-bearing W4 node,
keeps it private, pins the blueprint blob, and adds no reusable API whose future
compatibility must be maintained.

If the duplicated proof cannot be reconstructed solely from public lower-level
suppliers, the correct result is a source/API blocker with the exact first
missing declaration. It is not permission to modify a historical artifact or
to invent a neighboring source object.

## CODEX DIRECTIVE

```text
Execute exactly:
  H2A_4_1B_3C_1_13A_W4_CREATE_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN

Mode:
  CREATE_NEW_FILE_FROM_FROZEN_PACKET

Create exactly:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

Ship in the same commit:
  the Lean source;
  one SOURCE RECORD satisfying docs/routeB_bus/SUPPLIER_CONTRACT.md.

Do not:
  edit G6N1SelectedFerrersPacketVariation.lean;
  edit G6N1SelectedFerrersAbelPoissonL2.lean;
  create a packet-Lipschitz supplier module;
  call private declarations across modules;
  add any public declaration beyond the frozen surface;
  start G6N1SelectedFerrersFixedKShiftedRootEnergy.lean;
  perform W5 work;
  promote Route B;
  make an RH claim.

Stop on the first exact missing public lower-level theorem and report:
  declaration sought;
  source file searched;
  why the private W2 theorem cannot be used;
  smallest faithful theorem shape that would unblock reconstruction.
```

## META CLOSEOUT

**What became smaller?**

The W4 source/API fork is reduced to one file-creation transaction with a fixed
private reconstruction policy.

**What was killed?**

- `RESUME_EXISTING_ONE_LEAN_NODE` as a false source-status description;
- an unbound local kernel receipt as repository evidence;
- editing historical W2 to expose private helpers;
- a new public packet-Lipschitz supplier without a second consumer.

**What must not be tried again?**

Do not treat documentation of a path as materialization of that path. Do not
call private W2 helpers across modules. Do not widen the public API merely to
avoid local reconstruction.

**Current smallest named gap?**

```text
W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
```

**Next cheapest decisive test?**

Compile the first source cut through
`selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval` before
continuing to seam ordering and piecewise integration by parts.

**Fate of prior registered predictions**

```text
P_W4_AC_LEAN_1:
  NOT_SCORED.
  No committed source blob exists on which to score compilation.

P_W4_AC_LEAN_2:
  PARTIALLY_CONFIRMED_AT_API_AUDIT.
  The first repository-level obstruction is source absence/private API, not a
  mathematical counterexample.

P_W4_AC_LEAN_3:
  NOT_SCORED.
  No committed source blob exists.
```

**Memory entry**

```yaml
iteration: W4_absent_source_private_API_fork
target: W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
status: OPEN_AUTHORIZED_CREATE
failed_strategy: RESUME_NONEXISTENT_SOURCE
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
invariant_learned: private_W2_blueprints_may_be_reconstructed_but_not_imported
forbidden_future_move: edit_historical_W2_or_expand_public_API_without_second_consumer
next_decisive_test: kernel_gate_packet_AC_prefix_in_new_W4_file
```
