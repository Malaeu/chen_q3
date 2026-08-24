# STATUS: CONDITIONAL — TRY_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
```yaml
PRIMARY: TRY_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
OPERATIVE_CLASS: TRY_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
PRIMARY_COUNT: 1
DOCUMENT_ROLE: INDEPENDENT_OPERATIVE_REPAIR_VERDICT

REQUEST:
  ID: REQ-2026-08-24-W4-ZERO-ENDPOINT-JUMP-LEDGER
  PATH: docs/routeB_bus/CODEX_REQ_2026_08_24_W4_ZERO_ENDPOINT_JUMP_LEDGER_MISMATCH.md
  REQUEST_INTRODUCING_COMMIT: abb10b6934456304f70a08f52f83cfa2a8264dd6
  REQUEST_SHA256: 38791b1ab648beb4b5682d55cd1984576747dc3e179d32260dbeb264f697dbbc
  REQUEST_GIT_BLOB: 9e58266f1424c0b92ac85fab304c60741d9d80ea
  SOURCE_COMMIT: 76f523dcd4167053ecc2772f5344b58fe7e23392
  PHASE_KEY_HASH: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
  BLOCKER_FINGERPRINT: 0aabc895314f59028e540621af5e8382478aa7dbb6b010e04f779c8545a6ae04

SOURCE_LOCK:
  PRIOR_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_PIECEWISE_AC_AUTHORIZATION_2026-08-24.md
  PRIOR_VERDICT_BLOB: f7a2b40af604223e6bb7259793da3a8f5d7fdafb
  W2_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
  W2_BLOB: 0c57204461353f16ed91f1240173c90f94ad1b4d
  W3_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
  W3_BLOB: a064544af242608b8d09b94931412d1bccd5c392
  ESTAR_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarActualProlateEStarMemLp.lean
  ESTAR_BLOB: 7b13f27925392569128e49ffb05591c7fbd9e8ba
  JUDGE_RERAN_KERNEL: false

ADJUDICATION:
  frozen_jump_budget_as_written: INSUFFICIENT_FOR_THE_REPORTED_IBP_PROOF
  frozen_fourier_decay_statement_refuted: false
  finite_jump_fourier_decay_route: SURVIVES
  endpoint_cancellation_search: NOT_AUTHORIZED
  selected_repair: EXTEND_PUBLIC_SEAM_SUM_THROUGH_N_EQ_K_PLUS_2
  lower_one_sided_value: FULL_VALUE_MINUS_EXPLICIT_N_EQ_K_PLUS_2_ENDPOINT_TERM
  n_eq_k_plus_2_payment: SEPARATE_LAST_SUMMAND
  absorbed_by_endpoint_zero_or_norm_inequality: false
  production_packet_changed: false
  full_endpoint_convention_changed: false
  complex_valuedness_changed: false
  fixed_k_scope_changed: false

TASK_ID: H2A_4_1B_3C_1_13A_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR_LEAN
MODE: CODEX_RESUME_EXISTING_ONE_LEAN_NODE
LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
LEAN_MODULE: Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
ARISTOTLE: false

PUBLIC_SURFACE_POLICY:
  existing_signatures_preserved: true
  corrected_definition:
    - selectedFerrersAbelLogJumpBudget
  existing_theorems_preserved:
    - selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    - selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    - selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
    - selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    - selectedFerrersAbelLogZeroExtension_fourier_decay
  new_public_theorem_required: false
  local_private_right_limit_helpers_required: true

KERNEL_RECEIPT_REPORTED_BY_REQUEST:
  first_three_public_surfaces: GREEN
  axiom_profile:
    - propext
    - Classical.choice
    - Quot.sound
  judge_independently_verified_receipt: false

CLOSES:
  - W4_ZERO_ENDPOINT_JUMP_LEDGER_MISMATCH
  - W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
  - W4_LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY
OPENS:
  - W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
LEDGER_EFFECTIVE_ONLY_AFTER_KERNEL_GREEN: true
NEXT_LOAD_BEARING_GAP: W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: BOUNDARY_CASE
ROUTE_SCORE: 5

ARSENAL_MANDATE:
  ACCEPTED: true
  SIDECAR_EXECUTION_TRIGGERED: false
ARSENAL_CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

EXPECTED_AXIOM_PROFILE:
  - propext
  - Classical.choice
  - Quot.sound

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
W5_COFINAL_RATE: OUTSIDE_TRANSACTION
DOWNSTREAM_W4_ASSEMBLY: NOT_AUTHORIZED
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Item | Verdict | Exact boundary | Tags |
|---|---|---|---|
| Packet AC on its closed physical window | **SURVIVES** | Exact complex production packet; no midpoint or real surrogate. | `[ABSTRACT][LEAN]` |
| Log representative AC and derivative integrability | **SURVIVES** | Only on seam-free compact intervals. | `[ABSTRACT][LEAN]` |
| Old public jump budget | **INSUFFICIENT** | It pays `‖g(0)‖`, but the first IBP component starts at the right limit, and the omitted `n=k+2` endpoint term is unpaid. | `[ABSTRACT][PAPER]` |
| Endpoint cancellation `h_k(lambda_k)=0` | **NOT AVAILABLE** | No committed supplier and no source hypothesis forces it. Absence of a supplier does not prove nonvanishing. | `[ABSTRACT][PAPER]` |
| Repaired budget | **AUTHORIZED** | Keep `‖g(0)‖`; extend the seam sum from `2..k+1` to `2..k+2`. | `[ABSTRACT][CONDITIONAL]` |
| Fixed-`k` Fourier decay | **OPEN UNTIL GATE** | Same theorem statement, now spending the repaired budget. | `[ABSTRACT][CONDITIONAL]` |
| Shifted form-domain assembly | **NOT STARTED** | Remains the next transaction after this node is kernel-green. | `[ABSTRACT][CONDITIONAL]` |

The operative decision is **TRY**, not **KILL**.  The reported failure of one
sufficient ledger does not prove that the old numerical bound is false.  It
proves that the frozen proof contract omitted a boundary contribution.  An
unconditional one-summand repair exists, so killing the finite-jump
representation would reverse the logical direction of the finding.
`[ABSTRACT][PAPER]`

The operative decision is also not `RUN_W4_ZERO_ENDPOINT_CANCELLATION_IDENTITY`.
An endpoint cancellation theorem would be stronger than needed, is absent from
the shelf, and would introduce a new analytic supplier merely to avoid one
explicit finite term.  The repaired ledger has lower cost and no source-object
risk. `[ABSTRACT][PAPER]`

## MATHEMATICAL ADJUDICATION

Fix

\[
i_k=\operatorname{selectedFerrersPreAnchorIndex}(k),\qquad
m_k=i_k.m=k+2,
\]

\[
\lambda_k=\lambda_m(i_k)=\sqrt{k+2},\qquad
h_k=\operatorname{selectedFerrersLemma73SourcePacket}(k),
\]

and

\[
g_k(x)=\operatorname{selectedFerrersAbelLimit}
\left(k,\frac{e^x}{\lambda_k}\right).
\]

The committed source provides all structural facts needed for the boundary
audit:

1. `sourcePositiveIndexFinset i_k` is the inclusive positive range
   `1..m_k`.
2. `lambda_m i_k * lambda_m i_k = m_k`.
3. The production packet is only known to vanish **outside** the closed window
   `[-lambda_k,lambda_k]`; its endpoint value is retained.
4. W3's finite seam set contains the equations `u=lambda_k/n`, including
   `n=m_k`, hence `u=lambda_k⁻¹`, the lower selected-window endpoint.
5. The half-center shadow is continuous.

`[ABSTRACT][LEAN]`

At `x=0`, the top positive index contributes at the full endpoint:

\[
m_k\frac{e^0}{\lambda_k}=\lambda_k.
\]

Define the explicit endpoint term

\[
J_{0,k}:=\sqrt{\lambda_k^{-1}}\,h_k(\lambda_k).
\]

For every `x>0`,

\[
m_k\frac{e^x}{\lambda_k}=\lambda_k e^x>\lambda_k,
\]

so that term vanishes by the exact closed-window support theorem.  Therefore
the lower right-hand representative is

\[
g_k(0+):=g_k(0)-J_{0,k}.
\]

This is not a change of production representative.  It is the one-sided value
consumed by integration by parts on the first open component.  The isolated
full value `g_k(0)` remains exactly the production value. `[ABSTRACT][PAPER]`

The only unconditional norm comparison is

\[
\|g_k(0+)\|
\le
\|g_k(0)\|+\|J_{0,k}\|.
\]

No committed theorem supplies either

\[
h_k(\lambda_k)=0
\]

or

\[
\|g_k(0+)\|\le\|g_k(0)\|.
\]

Consequently the old budget does not dominate the boundary term produced by
the reported IBP decomposition. `[ABSTRACT][PAPER]`

## FROZEN REPAIR

### 1. Lower one-sided representative

Use local private helpers with the following exact meaning.  Equivalent Lean
normal forms are allowed, but not a different representative.

```lean
private noncomputable def selectedFerrersAbelLogLowerEndpointSeam
    (k : ℕ) : ℂ :=
  (((Real.sqrt
      (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ : ℝ) : ℂ) *
    selectedFerrersLemma73SourcePacket k
      (lambda_m (selectedFerrersPreAnchorIndex k)))

private noncomputable def selectedFerrersAbelLogLowerRightValue
    (k : ℕ) : ℂ :=
  selectedFerrersAbelLogRepresentative k 0 -
    selectedFerrersAbelLogLowerEndpointSeam k
```

The node must prove a right-limit statement equivalent to:

```lean
private theorem selectedFerrersAbelLogRepresentative_tendsto_lowerRightValue
    (k : ℕ) :
    Tendsto (selectedFerrersAbelLogRepresentative k)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (selectedFerrersAbelLogLowerRightValue k))
```

It must also prove that `selectedFerrersAbelLogLowerEndpointSeam k` is exactly
the `n=k+2` term in the repaired public seam sum.  This equality spends
`lambda_k^2=k+2`; it must not be accepted by numerical normalization.
`[ABSTRACT][CONDITIONAL]`

### 2. Corrected exact public jump-budget definition

Replace only the upper endpoint of the finite seam sum.  Keep the public name
and type unchanged.

```lean
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
```

The `n=k+2` summand pays `‖J_{0,k}‖` separately.  It is **not** absorbed by an
endpoint cancellation, a midpoint convention, or the unsupported inequality
`‖g_k(0+)‖≤‖g_k(0)‖`.

The formula is an exact public **safe budget**.  It is not claimed to be the
minimal total jump mass: the isolated point value is Fourier-invisible, and a
sharper private bound may use `‖g_k(0+)‖` directly.  The public over-budget is
chosen because it is unconditional and changes only one finite range endpoint.
`[ABSTRACT][PAPER]`

### 3. Corrected off-zero Fourier-decay theorem

Keep the existing theorem statement.  It now refers to the corrected
`selectedFerrersAbelLogJumpBudget`.

```lean
theorem selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      (selectedFerrersAbelLogDerivativeBudget k +
        selectedFerrersAbelLogJumpBudget k) /
      (2 * Real.pi * |t|)
```

The proof must first establish the sharper local inequality whose lower
boundary term is `‖selectedFerrersAbelLogLowerRightValue k‖`.  Only then may it
apply

\[
\|g_k(0+)\|\le\|g_k(0)\|+\|J_{0,k}\|
\]

and rewrite `J_{0,k}` as the `n=k+2` summand.  This order prevents the same
point-value/right-limit mismatch from being hidden by algebraic simplification.
`[ABSTRACT][CONDITIONAL]`

### 4. Global fixed-`k` decay theorem

Keep the existing quantifier spine and conclusion:

```lean
theorem selectedFerrersAbelLogZeroExtension_fourier_decay
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ,
        ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
          C / (1 + |t|)
```

The result remains `forall k, exists C_k`; no uniform or cofinal rate enters
this transaction. `[ABSTRACT][CONDITIONAL]`

## PROOF ORDER

1. Preserve the already reported kernel-green packet AC, log-representative AC,
   and complex derivative-integrability declarations without statement change.
2. Prove `m_k=k+2`, `lambda_k^2=m_k`, and membership of the top index in
   `sourcePositiveIndexFinset i_k` from committed definitions.
3. Decompose the lower finite comb into the erased-index sum plus the exact
   `n=k+2` endpoint term.
4. Prove that the top-index term is zero for every `x>0` and that all remaining
   finite terms tend to their values at `x=0` from the right.
5. Obtain the exact right limit `g_k(0+)=g_k(0)-J_{0,k}`.
6. Run piecewise complex integration by parts using:
   - `g_k(0+)` at the first lower boundary;
   - the internal seams `2..k+1`;
   - the left limit `g_k(L)` at the upper zero-extension boundary.
7. Telescope before taking norms.  Do not introduce the isolated value
   `g_k(0)` into the IBP identity itself.
8. Apply the triangle inequality to the lower right value and rewrite
   `J_{0,k}` as the final `n=k+2` summand of the corrected public budget.
9. Derive the unchanged `C_k/(1+|t|)` theorem from the corrected off-zero bound
   and the ordinary `L1` Fourier bound near zero.
10. Print axioms for every public declaration and every mandatory plant.

## MANDATORY PLANTS

Retain the four plants from the prior authorization and add:

```text
full_endpoint_value_does_not_control_lower_right_value_without_seam_plant
  Produce g0, right, J0 in C with g0 = right + J0 and
  norm(right) > norm(g0).  This kills the old unsupported inequality.

lower_endpoint_is_also_production_seam_plant
  Instantiate lambda^2 = k+2 and show the top finite index hits lambda at x=0
  but lies strictly outside the packet support for every x>0.
```

The endpoint plant must use exact arithmetic and the exact production support
theorem.  A float check or a midpoint packet does not count.

The prior guards remain binding:

```text
boundedVariation_without_absoluteContinuity_plant
ae_equal_representatives_can_disagree_on_absoluteContinuity_plant
global_absolute_continuity_fails_for_finite_jump_sources_plant
fixed_k_decay_does_not_supply_uniform_family_rate_plant
L2_WITHOUT_LOG_WEIGHTED_ENERGY
FULL_ENDPOINT_VS_MIDPOINT_SEAM
ORDINARY_FOURIER_VS_SYNTHESIZED_ISOMETRY
FIXED_K_FINITE_NOT_COFINAL_RATE
```

## REQUIRED IMPORTS AND EXISTING SUPPLIERS

Keep the authorized imports and add the exact finite-support supplier if it is
not already in the transitive import graph:

```lean
import Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2
import Q3.Proofs.RouteB.D0PstarActualProlateEStarMemLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
```

The load-bearing committed suppliers are:

```text
sourcePositiveIndexFinset
selectedFerrersLemma73SourcePacket
selectedFerrersAbelLimit
lambda_m
L_m
selectedFerrersPreAnchorIndex
prolateCombination_windowFiniteSupport
mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed
```

Private W2/W3 helpers remain proof blueprints only.  Do not call them across
modules.

## VALIDATION COMMANDS

The authorized path and commands are unchanged.

```text
WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

WORKDIR: q3.lean.aristotle
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

Every printed declaration and plant must have exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Success is:

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIRED_AND_FIXED_K_FOURIER_DECAY_KERNEL_GREEN
```

The failure codes are:

```text
W4_LOWER_RIGHT_LIMIT_SOURCE_GAP
W4_N_EQ_K_PLUS_2_SEAM_REWRITE_GAP
W4_ZERO_ENDPOINT_REPAIR_KERNEL_OR_SEMANTIC_GAP
```

Any `sorryAx`, changed production endpoint, removed complex component, widened
scope, or hidden cancellation returns the semantic failure code, regardless of
whether another declaration compiles.

## SEMANTIC ADMISSION AND PROVENANCE

All prior locks remain unchanged:

```text
source packet:
  selectedFerrersLemma73SourcePacket k

target multiplicative representative:
  selectedFerrersAbelLimit k

additive coordinate:
  x = log(lambda_m i * u)
  u = exp(x) / lambda_m i

selected index:
  i = selectedFerrersPreAnchorIndex k

selected window:
  x in [0, L_m i]
  u in I_m i

endpoint convention:
  production full endpoint values

lower one-sided interpretation:
  right limit = full lower value minus the explicit n=k+2 endpoint term

shadow:
  +(1/2) * selectedFerrersLemma73SourcePacket k 0 * sqrt(u)

scalar category:
  complex-valued throughout

Fourier provenance:
  ordinary Fourier decay is proved for the direct representative;
  synthesized-isometry transfer is only a.e. and is spent downstream

scope:
  fixed k only
```

The new verdict supersedes only the prior verdict's lower-endpoint seam range
and the public jump-budget body.  It does not mutate or revoke any historical
artifact. `[ABSTRACT][PAPER]`

## FORBIDDEN SHORTCUTS

- Do not replace the full-endpoint packet by midpoint, zero-endpoint, continuous,
  or mollified data.
- Do not assert `h_k(lambda_k)=0` without an exact supplier.
- Do not assert `‖g_k(0+)‖≤‖g_k(0)‖`.
- Do not use `g_k(0)` as the first IBP boundary value.
- Do not omit the `n=k+2` term after using the triangle inequality.
- Do not transport pointwise AC or one-sided limits through a.e. equality.
- Do not apply the global smooth `fourier_deriv` theorem.
- Do not call private W2/W3 declarations across modules.
- Do not infer shifted form-domain membership from W3 `L2` convergence.
- Do not start the downstream W4 assembly.
- Do not perform W5 cofinal-rate work.
- Do not edit historical pushed artifacts, `Q3.Main`, route state, `BUS_010`, or
  any RH export.

## FINAL PROPOSAL

Resume the already authorized one-file W4 node.  Preserve its kernel-green
first half.  Repair exactly one public definition by changing

```text
Finset.Icc 2 (k+1)
```

to

```text
Finset.Icc 2 (k+2).
```

Prove the right-limit identity before the IBP telescope, spend the new last
summand only through the triangle inequality, and rerun the full three-command
gate.  Do not search for endpoint cancellation. `[ABSTRACT][CONDITIONAL]`

## STRONGEST ATTACK

The strongest objection is:

> The absence of a repository theorem `h_k(lambda_k)=0` does not prove the old
> Fourier bound false.  Why modify the public budget instead of first proving
> the cancellation?

Correct.  This verdict does **not** claim the old bound is false.  It rejects the
reported proof contract because its boundary ledger does not dominate the term
actually produced by IBP.  The unconditional repair costs one explicit finite
summand, preserves every source convention, and has no effect on the fixed-`k`
convergence class.  A cancellation search would be a stronger, more expensive
new theorem with no downstream need.  K2 therefore selects the ledger repair.
`[ABSTRACT][PAPER]`

The second objection is:

> The corrected budget double-counts an isolated endpoint value that the
> Fourier integral cannot see.

Also correct.  The repaired public budget is deliberately safe rather than
minimal.  The sharp private IBP ledger uses `‖g_k(0+)‖`; the public theorem
majorizes it by `‖g_k(0)‖+‖J_{0,k}‖`.  This overcount cannot invalidate the
upper bound and avoids changing the public endpoint convention. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
Execute only:
  H2A_4_1B_3C_1_13A_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR_LEAN

Resume exactly:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

Preserve the three reported kernel-green public declarations.

Add local exact lower-endpoint seam and right-limit helpers.
Change only the public jump-budget seam range from 2..k+1 to 2..k+2.
Prove the sharp right-limit IBP estimate first, then derive the public budgeted
bound by triangle inequality.

Run the three validation commands and print axioms for every public theorem and
plant.

Do not create a downstream assembly file.
Stop on the first right-limit, endpoint-seam rewrite, source-object, or axiom
mismatch and report the exact smallest failed statement.
```

## META CLOSEOUT

**What became smaller?**

The W4 failure is no longer an unspecified piecewise-IBP problem.  It is one
missing finite endpoint summand and one exact right-limit identity.

**What was killed?**

- the classification of all production seams as only `2..k+1`;
- the use of the isolated full value `g_k(0)` as the first IBP boundary value;
- the unsupported inequality `‖g_k(0+)‖≤‖g_k(0)‖`;
- endpoint cancellation as an implicit assumption.

**What must not be tried again?**

Do not repair the mismatch by changing the packet representative, deleting the
full endpoint value, or treating absence of a cancellation supplier as proof of
noncancellation.

**Current smallest named gap?**

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
```

**Next smallest named gap after a green gate?**

```text
W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
```

**Next cheapest decisive test?**

Compile the same node with the repaired range and inspect the exact right-limit
and `n=k+2` rewrite obligations before any downstream work.

**Fate of prior registered predictions**

```text
P_W4_1:
  CONFIRMED.
  Exact fixed-k representative is piecewise AC with finite jumps.

P_W4_2:
  SURVIVES_WITH_EXPLICIT_LEDGER_REPAIR.
  Piecewise IBP still yields fixed-k 1/(1+|t|) decay; the old lower-endpoint
  budget was incomplete.

P_W4_3:
  CONFIRMED.
  No uniform-in-k or cofinal rate follows.

P_W4_AC_LEAN_1:
  REFUTED.
  The frozen complete public packet did not compile unchanged; its jump budget
  required correction.

P_W4_AC_LEAN_2:
  REFUTED_AS_FAILURE_CLASS.
  The first blocking failure was an endpoint-ledger mismatch, not private API
  reconstruction or complex derivative API shape.

P_W4_AC_LEAN_3:
  PARTIALLY_CONFIRMED_FIRST_HALF; FULL_NODE_UNTESTED.
  The three reported green declarations have the standard triple; the repaired
  full node has not yet passed the gate.
```

No prediction is retroactively rewritten.

**Predictions registered before the repaired Lean test**

```text
P_W4_ENDPOINT_REPAIR_1:
  p = 0.90
  Extending the seam sum through k+2 and proving the explicit right limit closes
  the Fourier-decay theorem without changing any public theorem statement.

P_W4_ENDPOINT_REPAIR_2:
  p = 0.86
  The first failure, if any, is a Lean normal-form issue in the right-limit or
  final-summand rewrite, not a counterexample to fixed-k Fourier decay.

P_W4_ENDPOINT_REPAIR_3:
  p = 0.96
  A green repaired node has exactly the standard axiom triple.
```

**Memory entry**

```yaml
iteration: W4_zero_endpoint_jump_ledger_repair
target: W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
status: OPEN_AUTHORIZED
failed_strategy: classify_lower_endpoint_only_as_zero_extension_jump
cognitive_operator_used: BOUNDARY_CASE
new_gap_name: W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
invariant_learned: a full endpoint point-value and the one-sided IBP value are distinct ledger objects when an active term disappears immediately to the right
forbidden_future_move: use_full_lower_value_as_right_limit_or_hide_n_eq_k_plus_2
next_decisive_test: compile_repaired_same_node_with_exact_right_limit_and_extended_seam_sum
```
