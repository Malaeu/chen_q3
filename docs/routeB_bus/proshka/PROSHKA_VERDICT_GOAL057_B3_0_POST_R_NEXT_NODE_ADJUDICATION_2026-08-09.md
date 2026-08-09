# STATUS: OPEN — B3.0S EXACT SHIFTED ARCHIMEDEAN FORM-DOMAIN DENSITY SELECTED FOR SCRATCH PREFLIGHT; PRODUCTION FORBIDDEN

```yaml
BINARY_RULING: SELECT_EXACTLY_ONE_SMALLEST_CHILD
SELECTED_CHILD: GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY
PRODUCTION_AUTHORIZED: false
SCRATCH_REQUIRED: true
SCRATCH_PATH: q3.lean.aristotle/Goal057B3_0S_ShiftedArchFormDomainDensity_Scratch.lean

PRIMARY: TRY_GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT
OPERATIVE_CLASS_COUNT: 1

TRANSACTION:
  ID: GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT
  MODE: UNTRACKED_EXACT_LEAN_PREFLIGHT
  SAME_LIVING_CHAT: true
  PHASE_KEY_CHANGE: false
  TRACKED_REPOSITORY_MUTATION_AUTHORIZED: false
  ROUTE_STATE_MUTATION_AUTHORIZED: false
  ARISTOTLE_SUBMISSION: NONE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  CONTROLLING_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0_POST_R_NEXT_NODE_ADJUDICATION_2026-08-09.txt
    observed_sha256: b7c686144903f6c5a7401848d4cd5339daf7ed761307f798e8b24b5a17c1882a
    observed_bytes: 8655
    observed_wc_lines: 239
    final_LF: true
    utf8: PASS
    read_byte_for_byte: true
    status: PASS

  HEAD:
    expected: 4a02e0fb836d9e65228164e45653ad11e37c44d7
    key_production_blob_at_pin_matches_live_rh_clean: true
    status: PASS

  EXECUTION_STATE:
    expected_sha256:
      faf53ba522b0544a97909442727e4ff28f2e4e60ff7b75d8361909eb4d02af7d
    content_at_pin_verified: true
    exact_sha256_rehash_by_judge: false
    local_preflight_rehash_required: true
    stage: RB-GOAL-057-B3-0R-CLOSED
    obligation: GOAL057_B3_0_POST_R_NEXT_NODE_ADJUDICATION
    status:
      GOAL_057_B3_0R_FINITE_MODE_SPAN_IN_SHIFTED_ARCH_FORM_DOMAIN_PROVED_NEXT_NODE_ADJUDICATION_PENDING

  ROUTE_STATE:
    expected_sha256:
      517068eeaa477298c5544c9b46dff7aab94766f1cfa1684c83566b8f580bad2e
    exact_sha256_rehash_by_judge: false
    local_preflight_rehash_required: true

  UNRELATED_STAGED_PATCH:
    expected_sha256:
      291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b
    preservation_required: true
    local_preflight_rehash_required: true

CLOSED_PARENT:
  ID: B3_0R
  FILE:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchFiniteModeDomain.lean
  SHA256:
    071e973665df61aa5d7ce01abb2390a9ab31dddf7e312ab8dedede47a812e66d
  THEOREM:
    E_m_N_le_sourceArchimedeanShiftedFormDomain
  STATUS: CLOSED
  REOPENED: false
  DIRECTLY_CONSUMED_BY_SELECTED_CHILD: false
  RETAINED_ROLE:
    exact_finite_trial_and_finite_Galerkin_consumer

DIRECT_DEPENDENCIES:
  - module: Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain
    file:
      q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchModeDomain.lean
    sha256:
      d961186606e32eaa8c12734d68fa40c394b889c53ca9def0f6cd253c94711fc8
    load_bearing_fact:
      V_n_m_mem_sourceArchimedeanShiftedFormDomain

  - module: Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
    file:
      q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean
    sha256:
      1001bd3c39dcf70ae4d7c31bbc8c0f188d1f9917331b22bb5b0f981cc832e949
    load_bearing_facts:
      - V_n_m_hilbertBasis
      - V_n_m_hilbertBasis_apply
      - HilbertBasis.dense_span

SELECTED_CHILD_CONTRACT:
  theorem:
    sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
  quantifier:
    forall_i_PairIndex
  exact_conclusion:
    topologicalClosure_sourceArchimedeanShiftedFormDomain_i_eq_top
  source_meaning:
    Hilbert_norm_density_of_the_constructed_shifted_archimedean_domain
  scope: ABSTRACT
  verifier: CONDITIONAL_UNTIL_EXACT_LEAN_PREFLIGHT

SEMANTIC_BOUNDARY:
  proves_Hilbert_space_density: true
  proves_literal_mode_membership: false
  proves_finite_span_inclusion: false
  proves_form_core_in_form_norm: false
  identifies_domain_with_D0_2: false
  defines_sesquilinear_form: false
  proves_closedness: false
  proves_lower_semicontinuity: false
  defines_associated_operator: false
  proves_operator_domain_membership: false
  proves_selected_kTrial_operator_domain: false
  proves_compression_or_continuum_numerator: false

FUTURE_PRODUCTION_PATH_NOT_AUTHORIZED:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchFormDomainDensity.lean

SCRATCH_CANDIDATE:
  filename:
    GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_CANDIDATE_2026-08-09.lean
  sha256:
    3addebc1c00c0aa56bd63566f92b22422ef1e9dda1474a17a510ccdb15f4cdee
  bytes: 938
  wc_lines: 25
  final_LF: true
  forbidden_token_matches: 0
  direct_Lean_run_by_judge: false
  status: EXACT_BYTES_PINNED_REQUIRES_DIRECT_LEAN

PUBLIC_SURFACE_IF_LATER_RELEASED:
  definitions: 0
  theorems:
    - sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
  total_public_declarations: 1

PRIVATE_SURFACE_IF_LATER_RELEASED:
  definitions: 0
  theorems: 0
  total_private_declarations: 0

PREFLIGHT_STOP:
  GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_PROVED

SPECIFIC_STOPS:
  - GOAL057_B3_0S_HILBERT_BASIS_DENSE_SPAN_API_GAP
  - GOAL057_B3_0S_TOPOLOGICAL_CLOSURE_MONOTONICITY_API_GAP
  - B3_0S_FINITE_SPAN_DENSITY_FALSE
  - B3_0S_LITERAL_BASIS_OR_DOMAIN_MISMATCH
  - B3_0S_DENSITY_TO_ALL_VECTOR_MEMBERSHIP_DRIFT
  - B3_0S_HILBERT_DENSITY_TO_FORM_CORE_DRIFT
  - B3_0S_FORM_OPERATOR_DOMAIN_COLLAPSE
  - SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
  - ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
  - B3_0S_SCOPE_SMUGGLE

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0T_SHIFTED_ARCH_SESQUILINEAR_FORM_WELLDEFINEDNESS

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect_after_preflight_success: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
CHILD_PROGRESS_IF_PROVED: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

FINAL_BOUNDARY:
  ROUTE: CHALLENGER_NOT_RH
  ACTIVE_BUS_GOAL: 057
  BUS_010: VOID
  GOAL_055: HOLD
  G2_CCM: FROZEN
  CURRENT_CHECKPOINT: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  COARSE_CHECKPOINTS_CLOSED: 0
  COARSE_CHECKPOINTS_REMAINING: 10
  H4A1B: OPEN
  ARISTOTLE_SUBMISSION: NONE
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  SOLE_OWNER_GATE: PX_RH_CLAIM
```

## 1. SOURCE_LOCK_CHECK

The controlling request was read byte-for-byte. Its observed lock is SHA-256 `b7c686144903f6c5a7401848d4cd5339daf7ed761307f798e8b24b5a17c1882a`, 8,655 bytes, 239 `wc` lines, valid UTF-8, with a final LF. It fixes B3.0R as closed, production as forbidden in this adjudication, and requires either one complete scratch candidate or a precise stop.  `[ABSTRACT][PAPER]`

The production B3.0R bytes at commit `4a02e0fb836d9e65228164e45653ad11e37c44d7` are the exact finite-carrier theorem stated in the request. The same file blob is present on live `rh_clean`.   `[ABSTRACT][LEAN]`

The physical execution state records:

```text
RB-GOAL-057-B3-0R-CLOSED
GOAL057_B3_0_POST_R_NEXT_NODE_ADJUDICATION
OPEN_ADJUDICATION_REQUIRED_NO_SUCCESSOR_AUTHORIZED
```

and keeps the coarse ledger at `0 closed / 10 remaining`.  `[ABSTRACT][PAPER]`

The exact SHA-256 values of the execution-state and route-state files were not independently recomputed through the connector. Codex must rehash both locally before creating the scratch file.

## 2. DEPENDENCY_AND_QUANTIFIER_AUDIT

B3.0Q proves, for every pair index and every integer mode,

[
V_{n,m}(i,n)\in
\operatorname{sourceArchimedeanShiftedFormDomain}(i).
]

It proves no density, finite-span, arbitrary-vector, D0.2, or operator-domain result.  `[ABSTRACT][LEAN]`

Independently, the production completeness bridge constructs the literal family `V_n_m i` as a complete Hilbert basis of `H_m i`. Its source-locked closeout records SHA-256 `1001bd3c…e949`, the public definitions `V_n_m_hilbertBasis` and `V_n_m_hilbertBasis_apply`, and the complete-basis validation.  `[ABSTRACT][LEAN]`

Pinned Mathlib v4.26 supplies the exact theorem:

```lean
HilbertBasis.dense_span :
  (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤
```

for a Hilbert basis `b`.  `[ABSTRACT][LEAN]`

Therefore the lawful quantifier/topology lift is:

[
\forall n,;V_{n,m}(i,n)\in\mathcal D_i
\quad+\quad
\overline{\operatorname{span}{V_{n,m}(i,n):n\in\mathbb Z}}=H_m(i)
]

[
\Longrightarrow
\boxed{\overline{\mathcal D_i}=H_m(i)}.
]

`[ABSTRACT][CONDITIONAL]`

This is not the invalid strengthening

[
\mathcal D_i=H_m(i).
]

A dense proper domain is exactly the expected category for an unbounded form or operator.

The D0.2 source lock says that the source form domain is generally a proper dense subspace, and that the full mode span is a form core. The selected theorem proves only Hilbert-norm density of the newly constructed shifted-archimedean carrier; it does not claim the stronger form-core or D0.2-identification statement.  `[ABSTRACT][PAPER]`

## 3. SMALLEST_CHILD_RATIONALE

### Selected: exact Hilbert-space density

The selected child closes one new topological wall:

```text
literal source modes belong to the constructed domain
+ literal source modes form a complete Hilbert basis
→ the constructed domain is dense in H_m.
```

It requires one theorem, no new object, no premise, no numerical input, and no source-form definition.

### Rejected: a public selected-`kTrial_m_N` form-domain wrapper

B3.0R already supplies the exact proof term for every `xE : E_m_N i`:

```lean
(E_m_N_le_sourceArchimedeanShiftedFormDomain i) xE.property
```

Applying this to `kTrial_m_N` needs no new public theorem. Minting such a wrapper would be convenience-only surface under C10.

### Rejected: all-integer span inclusion as a separate theorem

The inclusion

```text
span(range V_n_m) ≤ sourceArchimedeanShiftedFormDomain
```

is used once inside the density proof. Publishing it separately would merely expose an intermediate `Submodule.span_le` step. The density theorem can consume it locally without enlarging the API.

### Retained but not selected: shifted sesquilinear form

A form definition is larger. It must construct a quotient-safe weighted `Lp` representative on the subtype, prove sesquilinearity and representative independence, and state exactly which shifted archimedean functional it represents. That work must not be bundled into the density transaction.

### Why B3.0R is not discarded

B3.0R remains the exact finite-trial and finite-Galerkin interface. The density child follows the ambient branch from B3.0Q plus the already-proved complete basis. This is a frontier split inside the same phase, not a replacement or reopening of B3.0R.

## 4. EXACT_PUBLIC_SURFACE

Future production path, named but not authorized:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarShiftedArchFormDomainDensity.lean
```

Exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain
import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
```

Exact namespace:

```lean
namespace Q3.RouteB.D0Pstar
```

Exact sole public theorem:

```lean
theorem sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
    (i : PairIndex) :
    (sourceArchimedeanShiftedFormDomain i).topologicalClosure = ⊤
```

Public definitions: `0`.

Public theorems: `1`.

Private declarations: `0`.

The theorem deliberately exposes topological-closure equality rather than introducing a second `Dense` wrapper.

## 5. COMPLETE_SCRATCH_LEAN_FILE_OR_STOP

[Exact B3.0S scratch candidate](sandbox:/mnt/data/GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_CANDIDATE_2026-08-09.lean)

Exact byte lock:

```text
SHA-256:
  3addebc1c00c0aa56bd63566f92b22422ef1e9dda1474a17a510ccdb15f4cdee

bytes:
  938

wc-lines:
  25

final LF:
  true
```

```lean
import Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain
import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The exact shifted archimedean form-domain carrier is dense in `H_m i`.
This uses only literal-mode membership and the complete literal Hilbert basis.
It does not identify the domain with D0.2 or construct a form or operator. -/
theorem sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
    (i : PairIndex) :
    (sourceArchimedeanShiftedFormDomain i).topologicalClosure = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← (V_n_m_hilbertBasis i).dense_span]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.2
    rintro x ⟨n, rfl⟩
    rw [V_n_m_hilbertBasis_apply]
    exact V_n_m_mem_sourceArchimedeanShiftedFormDomain i n

#print axioms sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top

end Q3.RouteB.D0Pstar
```

The candidate is source- and API-shape audited. This judge did not execute the pinned Lean toolchain, so its verifier remains `[CONDITIONAL]` until the byte-identical scratch file compiles.

## 6. MANDATORY_JUDGES

### Positive controls

**P057_B3_0S_POS_1_EXACT_MODE_RANGE**

For arbitrary `i` and `n`, verify that the generator used by `HilbertBasis.dense_span` rewrites by `V_n_m_hilbertBasis_apply` to the exact B3.0Q vector.

**P057_B3_0S_POS_2_CLOSURE_CONSUMER**

For arbitrary `x : H_m i`, the theorem must allow:

```lean
show x ∈
    (sourceArchimedeanShiftedFormDomain i).topologicalClosure by
  rw [sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top]
  trivial
```

### Negative and semantic judges

| ID                                    | Mutation or attack                                                                                             | Required stop                                  |
| ------------------------------------- | -------------------------------------------------------------------------------------------------------------- | ---------------------------------------------- |
| `P057_B3_0S_1_FINITE_SPAN_NOT_DENSE`  | Replace the complete basis span by `E_m_N i` or `modeSet i`                                                    | `B3_0S_FINITE_SPAN_DENSITY_FALSE`              |
| `P057_B3_0S_2_COMPLETENESS_PARENT`    | Remove `V_n_m_hilbertBasis.dense_span` and use orthonormality alone                                            | `B3_0S_COMPLETENESS_PARENT_MISSING`            |
| `P057_B3_0S_3_LITERAL_BASIS`          | Replace `V_n_m_hilbertBasis` by a different family or transformed carrier                                      | `B3_0S_LITERAL_BASIS_OR_DOMAIN_MISMATCH`       |
| `P057_B3_0S_4_DIRECT_MODE_PARENT`     | Remove direct use of B3.0Q mode membership                                                                     | `B3_0S_B3_0Q_PARENT_NOT_CONSUMED`              |
| `P057_B3_0S_5_PREMISE_SURROGATE`      | Add closure-equals-top or density as a premise                                                                 | `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION` |
| `P057_B3_0S_6_ALL_VECTOR_DRIFT`       | Replace density by `⊤ ≤ sourceArchimedeanShiftedFormDomain i`                                                  | `B3_0S_DENSITY_TO_ALL_VECTOR_MEMBERSHIP_DRIFT` |
| `P057_B3_0S_7_FORM_CORE_DRIFT`        | Claim graph/form-norm core or equality with D0.2                                                               | `B3_0S_HILBERT_DENSITY_TO_FORM_CORE_DRIFT`     |
| `P057_B3_0S_8_FORM_OPERATOR_COLLAPSE` | Infer full-multiplier operator-domain membership                                                               | `B3_0S_FORM_OPERATOR_DOMAIN_COLLAPSE`          |
| `P057_B3_0S_9_DEPENDENCY`             | Add generated PSD, Step33, payload, PrimeCert, or Aristotle-output support                                     | `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`         |
| `P057_B3_0S_10_SCOPE`                 | Add a form, closedness, W02/Prime extension, graph, compression, numerator, H4a1b, checkpoint, PX, or RH claim | `B3_0S_SCOPE_SMUGGLE`                          |

The cheapest falsifier is P057_B3_0S_1: one finite Galerkin span cannot replace the complete integer-mode span. This directly distinguishes the selected theorem from a cosmetic restatement of B3.0R.

## 7. PROHIBITED_INFERENCES

A successful scratch preflight proves only:

[
\boxed{
\overline{
\operatorname{sourceArchimedeanShiftedFormDomain}(i)
}^{,|\cdot|_{H_m}}
==================

H_m(i).
}
]

`[ABSTRACT][LEAN]`

It does not prove:

* every vector belongs to the domain;
* the domain equals D0.2’s form domain;
* the full mode span is a core in the form norm;
* a sesquilinear or quadratic form has been defined;
* closedness or lower semicontinuity;
* a whole-space W02 or Prime perturbation;
* an associated graph or operator;
* full-multiplier operator-domain membership;
* selected-`kTrial_m_N` operator-domain membership;
* compression, invariance, projection-leakage decay, or the continuum numerator;
* H4a1b;
* any coarse checkpoint.

Density is not equality, and Hilbert-norm density is not form-core density. **[C04]**

## 8. NEXT_CONTROL_ACTION

Create only the untracked file:

```text
q3.lean.aristotle/
  Goal057B3_0S_ShiftedArchFormDomainDensity_Scratch.lean
```

by byte-for-byte copy of the 938-byte candidate.

Required source gates:

```bash
test "$(git rev-parse HEAD)" = \
  "4a02e0fb836d9e65228164e45653ad11e37c44d7"

test "$(git rev-parse origin/rh_clean)" = \
  "4a02e0fb836d9e65228164e45653ad11e37c44d7"

test "$(git diff --cached | sha256sum | cut -d' ' -f1)" = \
  "291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b"
```

Rehash the execution and route states before scratch creation:

```text
ROUTE_B_EXECUTION_STATE.json:
  faf53ba522b0544a97909442727e4ff28f2e4e60ff7b75d8361909eb4d02af7d

ROUTE_B_STATE.md:
  517068eeaa477298c5544c9b46dff7aab94766f1cfa1684c83566b8f580bad2e
```

Required candidate gate:

```text
SHA-256:
  3addebc1c00c0aa56bd63566f92b22422ef1e9dda1474a17a510ccdb15f4cdee

bytes:
  938

wc-lines:
  25

final LF:
  true
```

Run:

```bash
cd q3.lean.aristotle

lake env lean \
  Goal057B3_0S_ShiftedArchFormDomainDensity_Scratch.lean
```

Required result:

```yaml
direct_Lean_exit: 0

imports:
  exact_count: 2
  exact_order:
    - Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain
    - Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge

public_surface:
  definitions: 0
  theorems:
    - sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
  total: 1

private_surface:
  definitions: 0
  theorems: 0
  total: 0

forbidden_tokens: 0

axioms:
  exact:
    - propext
    - Classical.choice
    - Quot.sound
```

Run both positive controls and all ten negative/semantic judges in temporary copies. Delete every mutant. Then require:

```text
routeb_status.py --check:
  PASS

git diff --check:
  PASS

tracked repository mutation:
  NONE

route-state mutation:
  NONE

unrelated staged-patch SHA:
  UNCHANGED

same living chat:
  PRESERVED
```

### Binary return

```text
PASS:
  GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_PROVED
```

Return the exact scratch bytes, direct Lean output, axiom output, dependency fingerprints, all judge fates, and exact git status to this same chat for a separate production-release adjudication.

```text
FAIL:
  GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_FAILED
```

Return the first exact elaboration, `dense_span`, closure-monotonicity, or namespace defect. Do not change a candidate byte silently.

## 9. FINAL_BOUNDARY

A green scratch preflight establishes executability only.

```text
B3.0R:
  CLOSED.

B3.0S:
  SELECTED_FOR_SCRATCH_PREFLIGHT;
  NOT PRODUCTION-PROVED.

B3.0:
  OPEN.

current checkpoint:
  ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE;
  STRICTLY_ADVANCED_NOT_CLOSED.

coarse checkpoints:
  0 closed / 10 remaining.

next production child:
  NONE AUTHORIZED.

post-B3.0S mathematical child:
  UNSELECTED_AND_UNAUTHORIZED.
```

### Strongest attack

> The density proof does not consume B3.0R. Is this a disguised branch switch, and was B3.0R therefore unnecessary?

No.

B3.0R closes the exact finite-carrier interface needed by `kTrial_m_N`, finite synthesis, and finite matrix consumers. Density cannot follow from one fixed finite carrier. It necessarily uses the broader B3.0Q theorem over all integer modes plus the literal complete Hilbert basis. The two results serve different consumers inside the same source family and phase.

### Meta closeout

**What became smaller?**

The ambient form-domain wall is reduced to one exact topology theorem: the already-constructed domain must have topological closure `⊤`.

**What was killed?**

* a redundant selected-trial form-domain wrapper;
* a separate all-mode-span inclusion wrapper;
* finite-span density;
* orthonormality without completeness;
* density promoted to all-vector membership;
* Hilbert density promoted to D0.2 form-core equality;
* form-domain promoted to operator-domain membership.

**What must not be tried again?**

Do not infer density from B3.0R’s finite span. Do not identify the dense shifted domain with D0.2. Do not construct the associated operator before the exact form and its analytic properties exist.

**Current smallest named gap**

```text
GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_FAILED
```

until the exact candidate compiles.

**Registered prediction**

```text
Prediction:
  the exact 938-byte candidate compiles directly from B3.0Q,
  V_n_m_hilbertBasis_apply, HilbertBasis.dense_span, and
  Submodule.topologicalClosure_mono with the standard axiom triple.

Status:
  REGISTERED_NOT_YET_TESTED.
```

Route: CHALLENGER / NOT_RH
RH_CLAIM: NOT_MADE
checkpoints_closed: 0
checkpoints_remaining: 10
H4a1b: OPEN
Aristotle_submission: NONE
route_promotion: false
px_rh_claim: NOT_MADE

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT

MODE:
  UNTRACKED_EXACT_LEAN_PREFLIGHT
  PRODUCTION_AUTHORIZED: false
  TRACKED_REPOSITORY_MUTATION: false
  ROUTE_STATE_MUTATION: false

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 4a02e0fb836d9e65228164e45653ad11e37c44d7
  require_origin_equal: true

  controlling_request_sha256:
    b7c686144903f6c5a7401848d4cd5339daf7ed761307f798e8b24b5a17c1882a
  controlling_request_bytes: 8655
  controlling_request_wc_lines: 239
  controlling_request_final_LF: true

  execution_state_expected_sha256:
    faf53ba522b0544a97909442727e4ff28f2e4e60ff7b75d8361909eb4d02af7d
  route_state_expected_sha256:
    517068eeaa477298c5544c9b46dff7aab94766f1cfa1684c83566b8f580bad2e

  preserve_staged_patch_sha256:
    291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

  B3_0Q_file_sha256:
    d961186606e32eaa8c12734d68fa40c394b889c53ca9def0f6cd253c94711fc8
  completeness_bridge_file_sha256:
    1001bd3c39dcf70ae4d7c31bbc8c0f188d1f9917331b22bb5b0f981cc832e949

CREATE_UNTRACKED_ONLY:
  - q3.lean.aristotle/Goal057B3_0S_ShiftedArchFormDomainDensity_Scratch.lean

DO_NOT_CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchFormDomainDensity.lean

EXACT_CANDIDATE:
  source_artifact:
    GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_CANDIDATE_2026-08-09.lean
  method: BYTE_FOR_BYTE_COPY
  sha256:
    3addebc1c00c0aa56bd63566f92b22422ef1e9dda1474a17a510ccdb15f4cdee
  bytes: 938
  wc_lines: 25
  final_LF: true
  any_byte_change: STOP_AND_RETURN_CORRECTED_CANDIDATE

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain
  - Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
  total: 1

PRIVATE_SURFACE_EXACT:
  definitions: []
  theorems: []
  total: 0

MANDATORY_SEMANTICS:
  - exact_sourceArchimedeanShiftedFormDomain_i
  - exact_literal_V_n_m_Hilbert_basis
  - exact_B3_0Q_all_integer_mode_membership
  - exact_HilbertBasis_dense_span
  - exact_Submodule_topologicalClosure_mono
  - Hilbert_norm_density_only
  - no_all_vector_membership
  - no_D0_2_domain_or_form_core_identification
  - no_form_closedness_graph_operator_or_numerator_claim

MANDATORY_JUDGES:
  - P057_B3_0S_POS_1_EXACT_MODE_RANGE
  - P057_B3_0S_POS_2_CLOSURE_CONSUMER
  - P057_B3_0S_1_FINITE_SPAN_NOT_DENSE
  - P057_B3_0S_2_COMPLETENESS_PARENT
  - P057_B3_0S_3_LITERAL_BASIS
  - P057_B3_0S_4_DIRECT_MODE_PARENT
  - P057_B3_0S_5_PREMISE_SURROGATE
  - P057_B3_0S_6_ALL_VECTOR_DRIFT
  - P057_B3_0S_7_FORM_CORE_DRIFT
  - P057_B3_0S_8_FORM_OPERATOR_COLLAPSE
  - P057_B3_0S_9_DEPENDENCY
  - P057_B3_0S_10_SCOPE

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_execution_and_route_state_SHA256
  - verify_staged_patch_SHA256_unchanged
  - verify_B3_0Q_and_completeness_bridge_SHA256
  - verify_exact_scratch_SHA256_bytes_wc_lines_and_final_LF
  - forbidden_token_and_dependency_scan
  - direct_lake_env_lean_on_scratch
  - exact_two_import_audit
  - exact_public_surface_0_definitions_1_theorem
  - exact_private_surface_zero
  - print_axioms_for_public_theorem
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - run_all_positive_and_negative_judges_in_temporary_copies
  - remove_all_mutation_artifacts
  - routeb_status_check
  - git_diff_check
  - exact_git_status_report
  - prove_no_tracked_repository_mutation
  - prove_no_route_state_mutation
  - preserve_same_living_chat

PREFLIGHT_STOP:
  GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_PREFLIGHT_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0T_SHIFTED_ARCH_SESQUILINEAR_FORM_WELLDEFINEDNESS

NOT_AUTHORIZED:
  - create_the_B3_0S_production_file
  - select_or_authorize_any_post_B3_0S_child
  - add_a_selected_kTrial_form_domain_wrapper
  - prove_all_H_m_membership
  - claim_form_core_density
  - identify_the_domain_with_D0_2
  - define_the_shifted_archimedean_form
  - prove_closedness_or_lower_semicontinuity
  - construct_whole_space_W02_or_Prime_extensions
  - define_an_associated_graph_or_operator
  - infer_operator_domain_membership
  - assert_selected_kTrial_operator_domain_membership
  - assert_compression_or_invariance
  - claim_projection_leakage_decay_or_continuum_numerator
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - touch_frozen_parent_extract_schedules
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
