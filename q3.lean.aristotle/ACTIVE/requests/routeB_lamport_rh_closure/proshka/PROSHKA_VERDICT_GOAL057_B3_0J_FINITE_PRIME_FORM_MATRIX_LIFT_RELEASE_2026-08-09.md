# STATUS: OPEN — B3.0J EXACT FINITE PRIME SESQUILINEAR-FORM LIFT RELEASED

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT
OPERATIVE_CLASS_COUNT: 1

TRANSACTION:
  ID: GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT_RELEASE
  MODE: IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD
  PRODUCTION_RELEASE: AUTHORIZED
  PRODUCTION_ALREADY_PROVED: false
  AUTHORIZED_CHILDREN: 1
  SUCCESSOR_SELECTED: false
  SUCCESSOR_AUTHORIZED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  HEAD:
    expected: f0413ad72ce6bcb9c29edadfd42708fb80202f2f
    observed_origin_rh_clean: f0413ad72ce6bcb9c29edadfd42708fb80202f2f
    commit_message: "[MacOS][rh_clean][RouteB] Close Goal 057 B3.0I source prime pairing"
    status: PASS

  CONTROLLING_REQUEST:
    observed_sha256: 0dde25ede5a38ad6838a5461e3e26b68eace1215831b155b234f518bd53fd706
    observed_bytes: 12174
    observed_lines: 392
    read_byte_for_byte: true
    status: PASS

  ATTACHED_CANDIDATE:
    expected_sha256: ff5798119b52d74e30e65a534f85081f72e10e0e0237f08acdf5a7bf7c61e212
    observed_sha256: ff5798119b52d74e30e65a534f85081f72e10e0e0237f08acdf5a7bf7c61e212
    expected_bytes: 1123
    observed_bytes: 1123
    expected_lines: 36
    observed_lines: 36
    read_byte_for_byte: true
    status: PASS

  CLOSED_PARENT:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean
    packet_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
    GitHub_content_verified: true
    theorem_verified: sourcePrimeModePairing_eq_ccmPrimeEntryN1
    semantic_role: POSITIVE_ONE_SIDED_W_P_SHARP_COMPONENT
    status: PASS

  CARRIER_OWNER:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean
    packet_sha256: 282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89
    carrier: CCMModeFinite_i_N
    mode_map: ccmModeFinite_i_N
    literal_N2_control: ccmModeFinite_two_values
    status: PASS

  STRUCTURAL_ANALOGUE:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean
    packet_sha256: efc6e3e6060b3e6e6dc9e0726c649a025d79a1c5b2bbc164e94ce5878d8fe83c
    role: THEOREM_SHAPE_PRECEDENT_ONLY
    imported_by_candidate: false
    status: PASS

  TARGET_AT_PIN:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean
    present: false
    transaction_shape: CREATE_ONLY

PREFLIGHT:
  reported_direct_Lean_exit: 0
  candidate_byte_identical_to_scratch: true
  reported_axioms:
    - propext
    - Classical.choice
    - Quot.sound
  judge_reran_Lean: false
  production_rerun_required: true

STATIC_CANDIDATE_AUDIT:
  exact_imports: 2
  public_definitions: 0
  public_theorems: 1
  private_declarations: 0
  print_axioms_commands: 1
  forbidden_token_matches: 0
  generated_backend_matches: 0
  surface_match: PASS

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  theorem_statement: ACCEPTED_EXACTLY
  theorem_proof: ACCEPTED_EXACTLY
  exact_positive_component_sign: ACCEPTED
  finite_carrier: ACCEPTED
  ordered_mode_map: ACCEPTED
  coefficient_slot_orientation: ACCEPTED
  complex_codomain: ACCEPTED
  double_sum_shape: ACCEPTED
  parent_dependency: ACCEPTED
  public_surface: ACCEPTED
  candidate_byte_change_allowed: false
  first_mathematical_defect: NONE
  first_typing_defect: NONE
  first_dependency_defect: NONE
  first_source_provenance_defect: NONE

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean

EXACT_MATERIALIZATION:
  method: BYTE_FOR_BYTE_COPY
  expected_sha256: ff5798119b52d74e30e65a534f85081f72e10e0e0237f08acdf5a7bf7c61e212
  expected_bytes: 1123
  expected_lines: 36
  any_byte_change: STOP_AND_RETURN_NEW_RELEASE_PACKET

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourcePrimeModePairing
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems:
    - sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm
  total_public_declarations: 1

PRIVATE_SURFACE:
  definitions: 0
  theorems: 0
  total_private_declarations: 0

PROOF_DB_EXPECTATION:
  declarations: 1
  proven: 1
  repeat_import_row_drift: 0

PLANTS:
  registered_B3_0J_judges: 12
  production_rerun_required: true
  compile_failure_only_judging_sufficient: false
  static_or_semantic_judges_required: true
  external_P_PRIME_2:
    status: DEFERRED_TO_COMPLETE_FORM_BOUNDARY
    may_not_be_claimed_fired: true
  symmetry_blind_global_index_swap:
    status: KILLED_AS_NONDISCRIMINATING
    may_not_be_counted: true

STOP:
  GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT_MISSING

SUCCESS:
  GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

SEMANTIC_EFFECT_AFTER_SUCCESS:
  B3_0I_ENTRYWISE_PRIME_CROSSWALK: CLOSED
  B3_0J_FINITE_PRIME_FORM_LIFT: CLOSED
  COMPLETE_THREE_COMPONENT_SOURCE_WEIL_FORM: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  CONTINUUM_NUMERATOR: OPEN
  H4A1B: OPEN
  B3_0: OPEN

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

SCOPE: FINITE_CELL
VERIFIER: CONDITIONAL_UNTIL_PRODUCTION_LEAN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE:
  phase_key_change: false
  reuse_same_living_chat: true
  open_fresh_chat: false

FINAL_BOUNDARY:
  ROUTE: CHALLENGER_NOT_RH
  ACTIVE_BUS_GOAL: 057
  BUS_010: VOID
  GOAL_055: HOLD
  G2_CCM: FROZEN
  ARISTOTLE_SUBMISSION: NONE
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  SOLE_OWNER_GATE: PX_RH_CLAIM
```

## 1. Source-lock ruling

Both attachments were read in full. The candidate exactly matches the controlling SHA-256, size, and line count. Its surface is exactly two imports, one public theorem, zero definitions, zero private declarations, one `#print axioms`, and no forbidden or generated-backend token.   `[FINITE_CELL][LEAN]`

The live `rh_clean` branch is exactly `f0413ad72ce6bcb9c29edadfd42708fb80202f2f`, and that commit closes B3.0I source-prime pairing.  `[ABSTRACT][PAPER]`

The production parent contains the exact positive one-sided source-prime object and the generic entrywise crosswalk

```lean
sourcePrimeModePairing i n r =
  (Q3.RouteB.ccmPrimeEntryN1 i.m n r : ℂ).
```

Its definition keeps the complete-ledger minus sign outside the object.  `[ABSTRACT][LEAN]`

The finite carrier owner defines exactly

```lean
CCMModeFinite N := Fin (2 * N + 1)
ccmModeFinite N j := (j.1 : ℤ) - N
```

and publicly checks that `N = 2` means the literal order `-2,-1,0,1,2`.  `[FINITE_CELL][LEAN]`

The target production path does not exist at the pin. This is a clean create-only release.

## 2. Mathematical ruling

The theorem is the exact finite sesquilinear lift of the B3.0I entrywise crosswalk:

```lean
theorem sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourcePrimeModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmPrimeEntryN1
            i.m
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k
```

with proof:

```lean
by
  classical
  simp only [sourcePrimeModePairing_eq_ccmPrimeEntryN1]
```

 `[FINITE_CELL][LEAN]`

For every ordered pair `(j,k)`, B3.0I supplies the required scalar equality at exactly

```text
n = ccmModeFinite i.N j
r = ccmModeFinite i.N k.
```

Multiplication by `star (c j)` and `d k`, followed by finite summation, preserves equality. There is no sign transport, estimate, limit, symmetry argument, or additional source premise.

The positive sign is exact. This theorem represents the positive one-sided (W_p^#) component. The later full source ledger—not B3.0J—owns the subtraction

[
W_{0,2}-W_{\mathbb R}-W_{\mathrm{prime}}.
]

`[FINITE_CELL][LEAN]`

## 3. Why the theorem is not a surrogate

The candidate does not define a new source-prime object and does not unfold the source object into the target formula. Its only substantive rewrite is the already-proved B3.0I source-to-target theorem. The two direct imports are therefore both load-bearing:

* `D0PstarSourcePrimeModePairing` supplies the independently constructed source object and its entrywise theorem;
* `CCMFiniteWeilSourceMatrix` supplies the exact finite carrier and mode map.

A theorem proved from a newly introduced premise equaling the desired double-sum conclusion, or from a direct target alias, would be rejected as `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION`. **[C10]**

The existing W02 finite-form theorem is only a structural precedent. The candidate does not import or reuse it. Its analogous one-theorem, zero-helper shape confirms that B3.0J is the minimal public interface for the prime component.  `[FINITE_CELL][LEAN]`

## 4. Strongest attack

> The parent theorem is valid for every integer mode pair. Therefore many coherently wrong finite wrappers—wrong mode ordering, missing first-slot conjugation, real-part projection, or a quadratic specialization—could still compile after the same mutation is made on both sides. Does this one-line proof actually certify the intended source form?

Compilation alone does not certify those conventions.

This is the main C04 failure mode: the generic entrywise equality survives several forgetful or coherent wrapper changes. The release survives because the candidate bytes precommit the exact theorem type, while production validation must separately judge:

* the literal carrier and mode map;
* the first-slot `star`;
* second-slot linearity;
* complex codomain;
* two independent rows;
* full ordered double sum;
* positive component sign;
* direct parent consumption.

A plant may correctly reject a mutant through a static type, dependency, or semantic gate even when the mutant itself compiles. Reporting every plant as “Lean failed” would be false.

## 5. Exact plant-observability ruling

| Judge                                         | Required method                                                                        | Required stop                                   |
| --------------------------------------------- | -------------------------------------------------------------------------------------- | ----------------------------------------------- |
| `P057_B3_0J_1_EXACT_FINITE_CARRIER`           | Exact theorem-type fingerprint                                                         | `B3_0J_FINITE_CARRIER_MISMATCH`                 |
| `P057_B3_0J_2_LITERAL_MODE_MAP`               | Exact `ccmModeFinite i.N` fingerprint plus compiled `ccmModeFinite_two_values` control | `B3_0J_MODE_ORDER_MISMATCH`                     |
| `P057_B3_0J_3_ANTILINEAR_FIRST_SLOT`          | Exact `star (c j)` fingerprint plus nonsymmetric complex control                       | `B3_0J_CONJUGATE_SLOT_MISMATCH`                 |
| `P057_B3_0J_4_LINEAR_SECOND_SLOT`             | Exact unconjugated `d k` fingerprint plus nonsymmetric complex control                 | `B3_0J_SECOND_SLOT_LINEARITY_MISMATCH`          |
| `P057_B3_0J_5_POSITIVE_PRIME_COMPONENT_SIGN`  | One-sided sign mutation plus exact positive-component statement gate                   | `B3_0J_PRIME_COMPONENT_SIGN_CROSSCONTAMINATION` |
| `P057_B3_0J_6_EXACT_PROJECT_CUTOFF`           | Mutate target `i.m` cutoff while retaining the source parent                           | `B3_0J_PRIME_CUTOFF_MISMATCH`                   |
| `P057_B3_0J_7_COMPLEX_NOT_REAL_PART`          | Exact codomain/type gate; `.re` and real rows forbidden                                | `B3_0J_COMPLEX_CARRIER_COLLAPSE`                |
| `P057_B3_0J_8_ENTRYWISE_PARENT_LOAD_BEARING`  | Dependency fingerprint requiring the exact `simp only` parent call                     | `B3_0J_SOURCE_PARENT_ERASED`                    |
| `P057_B3_0J_9_EXACT_DOUBLE_SUM`               | Exact two-row/double-sum fingerprint plus nonsymmetric toy-matrix control              | `B3_0J_SESQUILINEAR_FORM_SHAPE_MISMATCH`        |
| `P057_B3_0J_10_COMPONENT_IDENTITY`            | Component-name allowlist; W02, WR, Tau and assembled entries forbidden                 | `B3_0J_COMPONENT_CROSSCONTAMINATION`            |
| `P057_B3_0J_11_DEFERRED_COMPLETE_LEDGER_SIGN` | Semantic scope gate; P-PRIME-2 remains deferred                                        | `B3_0J_COMPLETE_LEDGER_SCOPE_VIOLATION`         |
| `P057_B3_0J_12_SCOPE_FIREWALL`                | Static semantic boundary gate                                                          | `B3_0J_SCOPE_SMUGGLE`                           |

A global `j ↔ k` swap is not an independent orientation plant. Dummy reindexing and target symmetry can make it semantically blind. It must not be counted. **[C04]**

## 6. Exact production contract

Create only:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean
```

Materialize the attached candidate byte-for-byte, including its docstring and `#print axioms` command.

Required exact result:

```text
SHA-256:
  ff5798119b52d74e30e65a534f85081f72e10e0e0237f08acdf5a7bf7c61e212

bytes:
  1123

lines:
  36
```

No formatting, newline normalization, import reordering, comment amendment, theorem renaming, or proof substitution is permitted.

## 7. Validation gates

Production success requires:

```bash
test "$(git rev-parse HEAD)" = \
  "f0413ad72ce6bcb9c29edadfd42708fb80202f2f"

test "$(git rev-parse origin/rh_clean)" = \
  "f0413ad72ce6bcb9c29edadfd42708fb80202f2f"

test "$(git diff --cached | sha256sum | cut -d' ' -f1)" = \
  "291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b"

sha256sum \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean

cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk

lake build
```

Then require:

```text
scripts/q3_check.sh: PASS

direct imports:
  exactly 2

public surface:
  0 definitions
  1 theorem

private surface:
  0 declarations

forbidden/taint scan:
  no sorry
  no admit
  no exact?
  no unsafe
  no native_decide
  no declared axiom
  no opaque
  no Float
  no generated PSD / Step33 / hbox / payload import
  no direct Aristotle-output import

axioms:
  exactly [propext, Classical.choice, Quot.sound]

plants:
  all 12 B3.0J child-local judges pass under their correct
  compile/static/dependency/semantic classifications
  P-PRIME-2 remains deferred and is not counted
  symmetry-blind global index swap remains killed and is not counted

proof database:
  1 declaration
  1 proved
  repeat import causes zero row-count drift

orchestration:
  80/80 tests PASS
  strict Spine PASS
  semantic-index validation PASS
  knowledge.db integrity_check = ok
  aristotle_proofs.db integrity_check = ok
  observability.db integrity_check = ok

repository:
  no mutation artifact remains
  git diff --check PASS
  exact git status --short recorded
  route state updated last
  unrelated staged-patch hash unchanged
```

`[FINITE_CELL][CONDITIONAL]`

## 8. Exact semantic boundary after success

Successful B3.0J production proves only:

[
\boxed{
\sum_{j,k}
\overline{c_j},
W^{#}_{p,jk},
d_k
===

\sum_{j,k}
\overline{c_j},
\operatorname{ccmPrimeEntryN1}_{jk},
d_k.
}
]

`[FINITE_CELL][LEAN]`

It does not prove or authorize:

* the external negative prime sign in a complete source form;
* the full (W_{0,2}-W_{\mathbb R}-W_p) assembly;
* a matrix or operator wrapper;
* an associated operator graph;
* form-domain or operator-domain membership;
* compression;
* the continuum numerator;
* H4a1b;
* any coarse checkpoint;
* Route-B promotion;
* PX/RH.

The parent checkpoint is strictly advanced but remains open. The ledger remains `0 closed / 10 remaining`.

No successor transaction is selected or authorized in this verdict.

## 9. Meta closeout

**What became smaller?**

The positive prime component becomes a spendable finite complex sesquilinear form on the literal CCM carrier instead of remaining only an entrywise dictionary.

**What was killed?**

* an internal complete-ledger minus;
* `i.N` as the arithmetic cutoff;
* W02, WR, or full-Tau substitution;
* a real-part or quadratic specialization;
* symmetry as evidence for ordered coefficient slots;
* a premise-only replacement of the B3.0I source parent.

**What must not be tried again?**

Do not claim that a coherently mutated wrapper is source-faithful merely because the same entrywise rewrite still compiles. Do not count P-PRIME-2 as fired before the complete-form boundary.

**Current smallest open wall after success**

```text
The three independently proved finite components have not yet been assembled
into the complete source Weil form with signs:
  + W02
  + already-negative source archimedean component
  - positive source prime component.
```

That wall is recorded only; no child is minted here.

**Registered prediction fate**

```text
Prediction:
  B3.0J is the exact one-theorem finite-form lift of closed B3.0I.

Fate:
  CONFIRMED.

Risk:
  a one-line simp proof might fail to preserve source conventions.

Fate:
  NEUTRALIZED only by exact byte precommit plus independent
  type/dependency/semantic judges; compilation alone remains insufficient.
```

```yaml
iteration:
  target: GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT
  status: PROGRESS
  failed_strategy: compilation_alone_as_wrapper_convention_judge
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: COMPLETE_THREE_COMPONENT_SOURCE_WEIL_FORM_ASSEMBLY_UNMINTED
  invariant_learned: positive_prime_component_exact_carrier_conjugate_first_order_and_external_future_minus_are_independent_contracts
  forbidden_future_move: internalize_the_complete_ledger_minus_or_use_target_symmetry_as_order_evidence
  next_decisive_test: production_byte_copy_plus_full_release_gate
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: f0413ad72ce6bcb9c29edadfd42708fb80202f2f
  require_origin_equal: true
  controlling_request_sha256: 0dde25ede5a38ad6838a5461e3e26b68eace1215831b155b234f518bd53fd706
  candidate_sha256: ff5798119b52d74e30e65a534f85081f72e10e0e0237f08acdf5a7bf7c61e212
  candidate_bytes: 1123
  candidate_lines: 36
  parent_prime_pairing_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
  carrier_owner_sha256: 282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89
  preserve_staged_patch_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean

EXACT_MATERIALIZATION:
  source_attachment: GOAL057_B3_0J_FINITE_PRIME_FORM_MATRIX_LIFT_CANDIDATE_2026-08-09.txt
  method: BYTE_FOR_BYTE_COPY
  expected_sha256: ff5798119b52d74e30e65a534f85081f72e10e0e0237f08acdf5a7bf7c61e212
  expected_bytes: 1123
  expected_lines: 36
  any_byte_change: STOP_AND_RETURN_NEW_RELEASE_PACKET

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourcePrimeModePairing
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm
  total: 1

PRIVATE_SURFACE_EXACT:
  definitions: 0
  theorems: 0
  total: 0

PUBLIC_THEOREM_EXACT: |
  theorem sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm
      (i : PairIndex)
      (c d : CCMModeFinite i.N → ℂ) :
      (∑ j, ∑ k,
        star (c j) *
          sourcePrimeModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k) =
        ∑ j, ∑ k,
          star (c j) *
            (Q3.RouteB.ccmPrimeEntryN1
              i.m
              (ccmModeFinite i.N j)
              (ccmModeFinite i.N k) : ℂ) *
            d k := by
    classical
    simp only [sourcePrimeModePairing_eq_ccmPrimeEntryN1]

MANDATORY_SEMANTICS:
  - exact_CCMModeFinite_i_N_carrier
  - exact_ccmModeFinite_i_N_j_then_k_order
  - exact_star_c_j_first_slot
  - exact_unconjugated_d_k_second_slot
  - exact_positive_source_prime_component
  - exact_positive_ccmPrimeEntryN1_target
  - exact_i_m_arithmetic_cutoff
  - exact_complex_codomain
  - exact_two_independent_rows
  - exact_double_sum
  - direct_B3_0I_parent_consumed
  - complete_ledger_minus_remains_external
  - no_W02_WR_or_Tau_substitution

MANDATORY_JUDGES:
  - id: P057_B3_0J_1_EXACT_FINITE_CARRIER
    method: STATIC_EXACT_TYPE_GATE
    required_stop: B3_0J_FINITE_CARRIER_MISMATCH

  - id: P057_B3_0J_2_LITERAL_MODE_MAP
    method: STATIC_PLUS_ccmModeFinite_two_values_CONTROL
    required_stop: B3_0J_MODE_ORDER_MISMATCH
    card: C04

  - id: P057_B3_0J_3_ANTILINEAR_FIRST_SLOT
    method: STATIC_PLUS_NONSYMMETRIC_COMPLEX_CONTROL
    required_stop: B3_0J_CONJUGATE_SLOT_MISMATCH
    card: C04

  - id: P057_B3_0J_4_LINEAR_SECOND_SLOT
    method: STATIC_PLUS_NONSYMMETRIC_COMPLEX_CONTROL
    required_stop: B3_0J_SECOND_SLOT_LINEARITY_MISMATCH
    card: C04

  - id: P057_B3_0J_5_POSITIVE_PRIME_COMPONENT_SIGN
    method: ONE_SIDED_MUTATION_PLUS_EXACT_SIGN_GATE
    required_stop: B3_0J_PRIME_COMPONENT_SIGN_CROSSCONTAMINATION

  - id: P057_B3_0J_6_EXACT_PROJECT_CUTOFF
    method: ONE_SIDED_TARGET_MUTATION
    required_stop: B3_0J_PRIME_CUTOFF_MISMATCH

  - id: P057_B3_0J_7_COMPLEX_NOT_REAL_PART
    method: STATIC_EXACT_TYPE_GATE
    required_stop: B3_0J_COMPLEX_CARRIER_COLLAPSE
    card: C04

  - id: P057_B3_0J_8_ENTRYWISE_PARENT_LOAD_BEARING
    method: EXACT_DEPENDENCY_FINGERPRINT
    required_source_line: "simp only [sourcePrimeModePairing_eq_ccmPrimeEntryN1]"
    required_stop: B3_0J_SOURCE_PARENT_ERASED
    card: C10

  - id: P057_B3_0J_9_EXACT_DOUBLE_SUM
    method: STATIC_PLUS_NONSYMMETRIC_TOY_MATRIX_CONTROL
    required_stop: B3_0J_SESQUILINEAR_FORM_SHAPE_MISMATCH
    card: C04

  - id: P057_B3_0J_10_COMPONENT_IDENTITY
    method: COMPONENT_NAME_ALLOWLIST
    required_stop: B3_0J_COMPONENT_CROSSCONTAMINATION

  - id: P057_B3_0J_11_DEFERRED_COMPLETE_LEDGER_SIGN
    method: STATIC_SEMANTIC_GATE
    required_stop: B3_0J_COMPLETE_LEDGER_SCOPE_VIOLATION

  - id: P057_B3_0J_12_SCOPE_FIREWALL
    method: STATIC_SEMANTIC_GATE
    required_stop: B3_0J_SCOPE_SMUGGLE

DEFERRED_EXTERNAL_PLANT:
  id: P_PRIME_2_COMPLETE_LEDGER_PLUS_PRIME
  status: DEFERRED_TO_COMPLETE_FORM_BOUNDARY
  may_not_be_claimed_fired: true

KILLED_PLANT:
  mutation: global_j_k_swap
  reason: dummy_reindexing_and_symmetric_target_make_it_non_discriminating
  card: C04
  run: false
  count: false

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_unrelated_staged_patch_SHA256_unchanged
  - verify_exact_production_SHA256_bytes_lines
  - direct_lake_env_lean
  - target_lake_build
  - full_lake_build
  - scripts_q3_check
  - exact_two_import_audit
  - exact_public_surface_0_definitions_1_theorem
  - exact_private_surface_zero
  - forbidden_token_taint_and_generated_import_scan
  - exact_theorem_type_fingerprint
  - exact_parent_dependency_fingerprint
  - run_all_12_B3_0J_judges_under_correct_classification
  - do_not_count_deferred_P_PRIME_2
  - do_not_run_or_count_global_index_swap
  - remove_all_mutation_artifacts
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - proof_DB_import_1_declaration_1_proved
  - proof_DB_repeat_import_idempotence
  - orchestration_tests_80_of_80_PASS
  - strict_Spine_PASS
  - semantic_index_validation_PASS
  - three_SQLite_integrity_checks_PASS
  - routeb_status_check_after_state_sync
  - git_diff_check
  - exact_git_status_report
  - update_route_state_last
  - path_scoped_commit_and_push_only_the_owned_child_and_required_closeout_state_artifacts

CLOSEOUT_MUST_STATE:
  - GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED
  - EXACT_POSITIVE_SOURCE_PRIME_COMPONENT_RETAINED
  - EXACT_EXTERNAL_FUTURE_PRIME_MINUS_RETAINED
  - EXACT_CCMModeFinite_i_N_CARRIER_RETAINED
  - EXACT_ccmModeFinite_j_THEN_k_ORDER_RETAINED
  - EXACT_FIRST_SLOT_STAR_RETAINED
  - EXACT_SECOND_SLOT_LINEARITY_RETAINED
  - EXACT_i_m_PRIME_CUTOFF_RETAINED
  - EXACT_COMPLEX_DOUBLE_SUM_RETAINED
  - EXACT_B3_0I_PARENT_CONSUMED
  - P_PRIME_2_REMAINS_DEFERRED
  - GLOBAL_INDEX_SWAP_NOT_COUNTED
  - B3_0J_CLOSED
  - B3_0_OPEN
  - NO_COMPLETE_THREE_COMPONENT_SOURCE_WEIL_FORM
  - NO_MATRIX_OR_OPERATOR_WRAPPER
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT_MISSING

SUCCESS:
  GOAL057_B3_0J_FINITE_PRIME_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

NO_NEXT_CHILD:
  selected: false
  authorized: false

NOT_AUTHORIZED:
  - change_any_candidate_byte
  - add_or_modify_any_other_Lean_file
  - internalize_the_complete_ledger_prime_minus
  - define_complete_source_Weil_form
  - substitute_W02_WR_or_ccmWeilTauN1
  - add_matrix_or_operator_wrapper
  - define_associated_operator_graph
  - infer_form_or_operator_domain_membership
  - assert_compression_identity
  - claim_continuum_numerator
  - edit_D0PstarCCMCompressedWeilAction
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - mutate_frozen_parent_extract_schedule
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

PHASE:
  phase_key_change: false
  reuse_same_living_chat: true
  open_fresh_chat: false

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
