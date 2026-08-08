# STATUS: OPEN — B3.0F FINITE ARCHIMEDEAN SESQUILINEAR FORM LIFT RELEASED

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  LIVE_HEAD:
    expected: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
    observed_origin_rh_clean: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
    status: PASS

  PACKAGE_COMMIT:
    commit: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
    role: B3_0F_PREFLIGHT_ROUTE_RECORD_ONLY
    direct_parent: 219f854489754125102e013d69f092782d4b04be
    parent_role: B3_0E4C_PRODUCTION_CLOSEOUT
    package_changed_only:
      - q3.lean.aristotle/docs/INSIGHTS.md
    mathematical_parent_files_changed: false

  ORIGINAL_REQUEST:
    observed_sha256: 81c2e4198356b3a4811ad4edc42f2b1ca1d90d2a36f0aa684419ab75817d75c4
    observed_bytes: 9035
    observed_lines: 269
    status: PASS

  REPAIRED_RETURN:
    observed_sha256: 6631a3ce49dbe648db8ca9987b58a2d55b5544001f9bdee884515f0d1108fec8
    observed_bytes: 8387
    observed_lines: 272
    status: PASS_READ_IN_FULL

  AUTHORITATIVE_HARNESS:
    path: Goal057B3_0F_Scratch.lean
    expected_sha256: 7b4e075e82dc90c173098c459813a69e312d15ff10a616023def740a671779b7
    observed_sha256: 7b4e075e82dc90c173098c459813a69e312d15ff10a616023def740a671779b7
    expected_bytes: 3043
    observed_bytes: 3043
    expected_lines: 115
    observed_lines: 115
    status: PASS

  CONTROL_TAIL:
    reported_sha256: 1a7a2dbbc01c59d1696feade20654708ce4d37752de660cceed02d50d99e191d
    independently_matched: true
    exact_span: FIRST_EXAMPLE_THROUGH_END_OF_FILE_INCLUDING_NAMESPACE_CLOSE
    wording_repair: >-
      The return describes the span as ending at the axiom print, but the
      reported hash actually includes the following blank line and namespace
      close. This is a documentation repair, not an evidence failure.

  REPORTED_DIRECT_LEAN:
    command: lake env lean Goal057B3_0F_Scratch.lean
    exit_status: 0
    stdout_sha256: 41a3119321bba45c7223cf0f2ad48d5eeb5b14030bf9189be66cdb2c629ca178
    stderr_sha256: 21d490443f9947b35732a96388db21561b6395ab676c320eb46630122a748851
    reported_axioms:
      - propext
      - Classical.choice
      - Quot.sound
    judge_reran_Lean: false
    ruling: ACCEPTED_AS_BYTE_PINNED_RELEASE_EVIDENCE
    production_rerun_required: true

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  production_release: AUTHORIZED
  authorized_children: 1
  theorem_statement_repaired: false
  proof_body_repaired: false
  import_surface_repaired: false
  plant_suite_repaired: false
  materialization_wording_repaired: true
  first_mathematical_defect: NONE
  first_Lean_shape_defect: NONE
  target_file_present_at_pin: false

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems:
    - sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
  total_public_declarations: 1

PRIVATE_SURFACE:
  definitions: 0
  theorems: 0
  total_private_declarations: 0

HARNESS_TO_PRODUCTION:
  remove:
    - 5_control_examples
    - 1_print_axioms_command
  retain:
    - exact_imports
    - noncomputable_section
    - exact_opens
    - namespace
    - exact_public_theorem_statement
    - exact_public_theorem_proof
    - namespace_close
  semantic_change: forbidden
  additional_declaration: forbidden

PLANTS:
  required_total: 9
  compile_failure_plants: 7
  semantic_or_static_gate_plants: 2
  killed_not_counted:
    mutation: swap_j_and_k_everywhere
    reason: DUMMY_REINDEXING_AND_SYMMETRIC_TARGET_MAKE_IT_NONDISCRIMINATING
    card: C04
  status: PREFLIGHT_PASS_PRODUCTION_RERUN_REQUIRED

STOP_CODE:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_MISSING

SUCCESS_CODE:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E: CLOSED
  B3_0F: CLOSED
  B3_0: OPEN
  W02_SOURCE_PAIRING: OPEN
  PRIME_SOURCE_PAIRING: OPEN
  COMPLETE_SOURCE_WEIL_FORM: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY

NEXT_DISCRIMINATOR:
  B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT

NEXT_GAP_PRODUCTION_AUTHORIZED: false

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
  same_living_chat: true
  fresh_chat: false

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
  sole_owner_gate: PX_RH_CLAIM
```

## 1. Source-lock ruling

The repaired harness is now genuinely attached and byte-locked. Its SHA-256, size, line count, two-import surface, one public theorem, five controls, and zero private declarations all match the return packet. The reported direct Lean run exits successfully, the forbidden-token scan is empty, and the public theorem reports exactly the standard axiom triple.   `[FINITE_CELL][LEAN]`

Live `origin/rh_clean` is exactly `c22a4a9ca4e00f1f0443ef3509705bb9eda91082`. That commit records only the B3.0F preflight route in `INSIGHTS.md`; its direct parent is the validated B3.0E4C production closeout.   `[ABSTRACT][PAPER]`

The B3.0E4C parent proves the exact entrywise identity for every ordered pair of integer modes and was validated with direct Lean, target/full builds, `q3_check`, six repaired plants, the standard axiom triple, and no new generated backend. It explicitly names B3.0F as the next open atom.  `[ABSTRACT][LEAN]`

The Arsenal mandate is accepted. The repository materialization ledger pins the required deck SHA-256 and twelve-card inventory.   `[ABSTRACT][PAPER]`

### Minor source-lock wording repair

The return states that the immutable SHA-256 `1a7a2dbb…` covers the block “from the first `example` through the final axiom print.” Independent byte inspection shows that this hash covers the first `example` through the **end of the file**, including the blank line and `end Q3.RouteB.D0Pstar`.

The hash is valid. Only its prose description is one line too short. Production closeout must record the exact span; no new preflight is needed. `[FINITE_CELL][LEAN]`

## 2. Mathematical ruling

The public theorem is the exact finite sesquilinear lift of B3.0E4C:

```lean
theorem sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceArchimedeanModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i)
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k)
```

`[FINITE_CELL][CONDITIONAL]`

It preserves all five source contracts:

1. the coefficient carrier is exactly `CCMModeFinite i.N`;
2. `ccmModeFinite i.N j` is the literal ordered mode (j-N);
3. the first coefficient is conjugated by `star`;
4. the second coefficient remains linear;
5. the negative CCM-WR sign is outside the entire double sum.

The source request fixes precisely this antilinear-first coefficient law and forbids a real-part projection, mode substitution, changed carrier, or hidden source-form premise.  `[FINITE_CELL][PAPER]`

Production defines

```lean
CCMModeFinite N := Fin (2 * N + 1)
ccmModeFinite N j := (j.1 : ℤ) - N
```

so the finite order is literally

[
-N,-N+1,\ldots,0,\ldots,N.
]

`[FINITE_CELL][LEAN]`

Applying B3.0E4C entrywise gives

[
B^{\mathrm{arch}}_{jk}
======================

-W_{\mathbb R,jk}.
]

Multiplying by (\overline{c_j}) and (d_k), summing over the finite carrier, and distributing the common minus gives the submitted conclusion. No Hermitian symmetry or dummy-index reindexing is used. `[FINITE_CELL][LEAN]`

The proof

```lean
classical
simp [sourceArchimedeanModePairing_eq_neg_ccmWREntry]
```

is therefore sufficient and dependency-minimal.

## 3. Plant ruling

All nine repaired plants are accepted.

### Compile-failure plants

The following seven mutations fail against the immutable contract:

```text
P057_F_1_GLOBAL_WR_SIGN
P057_F_2_FIRST_SLOT_STAR
P057_F_3_SECOND_SLOT_STAR
P057_F_4_SECOND_MODE_COLLAPSE
P057_F_5_FINITE_CARRIER
P057_F_7_REAL_PROJECTION
P057_F_9_ABSTRACT_ENTRY_ORIENTATION
```

The key result is not merely that the mutations fail. The preflight first confirms that several wrong wrappers—missing first-slot conjugation, moved conjugation, coherent (N+1) carrier, and real projection—can compile before the unchanged source contract is reapplied. The immutable controls then reject them. This is the required C04/C09 behavior: compilation of a common wrong wrapper is not source correctness.   `[FINITE_CELL][LEAN]`

### Semantic/static plants

Two plants correctly compile and are rejected at a different gate:

```text
P057_F_6_PARENT_PROVENANCE
P057_F_8_DEPENDENCY
```

For P057_F_6, a theorem proved from a hypothesis identical to the desired finite-form equality is logically compilable but source-empty. The dependency fingerprint detects that E4C is no longer consumed and stops with:

```text
SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
```

This is a direct C10 plant.

For P057_F_8, the injected generated backend does not necessarily make Lean fail. The exact import allowlist rejects it with:

```text
ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
```

A semantic or dependency plant is not required to have `lean_exit = 1`; its designated gate must fire. The return reports both cases honestly.   `[FINITE_CELL][LEAN]`

### Killed plant remains killed

The mutation

```text
swap j and k everywhere
```

must not be run or counted.

It is dummy reindexing, and the literal CCM-WR target is symmetric. Any apparent failure would measure proof-script shape, not mathematical falsity. This remains a C04 kill.  `[FINITE_CELL][LEAN]`

## 4. Exact production contract

Create only:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean
```

Exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
```

The second import is load-bearing because E4C does not export the general finite carrier or the `ccmModeFinite` map. The original compile audit exposed this dependency directly.  `[FINITE_CELL][LEAN]`

Exact namespace and module preamble:

```lean
noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar
```

Exact public surface:

```yaml
definitions: 0
theorems:
  - sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
total: 1
```

Exact private surface:

```yaml
definitions: 0
theorems: 0
total: 0
```

Materialization must retain the harness’s exact imports, opens, namespace, theorem statement, and proof. Remove all **five** `example` controls and the final `#print axioms` command. The original request’s phrase “four control examples” is superseded by the repaired five-control harness. No helper, form definition, matrix wrapper, or convenience corollary may be added.

## 5. Validation gates

Production success requires:

```bash
test "$(git rev-parse HEAD)" = \
  "c22a4a9ca4e00f1f0443ef3509705bb9eda91082"

test "$(git rev-parse origin/rh_clean)" = \
  "c22a4a9ca4e00f1f0443ef3509705bb9eda91082"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourceArchFiniteFormCCMWRCrosswalk

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check
```

Additional gates:

```text
files:
  create exactly one production Lean file;
  modify no B3.0 parent;

imports:
  exactly two direct imports;
  no generated PSD, Step33, hbox, payload or new Aristotle-output import;

surface:
  public definitions = 0;
  public theorems = 1;
  private definitions = 0;
  private theorems = 0;
  expected proof-DB declarations = 1;

materialization:
  exact theorem statement and proof retained;
  exactly five examples removed;
  exactly one print-axioms command removed;
  every other semantic deviation is a stop;

taint:
  no sorry;
  no admit;
  no exact?;
  no unsafe;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;

axioms:
  #print axioms
    Q3.RouteB.D0Pstar
      .sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm

  require exactly:
    [propext, Classical.choice, Quot.sound];

plants:
  rerun all nine repaired plants;
  preserve the exact control tail during theorem-statement mutations;
  classify P057_F_6 and P057_F_8 as semantic/static gate fires;
  do not run or count the killed global j/k swap;
  remove all mutation artifacts;

observability:
  proof DB records 1/1 declaration as proved;
  strict Spine PASS;
  all three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  report exact git status --short;
  update route state only after all proof and semantic gates pass.
```

`[FINITE_CELL][CONDITIONAL]`

## 6. Exact boundary after success

B3.0F success proves the finite archimedean coefficient-form identity:

[
\boxed{
\sum_{j,k}
\overline{c_j},
B^{\mathrm{arch}}_{jk},
d_k
===

*

\sum_{j,k}
\overline{c_j},
W_{\mathbb R,jk},
d_k.
}
]

`[FINITE_CELL][LEAN]`

It closes the category transition:

```text
all-mode entrywise archimedean crosswalk
→ finite conjugate-first sesquilinear coefficient form.
```

It does **not** prove:

* the source (W_{0,2}) pairing;
* the source prime pairing;
* the complete finite source Weil form;
* equality with `ccmWeilTauN1` as a three-component form;
* a finite or ambient associated operator;
* form-domain or operator-domain membership;
* compression;
* the continuum residual or numerator;
* H4a1b;
* any coarse Goal-057 checkpoint.

Accordingly:

```text
B3.0F:
  CLOSED after production validation.

B3.0:
  OPEN.

Goal-057 ledger:
  0 closed / 10 remaining.
```

## 7. Next smallest gap

The next atom is the endpoint/pole component, not the complete source Weil form:

```text
GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
```

The next discriminator is:

```text
B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT
```

It must determine whether the source’s (W_{0,2}) functional already has a production object whose ordered mode entries are exactly `ccmW02Entry`, including normalization, coefficient order, rank-two structure, and real-to-complex coercion.

B3.0G is named only. It is not authorized by this verdict.

## 8. Strongest attack

> The theorem is a one-line `simp` consequence of E4C. It adds no mathematical fact and could be repeated privately in the eventual full source-form theorem.

The objection is correct about analytic novelty.

It does not change the release.

The theorem freezes a category transition where several wrong alternatives remain compilable:

```text
entrywise equality
→ finite complex sesquilinear form;
```

with:

* the exact finite carrier;
* the exact mode map;
* conjugation in the first coefficient slot;
* linearity in the second slot;
* the global negative archimedean sign;
* no real-part projection;
* direct provenance from E4C.

The repaired plants demonstrate that missing conjugation, moved conjugation, a coherent wrong carrier, and real projection can all produce valid-looking theorems unless the exact source contract remains fixed. The public cost is one theorem and zero support declarations. That is proportionate.

The theorem would become decorative only if the next complete-form assembly ignored it and privately rebuilt the coefficient law. The downstream source-form transaction must consume B3.0F directly.

## 9. Meta closeout

**What became smaller?**

The archimedean component is no longer only an entrywise dictionary. It now has a source-locked finite complex sesquilinear interface.

**What was killed?**

* release from unattached harness metadata;
* common wrong wrappers as source evidence;
* the global dummy-index swap as an orientation detector;
* premise-only finite-form reconstruction;
* generated-backend dependency injection.

**What must not be tried again?**

Do not redefine the finite archimedean form with altered conjugation, a real projection, a coherent (N+1) carrier, or a source-form hypothesis. Do not use symmetry to claim ordered-slot verification.

**Current smallest named gap**

```text
GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
```

**Next cheapest decisive test**

```text
B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT
```

**Prior prediction fate**

```text
B3.0F theorem-shape prediction:
  entrywise E4C lifts directly to the finite conjugate-first coefficient form.

Fate:
  CONFIRMED.

Previous release blocker:
  authoritative harness bytes and observable plants were missing.

Fate:
  CLOSED.

Global j/k swap prediction:
  it would test source mode orientation.

Fate:
  REFUTED under C04; the mutation is symmetry/reindexing blind.
```

```yaml
iteration:
  target: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
  status: PROGRESS
  failed_strategy: release_from_unattached_harness_metadata
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
  invariant_learned: finite_carrier_first_slot_conjugation_second_slot_linearity_global_sign_and_parent_provenance_are_independent_contracts
  forbidden_future_move: rebuild_the_finite_archimedean_form_privately_or_use_symmetric_index_swaps_as_orientation_evidence
  next_decisive_test: B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
  require_origin_equal: true
  mathematical_parent: 219f854489754125102e013d69f092782d4b04be
  request_sha256: 81c2e4198356b3a4811ad4edc42f2b1ca1d90d2a36f0aa684419ab75817d75c4
  repaired_harness_sha256: 7b4e075e82dc90c173098c459813a69e312d15ff10a616023def740a671779b7
  repaired_harness_bytes: 3043
  repaired_harness_lines: 115
  immutable_tail_sha256: 1a7a2dbbc01c59d1696feade20654708ce4d37752de660cceed02d50d99e191d
  immutable_tail_exact_span: first_example_through_namespace_close

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness
  - retain exact imports, scopes, namespace, theorem statement and proof
  - remove all five example controls
  - remove the final print-axioms command
  - retain the namespace close
  - add no definition
  - add no theorem
  - add no helper
  - record every semantic deviation as a stop

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
  total_public_declarations: 1

PRIVATE_SURFACE_EXACT:
  definitions: 0
  theorems: 0
  total_private_declarations: 0

PUBLIC_THEOREM_EXACT: |
  theorem sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
      (i : PairIndex)
      (c d : CCMModeFinite i.N → ℂ) :
      (∑ j, ∑ k,
        star (c j) *
          sourceArchimedeanModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k) =
        -(∑ j, ∑ k,
          star (c j) *
            (Q3.RouteB.ccmWREntry
              (L_m i)
              (ccmModeFinite i.N j)
              (ccmModeFinite i.N k) : ℂ) *
            d k) := by
    classical
    simp [sourceArchimedeanModePairing_eq_neg_ccmWREntry]

MANDATORY_SEMANTICS:
  - coefficient_carrier_is_exactly_CCMModeFinite_i_N
  - mode_map_is_exactly_ccmModeFinite_i_N
  - first_coefficient_slot_is_star_conjugated
  - second_coefficient_slot_is_linear
  - source_pairing_mode_order_is_j_then_k
  - CCM_WR_mode_order_is_j_then_k
  - global_negative_sign_is_outside_complete_double_sum
  - direct_E4C_parent_is_consumed
  - no_matrix_symmetry_argument
  - no_real_projection
  - no_source_form_premise
  - no_W02_or_prime_component

MANDATORY_PLANTS:
  - id: P057_F_1_GLOBAL_WR_SIGN
    required_stop: SOURCE_ARCH_FINITE_FORM_GLOBAL_SIGN_MISMATCH

  - id: P057_F_2_FIRST_SLOT_STAR
    required_stop: SOURCE_ARCH_FINITE_FORM_FIRST_SLOT_ANTILINEARITY_MISMATCH

  - id: P057_F_3_SECOND_SLOT_STAR
    required_stop: SOURCE_ARCH_FINITE_FORM_SLOT_CONJUGATION_MISMATCH

  - id: P057_F_4_SECOND_MODE_COLLAPSE
    required_stop: SOURCE_ARCH_FINITE_FORM_SECOND_MODE_COLLAPSED

  - id: P057_F_5_FINITE_CARRIER
    required_stop: SOURCE_ARCH_FINITE_FORM_CARRIER_MISMATCH

  - id: P057_F_6_PARENT_PROVENANCE
    expected_Lean_behavior: MAY_COMPILE
    required_semantic_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
    card: C10

  - id: P057_F_7_REAL_PROJECTION
    required_stop: SOURCE_ARCH_FINITE_FORM_COMPLEX_CARRIER_LOST

  - id: P057_F_8_DEPENDENCY
    expected_Lean_behavior: MAY_COMPILE
    required_static_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

  - id: P057_F_9_ABSTRACT_ENTRY_ORIENTATION
    host: TEMPORARY_HARNESS_ONLY
    required_stop: SOURCE_ARCH_FINITE_FORM_ENTRY_ORIENTATION_DETECTOR_MISSING
    card: C04

KILLED_PLANT:
  mutation: swap_j_and_k_everywhere
  reason: dummy_reindexing_and_ccmWREntry_symmetry_make_it_non_discriminating
  card: C04
  run: false
  count: false

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchFiniteFormCCMWRCrosswalk
  - full lake build
  - scripts/q3_check.sh on the production file
  - routeb_status.py --check
  - exact public surface 0_definitions_1_theorem
  - exact private surface 0_definitions_0_theorems
  - forbidden-token scan
  - exact two-import audit
  - no-new-generated-dependency audit
  - verify theorem statement and proof against the authoritative harness
  - rerun all nine repaired plants
  - preserve immutable controls during theorem-statement mutations
  - do not run or count the killed global index-swap plant
  - remove every mutation artifact
  - print axioms for the public theorem
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database import with 1 expected declaration
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status --short report
  - update route state only after every proof and semantic gate passes
  - close and commit only this one child after all gates pass

CLOSEOUT_MUST_STATE:
  - SOURCE_ARCH_FINITE_SESQUILINEAR_FORM_EQ_NEG_CCM_WR_MATRIX_FORM_PROVED
  - EXACT_CCMModeFinite_i_N_CARRIER_RETAINED
  - EXACT_ccmModeFinite_j_MINUS_N_ORDER_RETAINED
  - EXACT_FIRST_SLOT_STAR_RETAINED
  - EXACT_SECOND_SLOT_LINEARITY_RETAINED
  - EXACT_GLOBAL_NEGATIVE_CCM_WR_SIGN_RETAINED
  - EXACT_E4C_PARENT_CONSUMED
  - NONSYMMETRIC_ORIENTATION_CONTROL_HARNESS_ONLY
  - GLOBAL_INDEX_SWAP_PLANT_KILLED_AS_SYMMETRY_BLIND
  - B3_0F_CLOSED
  - B3_0_OPEN
  - NO_W02_SOURCE_PAIRING
  - NO_PRIME_SOURCE_PAIRING
  - NO_COMPLETE_SOURCE_WEIL_FORM
  - NO_MATRIX_OR_OPERATOR_WRAPPER
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_MISSING

SUCCESS:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0G_inside_this_transaction
  - define_W02_source_pairing
  - define_prime_source_pairing
  - define_complete_source_Weil_form
  - add_a_matrix_or_operator_wrapper
  - use_matrix_symmetry_to_swap_coefficient_slots
  - project_the_complex_form_to_its_real_part
  - replace_the_exact_finite_carrier
  - replace_E4C_by_an_all_form_premise
  - modify_any_B3_0_parent
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
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

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
