# STATUS: OPEN — B3.0F THEOREM SHAPE SURVIVES; BYTE-LOCKED PREFLIGHT REPAIR REQUIRED

```yaml
STATUS: OPEN

PRIMARY: RUN_GOAL057_B3_0F_REPAIRED_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: RUN_GOAL057_B3_0F_REPAIRED_PREFLIGHT
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

  REQUEST_ATTACHMENT:
    path: PROSHKA_REQUEST_GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_RELEASE_2026-08-08.md
    expected_sha256: NOT_SUPPLIED
    observed_sha256: 81c2e4198356b3a4811ad4edc42f2b1ca1d90d2a36f0aa684419ab75817d75c4
    observed_bytes: 9035
    observed_lines: 269
    status: PASS_READ_IN_FULL

  HARNESS:
    claimed_path: q3.lean.aristotle/Goal057B3_0F_Scratch.lean
    claimed_sha256: b1060045cf6cf22939ef04b45f324d7ab0af380fe920cb275bcc3f6623b56e95
    claimed_bytes: 2678
    claimed_lines: 106
    attachment_present: false
    present_at_pinned_commit: false
    GitHub_fetch_result: NOT_FOUND
    claimed_direct_Lean_PASS_verified: false
    claimed_declaration_counts_verified: false
    claimed_axiom_output_verified: false
    status: FAIL_CLOSED_MISSING_AUTHORITATIVE_BYTES

PARENT_E4C:
  theorem: sourceArchimedeanModePairing_eq_neg_ccmWREntry
  production_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchAllModeCCMWRCrosswalk.lean
  production_sha256: c711d00aaebbf404c520fcbdb027bd5f8cc23d3e7b9dc141a95d0ad14d836cd6
  public_surface: 0_DEFINITIONS_1_THEOREM
  closeout_status: PROVED_AND_VALIDATED
  retained: true
  reopened: false

THEOREM_RULING:
  theorem: sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
  mathematical_shape: ACCEPTED
  source_faithful: true
  finite_carrier: CCMModeFinite_i_N
  mode_map: ccmModeFinite_i_N_j_equals_j_minus_N
  first_coefficient_slot: STAR_CONJUGATE_LINEAR
  second_coefficient_slot: LINEAR
  entry_supplier: B3_0E4C
  global_WR_sign: NEGATIVE
  proof_route: ENTRYWISE_REWRITE_PLUS_FINITE_SUM_ALGEBRA
  dependency_surface: ACCEPTED
  public_value: SOURCE_LOCKED_ENTRYWISE_TO_SESQUILINEAR_CATEGORY_LIFT
  analytic_novelty: NONE
  production_release: false
  release_blocker: AUTHORITATIVE_HARNESS_BYTES_AND_PLANT_OBSERVABILITY_MISSING

TARGET_FILE_IF_LATER_RELEASED:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean

EXACT_IMPORTS_IF_LATER_RELEASED:
  - Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

PUBLIC_SURFACE_IF_LATER_RELEASED:
  definitions: []
  theorems:
    - sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
  total_public_declarations: 1

PRIVATE_SURFACE_IF_LATER_RELEASED:
  definitions: 0
  theorems: 0
  total: 0

PLANT_RULING:
  RETAIN:
    - P057_F_1_GLOBAL_WR_SIGN
    - P057_F_6_PARENT_PROVENANCE
    - P057_F_8_DEPENDENCY

  RETAIN_ONLY_WITH_IMMUTABLE_EXACT_CONTRACT_CONTROL:
    - P057_F_2_FIRST_SLOT_STAR
    - P057_F_3_SECOND_SLOT_STAR
    - P057_F_7_REAL_PROJECTION

  REPAIR:
    - old: P057_F_4_SOURCE_MODE_ORDER
      new: P057_F_4_SECOND_MODE_COLLAPSE
      mutation: source_pairing_second_mode_k_to_j_only
      required_stop: SOURCE_ARCH_FINITE_FORM_SECOND_MODE_COLLAPSED

    - id: P057_F_5_FINITE_CARRIER
      repaired_mutation: >-
        coherently replace CCMModeFinite i.N and ccmModeFinite i.N by
        CCMModeFinite (i.N+1) and ccmModeFinite (i.N+1) on both sides,
        while retaining the original exact-contract control
      required_stop: SOURCE_ARCH_FINITE_FORM_CARRIER_MISMATCH

  KILL:
    - id: GLOBAL_J_K_SWAP
      reason: >-
        swapping both dummy indices everywhere is alpha-equivalent after
        reindexing; on the literal target, ccmWREntry symmetry makes weaker
        entry-only swaps blind as well
      card: C04
      may_not_be_reported_as_fired: true

  ADD:
    - id: P057_F_9_ABSTRACT_ENTRY_ORIENTATION
      host: HARNESS_ONLY
      object: EXPLICIT_NON_SYMMETRIC_FIN2_MATRIX_WITH_C_EQ_E0_D_EQ_E1
      mutation: matrix_entry_A_j_k_to_A_k_j_with_coefficients_fixed
      required_stop: SOURCE_ARCH_FINITE_FORM_ENTRY_ORIENTATION_DETECTOR_MISSING

  total_required_after_repair: 9

REPAIRED_PREFLIGHT:
  production_authorized: false
  repository_mutation_authorized: false
  required_artifacts:
    - exact_harness_bytes
    - exact_sha256_byte_and_line_counts
    - direct_Lean_stdout_stderr_and_exit
    - exact_forbidden_token_scan
    - exact_public_private_surface_scan
    - print_axioms_output
    - nine_plant_results
    - proof_dependency_fingerprint_showing_direct_E4C_consumption
  same_living_chat_return_required: true
  fresh_chat: false

STOP:
  GOAL057_B3_0F_BYTE_PINNED_HARNESS_UNAVAILABLE_OR_PLANT_BLIND

SUCCESS:
  GOAL057_B3_0F_REPAIRED_PREFLIGHT_SOURCE_LOCKED

PRODUCTION_SUCCESS_CODE_RESERVED:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

POST_PRODUCTION_NEXT_GAP:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY

POST_PRODUCTION_NEXT_DISCRIMINATOR:
  B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT

POST_PRODUCTION_NEXT_GAP_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: UNCHANGED_PENDING_PREFLIGHT_REPAIR
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL_MANDATE: ACCEPTED
ARSENAL_DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: FINITE_CELL
VERIFIER: CONDITIONAL
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  w02_source_pairing: OPEN
  prime_source_pairing: OPEN
  complete_source_weil_form: OPEN
  associated_operator_graph: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
  sole_owner_gate: PX_RH_CLAIM
```

## 1. Source-lock ruling

The attached request was read in full and now has a local byte lock of SHA-256 `81c2e419…d75c4`, 9,035 bytes, and 269 lines. It claims a separate 2,678-byte Lean harness with SHA-256 `b1060045…6e95`, a direct Lean pass, four controls, and the standard axiom triple.  `[FINITE_CELL][CONDITIONAL]`

Live `origin/rh_clean` is exactly the requested commit `c22a4a9ca4e00f1f0443ef3509705bb9eda91082`.  `[ABSTRACT][PAPER]`

That commit is documentation-only. It has the proved B3.0E4C production closeout as its direct parent and modifies only `q3.lean.aristotle/docs/INSIGHTS.md`; it does not publish the scratch harness or alter either mathematical parent.  `[ABSTRACT][PAPER]`

The claimed `Goal057B3_0F_Scratch.lean` is not attached to this review and is not present at the pinned commit. Consequently, I cannot verify:

* its claimed SHA-256;
* its claimed 106-line content;
* the exact four controls;
* whether `simp` really closes under the pinned Lean toolchain;
* whether the public/private counts are exact;
* whether the displayed axiom output belongs to those bytes;
* whether the statement-mutation controls remain unchanged during the plants.

This is a load-bearing source-lock failure, not a cosmetic packet omission. Production release is therefore denied in this batch. `[FINITE_CELL][CONDITIONAL]`

## 2. Mathematical theorem audit

The mathematical statement itself survives.

The source-locked form contract states that the finite restriction is written in the ordered basis

[
(V_{-N},\ldots,V_N)
]

and that for coefficient rows (c,d),

[
B(f,g)
======

\sum_{j,k}
\overline{c_j},\tau_{j,k},d_k.
]

It explicitly fixes antilinearity in the first argument, linearity in the second, the complex coefficient carrier, and conjugate transpose on the left.  `[FINITE_CELL][PAPER]`

Production defines the exact finite carrier by

```lean
CCMModeFinite N := Fin (2 * N + 1)
```

and the exact ordered source label by

```lean
ccmModeFinite N j = (j.1 : ℤ) - N.
```

It also states that these are the literal source modes `{-N,…,N}`.  `[FINITE_CELL][LEAN]`

The closed B3.0E4C parent proves, for every ordered pair of integer modes,

```lean
sourceArchimedeanModePairing i n r =
  -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ).
```

`[ABSTRACT][LEAN]`

Applying that identity at each literal pair

```lean
(ccmModeFinite i.N j, ccmModeFinite i.N k)
```

gives

[
\sum_{j,k}
\overline{c_j},
B^{\mathrm{arch}}_{j,k},
d_k
===

\sum_{j,k}
\overline{c_j},
(-W_{\mathbb R,jk}),
d_k
===

-\sum_{j,k}
\overline{c_j},
W_{\mathbb R,jk},
d_k.
]

Thus the proposed global minus sign is correct, and it applies to the complete double sum. No coefficient sign is moved and no matrix symmetry is required. `[FINITE_CELL][LEAN]`

The full literal CCM entry is source-locked as

[
W_{0,2}-W_{\mathbb R}-W_{\mathrm{prime}},
]

so this child represents exactly the archimedean contribution and nothing more.  `[FINITE_CELL][LEAN]`

### Import ruling

Both direct imports are honest and minimal relative to the current module graph:

```lean
Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
```

The first supplies the entrywise theorem. The second supplies the general finite carrier and literal mode map; E4C’s import chain supplies only the source entry definitions, not this general finite wrapper. Replacing the second import by the wider finite-residual module would increase dependencies without adding proof authority. `[FINITE_CELL][LEAN]`

## 3. Why compilation metadata is insufficient here

This theorem has an unusual falsifier requirement.

The entrywise E4C theorem is strong enough to prove many **wrongly packaged** coefficient identities if the same wrong wrapper is placed on both sides. For example:

```text
star(c_j) → c_j on both sides
```

still leaves an algebraically valid consequence of E4C. Likewise:

```text
complex form → real part of both forms
```

remains true but loses the source’s complex sesquilinear carrier.

Therefore, the fact that the public theorem compiles is not by itself evidence that the public theorem has the correct source contract. The independent exact-contract and scaling controls are the real judges. **[C04][C09]**

The request says those controls exist and are retained during statement mutations. Without the harness bytes, that claim cannot be checked. This is precisely why the absent file blocks release despite the simplicity of the theorem. `[FINITE_CELL][CONDITIONAL]`

## 4. Plant audit

### Retained without repair

`P057_F_1_GLOBAL_WR_SIGN` is load-bearing. Removing the outer minus changes the source ledger.

`P057_F_6_PARENT_PROVENANCE` is load-bearing. Replacing E4C with a hypothesis identical to the desired finite-form equality is a premise surrogate and must stop with:

```text
SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
```

**[C10]**

`P057_F_8_DEPENDENCY` is load-bearing. This theorem requires no generated PSD, Step33, hbox, numeric payload, or direct Aristotle-output import.

### Retained only with immutable controls

`P057_F_2_FIRST_SLOT_STAR` is valid only if the original exact-contract control and first-slot scaling control remain byte-unchanged while the public statement is mutated. If both sides simply lose `star`, the mutated theorem can still compile.

`P057_F_3_SECOND_SLOT_STAR` has the same condition. Moving conjugation from the first coefficient to the second on both sides creates another algebraically valid but source-wrong wrapper.

`P057_F_7_REAL_PROJECTION` likewise needs the unchanged exact-contract control. Applying `.re` to both sides can remain a theorem while destroying the complex form.

The repaired preflight must record the hashes of the immutable controls before and after each such mutation.

### Repaired mode plant

The proposed mutation

```text
source pairing second mode k → j
```

does not reverse the mode order; it collapses the second mode to the first. Its exact classification should be:

```yaml
id: P057_F_4_SECOND_MODE_COLLAPSE
required_stop: SOURCE_ARCH_FINITE_FORM_SECOND_MODE_COLLAPSED
```

This is observable because the source side becomes diagonal in its mode entry while the CCM-WR side remains a full matrix form.

### Repaired carrier plant

A mere local type mismatch is too weak. The mutation should construct a coherent but wrong theorem on

```lean
CCMModeFinite (i.N + 1)
```

using

```lean
ccmModeFinite (i.N + 1)
```

on both sides. That mutated theorem may itself compile. The unchanged exact-contract control on `CCMModeFinite i.N` must reject it.

This tests source-family identity rather than parser failure. **[C04][C09]**

### Killed global index-swap plant

A mutation that swaps the dummy variables `j` and `k` **everywhere** is alpha-equivalent after reindexing the two finite sums. It does not test anything.

A weaker mutation that merely transposes the literal CCM-WR entry is also blind here because production proves `ccmWREntry` symmetric. The request correctly suspected this defect.  `[FINITE_CELL][LEAN]`

That plant is killed and must never be counted as fired. **[C04]**

### Exact replacement

Add a harness-only, non-symmetric two-dimensional orientation detector.

Choose an explicit matrix (A) on `Fin 2` with

[
A_{0,1}=1,\qquad
A_{0,0}=A_{1,0}=A_{1,1}=0,
]

and coefficient vectors

[
c=e_0,\qquad d=e_1.
]

Then

[
\sum_{j,k}\overline{c_j}A_{j,k}d_k=1,
]

whereas replacing only `A j k` by `A k j` gives (0).

The mutation must stop with:

```text
SOURCE_ARCH_FINITE_FORM_ENTRY_ORIENTATION_DETECTOR_MISSING
```

This test lives one category finer than the final symmetric CCM-WR matrix, where orientation has become invisible. **[C04]**

## 5. Repaired discriminator

The next transaction is one read-only/untracked preflight. It does not create production Lean.

The authoritative harness must contain exactly:

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

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
```

Only imports or opens already present in the original byte-pinned harness may be retained beyond this display. The next packet must attach the actual bytes rather than reconstructing them in prose.

The harness must also contain, outside production:

1. the exact-contract control for arbitrary `i,c,d`;
2. first-slot antilinear scaling;
3. second-slot linear scaling;
4. the literal mode-map control;
5. the new explicit non-symmetric `Fin 2` orientation control;
6. `#print axioms` for the public theorem.

Required commands:

```bash
sha256sum q3.lean.aristotle/Goal057B3_0F_Scratch.lean
wc -c -l q3.lean.aristotle/Goal057B3_0F_Scratch.lean

rg -n \
  'sorry|admit|exact\\?|unsafe|native_decide|opaque|axiom |Float' \
  q3.lean.aristotle/Goal057B3_0F_Scratch.lean

lake env lean \
  q3.lean.aristotle/Goal057B3_0F_Scratch.lean
```

All nine repaired plants must then be run in temporary copies or through stdin. No mutation file may remain in the repository.

### Binary outcome

```text
PASS:
  exact harness bytes attached;
  direct Lean exit 0;
  controls and axiom output verified;
  all nine repaired plants fire;
  return in this same chat for one production-release decision.

FAIL:
  retain B3.0F as open;
  report the first exact statement, dependency, control, or plant defect;
  do not create the production file.
```

## 6. Strongest attack

> This theorem is a one-line `simp` corollary. A future complete source-Weil-form theorem could repeat the same rewrite privately, so publishing it is duplicate API.

That objection is valid but does not kill the theorem shape.

The theorem does not add mathematics. Its value is that it freezes a category transition where several source conventions become simultaneously load-bearing:

* entrywise source pairing to finite coefficient form;
* the exact `-N,…,N` carrier;
* conjugate-linear first coefficients;
* linear second coefficients;
* the complete outer archimedean minus sign;
* no real projection;
* no use of symmetry to change ordered slots.

The direct future consumer is the complete finite source-Weil-form assembly. One public theorem and zero support declarations are a proportionate interface cost.

However, that justification works only if the exact controls demonstrate that the published statement—not merely some equational variant—carries those conventions. The missing harness therefore changes the operational verdict from `TRY` to `RUN`, not from `TRY` to `KILL`.

## 7. Boundary after a later successful production release

A later validated B3.0F production theorem would close only:

```text
finite archimedean sesquilinear matrix-form lift.
```

It would not close:

* the source (W_{0,2}) pairing;
* the source prime pairing;
* the complete source Weil form;
* a form-domain theorem;
* an associated operator;
* operator-domain membership;
* a compression identity;
* the actual continuum numerator;
* H4a1b;
* any coarse Goal-057 checkpoint.

The coarse ledger remains:

```text
0 closed / 10 remaining.
```

The smallest post-production source question is the rank-two endpoint/pole component:

```text
GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
```

The corresponding first discriminator should be a read-only source/API audit:

```text
B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT
```

The source matrix already isolates `ccmW02Entry`, `ccmWREntry`, and `ccmPrimeEntryN1` as separate components of the exact ledger, so W02 is a smaller successor than the complete Weil-form assembly.  `[FINITE_CELL][CONDITIONAL]`

That successor is named only. It is not authorized.

## 8. Meta closeout

**What became smaller?**

The B3.0F mathematical shape is accepted. The remaining release blocker is no longer theorem design; it is one exact byte-provenance and plant-observability transaction.

**What was killed?**

* the claim that the current packet contains an authoritative harness;
* compilation metadata as a substitute for harness bytes;
* a global `j ↔ k` mutation as an orientation plant;
* incoherent type failure as a sufficient carrier plant.

**What must not be tried again?**

Do not request production release from a Markdown summary of an unattached scratch file. Do not count a symmetric or dummy-index swap as orientation evidence. Do not mutate both sides of a wrapper theorem and call its continued compilation a successful source-convention plant.

**Current smallest named gap**

```text
GOAL057_B3_0F_BYTE_PINNED_HARNESS_UNAVAILABLE_OR_PLANT_BLIND
```

**Next cheapest decisive test**

```text
B3_0F_REPAIRED_PREFLIGHT_SOURCE_LOCK_AND_PLANT_OBSERVABILITY
```

**Prior prediction fate**

```text
E4C prediction:
  the next atom is a finite conjugate-first coefficient-form lift.

Fate:
  CONFIRMED mathematically.

B3.0F packet prediction:
  the attached material is an exact byte-pinned compiling harness package.

Fate:
  REFUTED.
  Only the request file is attached; the claimed harness bytes are absent.

Plant prediction:
  a global j/k swap tests source orientation.

Fate:
  REFUTED.
  The mutation is reindexing-blind, and the literal target is symmetric.
```

```yaml
iteration:
  target: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
  status: OPEN
  failed_strategy: release_from_unattached_harness_metadata
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: GOAL057_B3_0F_BYTE_PINNED_HARNESS_UNAVAILABLE_OR_PLANT_BLIND
  invariant_learned: exact_contract_controls_are_load_bearing_because_wrong_common_wrappers_can_still_follow_entrywise_E4C
  forbidden_future_move: treat_symmetric_or_dummy_index_swaps_as_slot_orientation_evidence
  next_decisive_test: B3_0F_REPAIRED_PREFLIGHT_SOURCE_LOCK_AND_PLANT_OBSERVABILITY
  progress_class: FALSIFICATION_PROGRESS
  route_score: 4
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  RUN_GOAL057_B3_0F_REPAIRED_PREFLIGHT

MODE:
  UNTRACKED_READ_ONLY_PREFLIGHT
  PRODUCTION_AUTHORIZED: false

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
  require_origin_equal: true
  request_attachment_sha256: 81c2e4198356b3a4811ad4edc42f2b1ca1d90d2a36f0aa684419ab75817d75c4
  claimed_harness_sha256: b1060045cf6cf22939ef04b45f324d7ab0af380fe920cb275bcc3f6623b56e95

TASK:
  - recover or regenerate the exact untracked B3.0F harness
  - attach its actual bytes in the next same-chat packet
  - if its SHA differs from the claimed hash, amend the lock honestly
  - do not summarize absent bytes as authoritative
  - make no production Lean edit

HARNESS_PATH:
  q3.lean.aristotle/Goal057B3_0F_Scratch.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

EXACT_PUBLIC_THEOREM: |
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

MANDATORY_CONTROLS:
  - exact_contract_arbitrary_i_c_d
  - first_slot_antilinear_scaling
  - second_slot_linear_scaling
  - literal_ccmModeFinite_j_minus_N
  - explicit_non_symmetric_Fin2_entry_orientation

CONTROL_IMMUTABILITY:
  - hash the controls before every statement-mutation plant
  - verify their bytes are unchanged afterward
  - a mutation of both the public theorem and its control is invalid

MANDATORY_PLANTS:
  - id: P057_F_1_GLOBAL_WR_SIGN
    required_stop: SOURCE_ARCH_FINITE_FORM_GLOBAL_SIGN_MISMATCH

  - id: P057_F_2_FIRST_SLOT_STAR
    required_stop: SOURCE_ARCH_FINITE_FORM_FIRST_SLOT_ANTILINEARITY_MISMATCH

  - id: P057_F_3_SECOND_SLOT_STAR
    required_stop: SOURCE_ARCH_FINITE_FORM_SLOT_CONJUGATION_MISMATCH

  - id: P057_F_4_SECOND_MODE_COLLAPSE
    mutation: source_pairing_second_mode_k_to_j_only
    required_stop: SOURCE_ARCH_FINITE_FORM_SECOND_MODE_COLLAPSED

  - id: P057_F_5_FINITE_CARRIER
    mutation: coherent_i_N_to_i_N_plus_one_on_both_sides_only
    required_stop: SOURCE_ARCH_FINITE_FORM_CARRIER_MISMATCH

  - id: P057_F_6_PARENT_PROVENANCE
    required_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION

  - id: P057_F_7_REAL_PROJECTION
    required_stop: SOURCE_ARCH_FINITE_FORM_COMPLEX_CARRIER_LOST

  - id: P057_F_8_DEPENDENCY
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

  - id: P057_F_9_ABSTRACT_ENTRY_ORIENTATION
    host: HARNESS_ONLY
    mutation: transpose_explicit_non_symmetric_Fin2_entry_with_coefficients_fixed
    required_stop: SOURCE_ARCH_FINITE_FORM_ENTRY_ORIENTATION_DETECTOR_MISSING

KILLED_PLANT:
  mutation: swap_j_and_k_everywhere
  reason: dummy_reindexing_and_target_symmetry_make_it_non_discriminating
  card: C04
  may_not_be_run_or_counted: true

VALIDATION:
  - sha256sum harness
  - exact byte and line counts
  - forbidden-token scan
  - direct lake env lean on harness
  - capture stdout/stderr, exit code, and stdout/stderr SHA-256
  - exact public surface 0_definitions_1_theorem
  - exact private surface 0_definitions_0_theorems
  - print axioms for public theorem
  - require exactly [propext, Classical.choice, Quot.sound]
  - run all nine repaired plants in temporary copies or stdin
  - remove every mutation artifact
  - dependency fingerprint must show direct E4C theorem consumption
  - exact git status --short report
  - no route-state update

PASS_RETURN:
  - attach the exact harness bytes
  - attach or quote exact command output
  - report all plant fates
  - return in this same living chat for one production-release review

STOP:
  GOAL057_B3_0F_BYTE_PINNED_HARNESS_UNAVAILABLE_OR_PLANT_BLIND

SUCCESS:
  GOAL057_B3_0F_REPAIRED_PREFLIGHT_SOURCE_LOCKED

NOT_AUTHORIZED:
  - create_D0PstarSourceArchFiniteFormCCMWRCrosswalk_production_file
  - modify_E4C_or_CCMFiniteWeilSourceMatrix
  - define_W02_or_prime_source_pairing
  - define_complete_source_Weil_form
  - add_matrix_or_operator_wrapper
  - use_global_j_k_swap_as_orientation_evidence
  - decrement_the_ten_checkpoint_ledger
  - invoke_or_close_H4A1B
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
  h4a1b: OPEN
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
