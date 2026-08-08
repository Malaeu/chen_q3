# PROSHKA RETURN — Goal 057 B3.0F repaired preflight source lock and plant observability

Date: 2026-08-08
Route: Route B / Goal 057 / B3.0F
Return class: same-living-chat repaired preflight
Requested decision: one production-release ruling only

## 0. Exact result

`GOAL057_B3_0F_REPAIRED_PREFLIGHT_SOURCE_LOCKED`

The repaired untracked harness is attached as actual bytes. The original
claimed lock is honestly superseded because the mandated non-symmetric
orientation control adds nine lines and 365 bytes.

```yaml
head: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
origin_rh_clean: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
head_equals_origin: true
request_sha256: 81c2e4198356b3a4811ad4edc42f2b1ca1d90d2a36f0aa684419ab75817d75c4
request_bytes: 9035
request_lines: 269
repair_verdict_sha256: 6b4cff1c1b9a96443050de689324012a028e97b7922fadd64a00d75e288ed4a2
repair_verdict_bytes: 25909
repair_verdict_lines: 815
old_harness_sha256_superseded: b1060045cf6cf22939ef04b45f324d7ab0af380fe920cb275bcc3f6623b56e95
old_harness_bytes_superseded: 2678
old_harness_lines_superseded: 106
new_harness_sha256: 7b4e075e82dc90c173098c459813a69e312d15ff10a616023def740a671779b7
new_harness_bytes: 3043
new_harness_lines: 115
```

## 1. Attached authoritative harness

Path:

`q3.lean.aristotle/Goal057B3_0F_Scratch.lean`

The file has exactly two imports, one public theorem, no public or private
definitions, no private theorems, five control examples and one
`#print axioms` command.

The fifth control is the mandated explicit non-symmetric `Fin 2` detector:

```lean
example :
    let A : Matrix (Fin 2) (Fin 2) ℂ :=
      fun j k => if j = 0 ∧ k = 1 then 1 else 0
    let c : Fin 2 → ℂ := fun j => if j = 0 then 1 else 0
    let d : Fin 2 → ℂ := fun k => if k = 1 then 1 else 0
    (∑ j, ∑ k, star (c j) * A j k * d k) = 1 ∧
      (∑ j, ∑ k, star (c j) * A k j * d k) = 0 := by
  norm_num [Fin.sum_univ_two]
```

## 2. Direct Lean evidence

Command:

```bash
lake env lean Goal057B3_0F_Scratch.lean \
  > /tmp/b30f_harness.stdout \
  2> /tmp/b30f_harness.stderr
```

Result:

```yaml
exit: 0
stdout_bytes: 132
stdout_lines: 3
stdout_sha256: 41a3119321bba45c7223cf0f2ad48d5eeb5b14030bf9189be66cdb2c629ca178
stderr_bytes: 137
stderr_lines: 1
stderr_sha256: 21d490443f9947b35732a96388db21561b6395ab676c320eb46630122a748851
```

Exact stdout:

```text
'Q3.RouteB.D0Pstar.sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exact stderr:

```text
warning: UnicodeBasic: repository '/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle/.lake/packages/UnicodeBasic' has local changes
```

The stderr warning is a pre-existing package-worktree condition and is not a
proof failure.

## 3. Static and dependency fingerprints

Forbidden-token scan pattern:

```text
sorry|admit|exact\?|unsafe|native_decide|opaque|axiom |Float
```

Findings: **0**.

Exact imports:

```text
1:import Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
2:import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
```

Direct E4C consumption:

```text
28:  simp [sourceArchimedeanModePairing_eq_neg_ccmWREntry]
```

Surface fingerprint:

```text
11:theorem sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
30:example
48:example
75:example
101:example (N : ℕ) (j : CCMModeFinite N) :
104:example :
113:#print axioms sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
```

```yaml
public_definitions: 0
public_theorems: 1
private_definitions: 0
private_theorems: 0
controls: 5
print_axioms_commands: 1
direct_parent_consumed: true
generated_dependency_tokens: 0
```

Immutable block from the first `example` through the final axiom print:

```text
sha256: 1a7a2dbbc01c59d1696feade20654708ce4d37752de660cceed02d50d99e191d
```

That SHA was rechecked after the statement-mutation plants and remained
unchanged.

## 4. Nine repaired plants

All mutation source lived only at `/tmp/Goal057B3_0F_Plant.lean`. It was
deleted after the ninth run. No mutation source remains in the repository or
at that `/tmp` path.

```yaml
plants:
  - id: P057_F_1_GLOBAL_WR_SIGN
    lean_exit: 1
    observed: correct form equals negative sum, mutation demands positive sum
    required_stop: SOURCE_ARCH_FINITE_FORM_GLOBAL_SIGN_MISMATCH
    log_sha256: e001752045b95cc0eed690f85d06d5235c85a63aa969f458e00895a53c70b408

  - id: P057_F_2_FIRST_SLOT_STAR
    wrong_wrapper_lean_status: COMPILES_BEFORE_EXACT_CONTROL
    final_lean_exit: 1
    observed: c_j wrapper cannot inhabit immutable star_c_j contract
    required_stop: SOURCE_ARCH_FINITE_FORM_FIRST_SLOT_ANTILINEARITY_MISMATCH
    log_sha256: 932d49a5625dd323729868c965574d6f477e5b09a4312ef77cef2a3be94b3cdf

  - id: P057_F_3_SECOND_SLOT_STAR
    wrong_wrapper_lean_status: COMPILES_BEFORE_EXACT_CONTROL
    final_lean_exit: 1
    observed: c_j_A_jk_star_d_k cannot inhabit immutable conjugate-first contract
    required_stop: SOURCE_ARCH_FINITE_FORM_SLOT_CONJUGATION_MISMATCH
    log_sha256: 3a145efce31294c7bc799c503a890a893003772ae8f9a976cc1923d13446a1af

  - id: P057_F_4_SECOND_MODE_COLLAPSE
    lean_exit: 1
    observed: diagonal WR_j_j source side differs from full WR_j_k form
    required_stop: SOURCE_ARCH_FINITE_FORM_SECOND_MODE_COLLAPSED
    log_sha256: c8675ce79f7f3eb85fe24b89853d27646c11b10b5807af22787eedb186ae9a53

  - id: P057_F_5_FINITE_CARRIER
    wrong_wrapper_lean_status: COHERENT_N_PLUS_ONE_THEOREM_COMPILES
    final_lean_exit: 1
    observed: immutable N contract rejects coherent N_plus_one family
    required_stop: SOURCE_ARCH_FINITE_FORM_CARRIER_MISMATCH
    log_sha256: 4486b8e18b95b1d1232d970b864e0c1697dc46b904845bae27ec3bd094b4d279

  - id: P057_F_6_PARENT_PROVENANCE
    lean_exit: 0
    observed_body: exact_hform_only
    direct_E4C_consumption: false
    semantic_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
    log_sha256: 21d490443f9947b35732a96388db21561b6395ab676c320eb46630122a748851

  - id: P057_F_7_REAL_PROJECTION
    real_projection_theorem_status: COMPILES
    final_lean_exit: 1
    observed: real equality cannot inhabit immutable complex equality
    required_stop: SOURCE_ARCH_FINITE_FORM_COMPLEX_CARRIER_LOST
    log_sha256: a63154c94fd80d2253ae84b55de13694bfbd916a5a917c341b2a8a7dd8da087e

  - id: P057_F_8_DEPENDENCY
    injected_import: Q3.Proofs.PSD_CenteredCoeffEntryHboxImport
    lean_exit: 0
    static_dependency_gate: FIRED
    semantic_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
    log_sha256: 21d490443f9947b35732a96388db21561b6395ab676c320eb46630122a748851

  - id: P057_F_9_ABSTRACT_ENTRY_ORIENTATION
    lean_exit: 1
    observed: transposed explicit nonsymmetric entry reduces expected 1 to False
    required_stop: SOURCE_ARCH_FINITE_FORM_ENTRY_ORIENTATION_DETECTOR_MISSING
    log_sha256: dff398c84639596a644b1f662d8a056130f4fd3af619b38bacca040da0586aac

killed_plant:
  mutation: swap_j_and_k_everywhere
  run: false
  counted: false
  reason: dummy_reindexing_and_target_symmetry_make_it_non_discriminating
```

## 5. Operational integrity

```yaml
routeb_status_check: OK
route: CHALLENGER_NOT_RH
active_bus_goal: 057
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
h4a1b: OPEN
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
production_file_created: false
route_state_updated: false
aristotle_submission: NONE
route_promotion: false
px_rh_claim: NOT_MADE
old_staged_patch_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b
old_staged_patch_preserved: true
```

## 6. Decision requested

The repaired preflight now supplies the authoritative bytes, exact direct
Lean output, five controls, immutable-control hash, all nine plant fates and
the direct E4C dependency fingerprint.

Please issue exactly one of:

```yaml
release:
  operative_class: TRY_GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
  production_authorized: exactly_one_child
  success_code: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED
stop:
  operative_class: KILL_GOAL057_B3_0F_AS_STATED
  stop_code: exact_new_stop_required
repair:
  operative_class: RUN_GOAL057_B3_0F_REPAIRED_PREFLIGHT
  production_authorized: false
```

Do not authorize B3.0G, W02 or prime pairings, complete source Weil form,
matrix/operator wrapper, coarse-checkpoint decrement, H4a1b, Bus 010,
Goal 055, G2/CCM, Aristotle, promotion, PX or RH. Reuse this same living chat.

ARSENAL_USED: `C04,C09,C10`
