# STATUS: OPEN — B3.0I EXACT SOURCE-PRIME MODE-PAIRING PRODUCTION RELEASE AUTHORIZED

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING
OPERATIVE_CLASS_COUNT: 1

TRANSACTION:
  ID: GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_PRODUCTION_RELEASE
  MODE: IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD
  PRODUCTION_RELEASE: AUTHORIZED
  PRODUCTION_ALREADY_PROVED: false
  AUTHORIZED_CHILDREN: 1
  LATER_CHILDREN_AUTHORIZED: 0

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  HEAD:
    expected: 2dfda1456501f3d027a4e1cfcfc42a93a64b9e91
    observed_origin_rh_clean: 2dfda1456501f3d027a4e1cfcfc42a93a64b9e91
    status: PASS

  RELEASE_REQUEST:
    observed_sha256: 2dd89cad6d4da6da4cbeccf7619a3e49cdd2dc52f402f79070274cd0d875540a
    observed_bytes: 11690
    observed_lines: 412
    read_byte_for_byte: true
    status: PASS

  ATTACHED_CANDIDATE:
    expected_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
    observed_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
    expected_bytes: 1782
    observed_bytes: 1782
    expected_lines: 49
    observed_lines: 49
    status: PASS

  CANDIDATE_BODY_FINGERPRINT:
    lines: 14_through_22
    expected_sha256: a60d4159fd0907203f70a742a82d532914e8b4b33181248e5043f08e2f53bc07
    observed_sha256: a60d4159fd0907203f70a742a82d532914e8b4b33181248e5043f08e2f53bc07
    status: PASS

  TARGET_AT_PIN:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean
    present: false
    transaction_shape: CREATE_ONLY

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  theorem_statement: ACCEPTED_EXACTLY
  theorem_proof: ACCEPTED_EXACTLY
  source_definition: ACCEPTED_EXACTLY
  import_surface: ACCEPTED_EXACTLY
  public_surface: ACCEPTED_EXACTLY
  private_surface: ACCEPTED_EXACTLY
  candidate_byte_change_allowed: false
  comment_or_whitespace_amendment_allowed: false
  first_mathematical_defect: NONE
  first_Lean_shape_defect: NONE
  first_source_provenance_defect: NONE

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean

EXACT_MATERIALIZATION:
  source_attachment: GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_CANDIDATE_2026-08-09.txt
  method: BYTE_FOR_BYTE_COPY
  expected_production_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
  expected_production_bytes: 1782
  expected_production_lines: 49
  any_mismatch: STOP

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions:
    - sourcePrimeModePairing
  theorems:
    - sourcePrimeModePairing_eq_ccmPrimeEntryN1
  total_public_declarations: 2

PRIVATE_SURFACE:
  definitions: 0
  theorems: 0
  total_private_declarations: 0

SOURCE_OBJECT:
  name: sourcePrimeModePairing
  meaning: POSITIVE_SIDE_W_P_SHARP_COMPONENT_BEFORE_FULL_LEDGER_SUBTRACTION
  stores_full_ledger_minus_sign: false
  claims_pointwise_or_form_nonnegativity: false

NORMALIZATION:
  support: Finset.Icc 2 i.m
  upper_endpoint_included: true
  cutoff_owner: i.m
  cutoff_owner_not: i.N

  arithmetic_weight: ArithmeticFunction.vonMangoldt k
  prime_power_policy: ALL_PRIME_POWERS_EXACTLY_ONCE
  exponent_multiplier: absent

  size_weight: inverse_sqrt_k
  outer_prime_weight_factor_two: absent
  correlation_reconstruction_factor_two: present

  logarithmic_coordinate: Real.log(k)
  logarithmic_coordinate_divided_by_two_pi: false

  first_mode: CONJUGATED_ANTILINEAR
  second_mode: UNCONJUGATED_LINEAR

TARGET:
  name: Q3.RouteB.ccmPrimeEntryN1
  target_sign: POSITIVE_COMPONENT
  full_Weil_ledger_sign: EXTERNAL_MINUS

C10_FIREWALL:
  ccmPrimeEntryN1_occurrences_in_public_definition: 0
  vonMangoldt_occurrences_in_public_definition: 1
  direct_formula_alias: false
  result: PASS

C04_FIREWALL:
  source_order_visible_before_target_symmetry: true
  target_symmetry_used_as_order_evidence: false
  nonsymmetric_presymmetry_control_required: true
  result: PASS

PLANTS:
  registered_total: 13
  judged_inside_this_child: 12
  deferred_outside_this_child:
    - P_PRIME_2_COMPLETE_LEDGER_PLUS_PRIME
  deferred_plant_claimed_fired: false
  target_symmetry_used_for_slot_plant: false
  production_rerun_required: true

STOP:
  GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_EQ_CCM_PRIME_ENTRY_N1_MISSING

SUCCESS:
  GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_EQ_CCM_PRIME_ENTRY_N1_PROVED

SCOPE: FINITE_CELL
VERIFIER: CONDITIONAL_UNTIL_PRODUCTION_LEAN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE:
  phase_key_change: false
  reuse_same_living_chat: true
  open_fresh_chat: false

FINAL_BOUNDARY:
  B3_0H: CLOSED
  B3_0I: RELEASED_FOR_PRODUCTION_NOT_YET_CLOSED
  B3_0: OPEN

  CURRENT_CHECKPOINT: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  CHECKPOINT_EFFECT: STRICTLY_ADVANCED_NOT_CLOSED
  COARSE_CHECKPOINTS_CLOSED: 0
  COARSE_CHECKPOINTS_REMAINING: 10

  ROUTE: CHALLENGER_NOT_RH
  BUS_010: VOID
  GOAL_055: HOLD
  G2_CCM: FROZEN
  H4A1B: OPEN
  ARISTOTLE_SUBMISSION: NONE
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  SOLE_OWNER_GATE: PX_RH_CLAIM
```

## 1. Byte and repository audit

Both attached files were read byte-for-byte. The candidate matches the required SHA-256, byte count, line count, and definition-body fingerprint exactly. The candidate must therefore be copied without normalization, reformatting, docstring edits, or whitespace changes.   `[FINITE_CELL][LEAN]`

The remote `rh_clean` head is exactly `2dfda1456501f3d027a4e1cfcfc42a93a64b9e91`, the commit closing B3.0H.  `[ABSTRACT][PAPER]`

The intended production path is absent both at the pin and on the live branch. This is a clean create-only transaction. `[FINITE_CELL][PAPER]`

The route state at the pin records B3.0H as closed, B3.0I as the open source-prime audit/release obligation, and the coarse ledger as `0 closed / 10 remaining`.  `[ABSTRACT][PAPER]`

## 2. Exact source-to-target proof

The parent theorem proves, for every production `PairIndex`, every ordered mode pair, and every nonnegative (x),

[
2\int_{\mathbb R}
\overline{\widehat V_{i,n}(t)}
\cos(2\pi tx)
\widehat V_{i,r}(t),dt
======================

\begin{cases}
\operatorname{ccmQKernel}(L_m(i),n,r,x),&x\le L_m(i),\
0,&x>L_m(i).
\end{cases}
]

It visibly preserves conjugation in the first mode, the external factor (2), the cycles-per-unit Fourier convention, and the ordered pair `(n,r)`.  `[ABSTRACT][LEAN]`

The literal target is

[
\operatorname{ccmPrimeEntryN1}(m,n,r)
=====================================

\sum_{k=2}^{m}
\Lambda(k),k^{-1/2}
\operatorname{ccmQKernel}(\log m,n,r,\log k),
]

with inclusive support `Finset.Icc 2 m`.  `[FINITE_CELL][LEAN]`

The candidate proof is therefore exact:

1. unfold the source object and the literal target;
2. distribute the real-to-complex cast over the finite sum;
3. fix (k\in[2,i.m]);
4. prove (0\le\log k\le L_m(i));
5. apply the parent cosine-correlation theorem at (x=\log k);
6. reduce `ccmL`, `L_m`, and `logLength`;
7. close by ring algebra.

No analytic interchange, numerical certificate, formula premise, source-family substitution, or symmetry argument is introduced. `[FINITE_CELL][LEAN]`

## 3. Sign ruling

`sourcePrimeModePairing` denotes the positive-side one-sided (W_p^#) component. “Positive-side” describes its place in the source ledger; it is **not** a theorem that arbitrary off-diagonal complex entries are nonnegative. `[ABSTRACT][PAPER]`

The complete source matrix keeps the prime minus outside this object:

[
\tau
====

W_{0,2}-W_{\mathbb R}-W_{\mathrm{prime}}.
]

Production fixes this independently as

```lean
ccmW02Entry - ccmWREntry - ccmPrimeEntryN1.
```

`[FINITE_CELL][LEAN]`

Thus:

* the new source object has no leading minus;
* the crosswalk target is positive `ccmPrimeEntryN1`;
* the later complete-form assembly must subtract the prime component;
* this child does not claim or test that later assembly.

P-PRIME-2 is therefore correctly **deferred outside this child**, not falsely reported as fired.

## 4. Prime-power support and normalization

The use of `ArithmeticFunction.vonMangoldt` is the exact single-sum reindexing of the source prime-power contribution. It includes prime powers, not only primes, and does not multiply by the exponent. `[FINITE_CELL][PAPER]`

The existing production normal form verifies:

[
\Lambda(4)=\Lambda(8)=\log2,\qquad
\Lambda(9)=\log3,
]

while unsupported composites such as (6,10,12) contribute zero. It also keeps the upper endpoint (13), producing the exact `log 13` contribution.  `[FINITE_CELL][LEAN]`

The candidate therefore retains all four independent normalization layers:

[
\Lambda(k),\qquad
k^{-1/2},\qquad
2\times\text{cosine correlation},\qquad
x=\log k.
]

The factor (2) belongs to reconstruction of the source correlation (q); it is not an additional prime-distribution weight. `[FINITE_CELL][LEAN]`

## 5. C10 and C04 audit

### C10 — functional, not surrogate

The public definition contains no occurrence of `ccmPrimeEntryN1` and no occurrence of `ccmQKernel`. It is written directly from:

* the source zero-extended modes;
* first-slot conjugation;
* the source cosine correlation;
* the exact von-Mangoldt weight;
* the exact inclusive cutoff.

Only the theorem proof crosses to the frozen CCM scalar. The object is therefore not a formula alias or premise surrogate. **[C10]** `[FINITE_CELL][LEAN]`

### C04 — ordered source law before symmetric target

The final CCM prime entry is real-symmetric and cannot detect a slot reversal by itself. The candidate preserves the ordered law before that forgetful step:

```lean
conj (Fourier mode n) * cosine * Fourier mode r.
```

The independent nonsymmetric complex control distinguishes first-slot conjugation from second-slot conjugation. Target symmetry is not counted as evidence. **[C04]** `[ABSTRACT][LEAN]`

The source object was also fixed before this release transaction, including its support, cutoff, sign layer, and coefficient normalization. The byte-pinned candidate is not a post hoc choice. **[C09]**

The Arsenal mandate and the relevant C04/C09/C10 attack rules are accepted.   `[ABSTRACT][PAPER]`

## 6. Strongest attack

> Because the parent theorem ultimately rewrites the source correlation to `ccmQKernel`, is the new definition merely laundering the target through an intermediate object from the same dependency tree?

No.

The public definition does not mention `ccmQKernel` or `ccmPrimeEntryN1`. It remains meaningful as a finite source Fourier-correlation sum before either CCM name is unfolded. The parent theorem supplies a previously proved source-to-kernel identity; the new theorem then applies that identity pointwise over the exact von-Mangoldt support.

The attack would become fatal under any of these mutations:

```text
sourcePrimeModePairing := ccmPrimeEntryN1;
sourcePrimeModePairing := sum of ccmQKernel terms;
remove direct consumption of the source-mode parent;
reverse slots and rely on target symmetry.
```

The exact candidate does none of them.

## 7. Plant ruling

The repaired matrix is accepted with the following classification:

| Plant class                                                                          | Ruling                                                                    |
| ------------------------------------------------------------------------------------ | ------------------------------------------------------------------------- |
| Object sign, support, cutoff, inverse-square-root weight, factor two, log coordinate | Exact definition-body and theorem-call fingerprints                       |
| Prime powers and unsupported composites                                              | Existing exact von-Mangoldt controls                                      |
| Upper endpoint                                                                       | Exact `Icc` fingerprint plus `13 ∈ Icc`, `13 ∉ Ico`, and `log 13` control |
| Ordered slots                                                                        | Definition fingerprint plus nonsymmetric complex control                  |
| Formula alias                                                                        | C10 definition-body firewall                                              |
| Generated or widened dependency                                                      | Exact one-import allowlist                                                |
| Complete-ledger `+ Prime` mutation                                                   | Correctly deferred; outside this child and not claimed fired              |

Production closeout must not state `13/13 plants fired`. It must state:

```text
12 child-local source/static/control judgments passed;
P-PRIME-2 remained explicitly deferred to the complete-form boundary.
```

## 8. Exact production and validation contract

Create only:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourcePrimeModePairing.lean
```

Copy the candidate byte-for-byte and require:

```text
SHA-256:
  ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34

bytes:
  1782

lines:
  49
```

The sole import, public surface, and private surface are immutable.

Production success requires:

```bash
test "$(git rev-parse HEAD)" = \
  "2dfda1456501f3d027a4e1cfcfc42a93a64b9e91"

test "$(git rev-parse origin/rh_clean)" = \
  "2dfda1456501f3d027a4e1cfcfc42a93a64b9e91"

test "$(git diff --cached | sha256sum | cut -d' ' -f1)" = \
  "291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b"

sha256sum \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean

cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourcePrimeModePairing

lake build
```

Then run:

```text
scripts/q3_check.sh;
repository-standard unit/orchestration suite;
routeb_status.py --check;
strict Spine;
three SQLite integrity checks;
proof-DB import twice with no row-count drift;
exact one-import and public-surface audit;
forbidden-token and taint scan;
all twelve child-local plant/control judges;
git diff --check;
exact git status --short.
```

The public theorem must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The proof database must record exactly two public declarations, both free of holes and project axioms. `[FINITE_CELL][CONDITIONAL]`

Only after every gate passes may the state say:

```text
GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_EQ_CCM_PRIME_ENTRY_N1_PROVED
```

## 9. Exact boundary

Successful production validation closes only the source-prime **entrywise** crosswalk.

It does not close or authorize:

* a finite prime sesquilinear form lift;
* the complete three-component source Weil form;
* any matrix or operator wrapper;
* an associated operator graph;
* form-domain or operator-domain membership;
* compression;
* the continuum numerator;
* H4a1b;
* a coarse checkpoint;
* Route-B promotion;
* PX/RH.

No subsequent child is selected or authorized in this verdict.

## 10. Meta closeout

**What became smaller?**

The prime component is reduced to one exact production file whose source object, sign layer, cutoff, support, weight, Fourier coordinate, and ordered slots are all fixed.

**What was killed?**

Formula aliasing, prime-only support, exponent-weighted prime powers, doubled prime weights, lost correlation factor, wrong cutoff, wrong logarithmic coordinate, and symmetry-based slot certification.

**What must not be tried again?**

Do not move the complete-ledger minus into `sourcePrimeModePairing`. Do not claim the deferred complete-form sign plant fired in this child. Do not alter a byte of the candidate.

**Current smallest named gap**

```text
GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_EQ_CCM_PRIME_ENTRY_N1_MISSING
```

**Prediction fate**

```text
Prediction:
  the exact 1,782-byte candidate is a source-faithful direct crosswalk.

Fate:
  CONFIRMED.

Risk:
  target symmetry could hide source slot reversal.

Fate:
  NEUTRALIZED by pre-symmetry definition fingerprint and independent
  nonsymmetric control.
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 2dfda1456501f3d027a4e1cfcfc42a93a64b9e91
  require_origin_equal: true
  release_request_sha256: 2dd89cad6d4da6da4cbeccf7619a3e49cdd2dc52f402f79070274cd0d875540a
  candidate_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
  candidate_bytes: 1782
  candidate_lines: 49
  candidate_body_lines_14_22_sha256: a60d4159fd0907203f70a742a82d532914e8b4b33181248e5043f08e2f53bc07
  preserve_staged_patch_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean

EXACT_MATERIALIZATION:
  source_attachment: GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_CANDIDATE_2026-08-09.txt
  method: BYTE_FOR_BYTE_COPY
  expected_sha256: ca3281f52f6752f537f97910104fe9e26bf4f2a2f2046d1f2bcaf1e84f67ac34
  expected_bytes: 1782
  expected_lines: 49
  any_byte_change: STOP_AND_RETURN_NEW_RELEASE_PACKET

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourcePrimeModePairing
  theorems:
    - sourcePrimeModePairing_eq_ccmPrimeEntryN1
  total: 2

PRIVATE_SURFACE_EXACT:
  definitions: 0
  theorems: 0
  total: 0

MANDATORY_SEMANTICS:
  - positive_side_W_p_sharp_object
  - no_internal_full_ledger_minus
  - exact_Finset_Icc_2_i_m_support
  - exact_inclusive_upper_endpoint
  - exact_vonMangoldt_prime_power_policy
  - exact_inverse_sqrt_k_weight
  - no_outer_prime_factor_two
  - exact_correlation_factor_two
  - exact_Real_log_k_coordinate
  - exact_conjugate_first_mode
  - exact_linear_second_mode
  - direct_source_mode_cosine_parent_consumed
  - no_ccmPrimeEntryN1_in_public_definition

PLANT_CLOSEOUT:
  child_local_judgments_required: 12
  P_PRIME_2_complete_ledger_sign:
    status: DEFERRED_OUTSIDE_CHILD
    may_not_be_claimed_fired: true
  target_symmetry_as_slot_evidence: forbidden

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_staged_patch_sha256_unchanged
  - verify_exact_production_sha256_bytes_lines
  - direct_lake_env_lean
  - target_lake_build
  - full_lake_build
  - scripts_q3_check
  - repository_standard_unit_and_orchestration_tests
  - routeb_status_check
  - exact_one_import_audit
  - exact_public_surface_1_definition_1_theorem
  - exact_private_surface_zero
  - forbidden_token_and_taint_scan
  - exact_definition_body_fingerprint
  - exact_parent_theorem_call_fingerprint
  - run_all_twelve_child_local_plant_and_control_judges
  - remove_all_mutation_artifacts
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - proof_db_import_two_public_declarations
  - proof_db_repeat_import_idempotence
  - strict_Spine
  - three_SQLite_integrity_checks
  - git_diff_check
  - exact_git_status_report
  - update_route_state_only_after_every_gate_passes
  - commit_and_push_only_this_owned_child_and_required_closeout_state_artifacts

STOP:
  GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_EQ_CCM_PRIME_ENTRY_N1_MISSING

SUCCESS:
  GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_EQ_CCM_PRIME_ENTRY_N1_PROVED

NO_NEXT_CHILD:
  selected: false
  authorized: false

NOT_AUTHORIZED:
  - change_any_candidate_byte
  - implement_finite_prime_form_lift
  - define_complete_source_Weil_form
  - hide_prime_minus_inside_sourcePrimeModePairing
  - use_prime_only_support
  - replace_i_m_cutoff_by_i_N
  - alter_factor_two
  - alter_Real_log_k_coordinate
  - use_target_symmetry_as_slot_evidence
  - add_matrix_or_operator_wrapper
  - define_associated_operator_graph
  - infer_form_or_operator_domain_membership
  - edit_D0PstarCCMCompressedWeilAction
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
  open_fresh_chat: false

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
