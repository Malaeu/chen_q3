# STATUS: OPEN — B3.0H EXACT FINITE W02 FORM LIFT RELEASED; PLANT OBSERVABILITY REPAIRED

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  HEAD:
    expected: 38f1172dfc6deea6ccd669dea15ce99a381798dc
    observed_origin_rh_clean: 38f1172dfc6deea6ccd669dea15ce99a381798dc
    status: PASS
    commit_message: "[MacOS][rh_clean][RouteB] Close Goal 057 B3.0G source W02 pairing"

  CONTROLLING_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0H_FINITE_W02_FORM_MATRIX_LIFT_RELEASE_2026-08-08.txt
    expected_sha256: 7d98bf32ca81f87e6a21545d583451b66fb258c720bf7cdaca1c3c058cc15c61
    observed_sha256: 7d98bf32ca81f87e6a21545d583451b66fb258c720bf7cdaca1c3c058cc15c61
    expected_bytes: 6915
    observed_bytes: 6915
    expected_lines: 231
    observed_lines: 231
    read_byte_for_byte: true
    status: PASS

  AUTHORITATIVE_HARNESS:
    path: Goal057B3_0H_Scratch.lean
    expected_sha256: aaaa51a5da430bb19c4645b34939d5d53fbb02bbc199bf8b43b0579bdb0307f8
    observed_sha256: aaaa51a5da430bb19c4645b34939d5d53fbb02bbc199bf8b43b0579bdb0307f8
    expected_bytes: 1023
    observed_bytes: 1023
    expected_lines: 35
    observed_lines: 35
    read_byte_for_byte: true
    status: PASS

  PARENT_1:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean
    expected_sha256: 61f5cce15c84db747edc7375d02aaf63d46bce0956d0e2ad156de00feeb01d3c
    observed_sha256: 61f5cce15c84db747edc7375d02aaf63d46bce0956d0e2ad156de00feeb01d3c
    bytes: 47444
    lines: 1150
    status: PASS

  PARENT_2:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean
    expected_sha256: 282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89
    observed_sha256: 282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89
    bytes: 9582
    lines: 283
    status: PASS

  TARGET_AT_PIN:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean
    present: false
    transaction_shape: CREATE_ONLY

PREFLIGHT:
  reported_direct_lean_exit: 0
  reported_axioms:
    - propext
    - Classical.choice
    - Quot.sound
  judge_reran_lean: false
  static_statement_and_dependency_audit: PASS
  production_rerun_required: true

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  production_release: AUTHORIZED
  authorized_children: 1
  theorem_statement: ACCEPTED_EXACTLY
  owned_file: ACCEPTED
  two_import_surface: REQUIRED
  public_surface: ACCEPTED
  private_surface: ACCEPTED
  semantic_scope: ACCEPTED
  plant_execution_model: REPAIRED
  mathematical_defect: NONE
  typing_defect: NONE
  source_provenance_defect: NONE

PRODUCTION_MATERIALIZATION:
  source: exact_authoritative_harness
  permitted_byte_change:
    - replace_every_occurrence_of_sourceW02FiniteForm_eq_ccmW02MatrixForm_preflight_with_sourceW02FiniteForm_eq_ccmW02MatrixForm
  all_other_byte_changes: forbidden
  expected_sha256: 1239d98489854b7d9dc645824b146b5d2d77b76431e15674cc794e2cafe99973
  expected_bytes: 1003
  expected_lines: 35

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceW02ModePairing
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems:
    - sourceW02FiniteForm_eq_ccmW02MatrixForm
  total_public_declarations: 1

PRIVATE_SURFACE:
  definitions: 0
  theorems: 0
  total_private_declarations: 0

PROVED_DIRECTION_AFTER_SUCCESS:
  source_one_sided_W02_mode_entries
  -> exact_finite_conjugate_first_W02_coefficient_form
  -> literal_CCM_W02_entry_form

PLANT_REPAIR:
  reason: >-
    Several coherent wrong conventions still satisfy the generic entrywise
    equality when both sides are mutated together. Compilation failure alone
    cannot judge carrier, order, slot conjugation, complex codomain, or exact
    double-sum shape.
  required_methods:
    - one_sided_compile_failure_mutations
    - exact_statement_fingerprint
    - exact_parent_dependency_fingerprint
    - independent_nonsymmetric_slot_and_index_controls
    - static_scope_firewall

STOP:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_MISSING

SUCCESS:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

NEXT_SMALLEST_ATOM_AFTER_SUCCESS:
  GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_SIGN_NORMALIZATION_AUDIT

NEXT_ATOM_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed_after_success: 0
  coarse_checkpoints_remaining_after_success: 10

PARENT_STATE_AFTER_SUCCESS:
  B3_0F_FINITE_ARCHIMEDEAN_FORM: CLOSED
  B3_0G_SOURCE_W02_ENTRY_CROSSWALK: CLOSED
  B3_0H_FINITE_W02_FORM_LIFT: CLOSED
  SOURCE_PRIME_PAIRING: OPEN
  COMPLETE_SOURCE_WEIL_FORM: OPEN
  ASSOCIATED_OPERATOR_GRAPH: OPEN
  CONTINUUM_NUMERATOR: OPEN
  H4A1B: OPEN
  B3_0: OPEN

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
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
  sole_owner_gate: PX_RH_CLAIM
```

## 1. Source-lock ruling

The controlling request and authoritative Lean attachment match all submitted byte locks exactly. The request is 6,915 bytes over 231 lines; the harness is 1,023 bytes over 35 lines.  `[FINITE_CELL][LEAN]`

The live `rh_clean` branch resolves to the requested commit `38f1172dfc6deea6ccd669dea15ce99a381798dc`, whose commit message closes production B3.0G.  `[ABSTRACT][PAPER]`

Parent 1 rehashes exactly to `61f5cce1…01d3c`, with 47,444 bytes and 1,150 lines. It contains the independent source-side integral object `sourceW02ModePairing` and the public generic theorem `sourceW02ModePairing_eq_ccmW02Entry`; the source object is not defined by the closed CCM formula.   `[ABSTRACT][LEAN]`

Parent 2 rehashes exactly to `282dc31c…df89`, with 9,582 bytes and 283 lines. It owns the literal finite carrier

```lean
CCMModeFinite N = Fin (2 * N + 1)
```

and the source mode map

```lean
ccmModeFinite N j = (j.1 : ℤ) - N.
```

The second import is therefore load-bearing; the first parent does not own this finite carrier interface.  `[FINITE_CELL][LEAN]`

The physical Goal-057 state names B3.0H as the exact next gap after B3.0G and explicitly requires a same-chat source-locked preflight before production.  `[ABSTRACT][PAPER]`

The Arsenal mandate is accepted. The relevant signatures are C04 for conventions forgotten by a symmetric scalar result, C09 for the precommitted exact public theorem shape, and C10 for requiring direct consumption of the source-side B3.0G theorem rather than a reflexive CCM-only wrapper.   `[ABSTRACT][PAPER]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT}
}
]

Exactly one production child is released.

The candidate is source-backed and minimal. It does not create another W02 object. It transports the already-proved entrywise source equality through the literal finite double sum consumed by subsequent complete-form assembly. The source theorem is used directly:

```lean
simp only [sourceW02ModePairing_eq_ccmW02Entry]
```

There is no new premise, symmetry argument, numerical computation, real projection, source alias, matrix wrapper, or operator wrapper. `[FINITE_CELL][LEAN]`

## 3. Exact production theorem

```lean
theorem sourceW02FiniteForm_eq_ccmW02MatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceW02ModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmW02Entry
            (L_m i)
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k := by
  classical
  simp only [sourceW02ModePairing_eq_ccmW02Entry]
```

`[FINITE_CELL][LEAN]`

The theorem preserves all of the following:

* the exact finite carrier `CCMModeFinite i.N`;
* the literal order (-N,\ldots,N) through `ccmModeFinite i.N`;
* conjugate-linearity in the first coefficient slot;
* linearity in the second slot;
* two independent coefficient rows `c` and `d`;
* the exact positive W02 sign;
* the exact source length `L_m i`;
* the complex-valued form, not its real part;
* the full double sum rather than a diagonal or quadratic specialization.

## 4. Strongest attack and mandatory repair

The strongest objection is real:

> The theorem follows from a generic equality valid for every integer pair. A coherently mutated carrier map, slot convention, or specialization can still compile if both sides are changed together. Does the preflight actually detect the intended finite source form?

Not by compilation alone.

For example, replacing `ccmModeFinite i.N` by the same reordered map on both sides leaves the entrywise rewrite valid. Removing `star` from both sides also leaves the rewrite valid. Projecting both sides through `Complex.re` produces a weaker theorem that may still compile. Replacing the two-vector sesquilinear statement by the quadratic case `c = d` also remains derivable.

This does **not** kill B3.0H. It means the plant suite must judge the exact public contract, not merely whether a mutant proof compiles. This is the C04 distinction between equality after a forgetful operation and equality in the finer ordered sesquilinear category. `[FINITE_CELL][LEAN]`

The repaired judge is:

```text
exact source theorem
+ exact declaration-statement fingerprint
+ independent convention controls
+ dependency fingerprint
+ scope firewall.
```

## 5. Ten mandatory plant rulings

### P057_B3_0H_1 — exact finite carrier

A coherently changed carrier may still compile.

Required gate:

```text
exact theorem-type fingerprint contains:
  c d : CCMModeFinite i.N → ℂ
```

Required stop:

```text
B3_0H_FINITE_CARRIER_MISMATCH
```

Classification: `STATIC_EXACT_TYPE_GATE`. `[FINITE_CELL][LEAN]`

### P057_B3_0H_2 — literal mode map

A simultaneous reorder on both sides is algebraically invisible to the parent equality.

Required gates:

```text
exact theorem-type fingerprint contains both occurrences of:
  ccmModeFinite i.N

independent carrier control consumes:
  ccmModeFinite_two_values
```

Required stop:

```text
B3_0H_MODE_ORDER_MISMATCH
```

Classification: `STATIC_PLUS_INDEPENDENT_CONTROL`; **C04**. `[FINITE_CELL][LEAN]`

### P057_B3_0H_3 — antilinear first slot

Deleting `star` coherently from both sides can still compile.

Required gates:

```text
exact statement fingerprint:
  star (c j)

temporary nonsymmetric complex-scalar control:
  first-slot scaling by a produces star a
```

Required stop:

```text
B3_0H_CONJUGATE_SLOT_MISMATCH
```

Classification: `STATIC_PLUS_INDEPENDENT_SLOT_CONTROL`. `[FINITE_CELL][LEAN]`

### P057_B3_0H_4 — linear second slot

Conjugating the second coefficient coherently can also survive the entrywise rewrite.

Required gates:

```text
exact statement fingerprint:
  * d k

temporary complex-scalar control:
  second-slot scaling by a produces a, not star a
```

Required stop:

```text
B3_0H_SECOND_SLOT_LINEARITY_MISMATCH
```

Classification: `STATIC_PLUS_INDEPENDENT_SLOT_CONTROL`. `[FINITE_CELL][LEAN]`

### P057_B3_0H_5 — W02 sign

Mutate only the CCM target to its negative while retaining the exact source side.

The proof must fail.

Required stop:

```text
B3_0H_W02_WR_SIGN_CROSSCONTAMINATION
```

Classification: `ONE_SIDED_COMPILE_FAILURE`. `[FINITE_CELL][LEAN]`

### P057_B3_0H_6 — exact log length

Mutate only the target length to `L_m i / 2`, `2 * L_m i`, or an independent `L`.

The proof must fail.

Required stop:

```text
B3_0H_LOG_LENGTH_NORMALIZATION_MISMATCH
```

Classification: `ONE_SIDED_COMPILE_FAILURE`. `[FINITE_CELL][LEAN]`

### P057_B3_0H_7 — complex codomain

Taking real parts on both sides would prove a weaker statement and may compile.

Required exact-type gate:

```text
codomain equality is in ℂ;
no Complex.re;
no real coefficient carrier;
no coercion through a real row.
```

Required stop:

```text
B3_0H_COMPLEX_CARRIER_COLLAPSE
```

Classification: `STATIC_EXACT_TYPE_GATE`; **C04**. `[FINITE_CELL][LEAN]`

### P057_B3_0H_8 — parent load-bearing

The production source must contain exactly:

```lean
simp only [sourceW02ModePairing_eq_ccmW02Entry]
```

and must import `D0PstarSourceW02ModePairing`.

A proof reconstructed from `ccmW02Entry` symmetry, reflexivity, or a new equality premise is forbidden.

Required stop:

```text
B3_0H_SOURCE_PARENT_ERASED
```

Classification: `DEPENDENCY_FINGERPRINT`; **C10**. `[FINITE_CELL][LEAN]`

### P057_B3_0H_9 — exact double sum

The actual W02 scalar formula is symmetric, so a global index-swap plant is not a reliable detector.

Required gates:

```text
exact theorem statement contains:
  ∑ j, ∑ k
  two independent rows c and d
  source entry at (ccmModeFinite ... j, ccmModeFinite ... k)
  target entry at the identical ordered pair

temporary nonsymmetric toy matrix control:
  A j k and A k j give distinct values for selected c,d.
```

Required stop:

```text
B3_0H_SESQUILINEAR_FORM_SHAPE_MISMATCH
```

Classification: `STATIC_PLUS_NONSYMMETRIC_CONTROL`; **C04**. `[FINITE_CELL][LEAN]`

### P057_B3_0H_10 — scope firewall

Any added prime term, complete Weil form, matrix/operator object, positivity claim, graph/domain result, compression identity, continuum numerator, H4a1b claim, or checkpoint decrement fails semantically even if Lean compiles.

Required stop:

```text
B3_0H_SCOPE_SMUGGLE
```

Classification: `STATIC_SEMANTIC_GATE`. `[ABSTRACT][PAPER]`

## 6. Exact production boundary

Create only:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean
```

The production file must be the authoritative 35-line harness with the identifier

```text
sourceW02FiniteForm_eq_ccmW02MatrixForm_preflight
```

replaced everywhere by

```text
sourceW02FiniteForm_eq_ccmW02MatrixForm.
```

No import, comment, whitespace, proof, command, or declaration may otherwise change. The expected resulting file is 1,003 bytes over 35 lines with SHA-256:

```text
1239d98489854b7d9dc645824b146b5d2d77b76431e15674cc794e2cafe99973
```

`[FINITE_CELL][LEAN]`

The exact two-import surface is required. The W02 parent supplies the substantive entrywise theorem; `CCMFiniteWeilSourceMatrix` supplies the finite carrier and literal mode map. Removing either import is a stop. `[FINITE_CELL][LEAN]`

## 7. Validation gates

Production success requires all of the following.

### Source and materialization

```text
HEAD = origin/rh_clean
     = 38f1172dfc6deea6ccd669dea15ce99a381798dc

request SHA-256:
  7d98bf32ca81f87e6a21545d583451b66fb258c720bf7cdaca1c3c058cc15c61

harness SHA-256:
  aaaa51a5da430bb19c4645b34939d5d53fbb02bbc199bf8b43b0579bdb0307f8

production SHA-256:
  1239d98489854b7d9dc645824b146b5d2d77b76431e15674cc794e2cafe99973
```

Any mismatch stops before compilation. `[FINITE_CELL][LEAN]`

### Lean and builds

```bash
cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourceW02FiniteFormCCMW02Crosswalk

lake build
```

Required results:

```text
direct Lean: PASS
target build: PASS
full build: PASS
```

`[FINITE_CELL][LEAN]`

### Project checks

```bash
bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

python orchestrator/spine.py --strict
git diff --check
git status --short
```

Also run the repository-standard orchestration suite used by the current Goal-057 closeouts. `[ABSTRACT][LEAN]`

### Surface and taint

Require exactly:

```yaml
imports: 2
public_definitions: 0
public_theorems: 1
private_definitions: 0
private_theorems: 0
proof_db_declarations: 1
proof_db_proven: 1
```

Reject:

```text
sorry
admit
exact?
unsafe
native_decide
declared axiom
opaque
Float
generated PSD/Step33/hbox/payload import
direct Aristotle-output import
```

`[FINITE_CELL][LEAN]`

### Axiom gate

The retained production `#print axioms` command must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No additional project or imported axiom is permitted. `[FINITE_CELL][LEAN]`

### Plant and observability gate

All ten plants must be reported under the repaired classification above. A mutant that compiles but violates an exact static or semantic gate still counts as correctly rejected; it is not an unexpected pass.

After the clean production file is restored:

```text
all mutation artifacts removed;
proof DB import PASS;
repeat import produces no row-count drift;
knowledge.db integrity_check = ok;
aristotle_proofs.db integrity_check = ok;
observability.db integrity_check = ok;
strict Spine PASS;
exact git status reported.
```

`[ABSTRACT][LEAN]`

## 8. Exact closeout language

A successful closeout must state all of the following:

```text
GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

B3_0G_ENTRYWISE_SOURCE_PARENT_CONSUMED
EXACT_CCM_MODE_FINITE_CARRIER_RETAINED
EXACT_MINUS_N_THROUGH_N_MODE_MAP_RETAINED
EXACT_ANTILINEAR_FIRST_SLOT_RETAINED
EXACT_LINEAR_SECOND_SLOT_RETAINED
EXACT_POSITIVE_W02_SIGN_RETAINED
EXACT_LOG_LENGTH_L_M_RETAINED
EXACT_COMPLEX_DOUBLE_SUM_RETAINED

B3_0H_CLOSED
B3_0_OPEN

NO_PRIME_SOURCE_PAIRING
NO_COMPLETE_SOURCE_WEIL_FORM
NO_MATRIX_OR_OPERATOR_WRAPPER
NO_ASSOCIATED_OPERATOR_GRAPH
NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
NO_COMPRESSION_IDENTITY
NO_CONTINUUM_NUMERATOR
H4A1B_OPEN

ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE_ADVANCED_NOT_CLOSED
CHECKPOINTS_CLOSED_0
CHECKPOINTS_REMAINING_10
```

`[FINITE_CELL][LEAN]`

## 9. Next smallest atom

After validated B3.0H production, the next smallest atom is:

```text
GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_SIGN_NORMALIZATION_AUDIT
```

Its job is to determine the independent source-side prime pairing, exact von-Mangoldt support, ordered coefficient convention, and whether the source object denotes positive (W_p) or the negative prime contribution already inserted into the full Weil ledger. That sign must be fixed before any prime equality theorem is stated.

B3.0I is named only. It is not authorized by this verdict. `[ABSTRACT][CONDITIONAL]`

The eventual direct consumer of B3.0F and B3.0H is a complete finite source-Weil-form assembly with the exact ledger

[
W_{0,2}-W_R-\sum_p W_p.
]

That consumer remains unavailable until the prime component is independently constructed and crosswalked. `[FINITE_CELL][CONDITIONAL]`

## 10. Meta closeout

**What became smaller?**

The W02 wall is reduced from a source integral plus a generic entrywise equality to an exact spendable finite sesquilinear form on the literal CCM carrier.

**What was killed?**

Compilation-only plant certification for coherent carrier, order, slot, complex-codomain, and double-sum mutations. Those conventions require exact statement fingerprints and independent controls.

**What must not be tried again?**

Do not use symmetry of `ccmW02Entry` to justify ordered source slots. Do not replace the two-row complex form by a quadratic or real-part specialization. Do not call the W02 lift a complete source Weil form.

**Current smallest named gap**

```text
GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_SIGN_NORMALIZATION_AUDIT
```

**Next cheapest decisive test**

```text
Read-only source/repository audit fixing the prime source object,
von-Mangoldt support, full-form sign, and literal ccmPrimeEntryN1 consumer.
```

**Registered prediction fate**

```text
Prediction:
  B3.0H is a one-theorem exact finite-form lift of the closed B3.0G parent.

Fate:
  CONFIRMED.

Prediction:
  the submitted ten plants are all compile-failure plants.

Fate:
  REFUTED.
  Six require static or independent semantic controls because coherent wrong
  conventions preserve the generic entrywise rewrite.
```

```yaml
iteration:
  target: GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
  status: PROGRESS
  failed_strategy: compilation_alone_as_convention_judge
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_SIGN_NORMALIZATION_AUDIT
  invariant_learned: exact_finite_carrier_mode_order_slot_conjugation_complex_codomain_and_double_sum_shape_must_be_judged_independently_of_symmetric_entrywise_equality
  forbidden_future_move: treat_a_coherently_mutated_bilinear_wrapper_as_semantically_certified_because_simp_still_closes_it
  next_decisive_test: source_locked_prime_pairing_sign_normalization_audit
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 38f1172dfc6deea6ccd669dea15ce99a381798dc
  require_origin_equal: true
  request_sha256: 7d98bf32ca81f87e6a21545d583451b66fb258c720bf7cdaca1c3c058cc15c61
  request_bytes: 6915
  request_lines: 231
  harness_sha256: aaaa51a5da430bb19c4645b34939d5d53fbb02bbc199bf8b43b0579bdb0307f8
  harness_bytes: 1023
  harness_lines: 35
  parent_1_sha256: 61f5cce15c84db747edc7375d02aaf63d46bce0956d0e2ad156de00feeb01d3c
  parent_2_sha256: 282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean

EXACT_MATERIALIZATION:
  source_file: q3.lean.aristotle/Goal057B3_0H_Scratch.lean
  replace_identifier:
    from: sourceW02FiniteForm_eq_ccmW02MatrixForm_preflight
    to: sourceW02FiniteForm_eq_ccmW02MatrixForm
  all_other_byte_changes: forbidden
  expected_production_sha256: 1239d98489854b7d9dc645824b146b5d2d77b76431e15674cc794e2cafe99973
  expected_production_bytes: 1003
  expected_production_lines: 35

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceW02ModePairing
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceW02FiniteForm_eq_ccmW02MatrixForm
  total: 1

PRIVATE_SURFACE_EXACT:
  definitions: 0
  theorems: 0
  total: 0

MANDATORY_SEMANTICS:
  - exact_CCMModeFinite_i_N_carrier
  - exact_ccmModeFinite_i_N_j_and_k_map
  - exact_star_c_j_first_slot
  - exact_linear_d_k_second_slot
  - exact_positive_W02_sign
  - exact_L_m_i_length
  - exact_complex_codomain
  - exact_two_vector_double_sum
  - direct_sourceW02ModePairing_eq_ccmW02Entry_consumption
  - no_prime_or_complete_form_scope

MANDATORY_PLANTS:
  - id: P057_B3_0H_1_EXACT_FINITE_CARRIER
    method: STATIC_EXACT_TYPE_GATE
    required_stop: B3_0H_FINITE_CARRIER_MISMATCH

  - id: P057_B3_0H_2_LITERAL_MODE_MAP
    method: STATIC_PLUS_INDEPENDENT_CONTROL
    control: ccmModeFinite_two_values
    required_stop: B3_0H_MODE_ORDER_MISMATCH
    card: C04

  - id: P057_B3_0H_3_ANTILINEAR_FIRST_SLOT
    method: STATIC_PLUS_COMPLEX_SCALAR_CONTROL
    required_stop: B3_0H_CONJUGATE_SLOT_MISMATCH

  - id: P057_B3_0H_4_LINEAR_SECOND_SLOT
    method: STATIC_PLUS_COMPLEX_SCALAR_CONTROL
    required_stop: B3_0H_SECOND_SLOT_LINEARITY_MISMATCH

  - id: P057_B3_0H_5_W02_SIGN
    method: ONE_SIDED_COMPILE_FAILURE
    required_stop: B3_0H_W02_WR_SIGN_CROSSCONTAMINATION

  - id: P057_B3_0H_6_EXACT_LOG_LENGTH
    method: ONE_SIDED_COMPILE_FAILURE
    required_stop: B3_0H_LOG_LENGTH_NORMALIZATION_MISMATCH

  - id: P057_B3_0H_7_COMPLEX_NOT_REAL_PART
    method: STATIC_EXACT_TYPE_GATE
    required_stop: B3_0H_COMPLEX_CARRIER_COLLAPSE
    card: C04

  - id: P057_B3_0H_8_ENTRYWISE_PARENT_LOAD_BEARING
    method: EXACT_DEPENDENCY_FINGERPRINT
    required_source_line: "simp only [sourceW02ModePairing_eq_ccmW02Entry]"
    required_stop: B3_0H_SOURCE_PARENT_ERASED
    card: C10

  - id: P057_B3_0H_9_EXACT_DOUBLE_SUM
    method: STATIC_PLUS_NONSYMMETRIC_TOY_MATRIX_CONTROL
    required_stop: B3_0H_SESQUILINEAR_FORM_SHAPE_MISMATCH
    card: C04

  - id: P057_B3_0H_10_SCOPE_FIREWALL
    method: STATIC_SEMANTIC_GATE
    required_stop: B3_0H_SCOPE_SMUGGLE

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_request_harness_parent_hashes
  - verify_exact_production_hash_size_and_line_count
  - direct_lake_env_lean
  - target_lake_build
  - full_lake_build
  - scripts_q3_check
  - routeb_status_check
  - exact_two_import_audit
  - exact_public_and_private_surface_audit
  - forbidden_token_and_taint_scan
  - exact_statement_fingerprint
  - exact_parent_dependency_fingerprint
  - run_all_ten_repaired_plants
  - remove_all_mutation_artifacts
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - proof_db_import_1_of_1_proven
  - proof_db_repeat_import_idempotence
  - repository_standard_orchestration_tests
  - strict_Spine
  - three_SQLite_integrity_checks
  - git_diff_check
  - exact_git_status_report
  - update_route_state_last
  - commit_and_push_only_the_closed_B3_0H_packet

STOP:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_MISSING

SUCCESS:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED

NEXT_ATOM_AFTER_SUCCESS:
  GOAL057_B3_0I_SOURCE_PRIME_MODE_PAIRING_SIGN_NORMALIZATION_AUDIT

NEXT_ATOM_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0I
  - define_prime_source_pairing
  - define_complete_source_Weil_form
  - add_matrix_or_operator_wrapper
  - infer_positivity
  - define_associated_operator_graph
  - infer_form_or_operator_domain_membership
  - assert_compression_identity
  - claim_continuum_numerator
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
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
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
