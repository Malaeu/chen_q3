# STATUS: OPEN — B3.0E4C ALL-MODE CCM-WR CASE ASSEMBLY RELEASED AFTER PLANT REPAIR

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  LIVE_HEAD:
    expected: 90fd2a3b6aca65e5dd9638a1ff203b0e8736c524
    observed_origin_rh_clean: 90fd2a3b6aca65e5dd9638a1ff203b0e8736c524
    status: PASS

  PACKAGE_COMMIT:
    commit: 90fd2a3b6aca65e5dd9638a1ff203b0e8736c524
    role: B3_0E4C_PREFLIGHT_ROUTE_RECORD_ONLY
    direct_parent: 311ab67feaf187f6e953f25f2188b3b432c13017
    parent_role: B3_0E4B2_PRODUCTION_CLOSEOUT
    package_changed_only:
      - q3.lean.aristotle/docs/INSIGHTS.md
    mathematical_parent_files_changed: false

  REQUEST_ATTACHMENT:
    path: PROSHKA_REQUEST_GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_NEG_CCM_WR_RELEASE_2026-08-08.md
    expected_sha256: bc4c9546e7b7f573758eb4082d73e0760583572cd2d7094b04481302ff5e1307
    observed_sha256: bc4c9546e7b7f573758eb4082d73e0760583572cd2d7094b04481302ff5e1307
    expected_bytes: 7312
    observed_bytes: 7312
    expected_lines: 230
    observed_lines: 230
    status: PASS

  HARNESS_ATTACHMENT:
    path: Goal057B3_0E4C_Scratch.lean
    expected_sha256: 10c6238544c172d7f9f90851eca28b8dee86271de36bb84eccebb8e8d60dfd66
    observed_sha256: 10c6238544c172d7f9f90851eca28b8dee86271de36bb84eccebb8e8d60dfd66
    expected_bytes: 1278
    observed_bytes: 1278
    expected_lines: 37
    observed_lines: 37
    status: PASS

  HARNESS_STATIC_AUDIT:
    explicit_imports: 2
    public_definitions: 0
    public_theorems: 1
    private_definitions: 0
    private_theorems: 0
    controls_examples: 3
    print_axioms_commands: 1
    sorry: 0
    admit: 0
    exact_question: 0
    unsafe: 0
    axiom_declarations: 0
    opaque: 0
    native_decide: 0
    Float: 0
    generated_backend_tokens: 0
    public_surface_match: PASS

  REPORTED_DIRECT_LEAN:
    result: PASS
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
  release: AUTHORIZED
  theorem_statement_repaired: false
  proof_architecture_repaired: false
  import_surface_repaired: false
  plant_suite_repaired: true
  first_mathematical_defect: NONE
  first_Lean_shape_defect: NONE
  target_file_present_at_pin: false

FIRST_LOAD_BEARING_ATTACK:
  target: P057_E4C_4_MODE_ORDER
  ruling: KILLED_AS_NONDISCRIMINATING
  reason: >-
    ccmWREntry is already proved symmetric in its two mode indices.
    Replacing ccmWREntry L n r by ccmWREntry L r n therefore produces an
    extensionally equivalent conclusion. A proof-script failure under that
    mutation would not be a semantic falsification.
  card: C04
  replacement:
    id: P057_E4C_4_PARENT_PROVENANCE
    required_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchAllModeCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems:
    - sourceArchimedeanModePairing_eq_neg_ccmWREntry
  total_public_declarations: 1

PRIVATE_SURFACE:
  definitions: 0
  theorems: 0
  total: 0

CONTROLS:
  central_diagonal_n0_r0: HARNESS_SMOKE
  forward_offdiagonal_n0_r1: HARNESS_SMOKE
  reverse_offdiagonal_n1_r0: HARNESS_SMOKE
  orientation_evidence: INHERITED_FROM_E3_AND_E4A_NOT_REPROVED_HERE
  production_disposition: OMIT_ALL_THREE

PLANTS:
  retained:
    - P057_E4C_1_FINAL_WR_SIGN
    - P057_E4C_2_DIAGONAL_BRANCH
    - P057_E4C_3_OFFDIAGONAL_BRANCH
    - P057_E4C_5_CASE_DISCRIMINATOR

  killed:
    - id: P057_E4C_4_MODE_ORDER
      reason: SYMMETRIC_TARGET_FORGETS_ORDER

  replacements_and_additions:
    - P057_E4C_4_PARENT_PROVENANCE
    - P057_E4C_6_DEPENDENCY

  total_required_before_closeout: 6

STOP_CODE:
  GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_MISSING

SUCCESS_CODE:
  GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E1: CLOSED
  B3_0E2: CLOSED
  B3_0E3: CLOSED
  B3_0E4A: CLOSED
  B3_0E4B1: CLOSED
  B3_0E4B2: CLOSED
  B3_0E4C: CLOSED
  B3_0E: CLOSED
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT

NEXT_DISCRIMINATOR:
  B3_0F_FINITE_ARCH_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_PRODUCTION_LEAN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 4

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

## 1. Source-lock and parent audit

The two attached files were read in full and independently rehashed. The request is exactly 7,312 bytes over 230 lines with SHA-256 `bc4c9546…1307`; the Lean harness is exactly 1,278 bytes over 37 lines with SHA-256 `10c62385…fd66`. The request’s complete theorem, proposed imports, public surface, plant suite, and immutable boundaries are therefore controlling.  `[ABSTRACT][PAPER]`

Live `origin/rh_clean` is exactly `90fd2a3b6aca65e5dd9638a1ff203b0e8736c524`.  `[ABSTRACT][PAPER]`

The live tip is a documentation-only B3.0E4C preflight record. Its direct parent is `311ab67feaf187f6e953f25f2188b3b432c13017`, and the package commit changes only `q3.lean.aristotle/docs/INSIGHTS.md`; it does not alter either closed mathematical parent.  `[ABSTRACT][PAPER]`

The parent ledger records B3.0E4A, B3.0E4B1, and B3.0E4B2 as closed; it records B3.0E as open solely because the generic all-mode case assembly is absent. It also keeps the source Weil form, associated graph, H4a1b, and all ten coarse checkpoints open.  `[ABSTRACT][LEAN]`

The off-diagonal production parent proves exactly

```lean
sourceArchimedeanModePairing i n r =
  -(ccmWREntry (L_m i) n r : ℂ)
```

under `n ≠ r`.  `[ABSTRACT][LEAN]`

The diagonal production parent proves the same equality at `(n,n)` for every integer mode.  `[ABSTRACT][LEAN]`

The intended production file does not exist at the pin. This is a clean one-file materialization, not an overwrite. `[ABSTRACT][PAPER]`

The Arsenal mandate is accepted. The repository’s byte-exact materialization ledger confirms the mandated card-deck SHA-256 and all twelve cards; the mandate requires C04, C09, and C10 attacks to remain active where their signatures occur.   `[ABSTRACT][PAPER]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY}
}
]

The exact theorem is source-faithful and dependency-minimal at the semantic level. It adds no analytic estimate, integral exchange, normalization, coercion bridge, or source premise. It packages two already-proved exhaustive cases into one total interface. `[ABSTRACT][LEAN]`

The released theorem is:

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
  by_cases h : n = r
  · subst r
    exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag i n
  · exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i h
```

`[ABSTRACT][CONDITIONAL]`

The reported scratch compile and standard axiom triple are accepted as release evidence. This judge did not rerun the project Lean toolchain, so the transaction remains `OPEN` until the production file passes the full validation gate.

## 3. Case-split audit

### 3.1 `n = r` is the exact source discriminator

The two parents partition the complete integer mode-pair domain:

[
(n,r)\in\mathbb Z^2
===================

{n=r};\dot\cup;{n\ne r}.
]

The CCM source definitions themselves use this same diagonal/off-diagonal partition in the literal `ccmQKernel` branch, and the production parent chain has separately discharged both branches.  `[ABSTRACT][LEAN]`

No parity, sign, mode size, or support condition is being substituted for equality of the two mode indices.

### 3.2 `subst r` preserves the ordered slots

In the diagonal branch, the context contains:

```lean
h : n = r
```

After `subst r`, both ordered inputs become `n`. This is substitution into the second slot, not a permutation of the two slots. The first slot remains the source antilinear slot, and the second remains the source linear slot; they simply carry the same mode label on the diagonal. `[ABSTRACT][LEAN]`

The exact source-form lock states that the finite coefficient law is conjugate-linear in the first coefficient and linear in the second.  `[ABSTRACT][PAPER]`

### 3.3 The off-diagonal parent receives exactly its hypothesis

In the second branch, Lean has:

```lean
h : ¬ n = r
```

which is definitionally the required `n ≠ r` argument of:

```lean
sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i h
```

No matrix symmetry, conjugate symmetry, mode reflection, or reversed ordered pair is invoked. `[ABSTRACT][LEAN]`

### 3.4 The negative sign is preserved in both branches

Both production parents conclude the negative `ccmWREntry` equality. The all-mode proof does not move or recompute the sign; each branch returns its parent theorem exactly. `[ABSTRACT][LEAN]`

This agrees with the source sign ledger:

[
\Psi = W_{0,2}-W_{\mathbb R}-\sum_p W_p.
]

The named `sourceArchimedeanModePairing` represents the archimedean contribution entering the full Weil form with the negative `W_{\mathbb R}` orientation.  `[ABSTRACT][PAPER]`

## 4. Import ruling

The production file retains both explicit imports:

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
import Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk
```

`[ABSTRACT][CONDITIONAL]`

The diagonal module already imports the off-diagonal module, so a one-import file would be syntactically sufficient. That does not make the explicit off-diagonal import dishonest. The released theorem directly consumes two independent public parents, and listing both exposes the complete logical parent set without introducing any additional transitive dependency. `[ABSTRACT][LEAN]`

For this transaction, dependency transparency is preferable to hiding one direct logical edge behind transitive availability. No parent refactor or import re-export change is authorized.

## 5. Control audit

The three compiled examples are accepted only as smoke checks:

```text
(0,0): diagonal branch is reachable;
(0,1): off-diagonal branch is reachable;
(1,0): reverse ordered call is type-correct.
```

`[ABSTRACT][LEAN]`

They are not independent evidence for source orientation. In particular, compiling both `(0,1)` and `(1,0)` does not prove that no hidden index reversal occurred. The final CCM-WR kernel is real-symmetric, so both ordered instances can survive a transposition. `[ABSTRACT][LEAN]`

All three examples must be omitted from production.

## 6. Plant audit and repair

### 6.1 Retained plant: final sign

```yaml
id: P057_E4C_1_FINAL_WR_SIGN
mutation: negative_ccm_wr_to_positive_ccm_wr
required_stop: SOURCE_ARCH_ALL_MODE_WR_SIGN_MISMATCH
```

This is a source-statement fingerprint. The assembled theorem must have exactly the same negative sign as both parents. A positive target is not the theorem supplied by either branch. `[ABSTRACT][LEAN]`

### 6.2 Retained plant: diagonal parent

```yaml
id: P057_E4C_2_DIAGONAL_BRANCH
mutation: replace_diagonal_parent_by_offdiagonal_parent
required_stop: SOURCE_ARCH_ALL_MODE_DIAGONAL_BRANCH_MISSING
```

After `subst r`, the off-diagonal parent would require a witness `n ≠ n`. The mutation must fail without manufacturing inconsistency or adding a premise. `[ABSTRACT][LEAN]`

### 6.3 Retained plant: off-diagonal parent

```yaml
id: P057_E4C_3_OFFDIAGONAL_BRANCH
mutation: replace_offdiagonal_parent_by_diagonal_parent
required_stop: SOURCE_ARCH_ALL_MODE_OFFDIAGONAL_BRANCH_MISSING
```

The diagonal parent concludes a theorem at `(n,n)` and does not discharge a target at arbitrary `(n,r)` under `n ≠ r`. The mutation must fail without using symmetry as a replacement theorem. `[ABSTRACT][LEAN]`

### 6.4 Killed plant: RHS mode-order swap

The proposed plant

```yaml
id: P057_E4C_4_MODE_ORDER
mutation: ccm_entry_n_r_to_r_n
```

is rejected as non-discriminating.

Production already proves:

```lean
ccmWREntry L n r = ccmWREntry L r n.
```

`[ABSTRACT][LEAN]`

Consequently, the mutated conclusion

```lean
sourceArchimedeanModePairing i n r =
  -(ccmWREntry (L_m i) r n : ℂ)
```

is extensionally equivalent to the released conclusion. Even if the unchanged proof script failed after this mutation, that failure would measure script orientation rather than mathematical falsity.

This is exactly the C04 failure mode: the final real-symmetric scalar kernel has forgotten the ordered sesquilinear-slot information. **[C04]**

The ordered-slot convention was already tested at the earlier mode-correlation and off-diagonal construction layers, where it remained observable. E4C inherits that result; it cannot re-detect it after symmetry has collapsed the distinction.

### 6.5 Replacement plant: no premise surrogate

```yaml
id: P057_E4C_4_PARENT_PROVENANCE
mutation: >-
  add an all-mode crosswalk hypothesis identical to the desired conclusion
  and prove the theorem from that hypothesis instead of consuming the two
  closed parent theorems
required_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
```

The proof-dependency fingerprint must confirm that the theorem body consumes:

```text
sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
```

and no premise containing the desired all-mode equality. `[ABSTRACT][LEAN]` **[C10]**

### 6.6 Retained plant: exact case discriminator

```yaml
id: P057_E4C_5_CASE_DISCRIMINATOR
mutation: replace_by_cases_n_eq_r_by_by_cases_n_eq_neg_r
required_stop: SOURCE_ARCH_ALL_MODE_CASE_SPLIT_MISMATCH
```

The mutated cases do not match the hypotheses of the two production parents. No parity or reflection theorem may be inserted to disguise this mismatch. `[ABSTRACT][LEAN]`

### 6.7 Added plant: dependency firewall

```yaml
id: P057_E4C_6_DEPENDENCY
mutation: >-
  add a generated PSD, Step33, hbox, numeric-payload, Aristotle-output,
  or premise-provider import
required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
```

The theorem needs exactly the two closed source crosswalk parents. Any generated analytic or numerical backend is unrelated to the two-case proof and must be rejected. `[ABSTRACT][LEAN]`

### Final plant count

```text
Valid retained plants: 4
Killed non-discriminating plant: 1
Replacement plant: 1
Added dependency plant: 1
Required production total: 6
```

The killed mode-order plant must not be reported as fired.

## 7. Exact production boundary

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceArchAllModeCCMWRCrosswalk.lean
```

Exact module content is the byte-pinned harness with only:

* the three final `example` controls removed;
* the final `#print axioms` command removed.

The exact imports, module scopes, namespace, theorem statement, and theorem body remain unchanged. `[ABSTRACT][CONDITIONAL]`

Exact public surface:

```yaml
definitions: 0
theorems:
  - sourceArchimedeanModePairing_eq_neg_ccmWREntry
total: 1
```

Exact private surface:

```yaml
definitions: 0
theorems: 0
total: 0
```

No helper declaration, source object, matrix wrapper, form structure, or coercion theorem may be added.

## 8. Validation gates

Production success requires:

```bash
test "$(git rev-parse HEAD)" = \
  "90fd2a3b6aca65e5dd9638a1ff203b0e8736c524"

test "$(git rev-parse origin/rh_clean)" = \
  "90fd2a3b6aca65e5dd9638a1ff203b0e8736c524"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchAllModeCCMWRCrosswalk.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchAllModeCCMWRCrosswalk.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check
```

`[ABSTRACT][CONDITIONAL]`

Additional gates:

```text
source:
  rehash both attached files before materialization;

files:
  create exactly one production Lean file;
  modify no B3.0 parent;

materialization:
  harness-to-production diff contains exactly:
    - three example deletions;
    - one print-axioms deletion;
  every other deviation is a stop;

imports:
  exactly the two released imports;
  no additional direct import;
  no new generated backend in the transitive closure;

surface:
  public definitions = 0;
  public theorems = 1;
  private definitions = 0;
  private theorems = 0;
  proof-DB declarations expected = 1;

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
      .sourceArchimedeanModePairing_eq_neg_ccmWREntry

  require exactly:
    [propext, Classical.choice, Quot.sound];

plants:
  run all six repaired plants;
  do not count the killed mode-order mutation;
  remove every mutation artifact;

observability:
  proof DB records 1/1 declaration as proved;
  strict Spine PASS;
  all three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after all proof and semantic gates pass.
```

`[ABSTRACT][CONDITIONAL]`

## 9. Exact semantic boundary after success

B3.0E4C success proves, for every production window and every ordered pair of integer modes,

[
\boxed{
\operatorname{sourceArchimedeanModePairing}(i,n,r)
==================================================

-\operatorname{ccmWREntry}(L_m(i),n,r).
}
]

`[ABSTRACT][LEAN]`

This closes the complete **entrywise archimedean/CCM-WR representation crosswalk**. It closes B3.0E after production validation.

It does **not** prove:

* a finite coefficient-sum sesquilinear form theorem;
* the endpoint/pole `W_{0,2}` mode-pairing crosswalk;
* the prime mode-pairing crosswalk;
* the complete source Weil form;
* equality of the full finite source form with `ccmWeilTauN1` or `ccmWeilMatFinite`;
* an associated operator graph;
* form-domain or operator-domain membership;
* selected-trial operator-domain membership;
* finite-to-ambient compression;
* the continuum residual or numerator;
* H4a1b;
* any coarse Goal-057 checkpoint.

`[ABSTRACT][CONDITIONAL]`

Therefore:

```text
B3.0E:
  CLOSED after production validation.

B3.0:
  OPEN.

Goal-057 coarse ledger:
  0 closed / 10 remaining.
```

## 10. Next smallest gap and discriminator

The next atom is **not** the complete source Weil form.

The source form has the exact three-component ledger:

[
\Psi
====

## W_{0,2}

## W_{\mathbb R}

\sum_p W_p,
]

and its finite coefficient law is conjugate-linear in the first coefficient and linear in the second.  `[ABSTRACT][PAPER]`

Before adding the endpoint and prime components, the entrywise E4C theorem must be lifted to the literal finite coefficient carrier. This is the first point after the symmetric entry theorem where ordered sesquilinear slots become observable again.

The exact next gap is:

```text
GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
```

The exact next discriminator is:

```text
B3_0F_FINITE_ARCH_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT
```

Its intended theorem shape is:

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

with only parenthesization adjustments allowed for the pinned Lean parser. `[FINITE_CELL][CONDITIONAL]`

The discriminator must enforce:

```text
carrier:
  CCMModeFinite i.N;

mode order:
  ccmModeFinite i.N j = j-N;

first coefficient:
  conjugated/starred;

second coefficient:
  linear;

entry supplier:
  the production E4C theorem;

forbidden:
  no real-part projection;
  no use of matrix symmetry to swap coefficient slots;
  no W02 or prime claim;
  no complete source-form claim.
```

That discriminator is named but **not authorized** by this verdict.

## 11. Strongest attack

> E4C is a vacuous duplicate API. Any downstream proof could repeat the same four-line `by_cases` argument, so publishing it adds no mathematics.

The attack is correct about novelty: E4C is representation packaging, not a new analytic theorem.

It does not change the release verdict.

The cost is exactly one theorem, zero definitions, zero private support, and no new assumptions. The benefit is that every later finite-form or operator construction receives one canonical all-mode supplier rather than privately repeating a case split and risking branch drift. It also closes the precisely named B3.0E representation wall.

The public theorem is justified only as the direct parent of the finite sesquilinear lift. It must not be advertised as the complete source Weil form or as progress on the operator graph.

## 12. Route map

| Node                         | Effect after production validation           | Status                      |
| ---------------------------- | -------------------------------------------- | --------------------------- |
| B3.0E4A                      | Off-diagonal source archimedean entries      | **CLOSED**                  |
| B3.0E4B2                     | Diagonal source archimedean entries          | **CLOSED**                  |
| B3.0E4C                      | One total theorem for all mode pairs         | **RELEASED**                |
| B3.0E                        | Entrywise archimedean/CCM-WR bridge          | **CLOSES after validation** |
| B3.0F                        | Finite conjugate-first coefficient-form lift | **NEXT, not authorized**    |
| Endpoint/pole source pairing | `W_{0,2}` component                          | **OPEN**                    |
| Prime source pairing         | von-Mangoldt component                       | **OPEN**                    |
| Complete source Weil form    | Three-component assembly                     | **OPEN**                    |
| Associated operator graph    | Domain-safe represented operator             | **OPEN**                    |
| Goal-057 coarse ledger       | `0 closed / 10 remaining`                    | **UNCHANGED**               |

## 13. Meta closeout

**What became smaller?**

The diagonal/off-diagonal branch distinction disappears from downstream consumers. The entire archimedean mode-entry crosswalk becomes one theorem.

**What was killed?**

The proposed RHS mode-order mutation as an adversarial plant. It cannot distinguish a wrong orientation after the target has become real-symmetric. **[C04]**

**What must not be tried again?**

Do not count `(n,r) ↦ (r,n)` on `ccmWREntry` as an orientation falsifier. Do not treat the all-mode entry theorem as the complete source form. Do not jump directly to the associated operator graph.

**Current smallest named gap**

```text
GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
```

**Next cheapest decisive test**

```text
B3_0F_FINITE_ARCH_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT
```

**Prediction fate**

```text
P-E4C-1:
  the exact two-case theorem closes with no helper or new source fact.

Fate:
  CONFIRMED by the byte-pinned compiling harness.

P-E4C-2:
  forward and reverse ordered controls, together with an RHS index-swap plant,
  independently certify mode orientation.

Fate:
  REFUTED.
  The controls are smoke only and ccmWREntry symmetry makes the proposed
  RHS-swap plant semantically inert.
```

```yaml
iteration:
  target: GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  status: PROGRESS
  failed_strategy: use_symmetric_final_entry_as_an_order_orientation_detector
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
  invariant_learned: diagonal_offdiagonal_partition_and_parent_provenance_are_visible_but_mode_order_is_forgotten_by_the_final_symmetric_kernel
  forbidden_future_move: claim_order_validation_from_ccmWREntry_n_r_equals_ccmWREntry_r_n
  next_decisive_test: B3_0F_FINITE_ARCH_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT
  progress_class: REPRESENTATION_PROGRESS
  route_score: 4
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 90fd2a3b6aca65e5dd9638a1ff203b0e8736c524
  require_origin_equal: true
  mathematical_parent: 311ab67feaf187f6e953f25f2188b3b432c13017
  request_sha256: bc4c9546e7b7f573758eb4082d73e0760583572cd2d7094b04481302ff5e1307
  request_bytes: 7312
  request_lines: 230
  harness_sha256: 10c6238544c172d7f9f90851eca28b8dee86271de36bb84eccebb8e8d60dfd66
  harness_bytes: 1278
  harness_lines: 37

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchAllModeCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness
  - retain exact imports, module scopes, namespace, theorem statement and proof
  - omit the three final example controls
  - omit the final print-axioms command
  - add no public declaration
  - add no private declaration
  - record every other deviation as a stop

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanModePairing_eq_neg_ccmWREntry
  total_public_declarations: 1

PUBLIC_THEOREM_EXACT: |
  theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry
      (i : PairIndex) (n r : ℤ) :
      sourceArchimedeanModePairing i n r =
        -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
    by_cases h : n = r
    · subst r
      exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag i n
    · exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i h

PRIVATE_SURFACE_EXACT:
  definitions: 0
  theorems: 0
  total: 0

CONTROLS:
  omit_from_production:
    - central_diagonal_n0_r0
    - forward_offdiagonal_n0_r1
    - reverse_offdiagonal_n1_r0
  closeout_classification: HARNESS_SMOKE_ONLY
  may_not_count_as_mode_order_falsifier: true

MANDATORY_PLANTS:
  - id: P057_E4C_1_FINAL_WR_SIGN
    mutation: negative_ccm_wr_to_positive_ccm_wr
    required_stop: SOURCE_ARCH_ALL_MODE_WR_SIGN_MISMATCH

  - id: P057_E4C_2_DIAGONAL_BRANCH
    mutation: replace_diagonal_parent_by_offdiagonal_parent
    required_stop: SOURCE_ARCH_ALL_MODE_DIAGONAL_BRANCH_MISSING

  - id: P057_E4C_3_OFFDIAGONAL_BRANCH
    mutation: replace_offdiagonal_parent_by_diagonal_parent
    required_stop: SOURCE_ARCH_ALL_MODE_OFFDIAGONAL_BRANCH_MISSING

  - id: P057_E4C_4_PARENT_PROVENANCE
    mutation: replace_both_parent_applications_by_an_all_mode_hypothesis
    required_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
    card: C10

  - id: P057_E4C_5_CASE_DISCRIMINATOR
    mutation: replace_n_eq_r_split_by_n_eq_neg_r
    required_stop: SOURCE_ARCH_ALL_MODE_CASE_SPLIT_MISMATCH

  - id: P057_E4C_6_DEPENDENCY
    mutation: inject_generated_PSD_Step33_hbox_payload_or_direct_Aristotle_import
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

KILLED_PLANT:
  id: P057_E4C_4_MODE_ORDER
  mutation: ccm_entry_n_r_to_r_n
  reason: ccmWREntry_symm_makes_mutation_extensionally_equivalent
  card: C04
  may_not_be_reported_as_fired: true

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - full lake build
  - scripts/q3_check.sh on the production file
  - routeb_status.py --check
  - exact public surface 0_definitions_1_theorem
  - exact private surface 0_definitions_0_theorems
  - forbidden-token scan
  - exact two-import audit
  - no-new-generated-dependency audit
  - harness-to-production diff permits only three examples and one print command deletion
  - run all six repaired plants
  - do not run or count the killed mode-order plant
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

CLOSEOUT_MUST_STATE:
  - SOURCE_ARCH_ALL_MODE_PAIRING_EQ_NEG_CCM_WR_PROVED
  - EXACT_N_EQ_R_CASE_SPLIT_RETAINED
  - EXACT_DIAGONAL_PARENT_CONSUMED
  - EXACT_OFFDIAGONAL_PARENT_CONSUMED
  - EXACT_FINAL_NEGATIVE_CCM_WR_SIGN_RETAINED
  - ORDERED_CONTROLS_SMOKE_ONLY
  - MODE_ORDER_PLANT_KILLED_AS_SYMMETRY_BLIND
  - B3_0E4C_CLOSED
  - B3_0E_CLOSED
  - B3_0_OPEN
  - NO_FINITE_COEFFICIENT_FORM_LIFT
  - NO_W02_SOURCE_PAIRING
  - NO_PRIME_SOURCE_PAIRING
  - NO_COMPLETE_SOURCE_WEIL_FORM
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_MISSING

SUCCESS:
  GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0F_FINITE_ARCH_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0F_inside_this_transaction
  - define_the_complete_source_Weil_form
  - define_the_W02_or_prime_source_pairing
  - use_ccmWREntry_symmetry_as_mode_order_evidence
  - add_any_finite_matrix_or_operator_wrapper
  - modify_any_B3_0_parent_file
  - widen_any_parent_public_surface
  - accept_the_all_mode_crosswalk_as_a_premise
  - define_the_source_associated_operator
  - infer_form_domain_or_operator_domain_membership
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
```
