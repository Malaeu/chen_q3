# STATUS: OPEN — B3.0G SOURCE W02 MODE-PAIRING PRODUCTION RELEASED WITH EXPLICIT DEPENDENCY-CLASSIFICATION REPAIR

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  RELEASE_PACKAGE_COMMIT_OBSERVED:
    commit: 9d6e3d00e0f3d26744a2e4343bd5d5479e170e36
    role: B3_0G_PREFLIGHT_RETURN_PACKAGE
    status: PASS

  MATHEMATICAL_SOURCE_PIN:
    commit: 1c5b01979e047413e895bffa27631146fd57d956
    status: PASS

  REQUEST_ATTACHMENT:
    sha256: ed423bcd1d364bcf71ab35139d01002fafcb69f261f1bb89a3349c69a9435f50
    bytes: 12226
    lines: 413
    status: PASS

  RETURN_ATTACHMENT:
    sha256: e61da83824c5f423f607b0f24bace9430028b6f638964de9fddc35055493d2dd
    bytes: 7136
    lines: 237
    status: PASS

  HARNESS_ATTACHMENT:
    path: Goal057B3_0G_A_Scratch.lean
    sha256: 85c9bac6ffd28bfa6bcba69e39b8f9f20f699284931dffcc4ff192d4ca32d9f5
    bytes: 47818
    lines: 1157
    status: PASS

  TARGET_FILE_AT_PACKAGE_PIN:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean
    present: false
    status: CLEAN_CREATE_ONLY_TRANSACTION

HARNESS_STATIC_AUDIT:
  explicit_imports: 1
  public_definitions: 1
  public_theorems: 1
  private_definitions: 2
  private_theorems: 10
  total_named_declarations: 14
  harness_only_examples: 1
  print_axioms_commands: 1
  forbidden_tokens: 0
  public_surface_match: PASS
  private_surface_match: PASS

REPORTED_DIRECT_LEAN:
  exit_status: 0
  stdout_sha256: 2fd4cdbf148e0fe89287d86021932514d301eac2981824049e51ecb0bcf93bcd
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
  source_object_repaired: false
  import_surface_repaired: false
  public_surface_repaired: false
  private_surface_repaired: false
  plant_classification_repaired: true
  proof_dependency_description_repaired: true
  first_mathematical_defect: NONE
  first_Lean_shape_defect: NONE

PROOF_DEPENDENCY_CLASSIFICATION:
  public_crosswalk:
    route: DIRECT_EXACT_ONE_SIDED_INTEGRAL_EVALUATION
    consumes_private_E3_witness_directly: false
    consumes_private_rank_two_witness_directly: false

  source_parent_witness:
    theorem: sourceW02ModePairing_eq_sourceModeCosineIntegral
    consumes:
      - two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    classification: PRIVATE_LOAD_BEARING_SOURCE_IDENTITY_WITNESS

  rank_two_witness:
    theorem: sourceW02ModePairing_eq_rankTwoLogEndpointMoments
    consumes_public_crosswalk: true
    classification: PRIVATE_STRUCTURAL_COMMUTING_WITNESS
    independent_proof_of_public_crosswalk: false

  ruling: ACCEPTED
  closeout_may_not_claim_rank_two_or_E3_is_a_direct_public_theorem_dependency: true

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions:
    - sourceW02ModePairing
  theorems:
    - sourceW02ModePairing_eq_ccmW02Entry
  total_public_declarations: 2

PRIVATE_SURFACE:
  definitions: 2
  theorems: 10
  total_private_declarations: 12
  additional_private_declarations: forbidden
  public_promotion: forbidden

MATERIALIZATION:
  exact_harness_copy: required
  remove:
    - one_final_harness_example
    - one_final_print_axioms_command
  retain:
    - exact_import
    - exact_linter_option
    - exact_opens
    - exact_namespace
    - exact_public_definition
    - exact_public_theorem
    - both_private_endpoint_moment_definitions
    - all_ten_private_theorems
    - namespace_close
  all_other_semantic_changes: forbidden

PLANTS:
  accepted_compile_failure:
    - P057_G_2_FULL_VS_SHARP
    - P057_G_3_ENDPOINT_PLUS_WEIGHT
    - P057_G_4_ENDPOINT_MINUS_WEIGHT
    - P057_G_5_LOG_LENGTH
    - P057_G_6_RANK_TWO
    - P057_G_7_SESQUILINEAR_SLOT
    - P057_G_8_COMPLEX_COERCION
    - P057_G_9_ORDER_DETECTOR

  repaired_to_compile_plus_static_fingerprint:
    - P057_G_1_FORMULA_ALIAS

  accepted_static_or_semantic_gate:
    - P057_G_10_SOURCE_PARENT
    - P057_G_11_COMPONENT_BOUNDARY
    - P057_G_12_DEPENDENCY

  total_required_before_closeout: 12

STOP_CODE:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_MISSING

SUCCESS_CODE:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E: CLOSED
  B3_0F: CLOSED
  B3_0G: CLOSED
  B3_0H: OPEN
  B3_0: OPEN
  PRIME_SOURCE_PAIRING: OPEN
  COMPLETE_SOURCE_WEIL_FORM: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT

NEXT_DISCRIMINATOR:
  B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_PRODUCTION_LEAN
PROGRESS_CLASS: PROOF_PROGRESS
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

The authoritative request and harness match their submitted SHA-256 values, byte counts, and line counts. The attached return packet independently hashes to `e61da838…3d2dd`. Its declaration counts, one-import surface, forbidden-token scan, plant ledger, and reported axiom output agree with the actual attached Lean bytes.  `[ABSTRACT][LEAN]`

The return is also published in the repository at commit `9d6e3d00e0f3d26744a2e4343bd5d5479e170e36`; it retains `1c5b01979e047413e895bffa27631146fd57d956` as the mathematical source pin.  `[ABSTRACT][PAPER]`

At both the mathematical pin and the return-package commit, the intended production file is absent. The transaction therefore creates one new file rather than overwriting or widening an existing B3.0 object.

The physical route state still records B3.0F as closed, B3.0G as the open source-audit obligation, Goal 057 as active, and the coarse ledger as `0 closed / 10 remaining`.  `[ABSTRACT][PAPER]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING}
}
]

Production materialization of exactly one B3.0G child is authorized.

The harness proves an actual analytic identity. It does not define the desired source object by the closed answer, assume the crosswalk as a premise, use a sampled equality, project to a real part, or import a generated certificate backend.

## 3. The source object is not a formula alias

The public definition is exactly

```lean
noncomputable def sourceW02ModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) *
      ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)
```

`[ABSTRACT][LEAN]`

This is not definitionally `ccmW02Entry`.

Production `ccmQKernel` is the literal (x)-dependent mode-correlation profile from source equations (2.9)–(2.10). Production `ccmW02Entry` is a different object: the closed scalar formula from source equation (4.2).  `[ABSTRACT][LEAN]`

The equality between them remains a substantive integral theorem:

```lean
theorem sourceW02ModePairing_eq_ccmW02Entry
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)
```

The direct alias

```lean
sourceW02ModePairing i n r :=
  (ccmW02Entry (L_m i) n r : ℂ)
```

remains killed under **C10** as:

```text
SURROGATE_BY_FORMULA_NOT_SOURCE_CONSTRUCTION
```

## 4. The one-sided normalization is exact

The definition contains the exact one-sided weight

[
e^{x/2}+e^{-x/2}
]

on the exact log interval

[
0\le x\le L_m(i).
]

There is no extra factor (2). The full-versus-sharp mutation was correctly tested: doubling the outer source integral breaks the exact contract. The source audit identifies this as the (W^#_{0,2}) object used in the finite mode matrix, not a second copy of the full two-sided functional.  `[ABSTRACT][PAPER]`

## 5. Source-parent provenance

The harness proves the exact private identity

```lean
private theorem sourceW02ModePairing_eq_sourceModeCosineIntegral
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      ∫ x in Set.Icc 0 (L_m i),
        (2 * ∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (Real.cos (2 * Real.pi * t * x) : ℂ) *
            𝓕 (logWindowZeroExtendedMode i r) t) *
          ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)
```

and consumes

```lean
two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
```

at the exact `Icc` source domain. `[ABSTRACT][LEAN]`

The E3 parent fixes:

* conjugation on the first Fourier mode;
* linearity in the second mode;
* the external factor (2);
* the cycles-per-unit cosine convention;
* the literal `ccmQKernel` on (x\le L_m(i));
* zero beyond the source window.  `[ABSTRACT][LEAN]`

This private theorem is a load-bearing **file-level source identity witness**. It is not a direct proof dependency of the public closed-form theorem. Production closeout must state that distinction exactly.

## 6. Rank-two contract

The harness defines the exact two log-coordinate endpoint moments:

```lean
sourceW02LogEndpointPlus
sourceW02LogEndpointMinus
```

and proves

```lean
private theorem sourceW02ModePairing_eq_rankTwoLogEndpointMoments
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      conj (sourceW02LogEndpointMinus i n) *
          sourceW02LogEndpointPlus i r +
        conj (sourceW02LogEndpointPlus i n) *
          sourceW02LogEndpointMinus i r
```

`[ABSTRACT][LEAN]`

This preserves the source’s ordered sesquilinear structure:

[
\overline{M_n^-}M_r^+
+
\overline{M_n^+}M_r^-.
]

The contribution is therefore genuinely rank at most two before the final real-symmetric closed formula forgets ordered-slot information.

### Dependency-description repair

The rank-two theorem is proved **after** the public crosswalk and rewrites through it. It is therefore a private structural commuting witness, not an independent proof route to the public crosswalk.

That is acceptable because the public object is already the exact one-sided source integral and its equality to `ccmW02Entry` is proved by exact diagonal/off-diagonal integration. Forcing a second, longer proof of the same public equality through endpoint moments would add proof surface without changing the represented object.

What is forbidden is claiming in the closeout that the public theorem was derived from the rank-two theorem. It was not.

## 7. Exact analytic proof split

The public theorem handles both source branches.

### Off diagonal

For (n\ne r), the harness integrates the exact sine-difference kernel, evaluates the two weighted sine integrals, and proves

[
\frac{
\frac{n}{L^2+16\pi^2n^2}
------------------------

\frac{r}{L^2+16\pi^2r^2}
}{
n-r
}
=

\frac{L^2-16\pi^2rn}
{(L^2+16\pi^2r^2)(L^2+16\pi^2n^2)}.
]

This produces the exact positive `ccmW02Entry` formula with no transpose or sign repair. `[ABSTRACT][LEAN]`

### Diagonal

For (n=r), the harness retains the literal triangular-cosine branch

[
2\frac{L-x}{L}\cos!\left(\frac{2\pi nx}{L}\right)
]

and evaluates the four complex exponential primitives. The integer-periodic phases at (x=L) reduce exactly, and the final algebra gives the same source formula at `(n,n)`. `[ABSTRACT][LEAN]`

The theorem is generic in `PairIndex i` and all integer modes. It is not restricted to the literal (N=1) pilot matrix.

## 8. Plant ruling

All twelve submitted plant classes are retained, with one classification repair.

### `P057_G_1_FORMULA_ALIAS`

The observed Lean failure is useful but is not, by itself, a complete C10 detector: a coherently rewritten alias implementation could repair its proof script.

Production must therefore add a static definition-body fingerprint requiring that `sourceW02ModePairing` contains exactly:

```text
integral over Icc 0 (L_m i)
ccmQKernel (L_m i) n r x
exp(x/2) + exp(-x/2)
```

and does not contain `ccmW02Entry`.

Required stop:

```text
SURROGATE_BY_FORMULA_NOT_SOURCE_CONSTRUCTION
```

### `P057_G_2`–`P057_G_8`

These are accepted as exact compile-failure mutations of:

* sharp normalization;
* both endpoint weights;
* log length;
* rank two;
* coefficient conjugation;
* complex codomain.

### `P057_G_9_ORDER_DETECTOR`

The nonsymmetric endpoint-moment control is accepted as the proper **C04** detector.

A global `n/r` swap in `ccmW02Entry` remains forbidden as a plant because the final closed formula is symmetric and cannot observe the ordered source slots.

### `P057_G_10`–`P057_G_12`

These are correctly classified as static or semantic gates:

```text
SOURCE_W02_SOURCE_MODE_PARENT_NOT_CONSUMED
SOURCE_W02_COMPONENT_ONLY_BOUNDARY_VIOLATED
ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
```

A Lean exit status of zero does not invalidate a static import, provenance, or scope gate.

## 9. Exact production contract

Create only:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceW02ModePairing.lean
```

Exact sole import:

```lean
import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
```

Exact public surface:

```yaml
definitions:
  - sourceW02ModePairing
theorems:
  - sourceW02ModePairing_eq_ccmW02Entry
total: 2
```

Exact private surface:

```yaml
definitions: 2
theorems: 10
total: 12
```

Materialization must equal the authoritative harness except for deletion of:

1. the final nonsymmetric `example`;
2. the final `#print axioms` command.

No helper may be added, promoted, renamed, or weakened.

## 10. Validation gates

Production success requires:

```bash
test "$(git rev-parse HEAD)" = \
  "9d6e3d00e0f3d26744a2e4343bd5d5479e170e36"

test "$(git rev-parse origin/rh_clean)" = \
  "9d6e3d00e0f3d26744a2e4343bd5d5479e170e36"

sha256sum q3.lean.aristotle/Goal057B3_0G_A_Scratch.lean
# require:
# 85c9bac6ffd28bfa6bcba69e39b8f9f20f699284931dffcc4ff192d4ca32d9f5

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourceW02ModePairing

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check
```

Additional mandatory gates:

```text
materialization:
  exact harness copied;
  exactly one example removed;
  exactly one #print command removed;
  every other semantic deviation is a stop;

imports:
  exactly one direct import;
  no generated PSD, Step33, hbox, payload or direct Aristotle-output import;

surface:
  public definitions = 1;
  public theorems = 1;
  private definitions = 2;
  private theorems = 10;
  expected named proof-DB declarations = 14;

source identity:
  sourceW02ModePairing exact-body fingerprint PASS;
  sourceW02ModePairing_eq_sourceModeCosineIntegral present;
  exact E3 theorem call present;
  rank-two theorem present;
  rank-two theorem classified as a structural witness;

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
  print axioms for both public declarations;
  public theorem must report exactly:
    [propext, Classical.choice, Quot.sound];
  public definition may use no axiom outside that same standard triple;

plants:
  rerun all twelve;
  classify P057_G_10, P057_G_11 and P057_G_12 as static/semantic gates;
  run P057_G_9 only in a temporary nonsymmetric harness;
  add the exact definition-body check to P057_G_1;
  remove every mutation artifact;

operational:
  preserve the unrelated staged patch with recorded SHA-256
    291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b;
  proof DB import and repeat-import idempotence PASS;
  repository-standard orchestrator tests PASS;
  strict Spine PASS;
  three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency and numeric-check views refreshed;
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after every proof and semantic gate passes.
```

## 11. Exact boundary after success

B3.0G success proves:

[
\boxed{
W^#_{0,2}(V_n,V_r)
==================

\operatorname{ccmW02Entry}(L_m(i),n,r)
}
]

for every production source window and every ordered integer mode pair. `[ABSTRACT][LEAN]`

It closes:

```text
source one-sided W02 mode-pairing
→ literal CCM W02 entry.
```

It does **not** prove:

* the finite W02 coefficient-form lift;
* the source prime pairing;
* the complete source Weil form;
* positivity of W02 or of the complete form;
* a rank-two operator realization;
* an associated operator graph;
* form-domain or operator-domain membership;
* compression;
* the actual continuum numerator;
* H4a1b;
* a coarse Goal-057 checkpoint.

Therefore:

```text
B3.0G:
  CLOSED after production validation.

B3.0:
  OPEN.

Goal-057 ledger:
  0 closed / 10 remaining.
```

## 12. Next smallest gap

The next atom is:

```text
GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
```

The next discriminator is:

```text
B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT
```

Its intended theorem must lift the generic entrywise B3.0G result to the exact finite carrier:

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
          d k
```

Only parenthesization adjustments are allowed.

B3.0H is named only and is not authorized by this verdict.

## 13. Strongest attack

> Candidate A still starts from a function named `ccmQKernel`. Is this merely laundering one CCM formula through an integral and calling it a source object?

No.

The input and output are different mathematical categories:

```text
ccmQKernel:
  x-dependent source correlation profile q(U_n,U_r)(x);

ccmW02Entry:
  scalar result of applying the one-sided endpoint functional.
```

The E3 theorem independently constructs `ccmQKernel` from the conjugate-first source Fourier modes. The new public theorem then performs the source one-sided integral exactly. The rank-two endpoint theorem verifies the source’s structural statement. A formula alias, missing source parent, lost endpoint weight, rank-one collapse, or generated dependency is separately rejected.

The one necessary correction is descriptive: the public theorem is proved by direct integral evaluation, while E3 and rank two are private semantic witnesses. Calling either one a direct dependency of the public theorem would be false and must fail closeout.

## 14. Meta closeout

**What became smaller?**

The W02 component is no longer a missing source object. After production validation, only its finite coefficient-form packaging remains before moving to the prime component.

**What was killed?**

* direct aliasing to `ccmW02Entry`;
* full-versus-sharp factor ambiguity;
* missing endpoint weights;
* half-length normalization;
* rank-one replacement;
* moved conjugation;
* real-part projection;
* symmetry-blind order testing;
* source-parent erasure;
* full-form scope smuggling;
* generated-backend injection.

**What must not be tried again?**

Do not redefine the source W02 object by the desired closed formula. Do not treat final scalar symmetry as ordered-slot evidence. Do not claim the private rank-two theorem was the proof parent of the public crosswalk.

**Current smallest named gap**

```text
GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
```

**Next cheapest decisive test**

```text
B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT
```

**Prediction fate**

```text
Candidate-A prediction:
  the one-sided q-kernel integral closes from current Mathlib and Route-B APIs.

Fate:
  CONFIRMED by the exact byte-pinned no-sorry harness.

C10 prediction:
  a direct ccmW02Entry alias is not an acceptable source construction.

Fate:
  CONFIRMED; retained as an exact-definition static firewall.

Rank-two prediction:
  the source contribution retains conjugate-first rank-two endpoint structure.

Fate:
  CONFIRMED as a private structural witness.
  It is not an independent proof of the public crosswalk.
```

```yaml
iteration:
  target: GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
  status: PROGRESS
  failed_strategy: direct_alias_or_formula_symmetry_as_source_provenance
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
  invariant_learned: one_sided_normalization_source_mode_parent_endpoint_rank_two_order_and_complex_coercion_are_independent_contracts
  forbidden_future_move: misstate_private_source_or_rank_two_witnesses_as_direct_public_crosswalk_dependencies
  next_decisive_test: B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 9d6e3d00e0f3d26744a2e4343bd5d5479e170e36
  require_origin_equal: true
  mathematical_source_pin: 1c5b01979e047413e895bffa27631146fd57d956
  request_sha256: ed423bcd1d364bcf71ab35139d01002fafcb69f261f1bb89a3349c69a9435f50
  return_sha256: e61da83824c5f423f607b0f24bace9430028b6f638964de9fddc35055493d2dd
  harness_sha256: 85c9bac6ffd28bfa6bcba69e39b8f9f20f699284931dffcc4ff192d4ca32d9f5
  harness_bytes: 47818
  harness_lines: 1157

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness
  - retain exact import, option, opens, namespace and all fourteen named declarations
  - remove the final nonsymmetric example
  - remove the final print-axioms command
  - add no declaration
  - rename no declaration
  - change no theorem statement or proof
  - record every other deviation as a stop

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceW02ModePairing
  theorems:
    - sourceW02ModePairing_eq_ccmW02Entry
  total_public_declarations: 2

PRIVATE_SURFACE_EXACT:
  definitions: 2
  theorems: 10
  total_private_declarations: 12

MANDATORY_SEMANTICS:
  - sourceW02ModePairing_is_literal_one_sided_Icc_integral
  - no_direct_alias_to_ccmW02Entry
  - exact_weight_exp_x_over_two_plus_exp_minus_x_over_two
  - no_outer_factor_two
  - exact_log_length_L_m
  - exact_ccmQKernel_mode_order_n_r
  - exact_complex_codomain
  - exact_positive_final_ccmW02Entry_sign
  - E3_source_mode_cosine_witness_retained
  - conjugate_first_rank_two_endpoint_witness_retained
  - public_crosswalk_classified_as_direct_integral_evaluation
  - private_witnesses_not_misreported_as_direct_public_dependencies
  - no_prime_or_complete_form_claim

MANDATORY_PLANTS:
  - id: P057_G_1_FORMULA_ALIAS
    lean_mutation: retain
    additional_gate: EXACT_PUBLIC_DEFINITION_BODY_FINGERPRINT
    required_stop: SURROGATE_BY_FORMULA_NOT_SOURCE_CONSTRUCTION
    card: C10

  - id: P057_G_2_FULL_VS_SHARP
    required_stop: SOURCE_W02_FULL_VS_SHARP_FACTOR_MISMATCH

  - id: P057_G_3_ENDPOINT_PLUS_WEIGHT
    required_stop: SOURCE_W02_ENDPOINT_WEIGHT_MISSING

  - id: P057_G_4_ENDPOINT_MINUS_WEIGHT
    required_stop: SOURCE_W02_ENDPOINT_WEIGHT_MISSING

  - id: P057_G_5_LOG_LENGTH
    required_stop: SOURCE_W02_LOG_LENGTH_NORMALIZATION_MISMATCH

  - id: P057_G_6_RANK_TWO
    required_stop: SOURCE_W02_RANK_TWO_STRUCTURE_LOST

  - id: P057_G_7_SESQUILINEAR_SLOT
    required_stop: SOURCE_W02_SESQUILINEAR_SLOT_MISMATCH

  - id: P057_G_8_COMPLEX_COERCION
    required_stop: SOURCE_W02_COMPLEX_COERCION_MISMATCH

  - id: P057_G_9_ORDER_DETECTOR
    host: TEMPORARY_NONSYMMETRIC_ENDPOINT_HARNESS
    required_stop: SOURCE_W02_ORDER_DETECTOR_MISSING
    card: C04

  - id: P057_G_10_SOURCE_PARENT
    expected_Lean_behavior: MAY_COMPILE
    required_static_stop: SOURCE_W02_SOURCE_MODE_PARENT_NOT_CONSUMED

  - id: P057_G_11_COMPONENT_BOUNDARY
    expected_Lean_behavior: MAY_COMPILE
    required_semantic_stop: SOURCE_W02_COMPONENT_ONLY_BOUNDARY_VIOLATED

  - id: P057_G_12_DEPENDENCY
    expected_Lean_behavior: MAY_COMPILE
    required_static_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - verify authoritative harness SHA-256
  - verify unrelated staged-patch SHA-256 remains unchanged
  - direct lake env lean on production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceW02ModePairing
  - full lake build
  - scripts/q3_check.sh on production file
  - routeb_status.py --check before and after state update
  - exact one-import audit
  - exact public surface 1_definition_1_theorem
  - exact private surface 2_definitions_10_theorems
  - exact fourteen-declaration proof-DB audit
  - forbidden-token and taint scan
  - exact source-definition body fingerprint
  - exact E3 theorem-call fingerprint
  - exact rank-two theorem fingerprint
  - rerun all twelve plants
  - remove every mutation artifact
  - print axioms for both public declarations
  - require no axiom outside [propext, Classical.choice, Quot.sound]
  - public theorem must report exactly the standard triple
  - proof DB repeat-import idempotence
  - repository-standard orchestrator tests
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - git diff --check
  - exact git status --short report
  - update route state only after every proof and semantic gate passes
  - commit only this one child and its required closeout/state artifacts

CLOSEOUT_MUST_STATE:
  - SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_PROVED
  - EXACT_ONE_SIDED_W02_SHARP_NORMALIZATION_RETAINED
  - EXACT_ENDPOINT_PLUS_AND_MINUS_WEIGHTS_RETAINED
  - EXACT_LOG_LENGTH_NORMALIZATION_RETAINED
  - EXACT_COMPLEX_CROSSWALK_RETAINED
  - EXACT_E3_SOURCE_MODE_PARENT_WITNESS_RETAINED
  - EXACT_CONJUGATE_FIRST_RANK_TWO_WITNESS_RETAINED
  - PUBLIC_CROSSWALK_PROVED_BY_DIRECT_INTEGRAL_EVALUATION
  - E3_AND_RANK_TWO_WITNESSES_ARE_NOT_DIRECT_PUBLIC_THEOREM_DEPENDENCIES
  - FINAL_CLOSED_FORM_SYMMETRY_NOT_USED_AS_ORDER_EVIDENCE
  - B3_0G_CLOSED
  - B3_0_OPEN
  - NO_FINITE_W02_FORM_LIFT
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
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_MISSING

SUCCESS:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0H_inside_this_transaction
  - promote_private_endpoint_moments_or_rank_two_theorem
  - define_sourceW02ModePairing_as_ccmW02Entry
  - claim_the_public_theorem_directly_consumes_E3_or_rank_two
  - use_ccmW02Entry_symmetry_as_ordered_slot_evidence
  - define_prime_source_pairing
  - define_complete_source_Weil_form
  - add_matrix_or_operator_wrapper
  - infer_positivity
  - define_source_associated_operator
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
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
