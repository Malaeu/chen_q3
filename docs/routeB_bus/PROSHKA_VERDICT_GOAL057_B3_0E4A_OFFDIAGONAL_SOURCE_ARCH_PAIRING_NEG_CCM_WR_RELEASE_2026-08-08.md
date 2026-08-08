STATUS: OPEN — B3.0E4A OFF-DIAGONAL NEGATIVE CCM-WR CROSSWALK RELEASED
YAML
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  LIVE_HEAD:
    expected: ce7f7f492cabfa48b5b3628a3842d09508114df8
    observed_origin_rh_clean: ce7f7f492cabfa48b5b3628a3842d09508114df8
    status: PASS

  MATHEMATICAL_PARENT:
    commit: 3df702ead9729e187d3fbdf461452e25bb7c8bae
    role: B3_0E3_PRODUCTION_CLOSEOUT
    relation_to_live_head: DIRECT_PARENT
    live_head_changes_only:
      - q3.lean.aristotle/docs/INSIGHTS.md
    mathematical_parent_files_changed: false

  REQUEST_ATTACHMENT:
    path: PROSHKA_REQUEST_GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_NEG_CCM_WR_RELEASE_2026-08-08.md
    expected_sha256: 3c01e6440d318d87b270f13c8388f6bfe72a16ab1507703af71391d9fe5f6b6a
    observed_sha256: 3c01e6440d318d87b270f13c8388f6bfe72a16ab1507703af71391d9fe5f6b6a
    observed_bytes: 5772
    observed_lines: 177
    observed_git_blob: 6029a9fc7c7a7ad8aa8cf0434717229d8d8dd869
    status: PASS

  HARNESS_ATTACHMENT:
    path: Goal057B3_0E4A_Scratch.lean
    expected_sha256: 4a9910f66a31400d244b240514b69dd8eb3f414401bc3226f503fd95385ce79e
    observed_sha256: 4a9910f66a31400d244b240514b69dd8eb3f414401bc3226f503fd95385ce79e
    observed_bytes: 12483
    observed_lines: 310
    observed_git_blob: 32c77361f47224fb8be928130fad28b119a6f96d
    status: PASS

  HARNESS_STATIC_AUDIT:
    explicit_imports: 4
    public_definitions: 0
    public_theorems: 1
    private_definitions: 2
    private_theorems: 11
    ordered_examples: 2
    forbidden_tokens: 0
    generated_backend_tokens: 0
    public_surface_match: PASS

  REPORTED_DIRECT_LEAN:
    exit_status: 0
    reported_axioms:
      - propext
      - Classical.choice
      - Quot.sound
    judge_reran_Lean: false
    ruling: ACCEPTED_AS_BYTE_PINNED_RELEASE_EVIDENCE_PRODUCTION_RERUN_REQUIRED

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  release: AUTHORIZED
  first_source_defect: NONE
  first_sign_or_factor_defect: NONE
  first_Fubini_defect: NONE
  first_coercion_defect: NONE
  theorem_statement_repaired: false
  proof_body_repaired: false
  plant_harness_repaired: true

FIRST_LOAD_BEARING_ATTACK:
  target: TWO_ORDERED_EXAMPLES_AS_INDEX_ORIENTATION_FALSIFIER
  ruling: NOT_INDEPENDENT
  reason: >-
    The final archimedean and CCM-WR kernels are Hermitian/real-symmetric.
    Instantiating the same theorem at (0,1) and (1,0) does not by itself
    distinguish a hidden n/r reversal.
  repair: >-
    Keep the two examples as harness-only smoke. Enforce index orientation
    through an exact source-statement fingerprint, the literal first-slot
    conjugation in bareModeProduct, and a non-real abstract control.

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchOffDiagonalCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
  - Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
  - Mathlib.MeasureTheory.Integral.Prod

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: []
  theorems:
    - sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
  total_public_declarations: 1

PRIVATE_SUPPORT:
  definitions: 2
  theorems: 11
  maximum_total: 13
  additional_private_declarations: forbidden
  reduction_by_refactor: allowed
  public_promotion: forbidden

ORDERED_CONTROLS:
  harness_examples:
    - n_0_r_1
    - n_1_r_0
  production_disposition: OMIT
  closeout_disposition: RECORD_AS_PREFLIGHT_SMOKE_ONLY

STOP_CODE:
  GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_MISSING

SUCCESS_CODE:
  GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E1: CLOSED
  B3_0E2: CLOSED
  B3_0E3: CLOSED
  B3_0E4A: CLOSED
  B3_0E: OPEN
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER

NEXT_DISCRIMINATOR:
  B3_0E4B1_DIAGONAL_ENDPOINT_LEDGER_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

SCOPE: ABSTRACT
VERIFIER: LEAN_AFTER_PRODUCTION_VALIDATION
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
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
1. Source-lock and parent audit

Both attachments were read in full. Their hashes and exact byte sizes match the controlling locks. The request defines one off-diagonal crosswalk transaction, preserves B3.0E4B as a separate branch, and forbids every coarse-checkpoint or RH-level promotion. 

PROSHKA_REQUEST_GOAL057_B3_0E4A…

 [ABSTRACT][PAPER]

Live origin/rh_clean is exactly ce7f7f492cabfa48b5b3628a3842d09508114df8. That commit is a documentation-only B3.0E4A preflight record whose direct parent is the proved B3.0E3 production closeout 3df702ead9729e187d3fbdf461452e25bb7c8bae. [ABSTRACT][PAPER]

The parent closeout records B3.0E3 as fully validated and leaves exactly this off-diagonal source-pairing/negative-ccmWREntry crosswalk open. It also records that the diagonal endpoint constant and one-sided assembly remain independent. [ABSTRACT][LEAN]

The Arsenal mandate is accepted. The fetched deck contains the C04, C09, and C10 mechanisms used below, while the standing mandate requires these adversarial checks to remain active. [ABSTRACT][PAPER]

2. Operative ruling
TRY_GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
	​


The exact theorem is mathematically correct and source-faithful. No source-sign, Fourier-scale, Fubini, support, or real-to-complex coercion defect was found. [ABSTRACT][LEAN]

The source fixes:

antilinearity in the first mode and linearity in the second;

W
R
	​

=−W
∞
	​

;

the full Weil form as W
0,2
	​

−W
R
	​

−∑
p
	​

W
p
	​

;

the one-sided formula for W
R
	​

(V
n
	​

,V
r
	​

). [ABSTRACT][PAPER]

Equation (4.4) gives the exact endpoint term plus the regularized integral represented in production by ccmWREntry. [FINITE_CELL][PAPER]

Production fixes the same objects:

sourceArchimedeanModePairing is the conjugate-first multiplier integral;

the exact multiplier is the constant −logπ−γ minus twice the regularized hyperbolic-kernel integral;

the kernel-mode product is jointly L
1
 on the literal positive-x product measure;

twice the cosine correlation is the literal ccmQKernel on 0≤x≤L
m
	​

(i) and zero outside.

ccmWREntry has exactly the equation-(4.4) endpoint and Ioc 0 L integral.

[ABSTRACT][LEAN]

3. Exact mathematical ledger

Write

B
n,r
	​

(t)=
V
i,n
	​

(t)
	​

V
i,r
	​

(t).

For n

=r, B3.0E3 at x=0 proves

∫
R
	​

B
n,r
	​

(t)dt=0.

This kills both the constant part of the exact multiplier and, after taking the inner t-integral, the e
−x
 regularizer term. [ABSTRACT][LEAN]

The exact multiplier identity gives

m
arch
	​

(t)=−logπ−γ−2∫
0
∞
	​

K
reg
	​

(t,x)dx.

The public B3.0E2 joint-L
1
 theorem legally permits the interchange

∫
t
	​

∫
x
	​

=∫
x
	​

∫
t
	​

.

The harness consumes MeasureTheory.integral_integral_swap; it does not substitute separate fiberwise integrability. [ABSTRACT][LEAN]

For x>0, the inner integral satisfies

2∫
R
	​

V
i,n
	​

(t)
	​

K
reg
	​

(t,x)
V
i,r
	​

(t)dt={
ccmWRIntegrand(L
m
	​

(i),n,r,x),
0,
	​

x≤L
m
	​

(i),
x>L
m
	​

(i).
	​


The factors are exact:

the outer multiplier contributes −2;

B3.0E3 contributes Q
n,r
	​

/2;

their product contributes the required final minus sign with no residual factor. [ABSTRACT][LEAN]

Because

ccmQKernel(L,n,r,0)=0(n

=r),

the endpoint term in ccmWREntry vanishes definitionally after the proved off-diagonal lemma. The remaining positive-x integral reduces exactly from Ioi 0 with the support cut to Ioc 0 (L_m i). Therefore

sourceArchimedeanModePairing(i,n,r)=−ccmWREntry(L
m
	​

(i),n,r)
	​


for every n

=r. [ABSTRACT][LEAN]

4. First load-bearing attack: the ordered controls

The two ordered examples are valid smoke tests:

lean
(n,r) = (0,1)
(n,r) = (1,0)

but the request overstates what they certify.

The final source pairing is Hermitian, and ccmWREntry is real-symmetric. Consequently, both ordered instances can survive an internal index transposition. They do not, by themselves, prove that symmetry was not used to hide an n/r reversal. [ABSTRACT][LEAN]

This does not invalidate the public theorem or its proof. The harness itself uses the literal source-oriented object

lean
conj (Fourier mode n) * Fourier mode r

and consumes B3.0E3 with the same (n,r) order. The repair is to change the plant, not the theorem.

The two examples therefore remain harness-only smoke and are omitted from production. The load-bearing orientation test must instead combine:

an exact statement/definition fingerprint for bareModeProduct;

a mutation deleting or moving first-slot conjugation;

a non-real abstract control, for example z
n
	​

=1, z
r
	​

=i, where

z
n
	​

	​

z
r
	​

=i,
z
r
	​

	​

z
n
	​

=−i.

This is the required C04 firewall.

5. Exact production contract

Owned file:

q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceArchOffDiagonalCCMWRCrosswalk.lean

Exact imports:

lean
import Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
import Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
import Mathlib.MeasureTheory.Integral.Prod

Exact namespace and scopes:

lean
noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

Sole public declaration:

lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)

[ABSTRACT][LEAN]

Private support is capped exactly at:

2 private definitions
11 private theorems
13 private declarations total

The two example controls and the final #print axioms command are omitted from production. No public control wrapper is added.

6. Mandatory plant suite
P057_B3_0E4A_1_OFFDIAGONAL_ZERO_CONSTANT

Mutation: remove hnr, retain a nonzero ccmQKernel L n r 0, or import the diagonal value 2.

Required stop:

SOURCE_OFFDIAGONAL_CCM_QKERNEL_ZERO_CONSTANT_MISSING
P057_B3_0E4A_2_FUBINI

Mutation: remove consumption of

lean
sourceArchimedeanKernelModeIntegrand_integrable

or replace joint product-measure integrability by fiberwise statements.

Required stop:

SOURCE_ARCH_JOINT_FUBINI_CARRIER_NOT_CONSUMED
P057_B3_0E4A_3_SIGN

Mutation:

source pairing = +ccmWREntry

or replace the exact outer -2 by +2.

Required stop:

SOURCE_ARCH_CCM_WR_FINAL_SIGN_MISMATCH
P057_B3_0E4A_4_FACTOR_TWO

Mutation: drop the factor 2 from either the hyperbolic multiplier or the B3.0E3 cosine-correlation theorem.

Required stop:

SOURCE_ARCH_CCM_WR_FACTOR_TWO_MISMATCH
P057_B3_0E4A_5_SUPPORT

Mutation: continue ccmQKernel past x=L
m
	​

(i), remove the zero-extension cut, or replace Ioc 0 (L_m i) by an unrestricted positive-half-line integral.

Required stop:

SOURCE_MODE_ZERO_EXTENSION_SUPPORT_MISMATCH
P057_B3_0E4A_6_ANTILINEAR_FIRST

Mutation: delete first-slot conjugation or conjugate the second mode.

Required stop:

SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

Harness: exact definition fingerprint plus a non-real complex control. Compilation of the final symmetric scalar identity is not sufficient.

P057_B3_0E4A_7_INDEX_ORDER_REPAIRED

Mutation: define the private bare product with (r,n) while retaining the public (n,r) source labels.

Required stop:

SOURCE_ARCH_OFFDIAGONAL_INDEX_ORDER_MISMATCH

The two ordered theorem instances are not the detector for this plant.

P057_B3_0E4A_8_REAL_COMPLEX_COERCION

Mutation: remove or reverse integral_complex_ofReal, or identify the complex integral with the real CCM integral without the exact coercion theorem.

Required stop:

SOURCE_ARCH_CCM_WR_REAL_COMPLEX_COERCION_MISMATCH
P057_B3_0E4A_9_DEPENDENCY

Mutation: add a new Step33, hbox, generated-PSD, numeric-payload, or direct Aristotle-output import.

Required stop:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

The previously audited tracked historical dependency inherited through the closed E1/E2/E3 chain remains recorded; this transaction may introduce no new generated backend.

7. Validation gates

Production success requires:

Bash
test "$(git rev-parse HEAD)" = \
  "ce7f7f492cabfa48b5b3628a3842d09508114df8"

test "$(git rev-parse origin/rh_clean)" = \
  "ce7f7f492cabfa48b5b3628a3842d09508114df8"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchOffDiagonalCCMWRCrosswalk.lean

lake build Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchOffDiagonalCCMWRCrosswalk.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

Additional mandatory gates:

files:
  create exactly one production Lean file;
  modify no B3.0 parent file;

materialization:
  copy the authoritative harness proof;
  omit exactly the two final ordered examples and the #print command;
  record every other deviation;

surface:
  public definitions = 0;
  public theorems = 1;
  private definitions <= 2;
  private theorems <= 11;
  proof-DB declarations expected = 14;

taint:
  no sorry;
  no admit;
  no exact?;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;

imports:
  exactly four direct imports;
  no new generated backend;
  inherited historical provenance recorded honestly;

axioms:
  #print axioms
    Q3.RouteB.D0Pstar
      .sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne

  require exactly:
    [propext, Classical.choice, Quot.sound];

plants:
  all nine repaired plants fire;
  no plant changes the released public theorem;
  all mutation artifacts removed;

observability:
  proof DB records all 14 declarations;
  all theorem declarations are proved;
  strict Spine PASS;
  three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after every proof and semantic gate passes.

[ABSTRACT][CONDITIONAL]

8. Exact boundary after success

B3.0E4A success proves the complete negative CCM-WR crosswalk for every off-diagonal mode pair:

n

=r⟹B
i
	​

(n,r)=−W
R,i
	​

(n,r).

[ABSTRACT][LEAN]

It does not prove:

the diagonal mode identity;

the diagonal endpoint constant;

the one-sided half-factor assembly in the diagonal branch;

an all-mode matrix theorem;

the complete source Weil-form decomposition;

the prime or pole operator components;

an associated operator graph;

form-domain or operator-domain membership;

finite-to-ambient compression;

the continuum numerator;

H4a1b;

a coarse Goal-057 checkpoint.

Therefore:

B3.0E4A:
  CLOSED after production validation.

B3.0E:
  OPEN.

Goal-057 coarse ledger:
  0 closed / 10 remaining.
9. Next smallest gap

The next atom is smaller than the full B3.0E4B diagonal crosswalk.

The off-diagonal proof works because both the multiplier constant and the regularizing e
−x
 term vanish after mode orthogonality. On the diagonal they do not vanish. Their cancellation must produce the exact logarithmic endpoint constant in equation (4.4).

The smallest source-locked atom is:

GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER

Proposed theorem:

lean
theorem sourceArchimedeanDiagonalRegularizer_endpointLedger
    (L : ℝ) (hL : 0 < L) :
    -Real.log Real.pi -
        (∫ x in Set.Ioc 0 L,
          2 * (1 - Real.exp (-x)) /
            (Real.exp x - Real.exp (-x))) +
        (∫ x in Set.Ioi L,
          2 * Real.exp (-x) /
            (Real.exp x - Real.exp (-x))) =
      -Real.log
        (4 * Real.pi *
          ((Real.exp L - 1) / (Real.exp L + 1)))

[ABSTRACT][CONDITIONAL]

This is the exact scalar ledger behind the diagonal endpoint term. It preserves the cancellation-bearing finite-region expression and the convergent tail. It must not split the near-zero regularizer into separately divergent pieces.

After B3.0E4B1, the next atom is:

GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

Only after B3.0E4B2 may an all-mode theorem be assembled by cases.

Neither B3.0E4B1 nor B3.0E4B2 is authorized in this verdict.

10. Strongest attack

The off-diagonal branch is the easy branch precisely because every endpoint term vanishes. Is this substantive route progress, or selective packaging that avoids the actual equation-(4.4) difficulty?

It is substantive but narrow proof progress.

B3.0E4A closes all off-diagonal entries uniformly in the window index and mode labels. It consumes all three newly built analytic layers—exact multiplier representation, joint Fubini carrier, and exact mode-correlation/CCM kernel—and proves the final source sign. It is not a wrapper.

But it does not reduce the diagonal endpoint ledger by implication. The diagonal branch contains a distinct cancellation between:

the constant −logπ−γ;

the e
−x
 regularizer;

the x>L tail;

the endpoint logarithm in ccmWREntry.

Calling B3.0E closed after E4A would be a C10 surrogate promotion. Splitting E4B first into the scalar endpoint ledger is the fail-closed repair.

11. Meta closeout

What became smaller?

The CCM-WR bridge is reduced from an all-entry analytic crosswalk to one diagonal scalar endpoint ledger plus its later diagonal assembly.

What was killed?

any residual sign or 2π ambiguity in the off-diagonal branch;

hidden fiberwise Fubini;

continuation of the mode correlation beyond the source window;

the claim that two symmetric ordered examples independently certify source index orientation;

promotion of the off-diagonal theorem to the full source form.

What must not be tried again?

Do not use (0,1) and (1,0) alone as an orientation plant. Do not merge the diagonal endpoint constant into E4A. Do not split the diagonal regularizer into separately divergent near-zero terms.

Current smallest named gap

GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER

Next cheapest decisive test

B3_0E4B1_DIAGONAL_ENDPOINT_LEDGER_NO_SORRY_PREFLIGHT

Prior prediction fate

B3.0E3 prediction:
  the off-diagonal branch should close first because Q_{n,r}(0)=0.

Fate:
  CONFIRMED.

B3.0E4A harness prediction:
  exact multiplier + joint Fubini + CCM correlation give the negative
  off-diagonal entry without a new source object.

Fate:
  CONFIRMED.

Ordered-control prediction:
  testing both (0,1) and (1,0) rules out an index reversal.

Fate:
  REFUTED AS AN INDEPENDENT FALSIFIER;
  retained only as smoke.
YAML
iteration:
  target: GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  status: PROGRESS
  failed_strategy: symmetric_ordered_instances_as_index_orientation_detector
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER
  invariant_learned: offdiagonal_orthogonality_final_minus_sign_joint_Fubini_and_literal_window_support_are_independent_contracts
  forbidden_future_move: promote_offdiagonal_crosswalk_to_full_CCM_WR_or_split_diagonal_regularization_into_divergent_parts
  next_decisive_test: B3_0E4B1_DIAGONAL_ENDPOINT_LEDGER_NO_SORRY_PREFLIGHT
  progress_class: PROOF_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: ce7f7f492cabfa48b5b3628a3842d09508114df8
  require_origin_equal: true
  mathematical_parent: 3df702ead9729e187d3fbdf461452e25bb7c8bae
  request_sha256: 3c01e6440d318d87b270f13c8388f6bfe72a16ab1507703af71391d9fe5f6b6a
  harness_sha256: 4a9910f66a31400d244b240514b69dd8eb3f414401bc3226f503fd95385ce79e
  harness_bytes: 12483
  harness_lines: 310

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchOffDiagonalCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
  - Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
  - Mathlib.MeasureTheory.Integral.Prod

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness proof
  - retain the exact imports, namespace, scopes, private definitions,
    private theorems and public theorem
  - omit the two final ordered examples
  - omit the final #print axioms command
  - add no public helper or control wrapper
  - record every other deviation from the harness

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
  total_public_declarations: 1

PUBLIC_THEOREM_EXACT: |
  theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
      (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
      sourceArchimedeanModePairing i n r =
        -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
    ...

PRIVATE_SUPPORT:
  maximum_definitions: 2
  maximum_theorems: 11
  maximum_total: 13
  additional_private_declarations: forbidden
  reduction_allowed: true
  public_promotion: forbidden

ORDERED_CONTROLS:
  retain_in_production: false
  retain_in_closeout_as_smoke: true
  may_not_count_as_orientation_plant: true

MANDATORY_PLANTS:
  - id: P057_B3_0E4A_1_OFFDIAGONAL_ZERO_CONSTANT
    required_stop: SOURCE_OFFDIAGONAL_CCM_QKERNEL_ZERO_CONSTANT_MISSING

  - id: P057_B3_0E4A_2_FUBINI
    required_stop: SOURCE_ARCH_JOINT_FUBINI_CARRIER_NOT_CONSUMED

  - id: P057_B3_0E4A_3_SIGN
    required_stop: SOURCE_ARCH_CCM_WR_FINAL_SIGN_MISMATCH

  - id: P057_B3_0E4A_4_FACTOR_TWO
    required_stop: SOURCE_ARCH_CCM_WR_FACTOR_TWO_MISMATCH

  - id: P057_B3_0E4A_5_SUPPORT
    required_stop: SOURCE_MODE_ZERO_EXTENSION_SUPPORT_MISMATCH

  - id: P057_B3_0E4A_6_ANTILINEAR_FIRST
    required_stop: SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

  - id: P057_B3_0E4A_7_INDEX_ORDER_REPAIRED
    harness: EXACT_DEFINITION_FINGERPRINT_PLUS_NONREAL_COMPLEX_CONTROL
    required_stop: SOURCE_ARCH_OFFDIAGONAL_INDEX_ORDER_MISMATCH

  - id: P057_B3_0E4A_8_REAL_COMPLEX_COERCION
    required_stop: SOURCE_ARCH_CCM_WR_REAL_COMPLEX_COERCION_MISMATCH

  - id: P057_B3_0E4A_9_DEPENDENCY
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the new file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - full lake build
  - scripts/q3_check.sh on the new file
  - routeb_status.py --check
  - exact public surface 0_definitions_1_theorem
  - exact private ceiling 2_definitions_11_theorems
  - forbidden-token scan
  - exact direct-import audit
  - no-new-generated-dependency audit
  - inherited historical provenance report
  - all nine repaired plants fire
  - remove every mutation artifact
  - print axioms for the public theorem
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database import with 14 expected declarations
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status --short report
  - update route state only after all proof and semantic gates pass

CLOSEOUT_MUST_STATE:
  - SOURCE_ARCH_OFFDIAGONAL_PAIRING_EQ_NEG_CCM_WR_PROVED
  - EXACT_OFFDIAGONAL_ZERO_CONSTANT_RETAINED
  - EXACT_JOINT_FUBINI_CARRIER_CONSUMED
  - EXACT_FINAL_MINUS_SIGN_RETAINED
  - EXACT_FACTOR_TWO_LEDGER_RETAINED
  - EXACT_ANTILINEAR_FIRST_ORIENTATION_RETAINED
  - EXACT_ZERO_EXTENDED_SUPPORT_RETAINED
  - ORDERED_EXAMPLES_SMOKE_ONLY
  - B3_0E4A_CLOSED
  - B3_0E_OPEN
  - NO_DIAGONAL_ENDPOINT_LEDGER
  - NO_DIAGONAL_CCM_WR_CROSSWALK
  - NO_ALL_MODE_CROSSWALK
  - NO_SOURCE_WEIL_FORM_DECOMPOSITION
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_MISSING

SUCCESS:
  GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0E4B1_DIAGONAL_ENDPOINT_LEDGER_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0E4B1_or_B3_0E4B2_inside_this_transaction
  - retain_ordered_examples_as_public_or_private_production_declarations
  - count_symmetric_ordered_examples_as_an_index_orientation_falsifier
  - state_an_all_mode_sourceArchimedeanModePairing_eq_neg_ccmWREntry
  - define_the_full_source_Weil_form
  - define_prime_or_pole_operator_components
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
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
