STATUS: OPEN — B3.0D SOURCE ARCHIMEDEAN MODE-PAIRING KERNEL HERMITIANITY RELEASED
YAML
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  ATTACHED_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY_RELEASE_2026-08-08.md
    observed_sha256: 9fdcb73782a7cf589be92056ea67cfa6aba2be7a11b74e143781cf247fe2ce60
    observed_bytes: 8689
    observed_lines: 264
    status: PASS

  MATHEMATICAL_PARENT:
    commit: a97fc22ba8b0179deeabbd1321f83c9737084925
    commit_exists: true
    role: B3_0C_PRODUCTION_CLOSEOUT

  LIVE_PACKAGE_HEAD:
    commit: ede4e828cf87f8769e76149d390b5b4b20198e41
    origin_rh_clean_equal: true
    relation_to_mathematical_parent: ONE_COMMIT_AHEAD
    package_changes_only:
      - B3_0D_release_request
      - B3_0D_insights_entry
    mathematical_parent_files_changed: false

  IMPLEMENTATION_EXPECTED_HEAD:
    ede4e828cf87f8769e76149d390b5b4b20198e41

  PARENT_B3_0C:
    file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingIntegrable.lean
    expected_sha256: cdad33d4e428dc541501d24b3254e72b3f01b3aae36bb482d5d59476bb16f27a
    result: GOAL057_B3_0C_SOURCE_ARCH_MULTIPLIER_MODE_PAIRING_INTEGRABILITY_PROVED
    retained: true
    reopened: false

  TARGET_FILE_PRESENT_AT_LIVE_HEAD: false

  SCRATCH_PREFLIGHT:
    claimed_sha256: fd319acf46f63c805d9e71706b8429be144d640c82a3cc4308d4f9dfc15c1b2c
    claimed_bytes: 856
    claimed_lines: 26
    claimed_result: PASS
    exact_scratch_bytes_attached_to_judge: false
    independently_rehashed_or_rerun_by_judge: false
    ruling: ACCEPTED_AS_PREFLIGHT_REPORT_PRODUCTION_RERUN_REQUIRED

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

RELEASED_ATOM:
  GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchModePairingIntegrable

NAMESPACE:
  Q3.RouteB.D0Pstar

MODULE_SCOPE:
  - noncomputable section
  - open Complex MeasureTheory
  - open scoped FourierTransform ComplexConjugate

EXACT_PUBLIC_DEFINITIONS:
  - sourceArchimedeanModePairing

EXACT_PUBLIC_THEOREMS:
  - sourceArchimedeanModePairing_conj_symm

PUBLIC_SURFACE:
  noncomputable_definitions: 1
  theorems: 1
  structures: 0
  total_public_declarations: 2

PRIVATE_SUPPORT_BUDGET:
  expected: 0
  maximum: 1
  permitted_role:
    - pointwise_conjugation_normal_form_only
  abstract_structure_or_premise_wrapper: forbidden

SELECTED_CHILD_SCOPE: ABSTRACT
SELECTED_CHILD_VERIFIER: CONDITIONAL_UNTIL_PRODUCTION_LEAN

SUCCESS_CODE:
  GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY_PROVED

STOP_CODE:
  GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY_MISSING

PLANTS:
  - P057_B3_0D_1_MODE_INDEX_ORIENTATION
  - P057_B3_0D_2_ANTILINEAR_FIRST
  - P057_B3_0D_3_MULTIPLIER_REALITY
  - P057_B3_0D_4_INTEGRAL_VALUE_HALLUCINATION
  - P057_B3_0D_5_KERNEL_AS_FULL_SOURCE_FORM
  - P057_B3_0D_6_FORM_TO_OPERATOR_GRAPH
  - P057_B3_0D_7_FIXED_TO_UNIFORM
  - P057_B3_0D_8_GENERATED_BACKEND_IMPORT
  - P057_B3_0D_9_DIAGONAL_REALITY
  - P057_B3_0D_10_TOTALIZED_INTEGRAL_ORPHAN

PARENT_AFTER_SUCCESS:
  B3_0D: CLOSED
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK

NEXT_GAP_AUTHORIZED: false

COARSE_CHECKPOINTS_CLOSED_AFTER_SUCCESS: 0
COARSE_CHECKPOINTS_REMAINING_AFTER_SUCCESS: 10
CURRENT_CHECKPOINT_EFFECT: STRICTLY_ADVANCED_NOT_CLOSED

PHASE_KEY_CHANGE: false
NEW_CHAT: false
OWNER_AUTHORITY_REQUIRED: false
SOLE_OWNER_GATE: PX_RH_CLAIM

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 4

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
1. Source-lock audit

The attached request was read in full and independently rehashed. It is exactly 8,689 bytes over 264 lines, with SHA-256 9fdcb737…ce60. Its requested public surface, plant suite, stop/success boundary, and no-promotion controls are therefore the controlling release contract. 

PROSHKA_REQUEST_GOAL057_B3_0D_S…

 [ABSTRACT][PAPER]

The request’s stated commit a97fc22…4925 is the valid mathematical parent: it is the production closeout of B3.0C and records the exact source-oriented fixed-mode L
1
 theorem. [ABSTRACT][PAPER]

Live origin/rh_clean has advanced by exactly one package commit to ede4e828…e41. That commit adds only this B3.0D request and its insights entry; it does not change the B3.0C production theorem or any earlier mathematical source. Codex must therefore implement from the live package head, while treating a97fc22… as the immutable mathematical parent. [ABSTRACT][PAPER]

The Arsenal mandate is accepted. The repository materialization ledger confirms the required deck hash and the twelve-card inventory. [ABSTRACT][PAPER]

2. Operative ruling
TRY_GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY
	​


Candidate A is source-faithful, minimal, and nonduplicative.

B3.0C already proves that, for every fixed PairIndex i and integers n r, the exact conjugate-first archimedean integrand is Bochner integrable. Its first Fourier factor is conjugated, its second is linear, and its multiplier is the exact Route-B source multiplier. [ABSTRACT][LEAN]

B3.0D adds precisely the two missing representation objects:

the scalar kernel entry obtained by integrating that legal L
1
 integrand;

the conjugate-symmetry law required of the archimedean component of a Hermitian form.

No stronger source theorem is imported or presumed.

3. Source-faithfulness: conjugation and n,r orientation

The source form is antilinear in its first slot and linear in its second. In the ordered Fourier-mode basis, its coefficient expansion is

BW
m,N
	​

(f,g)=
n,r
∑
	​

c
n
	​

	​

τ
n,r
	​

d
r
	​

.

Thus the source-oriented archimedean mode entry is

B
i
	​

(n,r)=∫
R
	​

V
i,n
	​

(t)
	​

m
arch
	​

(t)
V
i,r
	​

(t)dt.

The index n belongs to the conjugated, antilinear first slot. The index r belongs to the linear second slot. This is fixed by the source contract, not by the fact that the resulting kernel happens to be Hermitian. [ABSTRACT][PAPER]

The production definition

lean
sourceArchimedeanMultiplier : ℝ → ℝ

is genuinely real-valued. Its coercion to ℂ is therefore fixed by complex conjugation pointwise. No sign or nonvanishing hypothesis is needed for Hermitian symmetry. [ABSTRACT][LEAN]

Consequently,

B
i
	​

(n,r)
	​

	​

=∫
R
	​

V
i,n
	​

(t)
	​

m
arch
	​

(t)
V
i,r
	​

(t)
	​

dt
=∫
R
	​

V
i,r
	​

(t)
	​

m
arch
	​

(t)
V
i,n
	​

(t)dt
=B
i
	​

(r,n).
	​


Therefore the proposed orientation

lean
sourceArchimedeanModePairing i r n =
  conj (sourceArchimedeanModePairing i n r)

is exact.

A reversed definition could still produce a Hermitian kernel after transposition. That would not make it source-faithful. The source coefficient orientation must therefore be enforced by an exact statement fingerprint and control values, not by compilation of the symmetry theorem alone. [C04]

4. Exact released Lean contract

Owned file:

q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceArchModePairingKernel.lean

Exact import:

lean
import Q3.Proofs.RouteB.D0PstarSourceArchModePairingIntegrable

Exact namespace and scopes:

lean
noncomputable section

open Complex MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace Q3.RouteB.D0Pstar
Public definition
lean
/--
The exact fixed-mode archimedean source pairing in the production
Mathlib Fourier coordinate.

The first mode is the antilinear slot and is conjugated. This is only the
archimedean kernel component; it is not the full source Weil form.
-/
noncomputable def sourceArchimedeanModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ t : ℝ,
    conj (𝓕 (logWindowZeroExtendedMode i n) t) *
      (sourceArchimedeanMultiplier t : ℂ) *
      𝓕 (logWindowZeroExtendedMode i r) t
Public theorem
lean
/--
The exact archimedean source mode-pairing kernel is Hermitian.
-/
theorem sourceArchimedeanModePairing_conj_symm
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i r n =
      conj (sourceArchimedeanModePairing i n r) := by
  ...

[ABSTRACT][CONDITIONAL]

The theorem statement must not acquire an integrability premise, a nonvanishing premise, a sign premise, or a restricted mode-set premise.

5. Minimum implementation-sensitive Lean route

Pinned Mathlib v4.26 proves, without an integrability hypothesis,

lean
integral_conj :
  (∫ x, conj (f x) ∂μ) =
    conj (∫ x, f x ∂μ)

because the Bochner integral is total and conjugation is a linear isometry over the underlying real scalar structure. [ABSTRACT][LEAN]

The production proof should therefore remain four steps:

Unfold sourceArchimedeanModePairing.

Rewrite the right-hand conjugated integral with ← integral_conj.

Use integral_congr and simplify:

conjugation of products;

double conjugation;

conjugation of the real multiplier coerced to ℂ.

Close the pointwise commutative scalar identity with ring.

Implementation skeleton:

lean
theorem sourceArchimedeanModePairing_conj_symm
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i r n =
      conj (sourceArchimedeanModePairing i n r) := by
  unfold sourceArchimedeanModePairing
  rw [← integral_conj]
  apply integral_congr
  intro t
  -- Simplify `conj` through the product, use reality of the multiplier,
  -- eliminate double conjugation, and commute the scalar factors.
  simp only [map_mul, map_conj, conj_conj]
  ring

The exact simplifier lemma for the coerced real multiplier may follow the compiled preflight. It may not be replaced by a hypothesis that the multiplier is real.

Expected private support is zero. One private pointwise normal-form theorem is permitted only if the pinned simplifier cannot close the coercion directly. It must not become a second public theorem.

6. Why B3.0C remains semantically load-bearing

integral_conj is total, so the Hermitian identity can compile even for a nonintegrable arbitrary function: undefined Bochner integrals are totalized.

That creates a real reviewer attack:

Is B3.0D proving a legal source pairing, or merely a formal equality between two totalized zero integrals?

The answer is B3.0C. It proves that every literal source integrand used in the definition is genuinely L
1
. [ABSTRACT][LEAN]

Therefore the exact B3.0C import is not optional decoration. The B3.0D closeout must record:

PAIRING_LEGALITY:
  supplied by sourceArchimedeanModePairing_integrable.

HERMITIANITY:
  supplied by integral_conj and multiplier reality.

A file that proves the same totalized identity after dropping the B3.0C parent has not materialized the released source kernel. [C10]

7. Mandatory plants
P057_B3_0D_1_MODE_INDEX_ORIENTATION

Mutation:

B(n,r) :=
  ∫ conj(Fourier_r) * multiplier * Fourier_n

while retaining the public parameter names and claiming that n is the source first slot.

Required stop:

SOURCE_MODE_PAIRING_INDEX_ORIENTATION_MISMATCH

Harness: exact source-statement fingerprint plus a finite-support complex control with

F
n
	​

=1,F
r
	​

=i,m=1.

The correct first-slot convention gives i; the reversed convention gives −i. The mutant may remain Hermitian, so compile failure alone is not a valid harness. [C04]

P057_B3_0D_2_ANTILINEAR_FIRST

Mutation:

conj(Fourier_n)
→ Fourier_n

or move the conjugation to Fourier_r.

Required stop:

SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

Harness: exact public-definition fingerprint and an abstract compact-support control with F
n
	​

=1+i, F
r
	​

=1, and real multiplier 1.

P057_B3_0D_3_MULTIPLIER_REALITY

Mutation: replace

lean
sourceArchimedeanMultiplier : ℝ → ℝ

by an arbitrary complex-valued symbol, with no theorem that conjugation fixes it.

Required stop:

SOURCE_ARCH_MULTIPLIER_REALITY_MISSING

K1 control: choose the symbol m(t)=i and both mode factors equal to 1 on a finite-measure set. Then the proposed Hermitian identity requires i=−i, which is false.

P057_B3_0D_4_INTEGRAL_VALUE_HALLUCINATION

Mutation: add any claim that the diagonal value is nonnegative, strictly positive, zero, or equal to a closed formula.

Required stop:

SOURCE_ARCH_PAIRING_VALUE_NOT_PROVED

Hermitianity proves diagonal reality, not a sign. The exact multiplier is not assumed nonnegative.

P057_B3_0D_5_KERNEL_AS_FULL_SOURCE_FORM

Mutation:

sourceArchimedeanModePairing
=
BW_m on source modes

without the endpoint/pole and prime components and their exact sign ledger.

Required stop:

SOURCE_WEIL_FORM_DECOMPOSITION_MISSING

The source functional contains separate pole and prime terms. The archimedean kernel alone is not the full form. [C10]

P057_B3_0D_6_FORM_TO_OPERATOR_GRAPH

Mutation: infer form-domain membership, operator-domain membership, or an associated-operator graph from kernel Hermitianity.

Required stop:

FORM_DOMAIN_NOT_OPERATOR_DOMAIN

A Hermitian matrix coefficient law does not produce an H
m
	​

-valued representing vector.

P057_B3_0D_7_FIXED_TO_UNIFORM

Mutation: promote the fixed-mode equality to a norm bound uniform in i, n, r, m, N, or a cofinal family.

Required stop:

UNIFORM_COFINAL_MODE_BOUND_MISSING

The released theorem has no quantitative bound. [C09]

P057_B3_0D_8_GENERATED_BACKEND_IMPORT

Mutation: inject any generated PSD, Step33, hbox, payload, aristotle_output, or active request module.

Required stop:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

The sole B3.0C import is sufficient.

P057_B3_0D_9_DIAGONAL_REALITY

Positive control:

(1+i)
	​

(1+i)=2∈R.

Mutation: remove the first-slot conjugation:

(1+i)
2
=2i∈
/
R.

Required stop:

SOURCE_ARCH_PAIRING_DIAGONAL_REALITY_MISMATCH

Use 1+i, not merely i: the latter squares to −1, which is still real and would be a weak plant.

P057_B3_0D_10_TOTALIZED_INTEGRAL_ORPHAN

Mutation:

remove the B3.0C import or its semantic dependency;

replace the source integrand by an arbitrary function with no L
1
 certificate;

retain the totalized integral_conj proof.

Required stop:

SOURCE_ARCH_PAIRING_L1_CARRIER_NOT_BOUND

The mutant may compile. The dependency/semantic harness must still reject it because it no longer defines the source-certified legal pairing. [C10]

All plant artifacts must remain outside production and be removed before closeout.

8. Validation gates

Production success requires:

Bash
lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean

lake build Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

Additional gates:

source:
  live HEAD = origin/rh_clean =
    ede4e828cf87f8769e76149d390b5b4b20198e41;

ancestry:
  live HEAD is the one-commit request-package descendant of
    a97fc22ba8b0179deeabbd1321f83c9737084925;

files:
  create exactly one production Lean file;
  modify no B3.0A/B/C parent file;

imports:
  exactly one direct import:
    Q3.Proofs.RouteB.D0PstarSourceArchModePairingIntegrable;
  no forbidden generated dependency in the new transitive closure;

surface:
  exactly one public noncomputable definition;
  exactly one public theorem;
  zero public structures;
  zero or one private helper;
  no additional public declaration;

taint:
  no sorry;
  no admit;
  no exact?;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;
  no aristotle_output import;
  no ACTIVE RequestProject import;

axioms:
  #print axioms
    Q3.RouteB.D0Pstar.sourceArchimedeanModePairing_conj_symm

  require exactly:
    [propext, Classical.choice, Quot.sound];

plants:
  all ten plants fire;
  source-orientation plants use statement/control fingerprints rather than
    assuming every wrong orientation fails to compile;
  all mutation artifacts removed;

observability:
  proof DB records all declarations as proved;
  strict Spine PASS;
  three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view, and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  state updated only after every mathematical and semantic gate passes.
9. Exact semantic boundary after success

Success proves, for every fixed PairIndex i and integers n r:

the exact archimedean mode-pairing integral is represented by a named production scalar;

the scalar kernel is conjugate symmetric:

B
i
	​

(r,n)=
B
i
	​

(n,r)
	​

.

[ABSTRACT][LEAN]

It does not prove:

a value formula for the integral;

diagonal nonnegativity;

equality with ccmWREntry;

the sign relating this kernel to the -W_R term in the finite Weil matrix;

the endpoint/pole component;

the prime component;

the full source Weil-form decomposition;

a finite matrix crosswalk;

form-domain membership;

operator-domain membership;

an associated operator graph;

selected-trial domain membership;

finite-to-ambient compression;

a continuum residual;

H4a1b;

any uniform/cofinal estimate;

any coarse checkpoint.

The ledger therefore remains:

COARSE CHECKPOINTS CLOSED:
  0

COARSE CHECKPOINTS REMAINING:
  10

ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE:
  strictly advanced;
  not closed.
10. Strongest attack

This is a two-line theorem obtained from a real multiplier and integral_conj. Is it route progress or decorative API packaging?

It is representation progress, not an analytic estimate.

The transaction is justified only because it creates the exact scalar object consumed by the next source crosswalk and freezes three conventions that a later proof must not reconstruct privately:

first-slot conjugation;

n,r source orientation;

reality of the exact multiplier.

The theorem would become decorative if the next step merely wrapped it into a finite matrix and stopped. Therefore a separate public “matrix is Hermitian” packaging transaction is not selected. That fact may be a private helper inside the next substantive source crosswalk.

The second attack is stronger:

Since Lean totalizes the integral, the symmetry theorem could be true even if the integrand were not integrable.

Correct. That is why B3.0C remains a mandatory semantic parent and why P057_B3_0D_10_TOTALIZED_INTEGRAL_ORPHAN is binding. A totalized identity with no L
1
 source certificate does not count as B3.0D success.

11. Smallest next atom

The next non-orphaned atom is:

GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK

It must determine, from exact formulas rather than numerical fitting, the precise relationship between:

sourceArchimedeanModePairing i n r

and the existing CCM archimedean entry representation, including:

the sign with which W_R enters the full Weil form;

the source-angular-frequency versus Mathlib-frequency scaling;

any endpoint or pole term that is not part of the multiplier integral;

the mode order;

the exact real-to-complex coercion.

The first decisive controls should be the central entry n=r=0 and one off-diagonal entry. Agreement at one entry is not enough to infer the generic theorem.

This B3.0E atom is not authorized by the present verdict. Its parent wall remains:

SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION
12. Meta closeout

What became smaller?

The archimedean part of the source-form wall now has a named, legal fixed-mode scalar kernel with its exact Hermitian orientation.

What was killed?

ambiguity over which mode occupies the conjugated slot;

use of a complex multiplier without a reality theorem;

treating kernel symmetry as positivity;

treating the archimedean kernel as the entire Weil form;

relying on totalized integrals without the B3.0C L
1
 carrier.

What must not be tried again?

Do not reconstruct the archimedean pairing privately inside the full source-form file. Import this kernel and prove the exact CCM/sign/normalization crosswalk.

Current smallest named gap after success

GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK

Next cheapest decisive test

Symbolically compare the B3.0D kernel with the source CCM archimedean entry at n=r=0 and one off-diagonal mode, preserving the 2π coordinate conversion and the full sign ledger.

Prediction fate

B3.0C prediction:
  the next atom is the source archimedean pairing kernel and its exact
  conjugate symmetry.

Fate:
  CONFIRMED.

B3.0D preflight:
  reported to compile by integral_conj + simplification + ring.

Fate:
  PLAUSIBLE_AND_API_VERIFIED;
  not independently rerun because the scratch bytes were not attached;
  production validation remains mandatory.
YAML
iteration:
  target: GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY
  status: OPEN
  failed_strategy: detect_source_slot_orientation_from_Hermitianity_compilation_alone
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK
  invariant_learned: legal_L1_carrier_first_slot_conjugation_mode_order_and_multiplier_reality_are_independent_contracts
  forbidden_future_move: call_the_archimedean_kernel_the_full_Weil_form_or_ignore_totalized_integral_semantics
  next_decisive_test: exact_central_and_offdiagonal_CCM_WR_crosswalk
  progress_class: REPRESENTATION_PROGRESS
  route_score: 4
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_live_head: ede4e828cf87f8769e76149d390b5b4b20198e41
  require_origin_equal: true
  mathematical_parent: a97fc22ba8b0179deeabbd1321f83c9737084925
  request_attachment_sha256: 9fdcb73782a7cf589be92056ea67cfa6aba2be7a11b74e143781cf247fe2ce60
  parent_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingIntegrable.lean
  parent_expected_sha256: cdad33d4e428dc541501d24b3254e72b3f01b3aae36bb482d5d59476bb16f27a

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchModePairingIntegrable

NAMESPACE:
  Q3.RouteB.D0Pstar

MODULE_SCOPE:
  - noncomputable_section
  - open_Complex_MeasureTheory
  - open_scoped_FourierTransform_ComplexConjugate

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanModePairing
  theorems:
    - sourceArchimedeanModePairing_conj_symm
  structures: []
  total_public_declarations: 2

PUBLIC_DEFINITION_EXACT: |
  noncomputable def sourceArchimedeanModePairing
      (i : PairIndex) (n r : ℤ) : ℂ :=
    ∫ t : ℝ,
      conj (𝓕 (logWindowZeroExtendedMode i n) t) *
        (sourceArchimedeanMultiplier t : ℂ) *
        𝓕 (logWindowZeroExtendedMode i r) t

PUBLIC_THEOREM_EXACT: |
  theorem sourceArchimedeanModePairing_conj_symm
      (i : PairIndex) (n r : ℤ) :
      sourceArchimedeanModePairing i r n =
        conj (sourceArchimedeanModePairing i n r) := by
    ...

PRIVATE_SUPPORT:
  expected_count: 0
  maximum_count: 1
  permitted_role:
    - pointwise_conjugation_normal_form
  public_promotion: forbidden

PROOF_ROUTE:
  - unfold sourceArchimedeanModePairing
  - rewrite the conjugated integral using reverse integral_conj
  - apply integral_congr
  - simplify conjugation of products
  - simplify double conjugation
  - use that the exact multiplier is real-valued before coercion
  - close the commutative scalar identity by ring
  - do not add any integrability, nonvanishing, sign, or mode-set premise

MANDATORY_PLANTS:
  - id: P057_B3_0D_1_MODE_INDEX_ORIENTATION
    harness: SOURCE_STATEMENT_FINGERPRINT_PLUS_COMPLEX_CONTROL
    required_stop: SOURCE_MODE_PAIRING_INDEX_ORIENTATION_MISMATCH

  - id: P057_B3_0D_2_ANTILINEAR_FIRST
    harness: SOURCE_STATEMENT_FINGERPRINT_PLUS_COMPLEX_CONTROL
    required_stop: SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

  - id: P057_B3_0D_3_MULTIPLIER_REALITY
    harness: NONREAL_MULTIPLIER_COUNTEREXAMPLE
    required_stop: SOURCE_ARCH_MULTIPLIER_REALITY_MISSING

  - id: P057_B3_0D_4_INTEGRAL_VALUE_HALLUCINATION
    harness: PUBLIC_SURFACE_AND_SOURCE_CLAIM_SCAN
    required_stop: SOURCE_ARCH_PAIRING_VALUE_NOT_PROVED

  - id: P057_B3_0D_5_KERNEL_AS_FULL_SOURCE_FORM
    harness: SOURCE_COMPONENT_COMPLETENESS
    required_stop: SOURCE_WEIL_FORM_DECOMPOSITION_MISSING

  - id: P057_B3_0D_6_FORM_TO_OPERATOR_GRAPH
    harness: DOMAIN_AND_CARRIER_TYPE_CHECK
    required_stop: FORM_DOMAIN_NOT_OPERATOR_DOMAIN

  - id: P057_B3_0D_7_FIXED_TO_UNIFORM
    harness: QUANTIFIER_FINGERPRINT
    required_stop: UNIFORM_COFINAL_MODE_BOUND_MISSING

  - id: P057_B3_0D_8_GENERATED_BACKEND_IMPORT
    harness: DIRECT_AND_TRANSITIVE_IMPORT_SCAN
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

  - id: P057_B3_0D_9_DIAGONAL_REALITY
    harness: ONE_PLUS_I_DIAGONAL_CONTROL
    required_stop: SOURCE_ARCH_PAIRING_DIAGONAL_REALITY_MISMATCH

  - id: P057_B3_0D_10_TOTALIZED_INTEGRAL_ORPHAN
    harness: B3_0C_SEMANTIC_DEPENDENCY_AND_L1_CARRIER_CHECK
    required_stop: SOURCE_ARCH_PAIRING_L1_CARRIER_NOT_BOUND

VALIDATION:
  - verify live HEAD equals origin/rh_clean before edit
  - verify live HEAD is the one-commit package descendant of mathematical parent
  - direct lake env lean on the new file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
  - full lake build
  - scripts/q3_check.sh on the new file
  - routeb_status.py --check
  - exact public surface 1_noncomputable_definition_1_theorem
  - private surface at most 1_theorem
  - forbidden-token scan
  - direct and transitive forbidden-import audit
  - run all ten plants without changing the released public statements
  - remove every mutation artifact
  - print axioms for sourceArchimedeanModePairing_conj_symm
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database import
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status --short report
  - update route state only after all proof and semantic gates pass

CLOSEOUT_MUST_STATE:
  - SOURCE_ARCHIMEDEAN_FIXED_MODE_PAIRING_KERNEL_DEFINED
  - SOURCE_ARCHIMEDEAN_PAIRING_KERNEL_HERMITIAN
  - FIRST_SLOT_CONJUGATED_SECOND_SLOT_LINEAR
  - B3_0C_L1_CARRIER_RETAINED
  - B3_0D_CLOSED
  - B3_0_OPEN
  - NO_INTEGRAL_VALUE_FORMULA
  - NO_DIAGONAL_SIGN
  - NO_CCM_WR_ENTRY_CROSSWALK
  - NO_SOURCE_WEIL_FORM_DECOMPOSITION
  - NO_PRIME_OR_POLE_COMPONENT
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - NO_UNIFORM_COFINAL_MODE_BOUND
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY_MISSING

SUCCESS:
  GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK

NEXT_GAP_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0E_inside_this_transaction
  - change_any_B3_0A_B_C_parent
  - add_a_public_finite_matrix_packaging_wrapper
  - claim_a_pairing_value_or_diagonal_sign
  - identify_the_archimedean_kernel_with_the_full_Weil_form
  - define_prime_or_pole_components
  - define_the_source_associated_operator
  - infer_form_domain_or_operator_domain_membership
  - claim_any_uniform_or_cofinal_mode_bound
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
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
