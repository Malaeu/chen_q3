STATUS: OPEN — B3.0E3 ZERO-EXTENDED MODE COSINE CORRELATION / CCM Q-KERNEL RELEASED
YAML
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  LIVE_HEAD:
    observed_origin_rh_clean: fe5541fc56a10784499f7705e41bd0bda3f1cb80
    status: PASS
    role: B3_0E3_PROOF_ROUTE_PACKAGE_HEAD

  MATHEMATICAL_PARENT:
    commit: 3a4f582483f4009ca657e854b37292f46a3accf7
    role: B3_0E2_PRODUCTION_CLOSEOUT
    relation_to_live_head: DIRECT_PARENT
    mathematical_parent_files_changed_by_live_head: false

  REQUEST_ATTACHMENT:
    path: PROSHKA_REQUEST_GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL_RELEASE_2026-08-08.md
    expected_sha256: eb6a054802ee88db2f7c302f34504a8e5041eb640ab9824326fdd229964060cd
    observed_sha256: eb6a054802ee88db2f7c302f34504a8e5041eb640ab9824326fdd229964060cd
    observed_bytes: 7218
    observed_lines: 186
    observed_git_blob: 4a9fa6aff4ff233f98f54d11ced66794406fc2ce
    status: PASS
    attachment_is_controlling: true
    repository_copy_at_live_head: false

  HARNESS_ATTACHMENT:
    path: Goal057B3_0E3_Scratch.lean
    expected_sha256: 1d2ef3dbc00954e853d140a5ddc92455a093f320ff1f147e8102fe17aa6e5a4f
    observed_sha256: 1d2ef3dbc00954e853d140a5ddc92455a093f320ff1f147e8102fe17aa6e5a4f
    expected_bytes: 42746
    observed_bytes: 42746
    expected_lines: 1087
    observed_lines: 1087
    observed_git_blob: 7c72e3373fe1e01121a85835839af51b1a0c1de2
    status: PASS

  HARNESS_STATIC_AUDIT:
    explicit_imports: 4
    public_definitions: 0
    public_theorems: 6
    private_definitions: 9
    private_theorems: 32
    private_total: 41
    total_declarations: 47
    hole_tokens: 0
    forbidden_generated_backend_tokens: 0
    public_surface_match: PASS

  REPORTED_DIRECT_LEAN:
    exit_status: 0
    exact_stdout_bytes_attached: false
    independently_rerun_by_judge: false
    reported_axioms:
      - propext
      - Classical.choice
      - Quot.sound
    ruling: ACCEPTED_AS_RELEASE_EVIDENCE_PRODUCTION_RERUN_REQUIRED

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  release: AUTHORIZED
  first_exact_defect: NONE
  mathematical_statement_repaired: false
  public_surface_repaired: false
  production_file_already_exists: false

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceModeCosineCCMQKernel.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrixN1
  - Mathlib.Analysis.Fourier.Inversion
  - Mathlib.Analysis.Convolution

NAMESPACE:
  Q3.RouteB.D0Pstar

MODULE_SCOPE:
  - noncomputable_section
  - set_option_maxHeartbeats_800000
  - open_Complex_MeasureTheory_Set
  - open_scoped_ENNReal_FourierTransform_RealInnerProductSpace_ComplexConjugate_Convolution

PUBLIC_SURFACE:
  definitions: []
  theorems:
    - two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    - sourceModeCosineCorrelation_control_diag_zero
    - sourceModeCosineCorrelation_control_offdiag_zero
    - sourceModeCosineCorrelation_control_offdiag_inside
    - sourceModeCosineCorrelation_control_right_boundary
    - sourceModeCosineCorrelation_control_outside_zero
  total_public_declarations: 6

PRIVATE_SUPPORT:
  maximum_definitions: 9
  maximum_theorems: 32
  maximum_total: 41
  additional_private_declarations: forbidden
  reduction_by_refactor: allowed
  public_promotion: forbidden
  theorem_or_assumption_change: forbidden

STOP_CODE:
  GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL_MISSING

SUCCESS_CODE:
  GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E1: CLOSED
  B3_0E2: CLOSED
  B3_0E3: CLOSED
  B3_0E: OPEN
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

NEXT_DISCRIMINATOR:
  B3_0E4A_OFFDIAGONAL_NEG_CCM_WR_CROSSWALK_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

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

The controlling Markdown attachment and the authoritative Lean harness both match their supplied SHA-256 values exactly. The harness also matches its registered size and line count and was read in full. The request fixes one release-or-reject decision, six public theorems, seven semantic plants, and an explicit prohibition on endpoint assembly or the final ccmWREntry crosswalk. 

PROSHKA_REQUEST_GOAL057_B3_0E3_…

 [SOURCE][LEAN]

Live origin/rh_clean is fe5541fc56a10784499f7705e41bd0bda3f1cb80. That commit records only the B3.0E3 proof route and has the proved B3.0E2 production closeout as its direct parent; it does not modify the mathematical parent files. [SOURCE][ABSTRACT]

B3.0E2 is production-closed at exactly the joint-L
1
 carrier scope. Its closeout records the exact positive-x product measure, the conjugate-first orientation, seven fired plants, standard axioms, and the fact that mode correlation, one-sided endpoint assembly, and the ccmWREntry crosswalk remain open. [SOURCE][LEAN]

The intended production path does not exist at the live head, so this is a clean one-file materialization rather than an overwrite.

The Arsenal mandate is accepted. The byte-exact materialization ledger confirms the mandated deck hash and its twelve-card inventory. [SOURCE][ABSTRACT]

2. Operative ruling
TRY_GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL
	​


The attached theorem is source-faithful and bounded. No factor, sign, support, endpoint, mode-order, or Fourier-coordinate defect was found. [LEAN][DERIVED][ABSTRACT]

The literal CCM kernel is already defined in production by

Q
n,r
L
	​

(x)=
⎩
⎨
⎧
	​

2
L
L−x
	​

cos(
L
2πnx
	​

),
π(n−r)
sin(2πrx/L)−sin(2πnx/L)
	​

,
	​

n=r,
n

=r.
	​


The harness targets this exact definition rather than a fitted or reconstructed equivalent. [SOURCE][LEAN]

3. Mathematical convention audit
3.1 First-slot conjugation

The Fourier product is exactly

FV
i,n
	​

(t)
	​

FV
i,r
	​

(t),

so n remains the antilinear first slot and r remains the linear second slot. The reflected-conjugate convolution is constructed specifically to produce this orientation. [LEAN][DERIVED][ABSTRACT]

A theorem with the same absolute values but second-slot conjugation would still be analytically plausible and could still compile. It would represent the wrong source sesquilinear law. This remains a C04 statement-level firewall. [C04]

3.2 Fourier normalization and the factor 2

Mathlib’s real Fourier transform uses cycles-per-unit frequency. The proof applies

2cos(2πtx)=e
2πitx
+e
−2πitx
,

so twice the cosine integral becomes the sum of the source correlation at x and at −x:

2∫
R
	​

V
n
	​

(t)
	​

cos(2πtx)
V
r
	​

(t)dt=R
n,r
	​

(x)+R
n,r
	​

(−x).

[LEAN][DERIVED][ABSTRACT]

At x=0 and n=r, each correlation contributes one by the exact L
−1/2
 mode normalization. The total is therefore 2, matching ccmQKernel L n n 0 = 2. Dropping the outer factor 2 would miss the literal CCM diagonal normalization by exactly a factor of two. [LEAN][DERIVED][ABSTRACT]

3.3 Support and window orientation

The modes are zero-extended from the literal interval

[0,L
m
	​

(i)].

For 0≤x≤L
m
	​

(i), the two correlation orientations reduce to the exact overlaps

[0,L
m
	​

(i)−x]and[x,L
m
	​

(i)].

For x>L
m
	​

(i), both overlaps are empty and the correlation is zero. At x=L
m
	​

(i), both overlap integrals are over degenerate singleton intervals and are exactly zero. [LEAN][DERIVED][ABSTRACT]

This support statement is stronger and safer than extending the algebraic ccmQKernel branch beyond its source window. The released theorem states the literal piecewise object:

ccmQKernel on 0 ≤ x ≤ L_m;
zero for L_m < x.

It does not claim that the closed CCM expression is a global continuation of the correlation.

3.4 Off-diagonal sign and index order

The elementary exponential integrals naturally produce the complex frequency denominator

r−n.

The real CCM branch is written with denominator

n−r.

The harness reverses the sine numerator in the same calculation:

π(n−r)
sin(2πrx/L)−sin(2πnx/L)
	​

.

Thus there is no residual minus sign. Reversing only the denominator or only the numerator changes the theorem. [LEAN][DERIVED][ABSTRACT]

3.5 Right endpoint

At x=L
m
	​

(i), both diagonal and off-diagonal branches of the literal CCM kernel vanish:

the diagonal carries the factor L−x;

the off-diagonal contains integer-periodic sine values.

The harness proves the correlation side is zero independently from the overlap geometry rather than merely simplifying the CCM formula. This is a genuine positive control on the zero extension. [LEAN][DERIVED][ABSTRACT]

4. Exact released public contract

Owned file:

q3.lean.aristotle/Q3/Proofs/RouteB/
D0PstarSourceModeCosineCCMQKernel.lean

Exact imports:

lean
import Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrixN1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Convolution

The first import is accepted as the standing B3.0E parent/import route. The E3 proof does not itself consume the public B3.0E2 joint-kernel theorem; it uses the already established mode Fourier and L
2
 infrastructure available through that import chain. The closeout must therefore not misdescribe E3 as an application of the B3.0E2 Fubini theorem. [SOURCE][LEAN][DERIVED]

The import list adds no direct generated PSD, Step33, hbox, payload, or aristotle_output dependency. It inherits the already audited historical, tracked, hole-free Aristotle-output dependency present in the closed B3.0E1/B3.0E2 parent closure; this transaction introduces no new such dependency. [SOURCE][LEAN]

Public theorem 1 — exact piecewise source identity
lean
theorem two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    (i : PairIndex) (n r : ℤ) (x : ℝ) (hx : 0 ≤ x) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t
      =
        if x ≤ L_m i then
          (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ)
        else
          0

[ABSTRACT][LEAN]

Public theorem 2 — central diagonal control
lean
theorem sourceModeCosineCorrelation_control_diag_zero
    (i : PairIndex) (n : ℤ) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * 0) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t = 2

[ABSTRACT][LEAN]

Public theorem 3 — central off-diagonal control
lean
theorem sourceModeCosineCorrelation_control_offdiag_zero
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * 0) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t = 0

[ABSTRACT][LEAN]

Public theorem 4 — interior off-diagonal convention control
lean
theorem sourceModeCosineCorrelation_control_offdiag_inside
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t =
      (((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
          Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
        (Real.pi * ((n : ℝ) - (r : ℝ))) : ℝ) : ℂ)

[ABSTRACT][LEAN]

Public theorem 5 — exact right boundary
lean
theorem sourceModeCosineCorrelation_control_right_boundary
    (i : PairIndex) (n r : ℤ) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * L_m i) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t = 0

[ABSTRACT][LEAN]

Public theorem 6 — outside-window zero
lean
theorem sourceModeCosineCorrelation_control_outside_zero
    (i : PairIndex) (n r : ℤ) {x : ℝ}
    (hxL : L_m i < x) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t = 0

[ABSTRACT][LEAN]

The five controls are logically derivable from the main theorem, but they are accepted as public K1 convention fingerprints because they precommit five distinct failure surfaces: normalization, orthogonality, off-diagonal sign, boundary inclusion, and compact support. No further public convenience wrappers are authorized in this transaction. [ABSTRACT][CONDITIONAL]

5. Private proof architecture

The authoritative harness uses exactly nine private definitions and thirty-two private theorems.

The load-bearing sequence is:

define reflected-conjugate correlation;

prove both zero-extended modes are integrable;

prove Fourier convolution multiplication;

prove the reflected-conjugate Fourier identity;

prove continuity of the compactly supported correlation;

obtain L
2
 Fourier membership for each mode;

obtain L
1
 for the product by Hölder;

apply pointwise Fourier inversion;

turn 2*cos into the two correlation orientations;

identify the positive and negative overlap intervals;

evaluate the diagonal overlap;

evaluate the off-diagonal exponential integrals;

use integer periodicity at L
m
	​

(i);

assemble the literal CCM diagonal/off-diagonal branches;

prove the right-boundary and outside-window controls.

[LEAN][DERIVED][ABSTRACT]

No source identity is accepted as a premise. No numerical approximation, sampled sign, fitted scale, or finite-mode restriction appears.

Production may reduce the private surface by semantics-preserving refactoring. It may not exceed the observed ceiling, change a public theorem, add a hypothesis, or replace the source kernel by a new definition.

6. Mandatory plants
P057_B3_0E3_1_FACTOR_TWO

Mutation:

2 * integral
→ integral

or move the factor 2 only into one CCM branch.

Required stop:

SOURCE_MODE_COSINE_CORRELATION_FACTOR_TWO_MISMATCH

Positive control: at x=0, n=r, the released left side is exactly 2. [LEAN][ABSTRACT]

P057_B3_0E3_2_ANTILINEAR_FIRST

Mutation:

conj(Fourier_n) * cosine * Fourier_r

to either:

Fourier_n * cosine * Fourier_r

or:

Fourier_n * cosine * conj(Fourier_r).

Required stop:

SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

Harness: exact public-statement fingerprint plus a non-real abstract complex control. Compilation of a differently oriented integrability statement is not sufficient. [C04]

P057_B3_0E3_3_FOURIER_CONVENTION

Mutation:

cos(2*pi*t*x)
→ cos(t*x)

or use angular frequency without the 2π coordinate transport.

Required stop:

SOURCE_ANGULAR_CYCLES_NORMALIZATION_MISMATCH
P057_B3_0E3_4_OFFDIAG_SIGN

Mutation:

reverse only n-r;

reverse only the sine numerator;

swap n,r without transporting the first-slot conjugation.

Required stop:

CCM_QKERNEL_OFFDIAGONAL_SIGN_OR_INDEX_MISMATCH

The interior off-diagonal public control is the required detector.

P057_B3_0E3_5_LITERAL_SUPPORT

Mutation:

omit zero extension;

center the window;

replace [0,L_m] by another representative;

remove the outside-window branch.

Required stop:

SOURCE_MODE_ZERO_EXTENSION_SUPPORT_MISMATCH
P057_B3_0E3_6_RIGHT_BOUNDARY

Mutation:

x < L_m

in the CCM branch, treating x=L_m as merely outside, or leave the boundary value unproved.

Required stop:

SOURCE_MODE_CORRELATION_RIGHT_BOUNDARY_MISMATCH

The exact boundary theorem must remain independent of an if simplification.

P057_B3_0E3_7_NO_GENERATED_BACKEND

Mutation: add a direct generated PSD, Step33, hbox, numerical payload, or new Aristotle-output import.

Required stop:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

All mutation artifacts must remain outside production and be deleted before closeout.

7. Validation gates

Production success requires:

Bash
test "$(git rev-parse HEAD)" = \
  "fe5541fc56a10784499f7705e41bd0bda3f1cb80"

test "$(git rev-parse origin/rh_clean)" = \
  "fe5541fc56a10784499f7705e41bd0bda3f1cb80"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceModeCosineCCMQKernel.lean

lake build Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceModeCosineCCMQKernel.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

[LEAN][CONDITIONAL]

Additional mandatory gates:

source:
  the two attached byte locks are rechecked before materialization;

files:
  create exactly one production Lean file;
  modify no B3.0A/B/C/D/E1/E2 parent file;

materialization:
  copy the authoritative harness;
  retain the four imports, namespace, scopes, heartbeat option,
    six public statements and proof bodies;
  omit only the two final #print axioms commands;
  record every other deviation;

surface:
  public definitions = 0;
  public theorems = 6;
  private definitions ≤ 9;
  private theorems ≤ 32;
  total declarations ≤ 47;

taint:
  no sorry;
  no admit;
  no exact?;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;

imports:
  exact direct import list;
  no new generated PSD/Step33/hbox/payload dependency;
  no new direct Aristotle-output dependency;
  inherited parent provenance recorded honestly;

axioms:
  #print axioms on all six public theorems;
  each must print exactly:
    [propext, Classical.choice, Quot.sound];

plants:
  all seven plants fire;
  no plant changes a released public theorem;
  every mutation artifact is removed;

observability:
  proof DB records all 47 declarations;
  every theorem declaration is proved;
  strict Spine PASS;
  three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after every proof and semantic gate passes.

[LEAN][CONDITIONAL]

Linter suggestions or unused-private-item warnings are not mathematical failures, but they must be recorded. They may be removed only through private, statement-preserving refactoring within the declared ceiling.

8. Exact semantic boundary after success

B3.0E3 success proves, for every PairIndex i, integer modes n,r, and x≥0,

2∫
R
	​

V
i,n
	​

(t)
	​

cos(2πtx)
V
i,r
	​

(t)dt={
Q
n,r
L
m
	​

(i)
	​

(x),
0,
	​

0≤x≤L
m
	​

(i),
L
m
	​

(i)<x.
	​


[ABSTRACT][LEAN]

It also exposes five exact convention controls.

It does not prove:

the archimedean multiplier pairing after substituting the hyperbolic integral;

a public Fubini-swapped identity;

equality with ccmWRIntegrand;

the one-sided endpoint constant;

the factor 1/2 in ccmWREntry;

the diagonal ccmWREntry crosswalk;

the complete negative ccmWREntry crosswalk;

the full source Weil form;

a source-associated operator graph;

form-domain or operator-domain membership;

finite-to-ambient compression;

a continuum numerator;

H4a1b;

any coarse checkpoint.

[ABSTRACT][CONDITIONAL]

Therefore:

B3.0E3:
  CLOSED after production validation.

B3.0E:
  OPEN.

Goal-057 ledger:
  0 closed / 10 remaining.
9. Smallest successor atom

The smallest successor is not the full diagonal-and-off-diagonal crosswalk.

For n ≠ r,

ccmQKernel(L,n,r,0)=0.

Therefore:

the constant part of the exact archimedean multiplier pairing vanishes;

the regularizing e
−x
Q(0) term vanishes;

the x>L tail vanishes after B3.0E3;

the one-sided endpoint constant in ccmWREntry vanishes.

The remaining identity is the direct negative finite integral. [DERIVED][ABSTRACT]

The exact next atom is:

GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

Proposed theorem:

lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)

[ABSTRACT][CONDITIONAL]

Its exact inputs are:

B3.0D: the named source multiplier pairing;

B3.0E1: the regularized hyperbolic multiplier identity;

B3.0E2: the joint product-measure L
1
 carrier;

B3.0E3: the exact cosine correlation / CCM kernel theorem;

hnr: the source fact that the endpoint kernel value is zero.

The next discriminator is:

B3_0E4A_OFFDIAGONAL_NEG_CCM_WR_CROSSWALK_NO_SORRY_PREFLIGHT

Mandatory controls:

YAML
offdiagonal_zero_constant:
  prove ccmQKernel (L_m i) n r 0 = 0 from n ≠ r;

fubini:
  consume the B3_0E2 joint carrier;
  no fiberwise-only exchange;

sign:
  final result is negative ccmWREntry;

support:
  use B3_0E3 zero outside x > L_m i;

orientation:
  retain conjugate-first n,r order;

controls:
  test both ordered pairs (n,r) = (0,1) and (1,0).

Binary result:

PASS:
  return in the same chat for one B3.0E4A production release.

FAIL:
  retain B3.0E;
  identify the first sign/Fubini/coercion mismatch;
  do not proceed to diagonal endpoint assembly.

The diagonal endpoint ledger remains a separate later atom:

GOAL057_B3_0E4B_DIAGONAL_SOURCE_ARCH_CCM_WR_ENDPOINT_CONSTANT

Neither E4A nor E4B is authorized by this verdict.

10. Strongest attack

This is a 1,087-line proof of an elementary Fourier correlation identity. Is it route progress or excessive repackaging?

It is route progress because the identity is not merely a symbolic rewrite. It formally binds:

Mathlib’s Fourier sign and frequency units;

the literal zero-extended source modes;

first-slot conjugation;

exact overlap support;

the diagonal factor 2;

the off-diagonal sine sign;

the right endpoint;

the outside-window branch;

the already existing literal ccmQKernel.

[LEAN][DERIVED][ABSTRACT]

The theorem would be decorative if its closeout claimed the final ccmWREntry crosswalk. It does not. Its direct consumer is the first Fubini assembly theorem, and its exact route value is that no later file may privately reconstruct or alter the mode-correlation convention. [C10]

A second attack is public-surface size. Five of the six theorems are corollaries. They are accepted only as precommitted K1 source fingerprints. This verdict authorizes no further control wrappers.

A third attack is dependency direction. E3 imports B3.0E2 but does not consume its public joint-L
1
 theorem. That is not a truth defect. It must, however, be reported honestly, and the next E4A theorem—not E3—is where E2 and E3 become joint load-bearing inputs.

11. Meta closeout

What became smaller?

The mode-correlation part of the CCM-WR bridge is reduced from a source-paper formula to one exact production theorem with every factor, index, support branch, and endpoint fixed. [LEAN][DERIVED]

What was killed?

factor-one normalization;

second-slot conjugation;

angular-frequency substitution;

independent reversal of the off-diagonal numerator or denominator;

global extension of the CCM branch past the log window;

treating x=L
m
	​

 as an unaudited outside point.

What must not be tried again?

Do not reconstruct ccmQKernel inside the eventual ccmWREntry crosswalk. Import B3.0E3. Do not infer the endpoint constant from the correlation theorem.

Current smallest named gap:

GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

Next cheapest decisive test:

B3_0E4A_OFFDIAGONAL_NEG_CCM_WR_CROSSWALK_NO_SORRY_PREFLIGHT

Prior prediction fate:

B3.0E2 prediction:
  the next atom is the exact zero-extended cosine correlation / CCM Q-kernel
  crosswalk.

Fate:
  CONFIRMED.

B3.0E3 discriminator:
  correlation-first Fourier inversion closes without a source-object change.

Fate:
  REPORTED_PASS and mathematically audited;
  production rerun remains mandatory.

Registered support risk:
  the right boundary or outside-window branch would expose a zero-extension
  mismatch.

Fate:
  REFUTED; both controls close exactly.
YAML
iteration:
  target: GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL
  status: PROGRESS
  failed_strategy: direct_factorwise_Fubini_with_cosine_times_one_mode_as_L1
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  invariant_learned: factor_two_first_slot_conjugation_frequency_units_support_and_right_boundary_are_independent_source_contracts
  forbidden_future_move: infer_endpoint_constant_or_full_ccmWREntry_crosswalk_from_mode_correlation_alone
  next_decisive_test: B3_0E4A_OFFDIAGONAL_NEG_CCM_WR_CROSSWALK_NO_SORRY_PREFLIGHT
  progress_class: PROOF_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: fe5541fc56a10784499f7705e41bd0bda3f1cb80
  require_origin_equal: true
  mathematical_parent: 3a4f582483f4009ca657e854b37292f46a3accf7
  request_sha256: eb6a054802ee88db2f7c302f34504a8e5041eb640ab9824326fdd229964060cd
  request_bytes: 7218
  request_lines: 186
  harness_sha256: 1d2ef3dbc00954e853d140a5ddc92455a093f320ff1f147e8102fe17aa6e5a4f
  harness_bytes: 42746
  harness_lines: 1087

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceModeCosineCCMQKernel.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrixN1
  - Mathlib.Analysis.Fourier.Inversion
  - Mathlib.Analysis.Convolution

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness
  - retain noncomputable section
  - retain set_option maxHeartbeats 800000
  - retain exact opens and scoped opens
  - retain all proof bodies and all six public theorem statements
  - omit only the final two #print axioms commands
  - add no public definition or theorem
  - record every other deviation from the authoritative harness

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    - sourceModeCosineCorrelation_control_diag_zero
    - sourceModeCosineCorrelation_control_offdiag_zero
    - sourceModeCosineCorrelation_control_offdiag_inside
    - sourceModeCosineCorrelation_control_right_boundary
    - sourceModeCosineCorrelation_control_outside_zero
  total_public_declarations: 6

PRIVATE_SUPPORT:
  maximum_definitions: 9
  maximum_theorems: 32
  maximum_total: 41
  additional_private_declarations: forbidden
  reduction_allowed: true
  public_promotion: forbidden

MANDATORY_SEMANTICS:
  - use literal logWindowZeroExtendedMode
  - use literal ccmQKernel
  - first mode n is conjugated
  - second mode r is linear
  - Mathlib Fourier frequency is cycles per unit
  - retain external factor 2
  - retain offdiagonal numerator and denominator orientation together
  - retain source window [0,L_m]
  - retain exact x = L_m zero
  - retain zero for L_m < x
  - claim mode correlation only

MANDATORY_PLANTS:
  - id: P057_B3_0E3_1_FACTOR_TWO
    required_stop: SOURCE_MODE_COSINE_CORRELATION_FACTOR_TWO_MISMATCH

  - id: P057_B3_0E3_2_ANTILINEAR_FIRST
    required_stop: SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

  - id: P057_B3_0E3_3_FOURIER_CONVENTION
    required_stop: SOURCE_ANGULAR_CYCLES_NORMALIZATION_MISMATCH

  - id: P057_B3_0E3_4_OFFDIAG_SIGN
    required_stop: CCM_QKERNEL_OFFDIAGONAL_SIGN_OR_INDEX_MISMATCH

  - id: P057_B3_0E3_5_LITERAL_SUPPORT
    required_stop: SOURCE_MODE_ZERO_EXTENSION_SUPPORT_MISMATCH

  - id: P057_B3_0E3_6_RIGHT_BOUNDARY
    required_stop: SOURCE_MODE_CORRELATION_RIGHT_BOUNDARY_MISMATCH

  - id: P057_B3_0E3_7_NO_GENERATED_BACKEND
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the new production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
  - full lake build
  - scripts/q3_check.sh on the new file
  - routeb_status.py --check
  - exact public surface 0_definitions_6_theorems
  - private ceiling 9_definitions_32_theorems
  - forbidden-token scan
  - direct and transitive generated-backend audit
  - record inherited parent provenance honestly
  - run all seven plants without public-statement mutation
  - remove every mutation artifact
  - print axioms for all six public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database import
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status --short report
  - update route state only after every proof and semantic gate passes

CLOSEOUT_MUST_STATE:
  - SOURCE_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL_PROVED
  - EXACT_FACTOR_TWO_RETAINED
  - EXACT_ANTILINEAR_FIRST_ORIENTATION_RETAINED
  - EXACT_MATHLIB_FOURIER_COORDINATE_RETAINED
  - EXACT_OFFDIAGONAL_SIGN_AND_INDEX_ORDER_RETAINED
  - EXACT_RIGHT_BOUNDARY_ZERO_RETAINED
  - EXACT_OUTSIDE_WINDOW_ZERO_RETAINED
  - B3_0E3_CLOSED
  - B3_0E_OPEN
  - NO_PUBLIC_FUBINI_ASSEMBLY
  - NO_ONE_SIDED_ENDPOINT_CONSTANT
  - NO_DIAGONAL_CCM_WR_CROSSWALK
  - NO_FULL_CCM_WR_ENTRY_CROSSWALK
  - NO_SOURCE_WEIL_FORM_DECOMPOSITION
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL_MISSING

SUCCESS:
  GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_CCM_QKERNEL_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0E4A_OFFDIAGONAL_NEG_CCM_WR_CROSSWALK_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0E4A_inside_this_transaction
  - implement_diagonal_endpoint_constant_assembly
  - state_the_full_sourceArchimedeanModePairing_eq_neg_ccmWREntry
  - modify_any_B3_0_parent_file
  - widen_any_parent_public_surface
  - change_the_zero_extended_window
  - change_the_first_slot_conjugation
  - insert_or_remove_a_two_pi_factor
  - extend_ccmQKernel_beyond_the_source_window
  - import_generated_PSD_Step33_hbox_or_payload_support
  - define_the_full_source_Weil_form
  - define_the_source_associated_operator
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

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
