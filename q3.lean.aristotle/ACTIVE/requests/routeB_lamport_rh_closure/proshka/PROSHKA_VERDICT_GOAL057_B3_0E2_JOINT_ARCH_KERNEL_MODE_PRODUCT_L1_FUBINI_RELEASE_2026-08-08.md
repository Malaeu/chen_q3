STATUS: OPEN — B3.0E2 JOINT L
1
/FUBINI CARRIER RELEASED
YAML
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  LIVE_HEAD:
    expected: 3c3681f1a93d1115d26002ff2105fc0b6c0023d1
    observed_origin_rh_clean: 3c3681f1a93d1115d26002ff2105fc0b6c0023d1
    status: PASS

  PACKAGE_PARENT:
    commit: a916ca9a75cc62666379f04be0d6825be5eb5888
    relation: ONE_COMMIT_AHEAD
    package_commit_role: B3_0E2_PREFLIGHT_ONLY

  REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_RELEASE_2026-08-08.md
    expected_sha256: 737d65801a9ecbeef6aa7c4312aecef7a72be46b2a427191c88537a3a2d15c6f
    observed_sha256: 737d65801a9ecbeef6aa7c4312aecef7a72be46b2a427191c88537a3a2d15c6f
    expected_bytes: 6711
    observed_bytes: 6711
    expected_lines: 179
    observed_lines: 179
    local_git_blob: a893497863cd95bbc90579386d904e89ac105f65
    repository_git_blob: a893497863cd95bbc90579386d904e89ac105f65
    exact_repo_byte_match: true
    status: PASS

  HARNESS:
    path: Goal057B3_0E2_Scratch.lean
    expected_sha256: 1ff1ef467028a6a62a9d2722c2b96e0ec6aff94366645e32bab91ff5f82f7bde
    observed_sha256: 1ff1ef467028a6a62a9d2722c2b96e0ec6aff94366645e32bab91ff5f82f7bde
    expected_bytes: 27927
    observed_bytes: 27927
    expected_lines: 696
    observed_lines: 696
    local_git_blob: e21f85a7d352b12401965823d13acd9ccc17dcaf
    status: PASS

  HARNESS_STATIC_AUDIT:
    explicit_imports: 4
    public_definitions: 1
    public_theorems: 1
    private_definitions: 4
    private_theorems: 18
    private_total: 22
    hole_tokens: 0
    generated_backend_tokens: 0
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

PARENT_B3_0E1:
  result: GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_PROVED
  file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean
  file_sha256: 4fb022d88ded0d0afecbab8767f0b07642c7a0a97e1108736682687198e7a25d
  retained: true
  reopened: false

DECISION:
  release: AUTHORIZED
  first_exact_defect: NONE
  source_distribution_fallback_selected: false
  actual_Fubini_rewrite_proved_here: false
  mode_correlation_ccmQKernel_proved_here: false
  final_ccmWREntry_crosswalk_proved_here: false

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchKernelModeProductL1.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel
  - Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
  - Mathlib.MeasureTheory.Integral.Prod
  - Mathlib.Analysis.SpecialFunctions.Integrability.Basic

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions:
    - sourceArchimedeanKernelModeIntegrand
  theorems:
    - sourceArchimedeanKernelModeIntegrand_integrable
  total_public_declarations: 2

PRIVATE_SUPPORT:
  maximum_definitions: 4
  maximum_theorems: 18
  maximum_total: 22
  additional_private_declarations: forbidden
  reduction_by_refactor: allowed
  public_promotion: forbidden
  theorem_or_assumption_change: forbidden

STOP_CODE:
  GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_CARRIER_MISSING

SUCCESS_CODE:
  GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_CARRIER_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E1: CLOSED
  B3_0E2: CLOSED
  B3_0E: OPEN
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL

NEXT_DISCRIMINATOR:
  B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT

NEXT_GAP_AUTHORIZED_FOR_PRODUCTION: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL:
  mandate_accepted: true
  cards_applied:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

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
1. Source-lock ruling

The controlling request and the authoritative Lean harness match all supplied byte locks exactly. The request also matches the Git blob published at the live branch head, not merely a local reconstruction. 

PROSHKA_REQUEST_GOAL057_B3_0E2_…

 [SOURCE][LEAN][DERIVED]

Live origin/rh_clean is exactly 3c3681f1a93d1115d26002ff2105fc0b6c0023d1. That commit is the B3.0E2 preflight package and has the proved B3.0E1 production state as its direct parent. [SOURCE][ABSTRACT]

B3.0E1 is production-closed at its declared scalar scope: the exact regularized hyperbolic kernel is integrable on Ioi 0, and the exact source multiplier equals the Euler/log constant minus twice its positive-x integral. The closeout explicitly leaves the weighted joint carrier, mode correlation, endpoint assembly, and ccmWREntry crosswalk open. [SOURCE][LEAN]

The attached harness has exactly the requested two public declarations and exactly 22 private support declarations. Static inspection found no hole token, generated PSD/Step33/hbox/payload reference, public premise, alternative source kernel, or hidden numerical constant. [LEAN][DERIVED]

2. Mathematical audit of the joint carrier

The harness preserves the exact B3.0E1 kernel

K
reg
	​

(t,x)=
e
x
−e
−x
e
x/2
cos(2πtx)−e
−x
	​

.

This is the production source kernel, not an envelope or fitted density. [SOURCE][LEAN]

The released integrand is exactly

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

(t),

with n in the conjugated first slot and r in the linear second slot. The product variable is ordered as (t,x), and the measure is literally

dt⊗1
(0,∞)
	​

(x)dx.

No endpoint atom, centered-window replacement, transposed mode order, or implicit extension to negative x is introduced. [LEAN][DERIVED][ABSTRACT]

Near x=0

The proof keeps the cancellation-preserving numerator paired:

e
−2x
−e
−x/2
cos(2πtx).

It rewrites this as

(e
−2x
−e
−x/2
)+e
−x/2
(1−cos(2πtx))

and proves, for 0<x≤1,

∣K
reg
	​

(t,x)∣≤1+e
3/2
x
	​

∣2πt∣
	​

	​

.

The two original singular terms are never estimated separately. [LEAN][DERIVED][ABSTRACT]

The endpoint factor x
−1/2
 is integrable on (0,1]. The frequency cost is only 
∣t∣
	​

. [LEAN][DERIVED][ABSTRACT]

Frequency payment

For each fixed source mode, B3.0B1 supplies the resonance-safe bound

∣
V
i,n
	​

(t)∣≤
1+∣t∣
C
i,n
	​

	​

.

Using it for both modes gives

∣
V
i,n
	​

(t)
V
i,r
	​

(t)∣
∣t∣
	​

≤C
i,n,r
	​

(1+∣t∣)
−3/2
,

which is integrable on R. The proof therefore pays the square-root frequency loss without an unproved logarithmic kernel estimate and without a uniform-in-mode assertion. [LEAN][DERIVED][ABSTRACT]

Tail x>1

The harness proves

∣K
reg
	​

(t,x)∣≤(1−e
−2
)
−1
(e
−2x
+e
−x/2
),

uniformly in t. The right side is integrable on (1,∞), while the unweighted product of the two fixed Fourier modes is L
1
(dt) by Hölder L
2
×L
2
→L
1
. [LEAN][DERIVED][ABSTRACT]

Exact coverage

The near carrier is built on Ioc 0 1, the tail carrier on Ioi 1, and the proof uses the literal identity

(0,1]∪(1,∞)=(0,∞).

There is no uncovered junction and no duplicated endpoint obligation. The final measure is converted back to

lean
volume.prod (volume.restrict (Set.Ioi 0))

rather than a merely equivalent prose domain. [LEAN][DERIVED][ABSTRACT]

No mathematical defect was found in the cancellation, exponent, frequency, measure, or sesquilinear orientation.

3. Exact released production contract

The owned file is:

q3.lean.aristotle/Q3/Proofs/RouteB/
D0PstarSourceArchKernelModeProductL1.lean

The exact module preamble is:

lean
import Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel
import Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

[LEAN][CONDITIONAL]

Public definition
lean
def sourceArchimedeanKernelModeIntegrand
    (i : PairIndex) (n r : ℤ) (p : ℝ × ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) p.1) *
    (sourceArchimedeanRegularizedKernel p.1 p.2 : ℂ) *
    𝓕 (logWindowZeroExtendedMode i r) p.1

[LEAN][ABSTRACT]

Public theorem
lean
theorem sourceArchimedeanKernelModeIntegrand_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceArchimedeanKernelModeIntegrand i n r)
      (volume.prod (volume.restrict (Set.Ioi 0)))

[LEAN][ABSTRACT]

No hypothesis may be added. The theorem may not be weakened to iterated fiberwise integrability, IntegrableOn on an unnamed set, an almost-everywhere modified kernel, or an envelope in place of the exact kernel. [ABSTRACT][CONDITIONAL]

4. Private-support ceiling

The authoritative harness contains exactly:

YAML
private_definitions:
  - pairedNumerator
  - pairedDenominator
  - fixedModeNormProduct
  - fixedModeDecayConstant

private_theorems:
  - abs_one_sub_cos_le_two_mul_sqrt_abs
  - two_mul_exp_neg_two_mul_le_one_sub_exp_neg_two
  - pairedDenominator_pos
  - sourceArchimedeanRegularizedKernel_eq_paired
  - abs_pairedNumerator_le_den_add_oscillation
  - sourceArchimedeanRegularizedKernel_norm_le_near
  - sourceArchimedeanRegularizedKernel_norm_le_tail
  - integrableOn_one_Ioc_zero_one
  - integrableOn_inv_sqrt_Ioc_zero_one
  - integrableOn_tailMajorant_Ioi_one
  - logWindowZeroExtendedMode_integrable_local
  - fourier_logWindowZeroExtendedMode_memLp_two_local
  - fixedModeNormProduct_integrable
  - fixedModeDecayConstant_nonneg
  - fixedModeNormProduct_mul_sqrt_frequency_integrable
  - sourceArchimedeanKernelModeIntegrand_aestronglyMeasurable
  - sourceArchimedeanKernelModeIntegrand_integrable_near
  - sourceArchimedeanKernelModeIntegrand_integrable_tail

[LEAN][DERIVED]

The production ceiling is exactly 22 private declarations: at most four definitions and eighteen theorems. Semantics-preserving reduction is allowed. Any additional helper requires a new release because it would mean the authoritative compiling proof was not materialized as represented. [ABSTRACT][CONDITIONAL]

5. K6 object precommit
YAML
K6_OBJECT_PRECOMMIT:
  first_coordinate:
    name: t
    meaning: Mathlib_cycles_per_unit_Fourier_frequency
    measure: volume

  second_coordinate:
    name: x
    meaning: positive_regularized_hyperbolic_variable
    measure: volume_restrict_Ioi_zero

  exact_product_measure:
    volume.prod(volume.restrict(Ioi_zero))

  first_mode:
    index: n
    slot: antilinear
    operation: complex_conjugation

  second_mode:
    index: r
    slot: linear

  kernel:
    object: sourceArchimedeanRegularizedKernel
    source: proved_B3_0E1
    frequency_scale: cos_two_pi_t_x
    paired_endpoint_cancellation: retained

  theorem_scope:
    i_n_r: fixed_but_universally_quantified
    uniform_in_i_n_r: false
    cofinal_bound: false

  proved_meaning:
    exact_joint_absolute_integrability: true
    Fubini_carrier_available: true

  explicitly_not_precommitted:
    - a_public_Fubini_equality
    - cosine_correlation_equals_ccmQKernel
    - endpoint_half_factor
    - ccmWRIntegrand_identity
    - ccmWREntry_crosswalk
    - full_source_Weil_form
    - associated_operator_graph
    - form_or_operator_domain_membership
6. Mandatory plants
P057_B3_0E2_1_ANTILINEAR_FIRST

Mutation:

conj(Fourier_n) * kernel * Fourier_r

to either:

Fourier_n * kernel * Fourier_r

or:

Fourier_n * kernel * conj(Fourier_r).

Required stop:

SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

This is a source-statement fingerprint; a wrongly oriented integrability theorem might still compile. [C04] [ABSTRACT][CONDITIONAL]

P057_B3_0E2_2_PAIRED_ENDPOINT

Mutation: dominate

e
x
−e
−x
e
x/2
cos(2πtx)
	​

and
e
x
−e
−x
e
−x
	​


separately near zero.

Required stop:

SOURCE_ARCH_REGULARIZATION_CANCELLATION_DROPPED

Each separated term has a nonintegrable 1/x-scale singularity. [C09] [DERIVED][ABSTRACT]

P057_B3_0E2_3_SQRT_ENDPOINT

Mutation: replace the near endpoint carrier x
−1/2
 by x
−1
, or remove the theorem establishing integrability of x
−1/2
 on Ioc 0 1.

Required stop:

SOURCE_ARCH_ENDPOINT_L1_EXPONENT_MISSING

[LEAN][ABSTRACT]

P057_B3_0E2_4_MODE_DECAY_PAYS_FREQUENCY

Mutation: use only one fixed-mode inverse-linear decay while bounding the second transform uniformly.

The resulting frequency scale is only

∣t∣
	​

/(1+∣t∣),

which is not L
1
 at infinity.

Required stop:

SOURCE_ARCH_FREQUENCY_MAJORANT_NOT_L1

[DERIVED][ABSTRACT]

P057_B3_0E2_5_LITERAL_POSITIVE_X_MEASURE

Mutation:

replace Ioi 0 by univ, Ici 0, a centered domain, or an unnamed equivalent set;

drop the exact near/tail union;

swap the product coordinates without transporting the definition.

Required stop:

SOURCE_ARCH_POSITIVE_X_PRODUCT_MEASURE_MISMATCH

[C04] [LEAN][ABSTRACT]

P057_B3_0E2_6_NO_GENERATED_BACKEND

Mutation: import generated PSD, Step33, hbox, numerical payload, or Aristotle-output support.

Required stop:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

[SOURCE][LEAN]

P057_B3_0E2_7_JOINT_NOT_FIBERWISE

Mutation: replace joint Integrable on the product measure by separate statements of the form

for every x, integrable in t;
for every t, integrable in x.

Required stop:

SOURCE_ARCH_JOINT_FUBINI_CARRIER_MISSING

Separate fiberwise integrability does not provide the absolute product-measure carrier required for Fubini. [ABSTRACT][CONDITIONAL]

7. Validation gates

Production success requires:

Bash
test "$(git rev-parse HEAD)" = \
  "3c3681f1a93d1115d26002ff2105fc0b6c0023d1"

test "$(git rev-parse origin/rh_clean)" = \
  "3c3681f1a93d1115d26002ff2105fc0b6c0023d1"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchKernelModeProductL1.lean

lake build Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchKernelModeProductL1.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

[LEAN][CONDITIONAL]

Additional gates:

files:
  create exactly one production Lean file;
  modify no B3.0A/B/C/D/E1 parent file;

imports:
  exactly four direct imports;
  no new generated PSD/Step33/hbox/payload/Aristotle dependency;

surface:
  exactly one public definition;
  exactly one public theorem;
  exactly four private definitions maximum;
  exactly eighteen private theorems maximum;
  no other declaration;

taint:
  no sorry;
  no admit;
  no exact?;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;

plants:
  all seven plants fire;
  no plant changes either public declaration;
  all mutation artifacts removed;

axioms:
  #print axioms
    Q3.RouteB.D0Pstar.sourceArchimedeanKernelModeIntegrand

  #print axioms
    Q3.RouteB.D0Pstar.sourceArchimedeanKernelModeIntegrand_integrable

  require exactly:
    [propext, Classical.choice, Quot.sound];

observability:
  proof DB records all 24 declarations as proved;
  strict Spine PASS;
  all three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view, and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after all proof and semantic gates pass.

[LEAN][CONDITIONAL]

The three final #print axioms lines from the scratch pattern are audit commands and must not remain in the production module. [LEAN][CONDITIONAL]

8. Exact semantic boundary after success

B3.0E2 success proves that for every fixed PairIndex i and integer modes n,r,

(t,x)⟼
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

(t)

belongs to

L
1
(R
t
	​

×(0,∞)
x
	​

,dtdx).

[ABSTRACT][LEAN]

This supplies the absolute carrier needed to apply the Bochner Fubini theorem to this exact integrand. It does not itself materialize a public swapped-integral identity. [ABSTRACT][LEAN]

Success does not prove:

the value of either iterated integral;

the Fourier-mode cosine correlation formula;

equality with ccmQKernel;

truncation of the correlation at x=L
m
	​

(i);

the one-sided half-factor;

the endpoint logarithmic constant;

equality with ccmWRIntegrand or ccmWREntry;

the full source Weil-form decomposition;

a source-associated operator graph;

a uniform or cofinal estimate;

any coarse Goal-057 checkpoint.

[ABSTRACT][CONDITIONAL]

Accordingly:

B3.0E2:
  CLOSED after production validation.

B3.0E:
  OPEN.

ledger:
  0 closed / 10 remaining.
9. Exact smallest B3.0E3 atom

The exact next atom is:

GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL

The source CCM kernel is piecewise explicit: on the diagonal it is

2
L
L−x
	​

cos(
L
2πnx
	​

),

and off the diagonal it is the corresponding sine-difference quotient. [SOURCE][LEAN]

The smallest exact target is one piecewise theorem:

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

[ABSTRACT][CONDITIONAL]

The factor 2 is load-bearing. At x=0, Plancherel gives the orthonormal-mode Kronecker value 1, while ccmQKernel L n r 0 equals 2 on the diagonal and 0 off it. [DERIVED][ABSTRACT]

For 0≤x≤L, the cosine multiplier averages the two translations of the zero-extended window and produces the exact overlap kernel. For x>L, both translated overlaps are empty, so the correlation is zero even though the algebraic CCM formula is not intended as an unrestricted tail formula. [DERIVED][ABSTRACT]

The next discriminator is:

B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT

Its mandatory controls are:

YAML
central_diagonal:
  x: 0
  n_equals_r: true
  expected: left_equals_2_and_ccmQKernel_equals_2

central_offdiagonal:
  x: 0
  n_equals_r: false
  expected: both_zero

interior_offdiagonal:
  domain: 0_lt_x_lt_L
  purpose: catch_sine_difference_sign_and_n_r_order

right_boundary:
  x: L
  expected: zero

outside_window:
  domain: L_lt_x
  expected: zero_correlation

[ABSTRACT][CONDITIONAL]

Binary outcome:

PASS:
  return in the same chat for one B3.0E3 production release.

FAIL by factor, sign, translation, support, or index mismatch:
  retain B3.0E;
  do not attempt one-sided endpoint assembly;
  repair the mode-correlation representation first.

B3.0E3 production is not authorized by this verdict.

10. Strongest attack

The child proves only joint integrability. Calling it a Fubini transaction may overstate its mathematical effect.

Correct. The released classification is therefore:

JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_CARRIER

not:

SOURCE_ARCH_PAIRING_FUBINI_CROSSWALK.

[ABSTRACT][DERIVED]

The theorem makes Fubini legally available for the exact integrand. It does not prove that the swapped inner integral is ccmQKernel, that the x>L part assembles correctly, or that CCM’s endpoint constant emerges. Any closeout claiming those consequences fails under C10. [ABSTRACT][CONDITIONAL]

A second attack is that the near estimate is deliberately coarse and grows like 
∣t∣
	​

. That is harmless only because both literal fixed modes contribute inverse-linear Fourier decay. The result is fixed-mode, not uniform in the mode indices or cell. Removing either decay estimate destroys the L
1
 frequency budget. [LEAN][DERIVED][ABSTRACT]

11. Meta closeout

What became smaller?
The Fubini wall is reduced from an unverified interchange to one exact joint-L
1
 theorem on the literal product measure. [LEAN][DERIVED]

What was killed?
The claim that a sharper logarithmic kernel estimate is required; factorwise endpoint domination; one-mode-only payment of the frequency cost; and fiberwise integrability as a substitute for a joint carrier. [LEAN][DERIVED]

What must not be tried again?
Do not exchange the t- and x-integrals using only separate fiber estimates. Do not identify the resulting cosine correlation with ccmQKernel before the factor-two, support, and index-orientation theorem passes. [ABSTRACT][CONDITIONAL]

Current smallest named gap:

GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL

Next cheapest decisive test:

B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT

Prior prediction fate:

Parent discriminator:
  a cancellation-preserving joint-L1 majorant either exists or the route
  shifts to a source-distribution action.

Fate:
  PASS_CONFIRMED.

Provisional prediction:
  a sharper logarithmic kernel bound is needed.

Fate:
  REFUTED.
  The square-root endpoint/frequency bound is sufficient.

Registered endpoint risk:
  splitting the two singular terms destroys integrability.

Fate:
  CONFIRMED_AND_AVOIDED.
YAML
iteration:
  target: GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI
  status: PROGRESS
  failed_strategy: seek_a_sharper_logarithmic_kernel_bound_before_testing_the_actual_product
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL
  invariant_learned: paired_endpoint_cancellation_two_mode_decay_and_literal_product_measure_are_jointly_load_bearing
  forbidden_future_move: infer_ccmQKernel_or_ccmWREntry_from_joint_integrability_alone
  next_decisive_test: B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT
  progress_class: PROOF_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 3c3681f1a93d1115d26002ff2105fc0b6c0023d1
  require_origin_equal: true
  request_sha256: 737d65801a9ecbeef6aa7c4312aecef7a72be46b2a427191c88537a3a2d15c6f
  request_git_blob: a893497863cd95bbc90579386d904e89ac105f65
  harness_sha256: 1ff1ef467028a6a62a9d2722c2b96e0ec6aff94366645e32bab91ff5f82f7bde
  harness_bytes: 27927
  harness_lines: 696

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchKernelModeProductL1.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel
  - Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
  - Mathlib.MeasureTheory.Integral.Prod
  - Mathlib.Analysis.SpecialFunctions.Integrability.Basic

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness
  - retain its namespace and module scopes exactly
  - omit only the two final #print axioms commands
  - add no public declaration
  - make no mathematical proof change unless required by production path resolution
  - record every deviation from the authoritative harness

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanKernelModeIntegrand
  theorems:
    - sourceArchimedeanKernelModeIntegrand_integrable
  total_public_declarations: 2

PRIVATE_SUPPORT:
  maximum_definitions: 4
  maximum_theorems: 18
  maximum_total: 22
  additional_private_declarations: forbidden
  reduction_allowed: true
  public_promotion: forbidden

PUBLIC_DEFINITION_EXACT: |
  def sourceArchimedeanKernelModeIntegrand
      (i : PairIndex) (n r : ℤ) (p : ℝ × ℝ) : ℂ :=
    conj (𝓕 (logWindowZeroExtendedMode i n) p.1) *
      (sourceArchimedeanRegularizedKernel p.1 p.2 : ℂ) *
      𝓕 (logWindowZeroExtendedMode i r) p.1

PUBLIC_THEOREM_EXACT: |
  theorem sourceArchimedeanKernelModeIntegrand_integrable
      (i : PairIndex) (n r : ℤ) :
      Integrable (sourceArchimedeanKernelModeIntegrand i n r)
        (volume.prod (volume.restrict (Set.Ioi 0))) := by
    ...

MANDATORY_SEMANTICS:
  - first coordinate is Fourier frequency t
  - second coordinate is positive hyperbolic variable x
  - first mode n is conjugated
  - second mode r is linear
  - use the exact B3_0E1 regularized kernel
  - preserve paired endpoint cancellation
  - retain the x^(-1/2) near carrier
  - pay sqrt(abs(t)) with both fixed-mode inverse-linear decays
  - retain the exact product measure
  - claim joint L1 only

MANDATORY_PLANTS:
  - id: P057_B3_0E2_1_ANTILINEAR_FIRST
    required_stop: SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH

  - id: P057_B3_0E2_2_PAIRED_ENDPOINT
    required_stop: SOURCE_ARCH_REGULARIZATION_CANCELLATION_DROPPED

  - id: P057_B3_0E2_3_SQRT_ENDPOINT
    required_stop: SOURCE_ARCH_ENDPOINT_L1_EXPONENT_MISSING

  - id: P057_B3_0E2_4_MODE_DECAY_PAYS_FREQUENCY
    required_stop: SOURCE_ARCH_FREQUENCY_MAJORANT_NOT_L1

  - id: P057_B3_0E2_5_LITERAL_POSITIVE_X_MEASURE
    required_stop: SOURCE_ARCH_POSITIVE_X_PRODUCT_MEASURE_MISMATCH

  - id: P057_B3_0E2_6_NO_GENERATED_BACKEND
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

  - id: P057_B3_0E2_7_JOINT_NOT_FIBERWISE
    required_stop: SOURCE_ARCH_JOINT_FUBINI_CARRIER_MISSING

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
  - full lake build
  - scripts/q3_check.sh on the production file
  - routeb_status.py --check
  - exact public surface 1_definition_1_theorem
  - exact private ceiling 4_definitions_18_theorems
  - forbidden-token scan
  - direct and transitive generated-backend audit
  - run all seven plants without changing the public statements
  - remove every mutation artifact
  - print axioms for both public objects
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
  - SOURCE_ARCH_JOINT_KERNEL_MODE_PRODUCT_L1_PROVED
  - EXACT_ANTILINEAR_FIRST_ORIENTATION_RETAINED
  - PAIRED_ENDPOINT_CANCELLATION_RETAINED
  - EXACT_POSITIVE_X_PRODUCT_MEASURE_RETAINED
  - FUBINI_CARRIER_ONLY
  - NO_PUBLIC_SWAPPED_INTEGRAL_IDENTITY
  - B3_0E2_CLOSED
  - B3_0E_OPEN
  - NO_MODE_CORRELATION_CCM_QKERNEL_CROSSWALK
  - NO_ONE_SIDED_HALF_FACTOR_ASSEMBLY
  - NO_CCM_WR_ENTRY_CROSSWALK
  - NO_SOURCE_WEIL_FORM_DECOMPOSITION
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - NO_UNIFORM_COFINAL_MODE_BOUND
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_CARRIER_MISSING

SUCCESS:
  GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_CARRIER_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0E3_in_this_transaction
  - state_the_mode_correlation_ccmQKernel_theorem
  - perform_one_sided_CCM_endpoint_assembly
  - state_the_final_negative_ccmWREntry_crosswalk
  - modify_any_B3_0_parent_file
  - widen_any_parent_public_surface
  - replace_joint_integrability_by_fiberwise_integrability
  - split_the_regularized_kernel_into_nonintegrable_endpoint_terms
  - infer_any_uniform_or_cofinal_mode_bound
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
