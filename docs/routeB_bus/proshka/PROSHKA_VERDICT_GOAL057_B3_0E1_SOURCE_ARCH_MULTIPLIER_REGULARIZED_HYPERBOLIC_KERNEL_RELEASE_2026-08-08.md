STATUS: OPEN — B3.0E1 SCALAR HYPERBOLIC IDENTITY RELEASED FOR PRODUCTION
YAML
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  EXPECTED_HEAD: 7d1638d0d7cd538ed82baca15a11a7efb62be988
  OBSERVED_ORIGIN_HEAD: 7d1638d0d7cd538ed82baca15a11a7efb62be988
  HEAD_ORIGIN_EQUAL: true

  REQUEST_ATTACHMENT:
    observed_sha256: 2964606d9955cec6a24b9c81e3f4d8f341c50867e8e9b87bcd94927090f417d0
    observed_bytes: 5521
    observed_lines: 154
    observed_git_blob: a90afbce5944768e1b5518d5efa98081f775ceb6
    repository_git_blob: a90afbce5944768e1b5518d5efa98081f775ceb6
    exact_repo_byte_match: true

  HARNESS_ATTACHMENT:
    expected_sha256: 49425edef5c5b972d93f4f1c9f84877b4f9c23063fe736b06856cc0bae16af47
    observed_sha256: 49425edef5c5b972d93f4f1c9f84877b4f9c23063fe736b06856cc0bae16af47
    expected_bytes: 23556
    observed_bytes: 23556
    expected_lines: 597
    observed_lines: 597
    status: PASS

  REPORTED_DIRECT_LEAN:
    command: lake env lean /tmp/Goal057B3_0E1_Scratch.lean
    exit_status: 0
    stdout_stderr_sha256: f77159b262cf159480b682f7433afd1b2b3f5d75f023ca5ba2cd0876cd2fd46f
    exact_output_bytes_attached: false
    independently_rerun_by_judge: false
    ruling: ACCEPTED_AS_RELEASE_EVIDENCE_PRODUCTION_RERUN_REQUIRED

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

RELEASE:
  authorized: true
  owned_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean
  namespace: Q3.RouteB.D0Pstar
  exact_imports:
    - Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

PUBLIC_SURFACE:
  definitions:
    - sourceArchimedeanRegularizedKernel
  theorems:
    - sourceArchimedeanRegularizedKernel_integrableOn
    - sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
  total_public_declarations: 3

PRIVATE_SUPPORT_BUDGET:
  parent_provisional_maximum: 12
  exact_harness_private_definitions: 7
  exact_harness_private_theorems: 26
  exact_harness_private_total: 33
  repaired_production_maximum: 33
  additional_private_declarations_allowed: 0
  reduction_by_refactor_allowed: true
  public_or_assumption_change_allowed: false

STOP_CODE:
  GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_MISSING

SUCCESS_CODE:
  GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E1: CLOSED
  B3_0E: OPEN
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E2_WEIGHTED_FUBINI_MODE_CORRELATION_CARRIER

NEXT_DISCRIMINATOR_AFTER_PRODUCTION_VALIDATION:
  B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT

COARSE_CHECKPOINTS_CLOSED_AFTER_SUCCESS: 0
COARSE_CHECKPOINTS_REMAINING_AFTER_SUCCESS: 10
CURRENT_CHECKPOINT_EFFECT: STRICTLY_ADVANCED_NOT_CLOSED

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE_KEY_CHANGE: false
NEW_CHAT: false
OWNER_AUTHORITY_REQUIRED: false
SOLE_OWNER_GATE: PX_RH_CLAIM

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
Source-lock and harness audit

The live branch is exactly the requested commit 7d1638d0d7cd538ed82baca15a11a7efb62be988. That commit is one step after the B3.0E wall package and contains the release request, archived parent verdict, reasoning log, and insight update; it contains no production B3.0E1 Lean file. [SOURCE][ABSTRACT][PAPER]

The attached Markdown request is byte-identical to the repository request: its locally computed Git blob is a90afbce…, matching the blob recorded by the package commit. The request correctly executes the parent verdict’s sole PASS branch. 

PROSHKA_REQUEST_GOAL057_B3_0E1_…

 [SOURCE][DERIVED][ABSTRACT]

The authoritative Lean attachment matches the supplied SHA-256, byte count, and line count exactly. Independent static inspection finds one explicit import, three public declarations, 33 private declarations, and no occurrence of sorry, admit, exact?, native_decide, declared axiom, opaque, Float, generated PSD, Step33, hbox, payload, or direct aristotle_output import. [LEAN][DERIVED][ABSTRACT]

The reported direct Lean exit and axiom output are credible release evidence, but the stdout/stderr byte stream was not attached and this judge environment has no Lean toolchain. Production validation must therefore rerun the exact proof after namespace and file-path materialization. [SOURCE][CONDITIONAL][LEAN]

The standing Arsenal mandate is accepted. The relevant attacks are C04 for the frequency/change-of-variable conventions, C09 for preserving the precommitted paired regularization, and C10 for rejecting a premise-only scalar identity. [SOURCE][ABSTRACT][PAPER]

Mathematical ruling

The harness proves the correct scalar identity. There is no detected sign, scale, domain, or source-object defect. [LEAN][DERIVED][ABSTRACT]

The private paired kernel is

1−e
−u
e
−u
−e
−u/4
cos(πtu)
	​

.

After the exact substitution u=2x,

1−e
−2x
e
−2x
−e
−x/2
cos(2πtx)
	​

=−
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

Thus the production kernel

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


is exactly the negative of the paired digamma kernel after scaling. The Jacobian du=2dx then gives

∫
0
∞
	​

1−e
−u
e
−u
−e
−u/4
cos(πtu)
	​

du=−2∫
0
∞
	​

K
reg
	​

(t,x)dx.

Combining this with the exact digamma series yields

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
	​


[LEAN][DERIVED][ABSTRACT]

The minus sign and factor 2 are therefore not fitted conventions. They are forced by the exact algebraic kernel identity and the u=2x Jacobian. [LEAN][DERIVED][ABSTRACT]

The near-zero cancellation is also genuine. Each numerator term separately has a nonzero constant term and would produce a 1/u-scale divergence against 1−e
−u
∼u. Their difference vanishes to first order:

e
−u
−e
−u/4
cos(πtu)=−
4
3
	​

u+O(u
2
),

so the paired quotient has a finite removable limit. The harness formalizes this with the quotient-of-slopes extension before proving local integrability. [LEAN][DERIVED][ABSTRACT]

The fact that Lean totalizes the displayed public quotient at x=0 is harmless here: both public theorems integrate over Set.Ioi 0, and changing a function at one excluded or null point does not alter the integral. This child does not yet encode CCM’s later one-sided half-endpoint term. [LEAN][DERIVED][ABSTRACT]

Exact production contract

The owned production file is:

q3.lean.aristotle/Q3/Proofs/RouteB/
D0PstarSourceArchHyperbolicKernel.lean

Its sole explicit import is:

lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

That parent fixes the exact production multiplier

−logπ+ℜψ(
4
1
	​

+iπt)

in Mathlib’s cycles-per-unit Fourier coordinate. [SOURCE][LEAN][ABSTRACT]

The public definition is exactly:

lean
def sourceArchimedeanRegularizedKernel (t x : ℝ) : ℝ :=
  (Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) -
      Real.exp (-x)) /
    (Real.exp x - Real.exp (-x))

[LEAN][ABSTRACT]

The public integrability theorem is exactly:

lean
theorem sourceArchimedeanRegularizedKernel_integrableOn
    (t : ℝ) :
    IntegrableOn
      (sourceArchimedeanRegularizedKernel t)
      (Set.Ioi 0)

[LEAN][ABSTRACT]

The public source identity is exactly:

lean
theorem sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
    (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Real.log Real.pi -
        Real.eulerMascheroniConstant -
        2 * ∫ x in Set.Ioi 0,
          sourceArchimedeanRegularizedKernel t x

[LEAN][ABSTRACT]

No hypothesis may be added to any of these declarations. In particular, the identity may not be accepted as a premise, restricted to a tail, or replaced by an equality almost everywhere. [ABSTRACT][CONDITIONAL]

Private-support budget repair

The parent wall provisionally proposed a maximum of 12 private helpers before a proof existed. The exact compiling harness uses 33:

7 private definitions
26 private theorems

The provisional 12 is therefore superseded by an exact production maximum of 33. [SOURCE][LEAN][DERIVED]

This is not a mathematical defect and does not widen the public contract. The additional private surface makes the cancellation, near-zero extension, tail majorant, Laplace-cosine integral, geometric summation, dominated integral/series interchange, digamma-series crosswalk, and final scale transport individually auditable. Rejecting the proof solely to compress these helpers would trade inspectability for line count. [DERIVED][ABSTRACT]

Codex may reduce the private count through semantics-preserving refactoring. It may not exceed 33, introduce a new public declaration, add a premise, or hide multiple analytic steps behind a private axiom-like interface. [CONDITIONAL][LEAN][ABSTRACT]

Mandatory plants
P057_B3_0E1_1_PAIRED_ENDPOINT_CANCELLATION

Mutation: split

e
−u
−e
−u/4
cos(πtu)

and try to dominate the two quotient terms separately near u=0.

Required stop:

SOURCE_ARCH_REGULARIZATION_CANCELLATION_DROPPED

Each separated term has a nonintegrable 1/u singularity. Only the paired difference is admissible. [C09] [DERIVED][ABSTRACT]

P057_B3_0E1_2_FINAL_MINUS_AND_TWO

Mutations:

u = 2*x but omit the Jacobian 2;
remove the sign from K(t,x) = -pairKernel(t,2*x);
replace -2 by +2, -1, or +1.

Required stop:

SOURCE_ARCH_SCALAR_HYPERBOLIC_SIGN_SCALE_MISMATCH

The harness’s exact pointwise crosswalk and change-of-variable ledger must reject every mutation. [C04] [LEAN][DERIVED][ABSTRACT]

P057_B3_0E1_3_NO_GENERATED_BACKEND

Mutation: import any generated PSD, Step33, hbox, numerical payload, or consumer-specific analytic backend.

Required stop:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

The single released import is sufficient. [LEAN][ABSTRACT]

P057_B3_0E1_4_FUBINI_CARRIER

Mutation: exchange the digamma tsum and the integral without the proved norm-sum integrability and hasSum_integral_of_dominated_convergence.

Required stop:

SOURCE_ARCH_FUBINI_CARRIER_MISSING

Compilation of a formally rearranged expression is not a source theorem unless the absolute-integrability carrier survives. [LEAN][ABSTRACT]

P057_B3_0E1_5_PREMISE_SURROGATE

Mutation: assume either the scalar integral identity or the tsum/integral equality and prove only a downstream receiver.

Required stop:

SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION

This is the direct C10 plant. [ABSTRACT][CONDITIONAL]

P057_B3_0E1_6_FREQUENCY_SCALE

Mutation:

cos(pi*t*u)
→ cos(t*u/2)
→ cos(2*pi*t*u)

without the matching source/Mathlib coordinate transport.

Required stop:

SOURCE_ANGULAR_CYCLES_NORMALIZATION_MISMATCH

After u=2x, the released source kernel must contain exactly cos (2*pi*t*x). [C04] [LEAN][DERIVED][ABSTRACT]

Validation gates

Production success requires the following commands from the exact live head. [CONDITIONAL][LEAN]

Bash
test "$(git rev-parse HEAD)" = \
  "7d1638d0d7cd538ed82baca15a11a7efb62be988"

test "$(git rev-parse origin/rh_clean)" = \
  "7d1638d0d7cd538ed82baca15a11a7efb62be988"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean

lake build Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

The production file must pass these additional gates. [CONDITIONAL][LEAN]

public surface:
  exactly 1 definition + 2 theorems;

private surface:
  at most 7 definitions + 26 theorems;
  no other private declaration;

holes and taint:
  no sorry;
  no admit;
  no exact?;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;

imports:
  exactly one direct import;
  no generated PSD/Step33/hbox/payload dependency added;

plants:
  all six fire;
  none changes the released public statements;
  all mutation files removed;

axioms:
  #print axioms
    Q3.RouteB.D0Pstar.sourceArchimedeanRegularizedKernel

  #print axioms
    Q3.RouteB.D0Pstar.sourceArchimedeanRegularizedKernel_integrableOn

  #print axioms
    Q3.RouteB.D0Pstar.sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral

  require exactly:
    [propext, Classical.choice, Quot.sound];

observability:
  proof database records every declaration as proved;
  strict Spine PASS;
  three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view, and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after all proof and semantic gates pass.

The three #print axioms commands in the scratch file should not remain in the production module. Run them as temporary audit commands after the production file compiles. [CONDITIONAL][LEAN]

Exact semantic boundary after success

B3.0E1 success proves the exact global scalar representation

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

(t,x)dx

for every real t, together with integrability of the regularized kernel in x. [ABSTRACT][LEAN]

It does not prove:

joint (t,x) absolute integrability against two mode transforms;
Fubini for the mode-pairing integral;
mode correlation = ccmQKernel;
the one-sided 1/2 endpoint assembly;
sourceArchimedeanModePairing = -ccmWREntry;
the full source Weil-form decomposition;
a source-associated operator graph;
form-domain or operator-domain membership;
finite-to-ambient compression;
the continuum numerator;
H4a1b;
a coarse Goal-057 checkpoint.

[ABSTRACT][CONDITIONAL]

Accordingly:

B3.0E1:
  CLOSED after production validation.

B3.0E:
  OPEN.

ledger:
  0 closed / 10 remaining.

[ABSTRACT][CONDITIONAL]

Next discriminator

After production validation, run exactly one untracked discriminator:

B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT

Its decisive target is joint absolute integrability of

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

on

R
t
	​

×(0,∞)
x
	​


for every fixed PairIndex i and integers n,r. [ABSTRACT][CONDITIONAL]

Binary outcome:

PASS:
  B3.0E2 becomes executable in one later same-chat release.

FAIL because no cancellation-preserving product majorant exists:
  retain the B3.0E wall;
  do not exchange integrals;
  shift to the source-distribution-action representation.

[ABSTRACT][CONDITIONAL]

This verdict does not release B3.0E2.

Strongest attack

The strongest objection is that a 597-line, 33-helper proof is not a “small scalar preflight” and may merely hide the original wall inside private declarations.

The objection fails on semantics, but it changes the packaging budget. [DERIVED][ABSTRACT]

The harness does not accept the desired identity as input. It constructs:

the zero-endpoint regularization;

local and tail integrability;

the exact Laplace-cosine transform;

termwise digamma representation;

a cancellation-preserving norm summation;

the dominated integral/series interchange;

the exact digamma-series identification;

the u=2x sign and Jacobian.

Every load-bearing analytic step is inspectable and separately named. The public conclusion remains one scalar source identity. This is precisely the compression requested by the parent wall. [LEAN][DERIVED][ABSTRACT]

The private-budget overrun must not be hidden: 12 is killed as an inaccurate preflight cost estimate and replaced by the observed exact maximum 33. That is a budget repair, not theorem weakening. [SOURCE][DERIVED][ABSTRACT]

Meta closeout

What became smaller?
The first missing B3.0E source theorem is no longer a wall. It has an exact, no-premise, compiled Lean construction. [LEAN][DERIVED][ABSTRACT]

What was killed?
The claim that the digamma-to-regularized-hyperbolic identity was unavailable in the current production import closure; the provisional 12-helper estimate; factorwise near-zero domination; and premise-only repair. [SOURCE][DERIVED][ABSTRACT]

What must not be tried again?
Do not jump directly from the scalar identity to ccmWREntry. The weighted joint L
1
 carrier, mode correlation, and one-sided endpoint assembly remain separate obligations. [ABSTRACT][CONDITIONAL]

Current smallest named gap:

GOAL057_B3_0E2_WEIGHTED_FUBINI_MODE_CORRELATION_CARRIER

[ABSTRACT][CONDITIONAL]

Next cheapest decisive test:

B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT

[ABSTRACT][CONDITIONAL]

Prior prediction fate:

Parent prediction:
  the scalar digamma-to-hyperbolic theorem is the first missing formal object,
  and a no-sorry preflight decides whether Candidate 2 becomes executable.

Fate:
  CONFIRMED.

Registered failure risk:
  factorwise zero-endpoint estimates destroy cancellation.

Fate:
  CONFIRMED and avoided by the attached proof.

[SOURCE][LEAN][DERIVED]

YAML
iteration:
  target: GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL
  status: PROGRESS
  failed_strategy: factorwise_near_zero_domination_and_one_shot_final_CCM_crosswalk
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0E2_WEIGHTED_FUBINI_MODE_CORRELATION_CARRIER
  invariant_learned: paired_endpoint_cancellation_and_exact_u_equals_2x_sign_scale_must_survive_before_Fubini
  forbidden_future_move: infer_final_ccmWREntry_crosswalk_from_the_scalar_identity_alone
  next_decisive_test: B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT
  progress_class: PROOF_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 7d1638d0d7cd538ed82baca15a11a7efb62be988
  require_origin_equal: true
  request_attachment_sha256: 2964606d9955cec6a24b9c81e3f4d8f341c50867e8e9b87bcd94927090f417d0
  request_git_blob: a90afbce5944768e1b5518d5efa98081f775ceb6
  harness_sha256: 49425edef5c5b972d93f4f1c9f84877b4f9c23063fe736b06856cc0bae16af47
  harness_bytes: 23556
  harness_lines: 597

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness declarations
  - replace namespace Q3.RouteB.D0Pstar.Goal057B3_0E1Scratch with Q3.RouteB.D0Pstar
  - retain noncomputable section
  - retain open scoped Real
  - retain open Set MeasureTheory
  - omit the three final #print axioms commands from production
  - make no mathematical proof change unless required by namespace resolution
  - record every deviation from the authoritative harness

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanRegularizedKernel
  theorems:
    - sourceArchimedeanRegularizedKernel_integrableOn
    - sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
  total_public_declarations: 3

PRIVATE_SUPPORT:
  maximum_total: 33
  maximum_definitions: 7
  maximum_theorems: 26
  additional_private_declarations: forbidden
  reduction_allowed: true
  assumption_or_public_surface_change: forbidden

PUBLIC_DEFINITION_EXACT: |
  def sourceArchimedeanRegularizedKernel (t x : ℝ) : ℝ :=
    (Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) -
        Real.exp (-x)) /
      (Real.exp x - Real.exp (-x))

PUBLIC_INTEGRABILITY_THEOREM_EXACT: |
  theorem sourceArchimedeanRegularizedKernel_integrableOn
      (t : ℝ) :
      IntegrableOn
        (sourceArchimedeanRegularizedKernel t)
        (Set.Ioi 0) := by
    ...

PUBLIC_IDENTITY_THEOREM_EXACT: |
  theorem sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
      (t : ℝ) :
      sourceArchimedeanMultiplier t =
        -Real.log Real.pi -
          Real.eulerMascheroniConstant -
          2 * ∫ x in Set.Ioi 0,
            sourceArchimedeanRegularizedKernel t x := by
    ...

MANDATORY_SEMANTICS:
  - preserve paired numerator before every near-zero estimate
  - prove the removable endpoint through the quotient-of-slopes extension
  - prove the tail through an explicit integrable exponential majorant
  - prove the integral/tsum interchange by dominated convergence
  - consume the exact Q3 digamma-series theorem
  - preserve cos(pi*t*u) before u=2*x
  - preserve cos(2*pi*t*x) after u=2*x
  - preserve final minus sign and factor 2
  - introduce no premise stating the desired identity

MANDATORY_PLANTS:
  - id: P057_B3_0E1_1_PAIRED_ENDPOINT_CANCELLATION
    required_stop: SOURCE_ARCH_REGULARIZATION_CANCELLATION_DROPPED

  - id: P057_B3_0E1_2_FINAL_MINUS_AND_TWO
    required_stop: SOURCE_ARCH_SCALAR_HYPERBOLIC_SIGN_SCALE_MISMATCH

  - id: P057_B3_0E1_3_NO_GENERATED_BACKEND
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

  - id: P057_B3_0E1_4_FUBINI_CARRIER
    required_stop: SOURCE_ARCH_FUBINI_CARRIER_MISSING

  - id: P057_B3_0E1_5_PREMISE_SURROGATE
    required_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION

  - id: P057_B3_0E1_6_FREQUENCY_SCALE
    required_stop: SOURCE_ANGULAR_CYCLES_NORMALIZATION_MISMATCH

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel
  - full lake build
  - scripts/q3_check.sh on the production file
  - routeb_status.py --check
  - exact public surface 1_definition_2_theorems
  - private surface at most 7_definitions_26_theorems
  - forbidden-token scan
  - direct and transitive generated-backend audit
  - run all six plants without changing the public target statements
  - remove every mutation artifact
  - print axioms for all three public declarations
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
  - SOURCE_ARCH_SCALAR_REGULARIZED_HYPERBOLIC_IDENTITY_PROVED
  - PAIRED_ZERO_ENDPOINT_CANCELLATION_RETAINED
  - EXACT_U_EQUALS_TWO_X_MINUS_AND_JACOBIAN_RETAINED
  - B3_0E1_CLOSED
  - B3_0E_OPEN
  - NO_WEIGHTED_MODE_FUBINI_CARRIER
  - NO_MODE_CORRELATION_CCM_QKERNEL_CROSSWALK
  - NO_ONE_SIDED_HALF_FACTOR_ASSEMBLY
  - NO_CCM_WR_ENTRY_CROSSWALK
  - NO_SOURCE_WEIL_FORM_DECOMPOSITION
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_MISSING

SUCCESS:
  GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E2_WEIGHTED_FUBINI_MODE_CORRELATION_CARRIER

NEXT_DISCRIMINATOR_AFTER_SUCCESS:
  B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT

NEXT_GAP_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0E2_inside_this_transaction
  - state_or_prove_the_final_negative_ccmWREntry_crosswalk
  - modify_B3_0A_B_C_D_parent_files
  - widen_any_parent_public_surface
  - accept_the_scalar_identity_as_a_premise
  - split_the_regularized_kernel_into_nonintegrable_near_zero_terms
  - exchange_joint_mode_and_kernel_integrals_without_absolute_integrability
  - omit_or_double_the_one_sided_half_factor
  - import_generated_PSD_Step33_hbox_or_numeric_payload_support
  - define_the_full_source_Weil_form
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
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
