STATUS: OPEN — GOAL 057 B3.0A EXACT MODE FOURIER FORMULA RELEASED
YAML
PRIMARY: TRY_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_RELEASE_2026-08-08.md
    expected_sha256: 98cfaba7d84611f3e4a3225b2de74e3966ba901e9d8e2d5157e2d24c5c4a7064
    observed_sha256: 98cfaba7d84611f3e4a3225b2de74e3966ba901e9d8e2d5157e2d24c5c4a7064
    bytes: 7952
    lines: 248
    status: PASS

  PREFLIGHT:
    path: q3.lean.aristotle/.scratch/Goal057B30APreflight.lean
    expected_sha256: a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0
    observed_sha256: a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0
    bytes: 4881
    lines: 146
    forbidden_token_scan: PASS
    declarations:
      public_definitions: 1
      public_theorems: 1
      private_theorems: 1
    reported_direct_Lean_exit: 0
    reported_axioms:
      - propext
      - Classical.choice
      - Quot.sound
    status: ACCEPTED_AS_BYTE_PINNED_DIRECT_LEAN_WITNESS
    production_rerun_required: true

  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: eb1c5d8cba978b7e7005819641fbabd532e3f97f
  ORIGIN_RH_CLEAN: eb1c5d8cba978b7e7005819641fbabd532e3f97f
  HEAD_ORIGIN_EQUAL: true

DECISION:
  release: AUTHORIZED
  exact_statement_repaired: false
  public_surface_expansion: false
  parent_B3_0_wall_reopened: false
  B3_0B_authorized: false
  associated_operator_graph_authorized: false

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0LogWindowMeasureTransport
  - Mathlib.Analysis.Fourier.FourierTransform

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - logWindowZeroExtendedMode
  theorems:
    - fourier_logWindowZeroExtendedMode
  total_public_declarations: 2

PRIVATE_HELPER_POLICY:
  allowed: true
  permitted_role:
    - rewrite_Mathlib_Fourier_integral_to_Icc_0_L
    - combine_source_mode_and_negative_Fourier_phase
    - prove_nonresonant_exponential_integral
    - discharge_positive_length_and_square_root_obligations
  public_promotion_forbidden: true
  statement_change_forbidden: true

STOP: GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_MISSING
SUCCESS: GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE

LEDGER_EFFECT_AFTER_SUCCESS:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  status: STRICTLY_ADVANCED_NOT_CLOSED
  delegated_checkpoints_closed: 0
  delegated_checkpoints_remaining: 10
  ten_checkpoint_count: UNCHANGED

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE:
  six_field_phase_key_change: false
  same_living_chat: true
  new_chat: false

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
Source-lock and release audit

The controlling request and direct Lean preflight were read in full from their attached bytes. Both SHA-256 values match exactly. The request limits this transaction to one production file, two public declarations, the exact displayed formula, and no B3.0B or associated-operator work. 

PROSHKA_REQUEST_GOAL057_B3_0A_E…

 [ABSTRACT][PAPER]

The live rh_clean reference is exactly:

eb1c5d8cba978b7e7005819641fbabd532e3f97f

matching the requested pin. [ABSTRACT][PAPER]

The target production file is absent at that pin, so this is a clean one-file materialization rather than an overwrite or competing implementation.

The pinned project uses Mathlib v4.26.0 at revision 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67. [ABSTRACT][LEAN]

Mathematical convention check

The source paper defines the additive log-window modes by

U
n
	​

(x)=L
−1/2
e
2πinx/L
,x∈[0,L].

[ABSTRACT][PAPER]

It also fixes the exact logarithmic isometry

κ(f)(u)=f(log(λu)),[0,L]⟶[λ
−1
,λ],d
∗
u⟼dx.

[ABSTRACT][PAPER]

Production Lean matches that source object:

lean
V_n_m i n u =
  (Real.sqrt (L_m i))⁻¹ *
    exp (2 * π * I * n *
      (log (lambda_m i * u) / L_m i)).

The carrier is Lp ℂ 2 (dStar.restrict (I_m i)), with dStar = du/u and I_m = [lambda_m⁻¹,lambda_m]. [ABSTRACT][LEAN]

Production already proves the exact scalar transport

∫
I
m
	​

	​

F(log(λ
m
	​

u))d
∗
u=∫
0
L
m
	​

	​

F(x)dx

and uses the same positive mode phase to establish V_n_m_orthonormal. [ABSTRACT][LEAN]

Pinned Mathlib defines the real Fourier transform by

Ff(t)=∫
R
	​

e
−2πixt
f(x)dx.

[ABSTRACT][LEAN]

Therefore the combined phase is exactly

e
−2πixt
e
2πinx/L
=e
2πi(n/L−t)x
.

For

f
i,n
	​

(x)=1
[0,L
m
	​

(i)]
	​

(x)L
m
	​

(i)
−1/2
e
2πinx/L
m
	​

(i)
,

the reference calculation is:

f
	​

i,n
	​

(t)=L
m
	​

(i)
−1/2
∫
0
L
m
	​

(i)
	​

e
2πi(n/L
m
	​

(i)−t)x
dx.

At resonance t=n/L
m
	​

(i),

f
	​

i,n
	​

(t)=L
m
	​

(i)
−1/2
L
m
	​

(i)=
L
m
	​

(i)
	​

.

Off resonance,

f
	​

i,n
	​

(t)=L
m
	​

(i)
−1/2
2πi(n/L
m
	​

(i)−t)
e
2πi(n/L
m
	​

(i)−t)L
m
	​

(i)
−1
	​

.

This is exactly the proposed theorem. No sign, scale, interval, or resonance mismatch was found. [ABSTRACT][LEAN]

The existing FplusConstantMode proof uses the same interval-exponential integration pattern and the same 2πi/L convention. [ABSTRACT][LEAN]

Exact released public surface

The production file must expose exactly:

lean
def logWindowZeroExtendedMode
    (i : PairIndex) (n : ℤ) : ℝ → ℂ :=
  Set.indicator (Set.Icc 0 (L_m i))
    (fun x =>
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * n *
            (x / L_m i)))

and:

lean
theorem fourier_logWindowZeroExtendedMode
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    𝓕 (logWindowZeroExtendedMode i n) t =
      if t = (n : ℝ) / L_m i then
        (Real.sqrt (L_m i) : ℂ)
      else
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          (Complex.exp
              (2 * Real.pi * Complex.I *
                (((n : ℝ) / L_m i - t) * L_m i))
            - 1) /
          (2 * Real.pi * Complex.I *
            ((n : ℝ) / L_m i - t))

[ABSTRACT][LEAN]

No public premise is permitted. In particular, the theorem may not acquire assumptions such as integrability, nonresonance, mode bounds, or a source-form hypothesis. All required positivity and nonzero facts already follow from PairIndex through logLength_pos.

Preflight ruling

The attached preflight is an acceptable direct Lean witness for release because:

its bytes match the registered hash;

its imports, namespace, public definition, and public theorem exactly match the requested child;

the only additional declaration is a private integral-rewrite theorem;

the theorem statement is unchanged;

the proof separates resonance from nonresonance;

it uses the pinned Real.fourier_eq' convention;

it contains no sorry, admit, exact?, native_decide, declared axiom, opaque, Float, or public hypothesis;

it includes #print axioms fourier_logWindowZeroExtendedMode;

the reported direct Lean run exited successfully with exactly the standard axiom triple.

The preflight remains a release witness, not the production validation itself. Codex must rerun every gate after copying or refactoring the proof into the owned production path.

Private refactoring is allowed only if the public definition and theorem remain byte-semantically identical. In particular, replacing Icc 0 L_m by a centered window, changing the Fourier sign, or simplifying the formula to a differently phased expression is not an implementation refactor.

Mandatory plants
P057_B3_0A_FOURIER_SIGN

Mutation:

exp(-2*pi*I*x*t)
→ exp(+2*pi*I*x*t)

or:

n/L_m - t
→ n/L_m + t.

The mutation moves the resonance from

t=n/L
m
	​


to

t=−n/L
m
	​

.

Required stop:

SOURCE_WEIL_FOURIER_SIGN_MISMATCH
P057_B3_0A_WINDOW_ORIENTATION

Mutation:

Icc 0 L_m
→ Icc (-L_m/2) (L_m/2)

or:

Icc (-L_m) 0

without the corresponding translation phase.

Required stop:

SOURCE_WEIL_ZERO_EXTENSION_WINDOW_PHASE_MISMATCH

The centered and uncentered windows are unitarily related, but their pointwise Fourier formulas differ by a nontrivial phase. [C04]

P057_B3_0A_MEASURE_TRANSPORT

Mutation:

x = log(lambda_m*u)
transports du to dx

instead of:

du/u to dx.

Required stop:

SOURCE_WEIL_DSTAR_TO_DX_TRANSPORT_MISMATCH

The production theorem integral_comp_logWindow_dStar fixes the Jacobian exactly; this is not a convention choice.

P057_B3_0A_DISCRETE_WEIGHT_SURROGATE

Mutation:

physicalFourierWeight

or a finite coefficient-energy sum is substituted for the continuous Fourier transform formula.

Required stop:

SOURCE_WEIL_DISCRETE_PHYSICAL_WEIGHT_NOT_ARCH_MULTIPLIER

A discrete mode energy and a continuous Fourier transform can share frequency notation while living under different laws. [C04][C10]

All four plants must fail without changing the target statement. A mutant that survives by weakening or rewriting the theorem is a failed plant harness.

Validation gate

Production success requires all of the following.

Direct and build gates
Bash
lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean

lake build Q3.Proofs.RouteB.D0PstarVModeFourierFormula

lake build
Route checker
Bash
bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean

Run the repository Route-B state checker and record exact stdout:

Bash
python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check
Surface and taint gates

Require:

public definitions:
  exactly 1.

public theorems:
  exactly 1.

all other declarations:
  private.

Scan the new file for:

sorry
admit
exact?
native_decide
axiom
opaque
Float
aristotle_output imports
ACTIVE/RequestProject imports

Every hit is a failure unless it occurs solely in an explanatory string that the repository checker explicitly permits.

Axiom gate
lean
#print axioms
  Q3.RouteB.D0Pstar.fourier_logWindowZeroExtendedMode

Required result exactly:

[propext, Classical.choice, Quot.sound]

A subset is not the requested closeout report; record the exact printed set.

Plant gate

Run all four independent semantic mutants and record:

mutation;
compile or theorem failure;
required stop code;
confirmation that the public target was not changed.

Delete every mutation artifact before closeout.

Observability gate

After the proof gates:

refresh the proof database;

require every declaration in the new file to be recorded as proved;

run the three repository SQLite integrity checks;

refresh strict Spine and require PASS;

refresh proof graph, taint graph, taint sources, sorry frontier, dependency view, and numeric-check classification;

require no stale source introduced by the new file;

run the repository-standard orchestrator test suite and record its exact pass count;

run git diff --check;

report exact git status --short.

The state and observability files are updated only after the mathematical file passes all proof gates.

Scope of success

A successful child proves:

the exact pointwise Fourier transform of one literal zero-extended source log-window mode.
	​


[ABSTRACT][LEAN]

It does not prove:

an L² Plancherel carrier equivalence;

logarithmically weighted Fourier integrability;

membership in a source Weil form domain;

membership in the associated operator domain;

the source Weil form decomposition;

a source-associated operator graph;

finite-to-ambient compression;

an actual continuum residual;

H4a1b;

any checkpoint closure.

The sole next gap is:

GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE

That next transaction is not authorized by this verdict.

Strongest attack

The theorem is only a pointwise Fourier integral of an elementary compactly supported exponential. Does it materially advance the source-associated operator route?

Yes, but only as a convention lock.

The parent B3.0 route failed because it attempted to hide the exact Fourier carrier, zero extension, source form, multiplier, and associated graph in one file. This child removes the first ambiguity: the literal source mode now has one exact continuous Fourier formula with a fixed sign, window, resonance, and normalization.

It does not solve the operator-domain problem. Its route value is that every later logarithmic-weight estimate and graph construction must consume this exact theorem rather than reconstructing a Fourier convention privately.

A file that uses this theorem to claim weighted-L
2
 integrability without a separate domination proof would be a C10 surrogate jump. A file that silently recenters the interval without carrying the translation phase would be a C04 category error.

Final proposal

Materialize the two-declaration child exactly as preflighted.

Registered predictions:

P057-B3.0A-R1:
  production direct Lean and full build pass without changing the theorem.

P057-B3.0A-R2:
  all four convention plants fire independently.

P057-B3.0A-R3:
  the next substantive obstruction is the logarithmically weighted L2
  certificate, not the elementary Fourier formula.

Prior prediction fate:

Parent prediction:
  the first implementation friction is the exact zero-extension/Fourier
  representative of the production modes.

Fate:
  CONFIRMED.

The direct preflight now removes that friction at theorem shape.
Production materialization remains pending.
Meta closeout

What became smaller?

source Weil associated-operator graph

has been reduced first to one production-ready exact formula:

F(1
[0,L]
	​

L
−1/2
e
2πinx/L
).

What was killed?

any remaining ambiguity in the Mathlib Fourier sign;

any ambiguity about the source window orientation;

any fitted normalization at resonance;

use of the discrete physical-frequency energy as the continuous Fourier transform;

reopening the six-declaration B3.0 bundle.

What must not be tried again?

Do not reconstruct this formula privately inside the weighted-L
2
 or operator-graph files. Import the production theorem.

Current smallest named gap

GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE

Next cheapest decisive test

Using the exact released formula, prove an explicit global majorant of the form

	​

f
i,n
	​

	​

(t)
	​

≤C
i,n
	​

min(1,
∣t−n/L
m
	​

(i)∣
1
	​

),

then test whether multiplication by the exact logarithmic archimedean weight is square-integrable. That test belongs to B3.0B and is not part of this release.

YAML
iteration:
  target: GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA
  status: OPEN
  failed_strategy: hide_zero_extension_Fourier_carrier_and_operator_graph_in_one_child
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE
  invariant_learned: Fourier_sign_window_measure_resonance_and_normalization_are_fixed_before_any_domain_claim
  forbidden_future_move: treat_pointwise_Fourier_formula_as_Plancheler_or_operator_domain_theorem
  next_decisive_test: exact_log_weighted_L2_majorant_from_released_formula
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: eb1c5d8cba978b7e7005819641fbabd532e3f97f
  require_origin_equal: true
  request_sha256: 98cfaba7d84611f3e4a3225b2de74e3966ba901e9d8e2d5157e2d24c5c4a7064
  preflight_sha256: a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0LogWindowMeasureTransport
  - Mathlib.Analysis.Fourier.FourierTransform

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - logWindowZeroExtendedMode
  theorems:
    - fourier_logWindowZeroExtendedMode
  total_public_declarations: 2

PUBLIC_DEFINITION_EXACT: |
  def logWindowZeroExtendedMode
      (i : PairIndex) (n : ℤ) : ℝ → ℂ :=
    Set.indicator (Set.Icc 0 (L_m i))
      (fun x =>
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * n *
              (x / L_m i)))

PUBLIC_THEOREM_EXACT: |
  theorem fourier_logWindowZeroExtendedMode
      (i : PairIndex) (n : ℤ) (t : ℝ) :
      𝓕 (logWindowZeroExtendedMode i n) t =
        if t = (n : ℝ) / L_m i then
          (Real.sqrt (L_m i) : ℂ)
        else
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            (Complex.exp
                (2 * Real.pi * Complex.I *
                  (((n : ℝ) / L_m i - t) * L_m i))
              - 1) /
            (2 * Real.pi * Complex.I *
              ((n : ℝ) / L_m i - t)) := by
    ...

PRIVATE_HELPERS:
  may_copy_or_refactor_from_preflight: true
  must_remain_private: true
  may_change_public_statement: false

MANDATORY_PLANTS:
  - id: P057_B3_0A_FOURIER_SIGN
    required_stop: SOURCE_WEIL_FOURIER_SIGN_MISMATCH
  - id: P057_B3_0A_WINDOW_ORIENTATION
    required_stop: SOURCE_WEIL_ZERO_EXTENSION_WINDOW_PHASE_MISMATCH
  - id: P057_B3_0A_MEASURE_TRANSPORT
    required_stop: SOURCE_WEIL_DSTAR_TO_DX_TRANSPORT_MISMATCH
  - id: P057_B3_0A_DISCRETE_WEIGHT_SURROGATE
    required_stop: SOURCE_WEIL_DISCRETE_PHYSICAL_WEIGHT_NOT_ARCH_MULTIPLIER

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the new file
  - target lake build for Q3.Proofs.RouteB.D0PstarVModeFourierFormula
  - full lake build
  - scripts/q3_check.sh on the new file
  - Route-B state checker
  - exact public-surface count 1_definition_1_theorem
  - forbidden-token scan
  - forbidden-import scan
  - all four plants fire without statement mutation
  - mutation artifacts removed
  - print axioms public theorem
  - require exactly [propext, Classical.choice, Quot.sound]
  - strict Spine PASS
  - proof database import
  - three SQLite integrity checks
  - graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status report

CLOSEOUT_MUST_STATE:
  - EXACT_POINTWISE_MODE_FOURIER_FORMULA_ONLY
  - NO_L2_PLANCHEREL_CARRIER
  - NO_ARCH_SYMBOL_WEIGHTED_L2_CERTIFICATE
  - NO_SOURCE_WEIL_FORM
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_MISSING

SUCCESS:
  GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE

NOT_AUTHORIZED:
  - implement_B3_0B
  - define_SourceWeilFormDomain
  - define_SourceWeilAssociatedGraph
  - define_SourceWeilOperatorDomain
  - define_sourceWeilAssociatedOperator
  - edit_D0PstarCCMCompressedWeilAction
  - treat_pointwise_formula_as_L2_Plancheler
  - claim_weighted_L2_integrability
  - infer_form_or_operator_domain_membership
  - close_H4a1b
  - decrement_ten_checkpoint_ledger
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
