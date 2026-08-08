STATUS: OPEN — CANDIDATE A RELEASED AFTER A MANDATORY FOURIER-COORDINATE REPAIR
YAML
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_REPAIRED
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_REPAIRED
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_RELEASE_2026-08-08.md
    expected_sha256: 4b4ea792a8040b7cca92b81bed5edde9ec096c529a4c71c46b2aa7803e1d6876
    observed_sha256: 4b4ea792a8040b7cca92b81bed5edde9ec096c529a4c71c46b2aa7803e1d6876
    expected_bytes: 10501
    observed_bytes: 10501
    expected_lines: 336
    observed_lines: 336
    status: PASS

  PACKAGE_HEAD:
    expected: 3cb6a391182d28568d95bad42a79f5e0c715bcf4
    observed_origin_rh_clean: 3cb6a391182d28568d95bad42a79f5e0c715bcf4
    status: PASS

  MATHEMATICAL_SOURCE_LOCK:
    commit: c3885e03b67c9cf8c6361d3d451c1404ca565709
    commit_exists: true
    package_is_one_commit_ahead: true
    source_files_unchanged_by_package_commit: true

  PARENT_B3_0B1:
    result: GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2_PROVED
    file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean
    recorded_sha256: beb6f951a5b3db4a0b234137a61e9968696f77ba53393419fabdeed239262c87
    retained: true
    reopened: false

  TEMP_SCALING_AUDIT:
    reported_compile: PASS
    exact_bytes_available: false
    independently_rehashed: false
    mathematical_identity_independently_verified_from_production_definitions: true

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

CANDIDATES:
  A_DIRECT_MINIMAL_ROUTE_B_DERIVATION:
    status: SELECTED_AFTER_COORDINATE_REPAIR
    bounded_executable: true

  B_IMPORT_STEP33_BACKEND:
    status: KILLED_AS_PRODUCTION_DEPENDENCY
    code: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
    theorem_shape_evidence_may_be_read: true

  C_REFACTOR_GENERIC_CORE:
    status: DEFERRED
    reason: >-
      Direct Route B proof duplicates only a bounded comparison argument,
      not the generated Step33 payload machinery.

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
  - Q3.DigammaRemainder

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions:
    - sourceArchimedeanMultiplier
  theorems:
    - sourceArchimedeanMultiplier_eq_neg_aStar_scaled
    - abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope
  public_declarations_total: 3

CONSTANT_POLICY:
  mode: explicit
  value: "|Real.log Real.pi| + Real.log 4 + 7"
  numerical_fit: forbidden
  premise_supplied_constant: forbidden

IMMEDIATE_MEMLP_COROLLARY:
  disposition: NEXT_CHILD
  reason: >-
    Pointwise domination is bounded in the requested two-import file.
    The exact-symbol MemLp transfer additionally needs an
    AEStronglyMeasurable/continuity supplier for the exact multiplier;
    that is not definitional bookkeeping under this exact import boundary.
  next_child: GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER

STOP_CODE:
  GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_MISSING

SUCCESS_CODE:
  GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER

CHECKPOINT_EFFECT:
  closed_integer: 0
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  checkpoints_remaining: 10
  parent_B3_0B_closed: false

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

PHASE:
  six_field_phase_key_change: false
  same_living_chat: true
  new_chat: false

ROUTE: CHALLENGER_NOT_RH
ACTIVE_BUS_GOAL: 057
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
H4A1B: OPEN
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
Source-lock ruling

The attachment matches the required SHA-256, byte count, and line count exactly. The published branch tip is exactly 3cb6a391182d28568d95bad42a79f5e0c715bcf4; its sole mathematical parent is the stated B3.0B1 source lock c3885e03b67c9cf8c6361d3d451c1404ca565709. The package commit adds the request and audit note but does not alter the mathematical source files under review. 

PROSHKA_REQUEST_GOAL057_B3_0B2_…

 [ABSTRACT][PAPER]

The Arsenal mandate is accepted. The deck was fetched, and its byte-exact materialization ledger records the mandated SHA-256 and the twelve-card inventory. [ABSTRACT][PAPER]

The production definitions are exactly:

a
⋆
	​

(ξ)=2π(logπ−ℜψ(
4
1
	​

+iπξ)),

and the foundational theorem supplies the global Stieltjes remainder on every z with ℜz>0. [ABSTRACT][LEAN]

Therefore the newly found supplier is real, global, and sufficient for a bounded Candidate-A transaction.

Mandatory coordinate repair

The proposed definition in the request,

lean
-log π + Re ψ(1/4 + i*t/2),

is the source symbol in the paper’s angular-frequency variable s, whose Fourier kernel is e
−isx
.

B3.0A and B3.0B1 use Mathlib’s Fourier variable t, whose kernel is:

e
−2πixt
.

The source form uses

∫
R
	​

∣
f
	​

(s)∣
2
2π
h
+
	​

(s)
	​

ds,h
+
	​

(s)=−logπ+ℜψ(
4
1
	​

+
2
is
	​

).

After the exact substitution s=2πt, the multiplier acting on the production Mathlib transform is:

m
arch
	​

(t)=h
+
	​

(2πt)=−logπ+ℜψ(
4
1
	​

+iπt)=−
2π
a
⋆
	​

(t)
	​

.
	​


The source’s angular-frequency formula and the production Mathlib kernel are both explicit. [ABSTRACT][PAPER] [ABSTRACT][LEAN]

Accordingly, the request’s temporary theorem

h
+
	​

(s)=−
2π
a
⋆
	​

(s/(2π))
	​


is correct, but it is oriented opposite to the direct B3.0B1 consumer. Using h
+
	​

(t) directly beside 𝓕 ... t would pair the same coordinate name with two different frequency laws.

That is a C04 same-coordinates/two-laws defect. It is repairable locally and does not kill Candidate A.

Exact released public surface
1. Actual multiplier in production Fourier coordinates
lean
/--
The source archimedean multiplier in the same frequency coordinate used by
Mathlib's Fourier kernel `exp (-2 * pi * I * x * t)`.

This equals the paper's angular-frequency multiplier `hPlus` evaluated at
`2 * pi * t`.
-/
def sourceArchimedeanMultiplier (t : ℝ) : ℝ :=
  -Real.log Real.pi +
    (Q3.digamma
      ((1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ))).re

[ABSTRACT][LEAN]

2. Exact normalization theorem
lean
theorem sourceArchimedeanMultiplier_eq_neg_aStar_scaled
    (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Q3.a_star t / (2 * Real.pi) := by
  ...

[ABSTRACT][LEAN]

This is the direct-consumer orientation. The inverse statement from the temporary audit may remain a private corollary; it does not need a second public name.

3. Global explicit domination
lean
theorem abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope
    (t : ℝ) :
    |sourceArchimedeanMultiplier t| ≤
      (|Real.log Real.pi| + Real.log 4 + 7) *
        vModeLogGrowthEnvelope t := by
  ...

where B3.0B1 already fixes:

lean
vModeLogGrowthEnvelope t = 1 + Real.log (2 + |t|)

and explicitly states that this envelope is not the exact symbol. [ABSTRACT][LEAN]

No public existential constant, arbitrary symbol, source-form premise, or tail threshold is permitted.

Minimum proof route

Let

z
t
	​

=
4
1
	​

+iπt.
1. Right-half-plane premise

Prove directly:

ℜz
t
	​

=
4
1
	​

>0.

Then instantiate:

lean
Q3.re_digamma_remainder_bound_stieltjes z_t hz

The domain premise remains visible. It may be discharged by norm_num or simp, but it may not disappear from the mathematical proof object.

2. Uniform lower norm bound

From

∣ℜz
t
	​

∣≤∥z
t
	​

∥,

obtain:

4
1
	​

≤∥z
t
	​

∥.

Consequently:

	​

2∥z
t
	​

∥
2
ℜz
t
	​

	​

	​

≤2,
4∥z
t
	​

∥
2
1
	​

≤4.

Thus the two non-logarithmic Stieltjes terms cost at most 6.

3. Global logarithm bound

Use the triangle inequality and π<4 to obtain a coarse global upper estimate:

∥z
t
	​

∥≤
4
1
	​

+π∣t∣≤4(2+∣t∣).

Together with ∥z
t
	​

∥≥1/4, this gives:

∣log∥z
t
	​

∥∣≤log4+log(2+∣t∣).

This step covers t=0, the entire compact region, and both tails. There is no eventual or asymptotic quantifier.

4. Final triangle ledger

The Stieltjes remainder yields:

∣m
arch
	​

(t)∣≤∣logπ∣+6+log4+log(2+∣t∣).

Since

vModeLogGrowthEnvelope(t)=1+log(2+∣t∣)≥1,

the explicit constant

C
arch
	​

=∣logπ∣+log4+7

gives the released theorem.

No numerical evaluation of C
arch
	​

 is part of the proof.

Candidate disposition
Candidate A — selected after repair

The global Stieltjes supplier reduces the proof to one elementary norm/log comparison. This is a bounded, source-faithful production child. [ABSTRACT][CONDITIONAL]

Candidate B — killed as a Route B dependency

The Step33 backend contains useful proof-shape evidence and already consumes the same Stieltjes theorem, but it imports generated payload, dictionary, hbox, and PSD-specific modules. Route B importing it would reverse the dependency layering.

Required code:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

Its theorem may be inspected; its module may not become a production import.

Candidate C — deferred

A common core refactor would be sensible only if both clients needed substantial shared machinery. Here the direct Route B theorem needs only:

the foundational Stieltjes remainder;

elementary norm bounds;

an elementary log comparison.

Refactoring the 9,107-line backend first would widen the transaction without reducing the current mathematical gap.

Why the immediate MemLp corollary is deferred

B3.0B1 proves:

lean
MemLp
  (fun t =>
    (vModeLogGrowthEnvelope t : ℂ) *
      𝓕 (logWindowZeroExtendedMode i n) t)
  2 volume

using continuity of the envelope and the pointwise Fourier transform. [ABSTRACT][LEAN]

Pointwise domination of the exact symbol is enough analytically to transfer this result. In Lean, however, MemLp.of_le_mul also requires an AEStronglyMeasurable certificate for the exact-symbol product. The exact two-import B3.0B2 boundary contains the global remainder theorem but does not import the existing production continuity theorem for a_star. That continuity theorem exists in Q3.Proofs.A_Star_Properties.lean, but adding it here would widen the dependency surface beyond the requested direct comparison child. [ABSTRACT][LEAN]

Therefore:

IMMEDIATE_MEMLP_COROLLARY: NEXT_CHILD

The exact next theorem is:

lean
theorem
    sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume

That theorem is not authorized in this transaction.

Mandatory plants
P057_B3_0B2_1_SCALE_PI_TO_HALF

Mutation:

digamma argument:
  1/4 + I*(pi*t)
→ 1/4 + I*(t/2)

while retaining the production-Mathlib-frequency theorem.

Required result:

SOURCE_ARCH_SYMBOL_SCALE_MISMATCH

This is the executable C04 plant: source angular frequency and Mathlib Fourier frequency may not share one unscaled variable.

P057_B3_0B2_2_SIGN

Mutation:

-a_star t / (2*pi)
→ +a_star t / (2*pi)

Required result:

SOURCE_ARCH_SYMBOL_SIGN_MISMATCH
P057_B3_0B2_3_ONE_SIDED_NOT_ABSOLUTE

Mutation:

|sourceArchimedeanMultiplier t| ≤ ...
→ sourceArchimedeanMultiplier t ≤ ...

Required result:

ARCH_SYMBOL_ABSOLUTE_DOMINATION_MISSING

A one-sided upper bound does not control the norm of multiplication by the symbol.

P057_B3_0B2_4_TAIL_NOT_GLOBAL

Mutation:

∀ t
→ ∀ t, T < |t| → ...

or only T < t.

Required result:

ARCH_SYMBOL_COMPACT_REGION_MISSING
P057_B3_0B2_5_NUMERIC_OR_PREMISE_CONSTANT

Mutation:

fit C from sampled values; or

introduce the desired global inequality as a hypothesis.

Required result:

ARCH_SYMBOL_SOURCE_PROOF_MISSING

This is a C09/C10 guard.

P057_B3_0B2_6_HEAVY_BACKEND_IMPORT

Mutation:

lean
import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend

Required result:

ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
P057_B3_0B2_7_ENVELOPE_AS_SYMBOL

Mutation:

sourceArchimedeanMultiplier := vModeLogGrowthEnvelope

or state their equality.

Required result:

ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL

This is the direct C10 surrogate plant.

P057_B3_0B2_8_RE_POS_ERASURE

Mutation:

Stieltjes argument:
  1/4 + I*(pi*t)
→ I*(pi*t)

or invoke the Stieltjes theorem without an explicit positive-real-part witness.

Required result:

DIGAMMA_STIELTJES_DOMAIN_PREMISE_MISSING
Validation gates

Required after materialization:

Bash
lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean

lake build Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

Additional mandatory gates:

source:
  verify implementation starts from package head 3cb6a391...;
  verify parent mathematical files match source lock c3885e03...;

public surface:
  exactly 1 definition + 2 theorems;
  every helper private;

imports:
  exactly the two released imports;
  no PSD_CenteredCoeffAnalyticABoundsBackend;
  no generated Step33 supplier transitively introduced by the new file;

taint:
  no sorry;
  no admit;
  no exact?;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;
  no aristotle_output;
  no ACTIVE RequestProject import;

plants:
  all 8 fire;
  no plant changes the public target statement;
  all mutation files removed;

axioms:
  #print axioms sourceArchimedeanMultiplier_eq_neg_aStar_scaled
  #print axioms abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope
  exact expected set:
    [propext, Classical.choice, Quot.sound];

observability:
  proof DB imports every declaration as proved;
  strict Spine PASS;
  three SQLite integrity checks;
  proof graph, taint graph, taint sources, sorry frontier,
  dependency view, and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported.
Scope after success

Success proves:

∀t∈R,∣m
arch
	​

(t)∣≤C
arch
	​

(1+log(2+∣t∣)),
	​


for the exact source archimedean multiplier in the same Fourier coordinate as the production mode transform. [ABSTRACT][LEAN]

It does not prove:

the exact-symbol-times-mode MemLp theorem;

a Plancherel carrier for arbitrary H_m;

the source Weil form;

an associated operator graph;

form-domain or operator-domain membership;

selected-trial domain membership;

finite-to-ambient compression;

the continuum numerator;

H4a1b;

any coarse checkpoint closure.

Strongest attack

The request already proved the t/(2π) crosswalk. Why alter the proposed definition?

Because that theorem uses the paper’s angular-frequency variable, while the immediate production consumer uses Mathlib’s cycles-per-unit Fourier variable. Both can be named t, both produce correct standalone formulas, and combining them without s=2πt produces a theorem about the wrong multiplier.

A proof of the requested unscaled definition could compile and still fail to advance the B3 route. That is exactly the C04 failure mode.

The repaired definition does not change the source mathematics. It performs the required coordinate transport before the public object is minted.

Final proposal

Release Candidate A with the repaired Mathlib-frequency definition, an exact a_star normalization theorem, and one explicit global domination theorem.

Registered predictions:

P057-B3.0B2-A1:
  the normalization theorem closes by unfolding and the nonzero fact pi ≠ 0.

P057-B3.0B2-A2:
  the global domination closes from the Stieltjes remainder with the explicit
  constant |log pi| + log 4 + 7; no compact/tail split is needed.

P057-B3.0B2-A3:
  the first remaining API obligation after success is exact-multiplier
  measurability for the MemLp transfer, not another special-function estimate.

Prior prediction fate:

B3.0B1 prediction:
  exact source-symbol domination remains an independent wall.

Fate:
  REFUTED AS AN API-ABSENCE CLAIM;
  CONFIRMED AS AN INDEPENDENT THEOREM BOUNDARY.

The hidden foundational Stieltjes supplier makes the theorem executable.
The previous claim that no such supplier existed is killed.
Meta closeout

What became smaller?

exact archimedean special-function wall

became one global inequality from an already proved Stieltjes remainder.

What was killed?

the claim that no global complex-digamma supplier exists;

the angular-frequency definition as the direct Mathlib-frequency multiplier;

importing the generated Step33 backend;

arbitrary or numerically fitted domination constants;

identifying the elementary envelope with the exact symbol.

What must not be tried again?

Do not multiply B3.0B1’s Mathlib Fourier transform by h
+
	​

(t) in the source angular variable. Use h
+
	​

(2πt).

Current smallest named gap after success

GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER

Next cheapest decisive test

Use the normalization theorem plus the existing a_star continuity theorem to build the exact-symbol product’s measurability certificate, then transfer B3.0B1 through the explicit pointwise domination.

YAML
iteration:
  target: GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION
  status: OPEN
  failed_strategy: treat_source_angular_frequency_and_Mathlib_Fourier_frequency_as_one_coordinate
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER
  invariant_learned: source angular frequency s equals 2*pi times the Mathlib Fourier frequency
  forbidden_future_move: combine_hPlus_t_with_Mathlib_fourier_at_t_without_rescaling
  next_decisive_test: exact_symbol_measurability_and_MemLp_transfer
  progress_class: PROOF_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_REPAIRED

MODE:
  IMPLEMENT_EXACTLY_ONE_REPAIRED_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 3cb6a391182d28568d95bad42a79f5e0c715bcf4
  require_origin_equal: true
  mathematical_parent: c3885e03b67c9cf8c6361d3d451c1404ca565709
  request_sha256: 4b4ea792a8040b7cca92b81bed5edde9ec096c529a4c71c46b2aa7803e1d6876
  parent_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean
  parent_recorded_sha256: beb6f951a5b3db4a0b234137a61e9968696f77ba53393419fabdeed239262c87

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
  - Q3.DigammaRemainder

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanMultiplier
  theorems:
    - sourceArchimedeanMultiplier_eq_neg_aStar_scaled
    - abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope
  total_public_declarations: 3

PUBLIC_DEFINITION_EXACT: |
  def sourceArchimedeanMultiplier (t : ℝ) : ℝ :=
    -Real.log Real.pi +
      (Q3.digamma
        ((1 / 4 : ℂ) +
          Complex.I * ((Real.pi * t : ℝ) : ℂ))).re

PUBLIC_NORMALIZATION_EXACT: |
  theorem sourceArchimedeanMultiplier_eq_neg_aStar_scaled
      (t : ℝ) :
      sourceArchimedeanMultiplier t =
        -Q3.a_star t / (2 * Real.pi) := by
    ...

PUBLIC_DOMINATION_EXACT: |
  theorem abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope
      (t : ℝ) :
      |sourceArchimedeanMultiplier t| ≤
        (|Real.log Real.pi| + Real.log 4 + 7) *
          vModeLogGrowthEnvelope t := by
    ...

PRIVATE_HELPERS_ALLOWED:
  - exact digamma argument real-part lemma
  - norm lower bound one_fourth_le
  - norm upper bound by four_mul_two_add_abs
  - inverse-square correction bounds
  - absolute log-norm bound
  - final triangle and envelope absorption
  - inverse angular-frequency scaling corollary

PRIVATE_HELPER_POLICY:
  all_support_private: true
  no_public_constant_definition: true
  no_public_arbitrary_symbol: true
  no_public_domination_premise: true

PROOF_ROUTE:
  - unfold the normalization theorem and close with Real.pi_ne_zero
  - set z = 1/4 + I*(pi*t)
  - prove z.re = 1/4 and z.re > 0
  - consume Q3.re_digamma_remainder_bound_stieltjes z hz
  - prove 1/4 <= norm z
  - bound the two inverse-square Stieltjes terms by 2 and 4
  - prove norm z <= 4*(2+abs t)
  - prove abs(log(norm z)) <= log 4 + log(2+abs t)
  - combine by triangle inequality
  - absorb the additive ledger into the explicit envelope constant
  - perform no tail split and use no numerical constant fitting

MANDATORY_PLANTS:
  - id: P057_B3_0B2_1_SCALE_PI_TO_HALF
    mutation: replace I*(pi*t) by I*(t/2)
    required_stop: SOURCE_ARCH_SYMBOL_SCALE_MISMATCH

  - id: P057_B3_0B2_2_SIGN
    mutation: replace negative a_star scaling by positive
    required_stop: SOURCE_ARCH_SYMBOL_SIGN_MISMATCH

  - id: P057_B3_0B2_3_ONE_SIDED_NOT_ABSOLUTE
    mutation: remove absolute value from multiplier domination
    required_stop: ARCH_SYMBOL_ABSOLUTE_DOMINATION_MISSING

  - id: P057_B3_0B2_4_TAIL_NOT_GLOBAL
    mutation: restrict domination to an eventual or one-sided tail
    required_stop: ARCH_SYMBOL_COMPACT_REGION_MISSING

  - id: P057_B3_0B2_5_NUMERIC_OR_PREMISE_CONSTANT
    mutation: fit or assume the domination constant
    required_stop: ARCH_SYMBOL_SOURCE_PROOF_MISSING

  - id: P057_B3_0B2_6_HEAVY_BACKEND_IMPORT
    mutation: import PSD_CenteredCoeffAnalyticABoundsBackend
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

  - id: P057_B3_0B2_7_ENVELOPE_AS_SYMBOL
    mutation: define the exact symbol as vModeLogGrowthEnvelope
    required_stop: ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL

  - id: P057_B3_0B2_8_RE_POS_ERASURE
    mutation: remove the positive real part by replacing 1/4 with 0
    required_stop: DIGAMMA_STIELTJES_DOMAIN_PREMISE_MISSING

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the new file
  - target lake build Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination
  - full lake build
  - scripts/q3_check.sh on the new file
  - routeb_status.py --check
  - exact public surface 1_definition_2_theorems
  - all support declarations private
  - forbidden-token scan
  - forbidden-import and transitive-dependency audit
  - all eight plants fire without public target mutation
  - remove all mutation artifacts
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database import
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status --short report

CLOSEOUT_MUST_STATE:
  - EXACT_SOURCE_ARCH_SYMBOL_GLOBAL_DOMINATION_ONLY
  - MATHLIB_FOURIER_FREQUENCY_COORDINATE
  - SOURCE_ANGULAR_FREQUENCY_EQUALS_TWO_PI_TIMES_MATHLIB_FREQUENCY
  - NO_IMMEDIATE_EXACT_SYMBOL_MEMLP
  - NO_PLANCHEREL_CARRIER
  - NO_SOURCE_WEIL_FORM
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_MISSING

SUCCESS:
  GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER

NOT_AUTHORIZED:
  - implement the B3_0B3 MemLp transfer
  - import PSD_CenteredCoeffAnalyticABoundsBackend
  - import generated Step33 payload or hbox suppliers
  - use the source angular-frequency multiplier at the unscaled Mathlib frequency
  - define the envelope as the exact symbol
  - accept or fit a domination constant
  - define SourceWeilFormDomain
  - define SourceWeilAssociatedGraph
  - define SourceWeilOperatorDomain
  - define sourceWeilAssociatedOperator
  - edit D0PstarCCMCompressedWeilAction
  - infer form-domain or operator-domain membership
  - invoke or close H4a1b
  - decrement the ten-checkpoint ledger
  - create Bus_010
  - release Goal_055
  - unfreeze G2_CCM
  - submit Aristotle
  - promote Route_B
  - make PX or RH claim
  - open a fresh chat

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
