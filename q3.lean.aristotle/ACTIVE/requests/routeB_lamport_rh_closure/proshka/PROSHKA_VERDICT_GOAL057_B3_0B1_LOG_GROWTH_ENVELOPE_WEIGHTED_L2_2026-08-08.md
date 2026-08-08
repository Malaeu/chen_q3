STATUS: OPEN — B3.0B1 LOG-GROWTH ENVELOPE WEIGHTED-L
2
 CHILD RELEASED
YAML
PRIMARY: TRY_GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_RELEASE_2026-08-08.md
    expected_sha256: b83b7a57f97385df4b2eb7ad3bc09af3fdcc63a297a41620ba6cf2d7b54af52b
    observed_sha256: b83b7a57f97385df4b2eb7ad3bc09af3fdcc63a297a41620ba6cf2d7b54af52b
    expected_bytes: 10955
    observed_bytes: 10955
    expected_lines: 315
    observed_lines: 315
    status: PASS

  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: bd8692ced371565232c5ce8df088654fcd0a41ae
  ORIGIN_RH_CLEAN: bd8692ced371565232c5ce8df088654fcd0a41ae
  HEAD_ORIGIN_EQUAL: true

  PARENT_PRODUCTION:
    file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean
    sha256_recorded_at_pin: a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0
    bytes: 4881
    lines: 146
    result: GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_PROVED
    retained: true
    reopened: false

CANDIDATE_RULING:
  A_EXACT_SYMBOL_ONE_FILE:
    selected: false
    status: DEFERRED
    reason: EXACT_DIGAMMA_GLOBAL_DOMINATION_SUPPLIER_MISSING

  B_SPLIT_ENVELOPE_FROM_EXACT_SYMBOL:
    selected: true
    child: B3_0B1
    source_faithful: true
    closes_full_B3_0B: false

  C_PREMISE_ONLY_ARBITRARY_SYMBOL:
    selected: false
    status: KILLED_AS_PUBLIC_SOURCE_CERTIFICATE
    code: ARCH_SYMBOL_DOMINATION_PREMISE_ONLY_WRAPPER

SELECTED_TRANSACTION:
  id: GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2
  owned_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean
  namespace: Q3.RouteB.D0Pstar
  public_definitions: 1
  public_theorems: 2
  total_public_declarations: 3
  progress_class: PROOF_PROGRESS

STOP: GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2_MISSING
SUCCESS: GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_BY_LOG_GROWTH_ENVELOPE

FULL_PARENT_GAP_AFTER_B3_0B1:
  GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE
  status: OPEN_UNTIL_B3_0B2

LEDGER_EFFECT_AFTER_SUCCESS:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  checkpoint_status: STRICTLY_ADVANCED_NOT_CLOSED
  delegated_checkpoints_closed: 0
  delegated_checkpoints_remaining: 10
  ten_checkpoint_count: UNCHANGED

PHASE:
  six_field_phase_key_change: false
  same_living_chat: true
  new_chat: false

ARISTOTLE_SUBMISSION: NONE
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
Source-lock audit

The controlling attachment rehashes exactly to b83b7a57…af52b, with exactly 10,955 bytes and 315 lines. Its correction concerning totalized division at resonance is therefore part of the controlling source, not an informal addendum. 

PROSHKA_REQUEST_GOAL057_B3_0B_A…

The live rh_clean reference is exactly bd8692ced371565232c5ce8df088654fcd0a41ae. The corresponding commit is the production closeout of B3.0A. [ABSTRACT][PAPER]

The fetched parent file has the exact source mode, exact uncentered interval, exact negative Mathlib Fourier sign, and the public resonance/off-resonance formula stated in the request. [ABSTRACT][LEAN]

The Goal 057 ledger records B3.0A as a closed child with:

LEAN_SHA256 = a7cf2898…19f0
TARGET_BUILD = PASS
FULL_BUILD = PASS
Q3_CHECK = PASS
STANDARD_AXIOMS_ONLY = true
CHECKPOINTS = 0 closed / 10 remaining

and names B3.0B as the next gap requiring a new same-chat release. [ABSTRACT][PAPER]

Candidate ruling
Candidate A — exact source symbol in the same child

Not selected.

The mathematical symbol

h
+
	​

(t)=−logπ+ℜΨ(
4
1
	​

+
2
it
	​

)

is source-pinned, but the current production environment does not contain:

a source-faithful complex digamma declaration at this argument;

a theorem identifying the required derivative/log-Gamma convention;

a global explicit estimate

∣h
+
	​

(t)∣≤C(1+log(2+∣t∣)).

The request’s API audit explicitly reports this missing supplier. Bundling the digamma construction, its global domination, the mode decay theorem, and the final MemLp certificate into one file would recreate the oversized B3.0 bundle. 

PROSHKA_REQUEST_GOAL057_B3_0B_A…

 [ABSTRACT][PAPER]

This is not evidence against the multiplier route. It is a dependency boundary.

Candidate B — elementary envelope first
SELECTED
	​


B3.0B1 can be proved entirely from:

the exact released Fourier formula;

elementary exponential bounds;

elementary logarithm-versus-quarter-power bounds;

standard real-line integrability of (1+∣t∣)
−3/2
;

the standard MemLp characterization at exponent 2.

Pinned Mathlib exposes both:

lean
memLp_two_iff_integrable_sq_norm

and:

lean
integrable_one_add_norm

with the latter proving integrability of (1+∥x∥)
−r
 in dimension one for r>1. [ABSTRACT][LEAN]

This is one bounded theorem transaction.

Candidate C — arbitrary symbol plus a domination premise

Killed as a public source certificate under C10.

A theorem taking:

lean
archSymbol : ℝ → ℝ
harch : ∀ t, |archSymbol t| ≤ C * vModeLogGrowthEnvelope t

would be a valid private generic helper. It would not prove anything about the source archimedean symbol unless the same transaction also constructed that exact symbol and proved harch.

Therefore no public premise-only symbol theorem is permitted in B3.0B1.

Resonance correction

The previous candidate bound

Cmin(1,
∣t−n/L∣
1
	​

)

is false as a pointwise Lean statement.

At

t=
L
n
	​

,

Lean evaluates

∣t−n/L∣
1
	​

=
0
1
	​

=0,

so the right-hand side is zero. The parent theorem gives

	​

f
	​

i,n
	​

(
L
n
	​

)
	​

=
L
m
	​

(i)
	​

>0.

This is an exact K1 counterexample, not merely an API inconvenience. 

PROSHKA_REQUEST_GOAL057_B3_0B_A…

 [ABSTRACT][LEAN]

The released child must instead use the following global denominator:

1+∣t∣.

This avoids the resonant singularity entirely and is stronger for the subsequent integrability proof.

Exact released public surface

Owned file:

q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarVModeLogWeightedL2.lean

Exact imports:

lean
import Q3.Proofs.RouteB.D0PstarVModeFourierFormula
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.MeasureTheory.Function.L2Space

Exact namespace:

lean
namespace Q3.RouteB.D0Pstar
Public definition 1 — envelope, not symbol
lean
/--
An explicit logarithmic-growth envelope used to separate elementary
mode decay from the still-open exact Riemann--Siegel/digamma symbol bound.

This is not the source archimedean symbol.
-/
def vModeLogGrowthEnvelope (t : ℝ) : ℝ :=
  1 + Real.log (2 + |t|)

[ABSTRACT][LEAN]

The name and docstring must preserve the distinction between an envelope and the source multiplier.

Public theorem 1 — resonance-safe global decay
lean
theorem norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
      ((2 * Real.sqrt (L_m i) +
          2 / (Real.pi * Real.sqrt (L_m i))) *
        (1 + |(n : ℝ) / L_m i|)) /
      (1 + |t|) := by
  ...

[ABSTRACT][LEAN]

The theorem is deliberately not uniform in i or n. Such uniformity is neither needed nor proved in this child.

Why the bound is correct

Write

a=
L
m
	​

(i)
n
	​

,δ=t−a.

The exact Fourier integral gives the uniform estimate

∣
f
	​

i,n
	​

(t)∣≤
L
m
	​

(i)
	​

.

Away from resonance, the parent formula and

∣e
iθ
−1∣≤2

give

∣
f
	​

i,n
	​

(t)∣≤
π
L
m
	​

(i)
	​

∣δ∣
1
	​

.

Splitting into ∣δ∣≤1 and ∣δ∣>1 yields

∣
f
	​

i,n
	​

(t)∣≤
1+∣δ∣
2
L
m
	​

(i)
	​

+2/(π
L
m
	​

(i)
	​

)
	​

.

Finally,

1+∣t∣≤(1+∣a∣)(1+∣t−a∣)

produces the displayed unshifted bound.

No division by the resonant frequency occurs in the final theorem.

Public theorem 2 — logarithmically weighted L
2
lean
theorem
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (vModeLogGrowthEnvelope t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume := by
  ...

[ABSTRACT][LEAN]

This theorem concerns the exact pointwise Fourier transform already proved in B3.0A. It does not assert a Plancherel equivalence for arbitrary H_m objects.

Private-helper dependency order

All declarations below remain private.

1. Positivity and measurability
lean
vModeLogGrowthEnvelope_pos
vModeLogGrowthEnvelope_continuous
fourier_logWindowZeroExtendedMode_aestronglyMeasurable

The Fourier measurability proof may rewrite by the public B3.0A formula and use measurable piecewise algebra. It need not construct an L
2
 Fourier-transform operator.

2. Uniform Fourier bound

Prove privately:

lean
norm_fourier_logWindowZeroExtendedMode_le_sqrt

using the generic Fourier L
1
-norm bound on the compactly supported normalized mode.

3. Far-field bound

Prove privately:

lean
norm_fourier_logWindowZeroExtendedMode_le_of_one_lt_frequencyDistance

by rewriting with fourier_logWindowZeroExtendedMode, taking norms, using:

‖exp(iθ) - 1‖ ≤ 2,

and the positivity of L_m i.

4. Shifted resonance-safe decay

Combine the near and far branches:

∣
f
	​

(t)∣≤
1+∣t−n/L∣
2
L
	​

+2/(π
L
	​

)
	​

.
5. Unshifted public decay

Use:

1+∣t∣≤(1+∣n/L∣)(1+∣t−n/L∣).
6. Explicit logarithmic power bound

Privately prove a global estimate of the form

1+log(2+∣t∣)≤C
log
	​

(1+∣t∣)
1/4
,

with a concrete constant, for example

C
log
	​

=1+4⋅2
1/4
.

This can be derived from:

logy≤y−1

applied to a positive fourth root. No asymptotic or nonconstructive eventual bound is required.

7. Scalar majorant integrability

Prove privately:

lean
integrable_vModeLogGrowthEnvelope_sq_div_one_add_abs_sq

for

t⟼
(1+∣t∣)
2
(vModeLogGrowthEnvelope(t))
2
	​

.

The quarter-power bound reduces this to a constant multiple of

(1+∣t∣)
−3/2
,

which is integrable by integrable_one_add_norm because

dim
R
	​

R=1<
2
3
	​

.
8. Final MemLp

Apply:

lean
memLp_two_iff_integrable_sq_norm

and dominate the squared norm using the public decay theorem and the private scalar integrability lemma.

K6 object precommit
YAML
K6_OBJECT_PRECOMMIT:
  exact_mode:
    object: logWindowZeroExtendedMode i n
    support: Icc 0 (L_m i)
    normalization: inverse_sqrt_L_m
    source_phase: plus_2pi_I_n_x_over_L

  exact_transform:
    object: FourierTransform.fourier
    kernel_sign: negative
    measure: Lebesgue_volume
    resonance: t_equals_n_over_L
    resonance_value: sqrt_L

  envelope:
    object: vModeLogGrowthEnvelope
    formula: 1_plus_log_2_plus_abs_t
    exact_source_arch_symbol: false

  public_decay:
    denominator: 1_plus_abs_t
    frequency_shift_absorbed_into_constant: true
    uniform_in_i_or_n: false

  weighted_certificate:
    object: envelope_times_exact_pointwise_mode_transform
    exponent: 2
    measure: volume

  explicitly_not_precommitted:
    - exact_digamma_symbol
    - exact_arch_symbol_domination
    - L2_Plancheler_equivalence
    - source_Weil_form
    - associated_operator_graph
    - form_domain_membership
    - operator_domain_membership
    - finite_to_ambient_compression
    - cofinal_uniform_mode_bound
Mandatory plants
P057-B3.0B1-1 — totalized resonance

Mutation:

global RHS =
  C * min 1 (1 / |t - n/L|)

Required evaluation:

t = n/L
RHS = 0
LHS = sqrt(L) > 0

Required stop:

LOG_WEIGHT_TOTALIZED_RESONANCE_MISMATCH
P057-B3.0B1-2 — missing decay power

Mutation:

retain only the uniform bound
  ‖Fourier(mode)(t)‖ ≤ sqrt(L)

and attempt to prove the weighted MemLp theorem from it.

The resulting control function is bounded below by a positive constant times the envelope and is not square-integrable on the infinite-volume real line.

Required stop:

LOG_WEIGHT_DECAY_POWER_MISSING

A half-power denominator is also insufficient: after squaring, it leaves a nonintegrable 1/(1+∣t∣)-scale before the logarithmic factor is even charged.

P057-B3.0B1-3 — envelope relabeled as source symbol

Mutation:

vModeLogGrowthEnvelope
→ sourceArchimedeanSymbol

or any closeout claiming that B3.0B1 proves the exact symbol certificate.

Required stop:

ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL
P057-B3.0B1-4 — discrete physical weight substitution

Mutation:

physicalFourierWeight

or a finite coefficient-energy weight replaces the continuous function

1+log(2+∣t∣).

Required stop:

SOURCE_WEIL_DISCRETE_PHYSICAL_WEIGHT_NOT_ARCH_MULTIPLIER
P057-B3.0B1-5 — form/operator-domain promotion

Mutation:

weighted mode transform is MemLp 2
⇒ V_n_m ∈ SourceWeilOperatorDomain

without the exact source symbol, bounded prime/pole operators, source form, and graph identity.

Required stop:

FORM_DOMAIN_NOT_OPERATOR_DOMAIN
P057-B3.0B1-6 — exact-symbol transfer without digamma domination

Mutation:

B3.0B1 envelope certificate
⇒ exact h_+ weighted-L2 certificate

without a source-specific theorem

∣h
+
	​

(t)∣≤CvModeLogGrowthEnvelope(t).

Required stop:

SOURCE_WEIL_DIGAMMA_DOMINATION_MISSING
Validation gates

Required production validation:

Bash
lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean

lake build Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check

Surface gate:

public definitions:
  exactly 1.

public theorems:
  exactly 2.

all supporting declarations:
  private.

Forbidden-token and import scan:

sorry
admit
exact?
native_decide
axiom
opaque
Float
aristotle_output
ACTIVE/RequestProject
physicalFourierWeight
digamma premise or source-symbol premise

The string physicalFourierWeight may occur only in a rejection comment or plant fixture, not in a proof dependency.

Axiom gates:

lean
#print axioms
  Q3.RouteB.D0Pstar.norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe

#print axioms
  Q3.RouteB.D0Pstar.vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp

Required set for each theorem:

[propext, Classical.choice, Quot.sound]

Also require:

all six plants fire;

all mutation files are removed;

proof DB import records all declarations as proved;

strict Spine passes;

all three SQLite integrity checks pass;

proof graph, taint graph, taint sources, sorry frontier, dependency view, and numeric-check view are refreshed;

repository-standard orchestrator tests pass;

git diff --check passes;

exact git status --short is reported.

Scope of success

A successful B3.0B1 transaction proves:

(1+log(2+∣t∣))
f
	​

i,n
	​

(t)∈L
2
(R,dt)
	​


for every fixed literal production mode i,n. [ABSTRACT][LEAN]

It also proves a global resonance-safe O((1+∣t∣)
−1
) pointwise bound with an explicit mode-dependent constant.

It does not prove:

the envelope is the exact source symbol;
the exact digamma symbol is dominated by the envelope;
an L2 Fourier transform or Plancherel equivalence for arbitrary H_m elements;
uniform estimates in i, n, m, or N;
a source Weil form;
an associated operator graph;
form-domain membership;
operator-domain membership;
finite-to-ambient compression;
the continuum numerator;
H4a1b;
a coarse checkpoint.

For a fixed finite Galerkin trial, finite linearity can later combine the mode certificates. No cofinal or uniform bound is obtained here.

Strongest attack

B3.0B1 proves an elementary theorem about a convenient envelope, while the real source multiplier is still absent. Is this another non-source wrapper?

That objection is valid unless the boundary is kept exact.

B3.0B1 has route value because it removes the entire mode-side analytic obligation:

exact mode transform
+ logarithmic growth
→ L2.

After this child, the remaining source-special-function obligation is one sharply typed theorem:

∃C>0 ∀t∈R,
	​

−logπ+ℜΨ(
4
1
	​

+
2
it
	​

)
	​

≤C(1+log(2+∣t∣)).
	​


That theorem is B3.0B2. It cannot be replaced by a hypothesis, a fitted constant, a paper asymptotic without a global bound, or a discrete weight.

If B3.0B2 fails, B3.0B1 remains a valid analytic lemma but does not close the source route. That is why the coarse ledger does not move.

A second attack is that the majorant constant grows with the mode frequency n/L
m
	​

. Correct: B3.0B1 is not a cofinal uniform estimate. It is a fixed-mode operator-domain ingredient. Uniformity, if later required, is a separate theorem and may not be inferred from this child.

Meta closeout

What became smaller?

The B3.0B weighted-L
2
 wall is split into:

B3.0B1:
  exact mode + explicit logarithmic envelope → L2.

B3.0B2:
  exact source digamma symbol ≤ constant × envelope.

What was killed?

the totalized min(1,1/|δ|) majorant;

one-file exact-symbol bundling at the current API state;

arbitrary-symbol premise wrappers;

discrete physical weight substitution;

promotion from weighted mode integrability directly to operator domain.

What must not be tried again?

Do not write any pointwise bound that divides by the resonant frequency without either branching or adding a positive denominator. Do not call the envelope the source symbol.

Current smallest named gap after success

GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_BY_LOG_GROWTH_ENVELOPE

Next cheapest decisive test

Locate or derive a global, not merely asymptotic, bound for

−logπ+ℜΨ(
4
1
	​

+
2
it
	​

)

in the exact source normalization, and test it at t=0, the small-∣t∣ compact region, and both tails before any associated-operator declaration is reopened.

Prediction fate

Parent prediction:
  after the exact Fourier formula, the next substantive obstruction is
  the logarithmically weighted L2 certificate.

Fate:
  CONFIRMED, then split.

Mode-side envelope certificate:
  selected as executable B3.0B1.

Exact source-symbol domination:
  remains the independent B3.0B2 wall.
YAML
iteration:
  target: GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE
  status: OPEN
  failed_strategy: one_file_exact_digamma_symbol_plus_mode_decay_plus_operator_domain
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_BY_LOG_GROWTH_ENVELOPE
  invariant_learned: resonance_safe_decay_and_exact_source_symbol_domination_are_independent_obligations
  forbidden_future_move: use_totalized_reciprocal_at_resonance_or_relabel_envelope_as_exact_symbol
  next_decisive_test: global_exact_digamma_domination_source_audit
  progress_class: PROOF_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: bd8692ced371565232c5ce8df088654fcd0a41ae
  require_origin_equal: true
  request_sha256: b83b7a57f97385df4b2eb7ad3bc09af3fdcc63a297a41620ba6cf2d7b54af52b
  parent_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean
  parent_sha256: a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0PstarVModeFourierFormula
  - Mathlib.Analysis.SpecialFunctions.JapaneseBracket
  - Mathlib.Analysis.SpecialFunctions.Log.Monotone
  - Mathlib.MeasureTheory.Function.L2Space

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - vModeLogGrowthEnvelope
  theorems:
    - norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe
    - vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp
  total_public_declarations: 3

PUBLIC_DEFINITION_EXACT: |
  def vModeLogGrowthEnvelope (t : ℝ) : ℝ :=
    1 + Real.log (2 + |t|)

PUBLIC_MAJORANT_EXACT: |
  theorem norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe
      (i : PairIndex) (n : ℤ) (t : ℝ) :
      ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
        ((2 * Real.sqrt (L_m i) +
            2 / (Real.pi * Real.sqrt (L_m i))) *
          (1 + |(n : ℝ) / L_m i|)) /
        (1 + |t|) := by
    ...

PUBLIC_MEMLP_EXACT: |
  theorem
      vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp
      (i : PairIndex) (n : ℤ) :
      MemLp
        (fun t : ℝ =>
          (vModeLogGrowthEnvelope t : ℂ) *
            𝓕 (logWindowZeroExtendedMode i n) t)
        2 volume := by
    ...

PRIVATE_PROOF_ORDER:
  - envelope positivity and continuity
  - Fourier measurability from the public B3.0A formula
  - uniform sqrt_L Fourier bound
  - off-resonance inverse-frequency bound
  - resonance-safe shifted denominator bound
  - shift removal to denominator 1_plus_abs_t
  - explicit log envelope le quarter-power bound
  - integrability reduction to one_plus_abs_t rpow minus_three_halves
  - memLp_two_iff_integrable_sq_norm

MANDATORY_PLANTS:
  - id: P057_B3_0B1_TOTALIZED_RESONANCE
    mutation: global_min_one_reciprocal_frequency_bound
    required_stop: LOG_WEIGHT_TOTALIZED_RESONANCE_MISMATCH

  - id: P057_B3_0B1_DECAY_POWER
    mutation: remove_inverse_linear_decay_or_replace_by_half_power
    required_stop: LOG_WEIGHT_DECAY_POWER_MISSING

  - id: P057_B3_0B1_ENVELOPE_AS_SYMBOL
    mutation: relabel_envelope_as_exact_arch_symbol_or_claim_full_B3_0B
    required_stop: ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL

  - id: P057_B3_0B1_DISCRETE_WEIGHT
    mutation: substitute_physicalFourierWeight
    required_stop: SOURCE_WEIL_DISCRETE_PHYSICAL_WEIGHT_NOT_ARCH_MULTIPLIER

  - id: P057_B3_0B1_FORM_TO_OPERATOR
    mutation: infer_operator_domain_from_envelope_weighted_MemLp
    required_stop: FORM_DOMAIN_NOT_OPERATOR_DOMAIN

  - id: P057_B3_0B1_DIGAMMA_TRANSFER
    mutation: infer_exact_symbol_certificate_without_global_digamma_domination
    required_stop: SOURCE_WEIL_DIGAMMA_DOMINATION_MISSING

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the new file
  - target lake build Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
  - full lake build
  - scripts/q3_check.sh on the new file
  - routeb_status.py --check
  - exact public surface 1_definition_2_theorems
  - all support declarations private
  - forbidden-token scan
  - forbidden-import scan
  - all six plants fire without target-statement mutation
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
  - LOG_GROWTH_ENVELOPE_WEIGHTED_MODE_L2_ONLY
  - ENVELOPE_IS_NOT_EXACT_ARCH_SYMBOL
  - NO_EXACT_DIGAMMA_DOMINATION
  - NO_L2_PLANCHEREL_CARRIER
  - NO_SOURCE_WEIL_FORM
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - NO_UNIFORM_COFINAL_MODE_BOUND
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2_MISSING

SUCCESS:
  GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_BY_LOG_GROWTH_ENVELOPE

NOT_AUTHORIZED:
  - implement_B3_0B2
  - define_the_exact_digamma_arch_symbol
  - accept_arch_symbol_domination_as_a_public_premise
  - define_SourceWeilFormDomain
  - define_SourceWeilAssociatedGraph
  - define_SourceWeilOperatorDomain
  - define_sourceWeilAssociatedOperator
  - edit_D0PstarCCMCompressedWeilAction
  - claim_Plancheler_or_L2_Fourier_equivalence
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

PHASE:
  phase_key_change: false
  reuse_same_living_chat: true

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
