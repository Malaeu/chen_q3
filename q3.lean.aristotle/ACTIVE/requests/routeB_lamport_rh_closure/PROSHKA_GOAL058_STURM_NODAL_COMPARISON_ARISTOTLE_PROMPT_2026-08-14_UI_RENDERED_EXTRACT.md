STATUS: OPEN — REPAIR TO NODAL-INTERVAL STURM COMPARISON; ARISTOTLE AUTHORIZED
PRIMARY: REPAIR_G3_STURM_COMPARISON_TO_NODAL_INTERVAL
PRIMARY_COUNT: 1

PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: 46a6fdde2f77b77b2d566f805fb7d69a3f75b832
  ORIGIN_HEAD_EQUALS_HEAD: OWNER_REPORTED

MYTHOS_HEAD:
  MATHEMATICALLY_FALSE_AS_WRITTEN: false
  OVER_SCOPED_FOR_ONE_BOUNDED_WRONSKIAN_LEAF: true
  REPAIR:
    require_lower_solution_zero_free_on_Ioo_x1_x2: true
    interpretation: x1_x2_are_one_consecutive_nodal_interval

CURRENT_STRUCTURE:
  TWO_LAMBDA_VALUES_EXPOSED: true
  SHARED_mProject_EXPOSED: true
  SHARED_K_EXPOSED: true
  EXACT_BINDERS:
    - mProject K : Nat
    - LambdaLo LambdaHi x1 x2 : Real
    - SLo : Mode4FerrersRegularEvenProlateSolution mProject K LambdaLo
    - SHi : Mode4FerrersRegularEvenProlateSolution mProject K LambdaHi
  ODE_POTENTIAL_MATCH:
    guaranteed_by_shared_mProject: true
    shared_K_role: source_construction_lock
    K_occurs_in_differential_equation: false

PROOF_AUDIT:
  ACTUAL_FIRST_DERIVATIVE_INTERFACE: PRESENT
  ACTUAL_SECOND_DERIVATIVE_INTERFACE: PRESENT
  PROLATE_ODE: PRESENT
  INTERIOR_ZERO_SIMPLICITY: PRESENT
  FUNCTION_NONTRIVIALITY: PRESENT
  NEW_SOURCE_ANALYSIS_REQUIRED: false
  LOAD_BEARING_MISSING_CONTINUITY_LEMMA: false
  LOAD_BEARING_MISSING_INTEGRABILITY_LEMMA: false
  EXPECTED_FRICTION: Mathlib_calculus_and_interval_order_API_only

SOURCE_ACCESS:
  MYTHOS_VERDICT_RAW_FETCH: CACHE_MISS_IN_THIS_RUNTIME
  JUDGMENT_SCOPE: >-
    The exact theorem-shape questions reproduced in the owner dispatch,
    together with the accepted source interface and prior kernel-checked
    leaves. No byte-level claim about omitted Mythos wording is made.

SOURCE_PIN_ORDER:
  COMPACT_INTERIOR_COMPARISON_BEFORE_EXTERNAL_PAGE_PINS: ALLOWED
  SINGULAR_ENDPOINT_DOMAIN_CROSSWALK: HOLD
  GLOBAL_ZERO_COUNT: HOLD
  ORDERED_PSI4_SELECTION: HOLD
  EXTERNAL_OSCILLATION_PAGE_PINS: REQUIRED_BEFORE_INDEX_SELECTION

NEXT_ACTION:
  class: ARISTOTLE
  target: GOAL058_G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON
  execution_by_this_verdict: false

ARISTOTLE_SUBMISSION_AUTHORIZED: true

G1: OPEN
G3: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

SUCCESS: G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON_PROVED
STOP: G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON_TYPED_STOP

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE MAP
Question	Ruling
Mythos comparison for arbitrary two lower-solution zeros	Mathematically true after extracting a consecutive pair, because the accepted nonzero ODE solution has isolated interior zeros.
Same head as one direct Wronskian leaf	Too broad. It additionally needs compact zero-set finiteness and consecutive-pair extraction.
Repaired public theorem	Require SLo to have no zero on Ioo x1 x2; this states that x1,x2 bound one nodal interval.
Current derivative interface	Sufficient. No new source assumption is needed.
Aristotle	Appropriate for the repaired bounded theorem.
External Sturm–Liouville page pins	Not needed for the compact interior comparison; still required before zero-count/eigenvalue-index/third-even claims.

[ABSTRACT][LEAN_CONDITIONAL]

JUDGMENT OF THE PROPOSED HEAD

The unrestricted statement

two distinct zeros x1 < x2 of the lower-parameter solution
→ a zero of the higher-parameter solution in (x1,x2)

is not mathematically false.

For a nontrivial regular second-order solution, interior zeros are isolated.
On the compact interval [x1,x2], the zero set is therefore finite, so one
can choose a consecutive pair inside it and apply ordinary Sturm comparison.

But that route adds a second theorem package:

simple zeros
→ zero set finite on a compact interior interval
→ existence of a consecutive subpair.

Mythos's proposed one-shot Wronskian/Picone proof instead needs a single
nodal interval, where the lower solution has fixed sign.

Therefore the bounded executable head must include:

hNodal :
  ∀ x ∈ Set.Ioo x1 x2,
    mode4FerrersSeries SLo.coefficients x ≠ 0

This is the weakest honest repair for one leaf.

It is not a claim that the unrestricted theorem is false.

EXACT OBJECT AND BINDER AUDIT

The current structure exposes the comparison family without ellipses:

{mProject K : ℕ}
{ΛLo ΛHi x1 x2 : ℝ}

(SLo :
  Mode4FerrersRegularEvenProlateSolution
    mProject K ΛLo)

(SHi :
  Mode4FerrersRegularEvenProlateSolution
    mProject K ΛHi)

This forces definitionally:

same mProject;
same K;
different Lambda values only through hLambda : ΛLo < ΛHi.

The common mProject fixes the same coefficient

mode4JacobiG mProject

and hence the same Sturm–Liouville potential.

The parameter K does not occur in the differential equation. It remains
valuable as a source-construction lock: both solutions come from the same
tail-splice architecture rather than merely satisfying the same abstract ODE.

The public theorem must not generalize to different mProject values.

WHY THE CURRENT INTERFACE IS SUFFICIENT

For each accepted solution S, the structure now supplies on (-1,1):

S.ferrersSeries_hasDerivAt_firstDerivativeSeries

S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries

S.prolateDifferentialEquation

The accepted downstream file supplies:

S.interior_zero_simple

Thus the actual function and the formal derivative series are connected.

For an interior compact interval [x1,x2]:

HasDerivAt gives pointwise continuity of the function and first derivative;

the two derivative identities and the ODE give the exact derivative of the
weighted Wronskian;

continuous functions on the compact interval are interval-integrable;

zero simplicity plus fixed sign gives the endpoint derivative signs.

No new weighted coefficient summability is needed here. That work was already
consumed when the derivative interface was built.

No singular-endpoint argument is used.

The remaining difficulty is Lean API assembly, not a missing source theorem.

MATHEMATICAL KERNEL

Write

[
u(x)=\operatorname{mode4FerrersSeries}(S_{\rm Lo})(x),
\qquad
v(x)=\operatorname{mode4FerrersSeries}(S_{\rm Hi})(x),
]

and

[
p(x)=1-x^2.
]

Both solve

\Lambda y.
]

Define the oriented Wronskian

p(x)\bigl(u(x)v'(x)-u'(x)v(x)\bigr).
]

Then on (-1,1):

(\Lambda_{\rm Lo}-\Lambda_{\rm Hi})u(x)v(x).
}
]

Assume for contradiction that v has no zero in (x1,x2).

The nodal hypothesis makes u constant-sign there. The contradiction
assumption makes v constant-sign there. Multiply each by an independent
sign in {−1,1} so both are positive on the interval.

Because the endpoint zeros of u are simple:

[
u'(x_1)>0,
\qquad
u'(x_2)<0.
]

Continuity gives:

[
v(x_1)\ge0,
\qquad
v(x_2)\ge0.
]

Therefore:

[
W(x_1)\le0,
\qquad
W(x_2)\ge0.
]

But ΛLo < ΛHi and u v > 0 imply:

[
W'(x)<0
\quad\text{on }(x_1,x_2),
]

hence:

[
W(x_2)<W(x_1),
]

a contradiction.

SOURCE-PIN ORDER

The compact interior theorem may be proved before exact external
Sturm–Liouville page pins.

It proves only a comparison law for two objects that already satisfy the same
accepted project ODE and regularity contract.

It does not claim:

existence of the matching roots;
singular self-adjoint realization;
completeness of the eigenfamily;
number of zeros of a selected solution;
ordered eigenvalue index;
third-even / psi4 identification.

Those claims remain blocked until the exact external source is pinned for:

singular endpoint domain;
self-adjoint realization;
discrete simple spectrum;
oscillation count;
parity/index convention.

This ordering is source-faithful.

AUTHORITATIVE ARISTOTLE PROMPT
TARGET_ID: GOAL058_G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON

PRIMARY_CLASS: REPAIRED_INTERIOR_STURM_COMPARISON

PIN:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: 46a6fdde2f77b77b2d566f805fb7d69a3f75b832

  ABORT_POLICY: >-
    Abort if HEAD or origin/rh_clean differs. Do not adapt the theorem to a
    later structure revision.

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    D0Mode4FerrersSturmComparison.lean

ALLOWED_IMPORTS:
  - Q3.Proofs.RouteB.D0Mode4FerrersInteriorZeroSimplicity

IMPORT_POLICY: >-
  No other direct Q3 import. Mathlib declarations available transitively
  through the allowed import may be used.

FORBIDDEN_IMPORTS:
  - Q3.Main
  - any file asserting actual ProlatePair construction
  - any root-existence or finite-left-sign file
  - any ordered-mode or zero-count file
  - any finite-Fourier eigenrelation file
  - any G1 gap/penalty file
  - any Route B export or RH file

EXACT_INPUT_OBJECTS:
  - Q3.RouteB.Mode4FerrersRegularEvenProlateSolution
  - Q3.RouteB.mode4FerrersSeries
  - Q3.RouteB.mode4FerrersFirstDerivativeSeries
  - Q3.RouteB.mode4FerrersSecondDerivativeSeries
  - >-
    Q3.RouteB.Mode4FerrersRegularEvenProlateSolution.
    ferrersSeries_hasDerivAt_firstDerivativeSeries
  - >-
    Q3.RouteB.Mode4FerrersRegularEvenProlateSolution.
    firstDerivativeSeries_hasDerivAt_secondDerivativeSeries
  - >-
    Q3.RouteB.Mode4FerrersRegularEvenProlateSolution.
    prolateDifferentialEquation
  - >-
    Q3.RouteB.Mode4FerrersRegularEvenProlateSolution.
    interior_zero_simple

EXACT_BINDERS:
  mProject: Nat
  K: Nat
  LambdaLo: Real
  LambdaHi: Real
  x1: Real
  x2: Real

  SLo: >-
    Q3.RouteB.Mode4FerrersRegularEvenProlateSolution
      mProject K LambdaLo

  SHi: >-
    Q3.RouteB.Mode4FerrersRegularEvenProlateSolution
      mProject K LambdaHi

EXACT_THEOREM_HEAD: |
  namespace Q3.RouteB

  theorem exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval
      {mProject K : ℕ}
      {ΛLo ΛHi x1 x2 : ℝ}
      (SLo :
        Mode4FerrersRegularEvenProlateSolution
          mProject K ΛLo)
      (SHi :
        Mode4FerrersRegularEvenProlateSolution
          mProject K ΛHi)
      (hΛ : ΛLo < ΛHi)
      (hx1 : x1 ∈ Set.Ioo (-1 : ℝ) 1)
      (hx2 : x2 ∈ Set.Ioo (-1 : ℝ) 1)
      (hxx : x1 < x2)
      (hz1 :
        mode4FerrersSeries SLo.coefficients x1 = 0)
      (hz2 :
        mode4FerrersSeries SLo.coefficients x2 = 0)
      (hNodal :
        ∀ x ∈ Set.Ioo x1 x2,
          mode4FerrersSeries SLo.coefficients x ≠ 0) :
      ∃ x ∈ Set.Ioo x1 x2,
        mode4FerrersSeries SHi.coefficients x = 0 := by
    -- proof

REQUIRED_AUXILIARY_LEMMAS:
  - name: mode4FerrersSturmWronskian
    visibility: private
    exact_role: >-
      Define
        (1-x^2) *
          (u(x)*v'(x) - u'(x)*v(x))
      using the exact stored first-derivative series.

  - name: mode4FerrersSturmWronskian_hasDerivAt
    visibility: private
    exact_statement: |
      For x in Ioo (-1) 1, prove:
        HasDerivAt
          (mode4FerrersSturmWronskian SLo SHi)
          ((ΛLo - ΛHi) *
            mode4FerrersSeries SLo.coefficients x *
            mode4FerrersSeries SHi.coefficients x)
          x
    exact_role: >-
      Use both actual derivative fields and both stored ODE identities.
      The common potential must cancel algebraically.

  - name: continuous_nonzero_on_interval_has_constant_sign
    visibility: private
    exact_role: >-
      On Ioo x1 x2, turn continuity plus pointwise nonvanishing into one
      constant sign. It may be proved by the intermediate value theorem and
      a midpoint witness.

  - name: derivative_pos_at_left_zero_of_pos_right
    visibility: private
    exact_role: >-
      For an interior differentiable function with a simple zero at x1 and
      strict positivity immediately to the right, derive derivative > 0.

  - name: derivative_neg_at_right_zero_of_pos_left
    visibility: private
    exact_role: >-
      Analogous right-endpoint result.

  - name: wronskian_strictAnti_on_nodal_interval
    visibility: private
    exact_role: >-
      From hΛ and sign-normalized u,v, prove strict decrease of W on
      Icc x1 x2, using either a derivative-sign monotonicity theorem or
      interval integration.

PROOF_MECHANISM:
  - Assume the conclusion is false.
  - Obtain nonvanishing of the high-parameter solution on `Ioo x1 x2`.
  - Sign-normalize the low and high solutions independently.
  - Prove the exact Wronskian derivative identity.
  - Derive strict negativity of the Wronskian derivative.
  - Derive the endpoint derivative signs from `interior_zero_simple`.
  - Derive `W x1 <= 0 <= W x2`.
  - Contradict strict decrease.
  - Do not use endpoint zero-flux at `±1`.
  - Do not use an external Sturm theorem as an axiom.

EXPECTED_OUTPUT:
  SUCCESS: >-
    Return the complete contents of the single owned Lean file. It must contain
    the exact public theorem, private helpers, mandatory falsifier declarations
    or compile-checked plants, and all required `#print axioms` commands.

  TYPED_STOP: >-
    If the theorem cannot be closed from the allowed import, return exactly one
    typed-stop code and the smallest missing Lean lemma signature. Do not remove
    hNodal, reverse hLambda, add a zero-count/index assumption, or import an
    external Sturm theorem.

SUCCESS_CODE:
  G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON_PROVED

TYPED_STOP_CODES:
  - G3_STURM_WRONSKIAN_DERIVATIVE_IDENTITY_GAP
  - G3_STURM_NODAL_SIGN_PROPAGATION_GAP
  - G3_STURM_ENDPOINT_DERIVATIVE_SIGN_GAP
  - G3_STURM_STRICT_MONOTONICITY_API_GAP
  - G3_STURM_INTERVAL_FTC_API_GAP
  - G3_STURM_NODAL_INTERVAL_GUARD_DROPPED
  - G3_STURM_PARAMETER_DIRECTION_MUTATION_SURVIVED
  - G3_STURM_POTENTIAL_MISMATCH
  - G3_STURM_SINGULAR_ENDPOINT_LEAK
  - G3_STURM_AXIOM_GATE_FAILED
  - G3_STURM_VALIDATION_FAILED

MANDATORY_FALSIFIERS:
  - id: P_STURM_1_PARAMETER_DIRECTION
    requirement: >-
      Include a compile-checked elementary comparison plant for
      `-y'' = Lambda*y`: the lower-frequency function `sin(x)` has zeros at
      `0, pi`, while `sin(2*x)` has an interior zero. The reversed comparison
      must not be accepted as the production direction. Also record the
      counter-direction example `sin(2*x)` on `(0,pi/2)` versus `sin(x)`,
      where the lower-frequency function has no interior zero.
    stop: G3_STURM_PARAMETER_DIRECTION_MUTATION_SURVIVED

  - id: P_STURM_2_NODAL_INTERVAL
    requirement: >-
      Record the exact plant `sin(2*x)` on `(0,pi)`: it has an interior zero,
      so the one-interval fixed-sign Wronskian proof may not drop `hNodal`.
      The public theorem type must contain `hNodal`.
    stop: G3_STURM_NODAL_INTERVAL_GUARD_DROPPED

  - id: P_STURM_3_COMMON_POTENTIAL
    requirement: >-
      Symbolically mutate the two solutions to different `mProject` values.
      The Wronskian derivative must expose the uncancelled potential-difference
      term. The production theorem must share one `mProject`.
    stop: G3_STURM_POTENTIAL_MISMATCH

  - id: P_STURM_4_INTERIOR_ONLY
    requirement: >-
      Mutate `hx1` or `hx2` from `Ioo (-1) 1` to a singular endpoint `-1` or
      `1`. The production theorem must reject the mutation and must not use
      endpoint zero-flux to hide the singular denominator.
    stop: G3_STURM_SINGULAR_ENDPOINT_LEAK

  - id: P_STURM_5_ACTUAL_DERIVATIVES
    requirement: >-
      The proof must consume both accepted `HasDerivAt` fields. A version that
      treats the formal derivative series as actual derivatives without these
      fields is rejected.
    stop: G3_STURM_FORMAL_DERIVATIVE_SURROGATE

AXIOM_GATE:
  REQUIRED_PRINT_HEADS:
    - Q3.RouteB.exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval

  ALLOWED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound

  FORBIDDEN:
    - sorryAx
    - any new project axiom
    - any opaque proof constant
    - native_decide

VALIDATION_COMMANDS:
  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    test "$(git rev-parse HEAD)" = \
      "46a6fdde2f77b77b2d566f805fb7d69a3f75b832"
    test "$(git rev-parse origin/rh_clean)" = \
      "46a6fdde2f77b77b2d566f805fb7d69a3f75b832"

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake env lean \
      Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake build Q3.Proofs.RouteB.D0Mode4FerrersSturmComparison

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake build

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    bash scripts/q3_check.sh \
      q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    rg -n \
      '\bsorry\b|\badmit\b|exact\?|native_decide|^[[:space:]]*axiom\b|^[[:space:]]*opaque\b' \
      q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    rg -n \
      'IsActualProlateModePair|zeroCount|ordered|psi4|thirdEven|finiteFourier|hroot|RH|WeilPositivity|hgap|hfloor' \
      q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    git diff --check -- \
      q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean

    test "$(
      git diff --name-only -- \
        q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean \
      | wc -l | tr -d ' '
    )" = "1"

NONCLAIMS:
  - NO_ZERO_COUNT
  - NO_ORDERED_PSI4
  - NO_THIRD_EVEN_SELECTION
  - NO_MATCHING_ROOT_EXISTENCE
  - NO_SINGULAR_ENDPOINT_DOMAIN_CROSSWALK
  - NO_PHYSICAL_SCALE
  - NO_FINITE_FOURIER_EIGENRELATION
  - NO_ACTUAL_PROLATEPAIR
  - NO_LEMMA_7_2
  - NO_G3
  - NO_G1
  - NO_ROUTE_B_PROMOTION
  - NO_RH
FINAL PROPOSAL

Submit exactly the repaired nodal-interval comparison theorem to Aristotle.

Registered prediction:

P_STURM_ART_1:
  prediction: exact Wronskian derivative identity closes
  confidence: 0.95

P_STURM_ART_2:
  prediction: the main proof friction is endpoint derivative-sign API
  confidence: 0.65

P_STURM_ART_3:
  prediction: no new mathematical source lemma is needed
  confidence: 0.90

Likeliest failure:

Mathlib does not expose the desired endpoint derivative-sign or strict
monotonicity lemma in the imported environment.

Response:

Return the smallest missing local calculus lemma signature.
Do not add source hypotheses or import an external Sturm theorem.
STRONGEST ATTACK

The strongest objection is:

This proves only one comparison step between two already-existing regular
solutions. It does not construct the Lambda-family or identify an ordered
mode.

Correct.

The theorem is accepted only as the interior comparison kernel.

It does not prove that matching roots exist for two Lambda values. It does not
prove monotonicity of a zero count as Lambda changes. It does not identify the
third even eigenfunction.

A second objection is:

Why require a nodal interval if the unrestricted two-zero theorem is true?

Because the unrestricted theorem requires an additional compact zero-set and
consecutive-pair extraction layer. That theorem can be built later from this
kernel plus interior_zero_simple.

The present transaction chooses the smallest bounded statement.

META CLOSEOUT
What became smaller?

The Sturm architecture is split into:

current bounded leaf:
  comparison on one nodal interval;

later topology leaf:
  arbitrary two zeros -> consecutive subinterval;

later source theorem:
  zero-count monotonicity and ordered mode selection.
What was killed?

The direct four-zero request at an unspecified matching root.

A one-shot comparison proof without a nodal-interval guard.

Using external singular Sturm theory as an axiom for an interior theorem.

What must not be tried again?

Do not claim mode index from comparison alone.

Do not compare different mProject potentials.

Do not let the formal derivative series bypass the actual derivative fields.

Current smallest named gap

[
\boxed{\texttt{Mode4SturmNodalIntervalComparison}}
]

Next cheapest decisive test

Aristotle proof search for the exact repaired theorem.

Fate of prior registered predictions
actual derivative interface was sufficient:
  CONFIRMED BY AUDIT.

four-zero / ordered-psi4 as immediate next leaf:
  REFUTED.

interior comparison before external source pins:
  CONFIRMED WITH NONCLAIMS.
Memory entry
iteration:
  target: Goal058_Mode4_Sturm_architecture
  status: OPEN
  failed_strategy: ask_for_four_zeros_at_unspecified_matching_root
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: Mode4SturmNodalIntervalComparison
  invariant_learned: Sturm comparison requires the same potential and one zero-free lower-solution nodal interval
  forbidden_future_move: infer_zero_count_or_ordered_mode_from_one_comparison_kernel
  next_decisive_test: Aristotle_nodal_interval_comparison
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
