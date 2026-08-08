STATUS: OPEN — CANDIDATE A SURVIVES; ONE SOURCE-LOCKED W02 PREFLIGHT IS AUTHORIZED, PRODUCTION IS NOT
YAMLSTATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT
OPERATIVE_CLASS_COUNT: 1
SELECTED_CANDIDATE: A_REPAIRED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  REVIEW_PIN:
    requested_short: 1c5b0197
    resolved_full: 1c5b01979e047413e895bffa27631146fd57d956
    status: PASS

  REQUEST_EMBEDDED_HEAD:
    value: dc2968ccb4302cd8001564868ca54a2453cee3c7
    status: STALE_SUPERSEDED_BY_CONTROLLING_REVIEW_PIN

  ATTACHED_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_SOURCE_AUDIT_2026-08-08.md
    observed_sha256: ed423bcd1d364bcf71ab35139d01002fafcb69f261f1bb89a3349c69a9435f50
    observed_bytes: 12226
    observed_lines: 413
    read_in_full: true

  PARENT_B3_0F:
    result: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED
    production_sha256: b075be90e7ae6f3cf484e8868683bc642a88be77919a29e9dfafcd63bf5d3d2f
    retained: true
    reopened: false

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  source_mathematics_available: true
  source_production_object_available: false
  candidate_A_mathematical_shape: ACCEPTED
  candidate_A_production_release: false
  candidate_A_no_sorry_preflight: AUTHORIZED
  candidate_B: RUNNER_UP_NOT_AUTHORIZED
  candidate_C_wall: REJECTED_AS_PREMATURE
  direct_alias_to_ccmW02Entry: KILLED_C10

RELEASED_ATOM:
  none: true
  reason: NO_BYTE_PINNED_COMPILING_W02_HARNESS

FIRST_MISSING_SOURCE_THEOREM:
  sourceW02ModePairing_eq_ccmW02Entry

CURRENT_EXACT_STOP:
  SOURCE_W02_FUNCTIONAL_PRODUCTION_OBJECT_MISSING

PREFLIGHT:
  id: B3_0G_A_ONE_SIDED_W02_SOURCE_INTEGRAL_NO_SORRY_PREFLIGHT
  path: q3.lean.aristotle/Goal057B3_0G_A_Scratch.lean
  tracked_repository_mutation: forbidden

PROPOSED_PRODUCTION_FILE_AFTER_LATER_RELEASE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean

EXACT_PREFLIGHT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

PROPOSED_PUBLIC_SURFACE:
  definitions:
    - sourceW02ModePairing
  theorems:
    - sourceW02ModePairing_eq_ccmW02Entry
  total_public_declarations: 2

PRIVATE_PREFLIGHT_BUDGET:
  definitions_maximum: 2
  theorems_maximum: 10
  total_maximum: 12
  exact_production_ceiling: TO_BE_FIXED_FROM_PASSING_HARNESS
  public_expansion: forbidden

SOURCE_PARENT_CONSUMED:
  required_theorem:
    two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
  status: MUST_BE_LOAD_BEARING_IN_PREFLIGHT
  naming_only_dependency: forbidden

RANK_TWO_CONTRACT:
  required: true
  production_public_surface: NOT_REQUIRED
  preflight_witness:
    sourceW02ModePairing_eq_rankTwoLogEndpointMoments
  rank_one_collapse: forbidden

COEFFICIENT_ORDER:
  first_slot: ANTILINEAR_CONJUGATED
  second_slot: LINEAR
  final_closed_formula: SYMMETRY_BLIND
  orientation_detector:
    NONSYMMETRIC_ENDPOINT_MOMENT_HARNESS

REAL_TO_COMPLEX_CROSSWALK:
  left: sourceW02ModePairing_in_Complex
  right: explicit_coe_of_real_ccmW02Entry
  real_part_projection: forbidden

STOP:
  GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT_MISSING

SUCCESS:
  GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT_SOURCE_LOCKED

PRODUCTION_SUCCESS_CODE_RESERVED:
  GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_PROVED

NEXT_GAP_AFTER_PRODUCTION_SUCCESS:
  GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT

NEXT_GAP_PRODUCTION_AUTHORIZED: false

CHECKPOINTS_CLOSED_AFTER_SUCCESS: 0
CHECKPOINTS_REMAINING_AFTER_SUCCESS: 10
CURRENT_CHECKPOINT_EFFECT: STRICTLY_ADVANCED_NOT_CLOSED

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_NO_SORRY_PREFLIGHT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE_KEY_CHANGE: false
REUSE_SAME_LIVING_CHAT: true
OWNER_ACTION_REQUIRED: false
SOLE_OWNER_GATE: PX_RH_CLAIM

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
1. Pin and parent ruling
The short review pin resolves to 1c5b01979e047413e895bffa27631146fd57d956. The repository state at that pin records B3.0F as proved, keeps the coarse ledger at 0/10, and names B3.0G as a source audit with production explicitly unauthorized.  [ABSTRACT][PAPER]
The B3.0F closeout confirms the exact finite archimedean sesquilinear lift, its SHA-256 b075be90…d2f, the first-slot conjugation, the literal j-N mode map, nine fired plants, and the absence of any W02, prime, complete-form, or operator claim.  [FINITE_CELL][LEAN]
The request’s embedded dc2968cc… head is stale relative to the controlling user pin. This is repaired by pinning the review to 1c5b0197…. It is not a mathematical stop because the relevant parent, source, CCM definitions, and source-mode theorem are all present and match the audited interfaces at the controlling pin. The attached request itself was read in full and hashes to ed423bcd…5f50. PROSHKA_REQUEST_GOAL057_B3_0G_S…  [ABSTRACT][PAPER]
The Arsenal mandate is accepted. The repository materialization ledger records the mandated deck SHA-256 and twelve-card inventory.    [ABSTRACT][PAPER]
2. Operative ruling
TRY_GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT​
Candidate A is the smallest source-faithful route.
It is not production-released in this verdict. The missing work is a generic symbolic integral theorem, not a source-acquisition wall. A byte-pinned, no-sorry harness must compile before production materialization.
Candidate B—the rank-two endpoint-moment construction—is retained as the sole runner-up. It is not authorized unless Candidate A fails its source-provenance or generic-integral discriminator.
3. Why Candidate A is not a C10 surrogate
The source separates two genuinely different objects:


the source correlation profile
q(Un​,Ur​)(x),
defined by the convolution formulas in equations (2.9)–(2.10);


the closed scalar W02 entry in equation (4.2).


The one-sided source functional is
W0,2#​(F)=∫1∞​F(x)(x1/2+x−1/2)d\*x.
For F(x)=q(Un​,Ur​)(logx), the substitution y=logx gives
∫0L​q(Un​,Ur​)(y)(ey/2+e−y/2)dy.​
The source then proves that this integral is the closed rank-two expression in equation (4.2).   [ABSTRACT][PAPER]
Production ccmQKernel is the literal q(Un​,Ur​) formula from equations (2.9)–(2.10), whereas ccmW02Entry is the separate closed scalar from equation (4.2).  [ABSTRACT][LEAN]
Therefore the definition
leannoncomputable def sourceW02ModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) *
      ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)
is not a disguised alias of ccmW02Entry. It defines the source one-sided functional by integrating the source correlation kernel. The desired equality remains a non-definitional analytic theorem. [ABSTRACT][CONDITIONAL]
By contrast,
leandef sourceW02ModePairing i n r :=
  (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)
is killed as:
SURROGATE_BY_FORMULA_NOT_SOURCE_CONSTRUCTION
That kill instantiates C10.
4. The one-sided normalization is exact
The finite matrix uses W0,2#​, not the full two-sided W0,2​.
The source proves
Ψ(h)=Ψ#(h)+Ψ#(h∘ι),
and Proposition 3.2 sends the restricted form directly to Ψ#(q∘log). Thus equation (4.1) already consumes the one-sided functional. There is no additional factor 2 in the mode entry.   [ABSTRACT][PAPER]
A mutant definition with
lean2 * ∫ x in Set.Icc 0 (L_m i), ...
must fail with:
SOURCE_W02_FULL_VS_SHARP_FACTOR_MISMATCH
5. Source-mode provenance must be load-bearing
The current production E3 theorem proves that, for 0≤x,
2∫R​Vi,n​(t)​cos(2πtx)Vi,r​(t)dt={ccmQKernel(Lm​(i),n,r,x),0,​x≤Lm​(i),x>Lm​(i).​
Its private construction starts from the reflected conjugate first mode and the second zero-extended mode, so the source antilinear-first convention is present before the final symmetric kernel forgets it.   [ABSTRACT][LEAN]
The preflight must therefore prove a private or harness-only theorem of the following exact shape:
leanprivate theorem sourceW02ModePairing_eq_sourceModeCosineIntegral
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      ∫ x in Set.Icc 0 (L_m i),
        (2 * ∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (Real.cos (2 * Real.pi * t * x) : ℂ) *
            𝓕 (logWindowZeroExtendedMode i r) t) *
          ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)
Only parenthesization adjustments are permitted.
This theorem must consume:
leantwo_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
with the exact 0 ≤ x ≤ L_m i facts supplied by the Icc domain. An import that merely makes the theorem available but never uses it does not satisfy SOURCE_PARENT_CONSUMED.
6. Rank-two contract and coefficient order
The source’s rank-two structure is:
W0,2#​(Vn​,Vr​)=Mn−​​Mr+​+Mn+​​Mr−​,
where, in the log coordinate,
Mn+​=∫0L​Un​(x)ex/2dx,Mn−​=∫0L​Un​(x)e−x/2dx.
The multiplicative-coordinate factors λ∓1/2 cancel crosswise; using the log-coordinate moments avoids hiding that cancellation. [ABSTRACT][PAPER]
The preflight must include private definitions equivalent to:
leanprivate noncomputable def sourceW02LogEndpointPlus
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (x / 2) : ℂ)

private noncomputable def sourceW02LogEndpointMinus
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (-x / 2) : ℂ)
and a theorem:
leanprivate theorem sourceW02ModePairing_eq_rankTwoLogEndpointMoments
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      conj (sourceW02LogEndpointMinus i n) *
          sourceW02LogEndpointPlus i r +
        conj (sourceW02LogEndpointPlus i n) *
          sourceW02LogEndpointMinus i r
This theorem is the rank-two and ordered-slot witness. It may be private in eventual production, but it must exist in the preflight.
The expected endpoint formulas are
Mn+​=L/2+2πinL​(eL/2−1)​,Mn−​=−L/2+2πinL​(e−L/2−1)​.
Their cross sum simplifies exactly to
32Lsinh2(L/4)(L2+16π2n2)(L2+16π2r2)L2−16π2nr​.
integral_exp_mul_complex and the interval-integral pattern already used by the exact mode Fourier theorem provide the appropriate pinned Lean route.  [ABSTRACT][LEAN]
7. Exact preflight contract
The untracked harness is:
q3.lean.aristotle/Goal057B3_0G_A_Scratch.lean
Its sole direct import is:
leanimport Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
The proposed public surface is exactly:
leannoncomputable def sourceW02ModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) *
      ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)

theorem sourceW02ModePairing_eq_ccmW02Entry
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)
The proof route is fixed:


Prove the source-mode/cosine-integral representation by consuming E3.


Define the two log-coordinate endpoint moments.


Evaluate both moments with integral_exp_mul_complex.


Prove the conjugate-first rank-two factorization.


Simplify the two endpoint products to the literal ccmW02Entry.


Make the final real-to-complex coercion explicit.


Use no formula premise, sampled equality, numeric normalization, matrix symmetry, or generated backend.


A passing packet must include:
exact harness bytes;
SHA-256, byte count and line count;
direct Lean command, exit status and complete stdout/stderr hashes;
exact public/private declaration counts;
forbidden-token scan;
#print axioms output;
proof-dependency fingerprint showing E3 consumption;
all mandatory plant fates;
exact git status showing no tracked production mutation.
8. Mandatory plants
The preflight must run all of the following.
P057_G_1_FORMULA_ALIAS
Mutation: define sourceW02ModePairing directly as ccmW02Entry.
Required semantic stop:
SURROGATE_BY_FORMULA_NOT_SOURCE_CONSTRUCTION
Card: C10.
P057_G_2_FULL_VS_SHARP
Mutation: multiply the one-sided integral by 2.
Required stop:
SOURCE_W02_FULL_VS_SHARP_FACTOR_MISMATCH
P057_G_3_ENDPOINT_PLUS_WEIGHT
Mutation: delete exp(x/2).
Required stop:
SOURCE_W02_ENDPOINT_WEIGHT_MISSING
P057_G_4_ENDPOINT_MINUS_WEIGHT
Mutation: delete exp(-x/2).
Required stop:
SOURCE_W02_ENDPOINT_WEIGHT_MISSING
P057_G_5_LOG_LENGTH
Mutation:
L_m i = 2 * log(lambda_m i)
to a half-length convention using only log(lambda_m i).
Required stop:
SOURCE_W02_LOG_LENGTH_NORMALIZATION_MISMATCH
P057_G_6_RANK_TWO
Mutation: retain only one endpoint outer product.
Required stop:
SOURCE_W02_RANK_TWO_STRUCTURE_LOST
P057_G_7_SESQUILINEAR_SLOT
Mutation: remove the first-slot conjugation or move it to the second slot.
Required stop:
SOURCE_W02_SESQUILINEAR_SLOT_MISMATCH
P057_G_8_COMPLEX_COERCION
Mutation: prove only the real part or insert .re.
Required stop:
SOURCE_W02_COMPLEX_COERCION_MISMATCH
P057_G_9_ORDER_DETECTOR
Do not swap n,r in the final ccmW02Entry; that mutation is symmetry-blind.
Use a harness-only nonsymmetric pair of endpoint vectors for which
Mn−​​Mr+​+Mn+​​Mr−​
changes when the coefficient slots are transposed without transporting conjugation.
Required stop:
SOURCE_W02_ORDER_DETECTOR_MISSING
Card: C04.
P057_G_10_SOURCE_PARENT
Mutation: remove consumption of the E3 source-mode/cosine theorem and retain only the CCM formula integral.
Required stop:
SOURCE_W02_SOURCE_MODE_PARENT_NOT_CONSUMED
P057_G_11_COMPONENT_BOUNDARY
Mutation: infer positivity, the complete Weil form, a source operator, or a checkpoint closure.
Required stop:
SOURCE_W02_COMPONENT_ONLY_BOUNDARY_VIOLATED
P057_G_12_DEPENDENCY
Mutation: add generated PSD, Step33, hbox, payload, or direct Aristotle-output support.
Required stop:
ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
9. Binary discriminator
B3_0G_A_ONE_SIDED_W02_SOURCE_INTEGRAL_NO_SORRY_PREFLIGHT
PASS
All of the following must hold:
the exact definition compiles;
the exact crosswalk compiles;
the E3 source parent is consumed;
the rank-two endpoint factorization compiles;
the real-to-complex crosswalk is explicit;
all twelve plants fire;
axioms are exactly [propext, Classical.choice, Quot.sound].
Then return the exact bytes to this same living chat for one production-release decision.
FAIL
If the first failure is only generic exponential-integral simplification, report the exact Lean/API blocker and switch the next discriminator to Candidate B:
B3_0G_B_RANK_TWO_ENDPOINT_MOMENT_NO_SORRY_PREFLIGHT
Candidate B remains unapproved until that failure occurs.
If Candidate A can prove the closed formula only by assuming the desired equality, aliasing ccmW02Entry, dropping the source parent, or using final-form symmetry as order evidence, kill Candidate A under C10/C04 and retain B3.0G as open.
10. Exact semantic boundary
A later successful B3.0G production theorem would prove only:
W0,2#​(Vn​,Vr​)=ccmW02Entry(Lm​(i),n,r)​
for every production window and integer mode pair. [ABSTRACT][LEAN]
It would not prove:


the finite W02 coefficient-form lift;


the prime source pairing;


the complete source Weil form;


positivity of W02 or of the full form;


a rank-two operator realization;


form-domain or operator-domain membership;


compression;


the actual continuum numerator;


H4a1b;


any coarse checkpoint.


The next smallest atom after a later validated B3.0G production theorem is:
GOAL057_B3_0H_FINITE_W02_SESQUILINEAR_FORM_MATRIX_LIFT
That child is not authorized here.
11. Strongest attack

ccmQKernel and ccmW02Entry are declared in the same CCM file. Is Candidate A merely laundering one CCM formula through an integral and calling it a source object?

No. ccmQKernel is an x-dependent transcription of the independent source correlation q(Un​,Ur​) from equations (2.9)–(2.10). ccmW02Entry is the result of applying the distinct source functional W0,2#​ and evaluating the integral in equation (4.2). The equality is not definitional and requires an actual analytic proof.   [ABSTRACT][PAPER][LEAN]
The attack remains valid at the provenance layer. If the preflight merely integrates ccmQKernel and never binds it back to the source-mode construction, the new name would still be too easy to detach from its source meaning. That is why E3 consumption and the endpoint-moment rank-two theorem are mandatory. Without them, Candidate A is killed under C10.
12. Route map
CandidateKill-powerCostRulingA — one-sided q-kernel integralHighMediumSelected for one untracked preflightB — endpoint-moment constructionVery highMedium–highRunner-up; not authorizedC — source-construction wallHighLowRejected because A is well-typed and source-backed
13. Meta closeout
What became smaller?
The W02 wall is no longer “define the source endpoint component somehow.” It is one exact generic integral identity with a pinned source correlation, a rank-two endpoint factorization, and an explicit real-to-complex target.
What was killed?
The direct sourceW02ModePairing := ccmW02Entry alias, full-versus-sharp factor ambiguity, formula symmetry as order evidence, and any claim that the source paper is missing the required mathematics.
What must not be tried again?
Do not publish a W02 source object whose only content is the desired closed formula. Do not count an n/r swap of the symmetric final scalar as an orientation plant. Do not bundle the prime component or finite source-form assembly into B3.0G.
Current smallest named gap
GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT_MISSING
Next cheapest decisive test
B3_0G_A_ONE_SIDED_W02_SOURCE_INTEGRAL_NO_SORRY_PREFLIGHT
Prediction fate
B3.0F prediction:
  the next source component is W02 rather than the complete Weil form.

Fate:
  CONFIRMED.

B3.0G audit prediction:
  source mathematics exists, but an independent source-side Lean object is absent.

Fate:
  CONFIRMED.

Candidate-A prediction:
  the one-sided q-kernel integral is source-faithful and should close from
  current exponential-integral APIs.

Fate:
  REGISTERED_NOT_YET_TESTED.
YAMLiteration:
  target: GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
  status: OPEN
  failed_strategy: direct_alias_of_the_closed_CCM_formula
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT_MISSING
  invariant_learned: one_sided_sharp_normalization_rank_two_endpoint_structure_first_slot_conjugation_and_source_parent_provenance_are_independent_contracts
  forbidden_future_move: use_symmetric_ccmW02Entry_as_evidence_for_ordered_source_slot_fidelity
  next_decisive_test: B3_0G_A_ONE_SIDED_W02_SOURCE_INTEGRAL_NO_SORRY_PREFLIGHT
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
