STATUS: OPEN — PLAIN-PI ISOMETRY KILLED; EUCLIDEAN FINITE-RIESZ CHILD RELEASED
YAMLPRIMARY: TRY_GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_REPAIRED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_REPAIRED
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: 1ba34ff53f80071c29018860ef826f636279de10
  ORIGIN_RH_CLEAN: 1ba34ff53f80071c29018860ef826f636279de10
  HEAD_ORIGIN_EQUAL: true
  PARENT_B2_KILL_ARCHIVED: true
  SELECTED_FILE_PRESENT_AT_PIN: false

ARSENAL:
  DECK_FETCHED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  MANDATE_ACCEPTED: true
  CARDS_USED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  EXACT_PROPOSED_CHILD:
    fate: KILLED_AS_TYPED
    code: GOAL057_B2_PLAIN_PI_ISOMETRY_CARRIER_MISMATCH
    reason: >-
      The plain function carrier CCMModeFinite i.N → ℂ has the ordinary
      product/sup norm, whereas the source coefficient Hilbert carrier is
      EuclideanSpace ℂ (CCMModeFinite i.N), i.e. PiLp 2. The literal synthesis
      is not an isometry from the former for N ≥ 1.

  REPAIRED_CHILD:
    release: AUTHORIZED
    public_names_unchanged: true
    public_declaration_count: 3
    theorem_statement_unchanged: true
    only_public_type_repair: >-
      ccmFiniteSynthesisEquiv must have source
      EuclideanSpace ℂ (CCMModeFinite i.N), not the plain Pi type.

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean

SOLE_IMPORT:
  Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions:
    - ccmFiniteSynthesisEquiv
    - sourceCCMFiniteRieszOperator
  theorems:
    - sourceCCMFiniteRieszOperator_apply_sourceTrial
  total: 3

STOP: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_MISSING
SUCCESS: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_PROVED

NEXT_GAP_AFTER_SUCCESS:
  SELECTED_KTRIAL_ASSOCIATED_WEIL_OPERATOR_DOMAIN_AND_COMPRESSION

LEDGER_EFFECT_AFTER_SUCCESS:
  ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE: ADVANCED_NOT_CLOSED
  DELEGATED_CHECKPOINTS_CLOSED: 0
  DELEGATED_CHECKPOINTS_REMAINING: 10
  TEN_CHECKPOINT_COUNT: UNCHANGED

PHASE:
  PHASE_KEY_CHANGE: false
  SAME_LIVING_CHAT: true
  NEW_CHAT: false

PROGRESS_CLASS: FALSIFICATION_PROGRESS
SELECTED_CHILD_PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
Source lock
The branch reference and requested pin agree exactly at 1ba34ff53f80071c29018860ef826f636279de10. The commit archives the direct hCompressedAction kill, preserves the ten-checkpoint ledger at 0 closed / 10 remaining, and selects this finite-Riesz prerequisite as the next atom.   [ABSTRACT][PAPER]
The parent B2 request correctly required a distinction between the coefficient matrix action, the finite subspace action, and the unavailable ambient associated Weil operator. PROSHKA_REQUEST_GOAL057_B2_COMP… [ABSTRACT][PAPER]
B1 remains intact at the new pin. It supplies:


the plain coefficient synthesis map;


the exact complex source row;


the complexified CCM matrix and coefficient operator;


synthesis of the source row to the literal normalized kTrial_m_N;


exact source-row unit dot product;


matrix Hermiticity;


real Rayleigh value;


finite residual orthogonality.


It does not supply an ambient associated operator or compression theorem.  [FINITE_CELL][LEAN]
The selected output file does not yet exist at this pin.
Decisive repair: the proposed isometry has the wrong source norm
The exact proposed public type was implicitly:
leanccmFiniteSynthesisEquiv
    (i : PairIndex) :
    (CCMModeFinite i.N → ℂ) ≃ₗᵢ[ℂ] E_m_N i
That type is not valid for the intended synthesis map.
Mathlib deliberately keeps the ordinary Pi type and the L2 product apart: plain finite functions carry their ordinary product/sup norm, while EuclideanSpace ℂ ι is defined as PiLp 2, precisely to carry the Hilbert L2 norm. An OrthonormalBasis represents a finite Hilbert space by EuclideanSpace, not by the plain Pi type.   [ABSTRACT][LEAN]
K1 falsifier
Choose any PairIndex with N = 1, and let the coefficient vector have two entries equal to 1 and the third equal to 0.
For the plain Pi norm:
∥q∥∞​=1.
The corresponding synthesis is the sum of two distinct production modes. Since V_n_m_orthonormal proves those modes orthonormal,
∥ccmFiniteSynthesis(q)∥2​=2​.
Therefore the literal synthesis cannot satisfy norm_map from the plain function carrier. The failure is mathematical, not API friction. The project already proves the required orthonormality and builds the finite projection from the resulting orthonormal basis.   [FINITE_CELL][LEAN]
This is a direct C04 kill: the plain Pi carrier and EuclideanSpace have the same coordinates but different norm laws. Treating the former as the Hilbert coefficient carrier would also be a C10 surrogate substitution.
Repaired public surface
The public names remain exactly the three requested names.
1. ccmFiniteSynthesisEquiv
leannoncomputable def ccmFiniteSynthesisEquiv
    (i : PairIndex) :
    EuclideanSpace ℂ (CCMModeFinite i.N) ≃ₗᵢ[ℂ] E_m_N i :=
  (ccmFiniteModeOrthonormalBasis i).repr.symm
The source must be EuclideanSpace, not:
leanCCMModeFinite i.N → ℂ
The underlying algebraic coefficient row remains the existing plain function. Conversion into the Hilbert coefficient carrier is exact:
leanWithLp.toLp 2 q
with inverse:
leanWithLp.ofLp
No numerical or fitted norm conversion is involved.
2. sourceCCMFiniteRieszOperator
leannoncomputable def sourceCCMFiniteRieszOperator
    (i : PairIndex) :
    Module.End ℂ (E_m_N i) :=
  (ccmFiniteSynthesisEquiv i).toLinearEquiv.conj
    (sourceCCMFiniteOperatorEuclidean i)
Here the private Euclidean coefficient operator is the exact algebraic operator transported through the WithLp wrapper:
leanprivate noncomputable def sourceCCMFiniteOperatorEuclidean
    (i : PairIndex) :
    Module.End ℂ (EuclideanSpace ℂ (CCMModeFinite i.N)) :=
  (WithLp.linearEquiv 2 ℂ
      (CCMModeFinite i.N → ℂ)).symm.conj
    (sourceCCMFiniteOperator i)
LinearEquiv.conj is the exact source-to-target endomorphism transport:
f⟼e∘f∘e−1.
3. Source-trial action theorem
The requested theorem statement remains unchanged:
leantheorem sourceCCMFiniteRieszOperator_apply_sourceTrial
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    let xE : E_m_N i :=
      kTrial_m_N
        i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i)
    ((sourceCCMFiniteRieszOperator i xE : E_m_N i) : H_m i) =
      ccmFiniteSynthesis i
        (sourceCCMFiniteOperator i
          (sourceCCMComplexRow S i)) := by
  ...
[FINITE_CELL][CONDITIONAL]
Minimum implementation-sensitive Lean route
Private helper 1 — exact index equivalence
Reproduce privately the existing exact bijection:
leanCCMModeFinite i.N ≃ {n : ℤ // n ∈ modeSet i}
with forward map:
leanj ↦ ⟨ccmModeFinite i.N j, ...⟩
This helper must remain private. Its source order is literally:
-N, -N+1, ..., 0, ..., N.
Private helper 2 — mode-indexed orthonormal basis
Reuse the exact construction already used by finite projection reconstruction:
leanlet sourceCarrier :=
  Submodule.span ℂ ((modeSet i).image (V_n_m i) : Set (H_m i))

let carrierEquiv :
    sourceCarrier ≃ₗᵢ[ℂ] E_m_N i :=
  LinearIsometryEquiv.ofEq sourceCarrier (E_m_N i) hcarrier

let b0 : OrthonormalBasis (modeSet i) ℂ (E_m_N i) :=
  (OrthonormalBasis.span
      (V_n_m_orthonormal i)
      (modeSet i)).map carrierEquiv
Then reindex it to the exact CCM carrier:
leanprivate noncomputable def ccmFiniteModeOrthonormalBasis
    (i : PairIndex) :
    OrthonormalBasis (CCMModeFinite i.N) ℂ (E_m_N i) :=
  b0.reindex
    (exact_CCMModeFinite_to_modeSet_equivalence i).symm
Pinned Mathlib supplies OrthonormalBasis.reindex, and its application law preserves exactly the mode selected by the inverse index equivalence. It also supplies OrthonormalBasis.sum_repr_symm, which reconstructs a vector from its Euclidean coordinates.   [ABSTRACT][LEAN]
Private helper 3 — forward-map identity
Prove privately:
leanprivate theorem ccmFiniteSynthesisEquiv_apply_toLp
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ) :
    ((ccmFiniteSynthesisEquiv i (WithLp.toLp 2 q) :
        E_m_N i) : H_m i) =
      ccmFiniteSynthesis i q := by
  ...
The proof uses:
leanOrthonormalBasis.sum_repr_symm
OrthonormalBasis.reindex_apply
plus the exact j ↦ j-N mode equivalence.
Public theorem proof
Let:
leanq := sourceCCMComplexRow S i
q₂ := WithLp.toLp 2 q
and let xE be the literal kTrial_m_N.


Prove:
leanccmFiniteSynthesisEquiv i q₂ = xE
by Subtype.ext, the private forward-map identity, and the already proved:
leanccmFiniteSynthesis_sourceCCMComplexRow S i


Rewrite xE through this equality.


Unfold the two conjugations.


Use:
leanLinearEquiv.conj_apply
LinearEquiv.apply_symm_apply


Reduce the Euclidean operator application to:
leanWithLp.toLp 2
  (sourceCCMFiniteOperator i q)


Apply the private forward-map identity again.


No form theorem, domain theorem, limit, or ambient operator appears.
K6 object precommit
YAMLK6_OBJECT_PRECOMMIT:
  algebraic_coefficient_carrier:
    type: CCMModeFinite_iN_to_Complex
    norm_semantics: NOT_USED_AS_HILBERT_NORM

  Hilbert_coefficient_carrier:
    type: EuclideanSpace_Complex_CCMModeFinite_iN
    norm: L2

  exact_wrapper:
    forward: WithLp.toLp_2
    inverse: WithLp.ofLp

  finite_subspace:
    type: E_m_N_i

  synthesis_isometry:
    source: EuclideanSpace_Complex_CCMModeFinite_iN
    target: E_m_N_i
    order: minus_N_through_N

  coefficient_operator:
    type: End_plain_coefficient_functions
    object: sourceCCMFiniteOperator_i

  Euclidean_coefficient_operator:
    type: End_EuclideanSpace
    construction: WithLp_conjugation

  finite_subspace_operator:
    type: End_E_m_N_i
    construction: synthesis_conjugation

  explicitly_not_claimed:
    - associated_ambient_Weil_operator_A_m
    - selected_trial_membership_in_Dom_A_m
    - P_m_N_A_m_compression
    - restricted_form_characterization_in_Lean
    - continuum_residual
    - H4a1b
Plants
The five B2 plants remain mandatory. One release-gate plant is added.
P057-B2-0 — plain-Pi norm mismatch
Mutation:
leanccmFiniteSynthesisEquiv :
  (CCMModeFinite i.N → ℂ) ≃ₗᵢ[ℂ] E_m_N i
Required result:
GOAL057_B2_PLAIN_PI_ISOMETRY_CARRIER_MISMATCH
Witness: N=1, two unit coefficients. Sup norm is 1; synthesis norm is sqrt 2.
P057-B2-1 — form compression is not operator compression
Mutation:
finite source matrix represents the restricted source form
⇒ finite operator = A_m restricted/compressed
Required result:
SOURCE_WEIL_FORM_COMPRESSION_NOT_OPERATOR_COMPRESSION
P057-B2-2 — operator-domain erasure
Mutation:
leanA_m : Module.End ℂ (H_m i)
Required result:
SOURCE_WEIL_OPERATOR_DOMAIN_ERASURE
P057-B2-3 — projection codomain mismatch
Mutation: identify P_m_N i : H_m i → E_m_N i with an ambient endomorphism without inclusion.
Required result:
SOURCE_WEIL_PROJECTION_CODOMAIN_MISMATCH
P057-B2-4 — coefficient/subspace carrier alias
Mutation:
sourceCCMFiniteOperator i
=
sourceCCMFiniteRieszOperator i
without both WithLp transport and ccmFiniteSynthesisEquiv.
Required result:
SOURCE_WEIL_COEFFICIENT_VS_SUBSPACE_CARRIER_MISMATCH
P057-B2-5 — mode-order mutation
Mutation: reverse j ↦ j-N without conjugating the matrix by the same permutation.
Required result:
SOURCE_WEIL_MODE_ORDER_INTERTWINER_MISMATCH
Scope and ledger effect
A successful child proves only:
exact coefficient CCM action⟷exact finite-subspace action on Em,N​.​
[FINITE_CELL][LEAN]
It does not prove that this operator is the compression of the domain-restricted associated Weil operator. It does not produce the continuum Input-B numerator.
Therefore:
ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE:
  ADVANCED_NOT_CLOSED.

TEN-CHECKPOINT LEDGER:
  0 closed / 10 remaining.
Strongest attack

Even after the Euclidean repair, sourceCCMFiniteRieszOperator is defined by conjugating the matrix. Is this merely a tautological rename?

Partly. The action theorem is algebraically short because the operator is intentionally defined by coordinate conjugation.
Its route value is narrower but real:


the coefficient carrier is replaced by the literal finite Hilbert subspace;


the exact source mode order is retained;


the normalized projected source trial becomes an actual input to an operator on E_m_N;


the next gap becomes a single domain-safe statement about the associated ambient operator.


The transaction must therefore be classified as:
FINITE_RIESZ_CARRIER_BIND
not:
LEAN_PROOF_OF_RESTRICTED_WEIL_FORM_REPRESENTATION
The name RieszOperator may remain because the source registry assigns that role to the exact matrix in the orthonormal basis. The file’s docstring and closeout must explicitly state that no Lean form-characterization theorem is proved here.
If the implementation claims more than coordinate/subspace transport, the transaction fails.
Final proposal
Implement the repaired child now.
Registered predictions:
P-B2R-1:
  The Euclidean-carrier construction compiles without a new project axiom.

P-B2R-2:
  The action theorem closes by two synthesis rewrites and conjugation
  simplification; no analytic theorem enters.

P-B2R-3:
  The next load-bearing blocker remains selected-kTrial membership in
  Dom(A_m), followed by domain-safe projected action equality.
Prior prediction fate:
P-A8-B2:
  CONFIRMED AND SHARPENED.

  The first obstruction was the source matrix-action boundary.
  This release audit found an additional norm-carrier defect inside the
  proposed repair: plain Pi coordinates are not the Euclidean Hilbert carrier.
Meta closeout
What became smaller?
The finite carrier bind is reduced to one exact change:
plain coefficient functions
→ WithLp/PiLp-2 Euclidean coefficients
→ E_m_N.
What was killed?


the plain-Pi LinearIsometryEquiv;


implicit use of the sup norm as the coefficient Hilbert norm;


direct aliasing of the coefficient operator with the subspace operator.


What must not be tried again?
Do not place Hilbert semantics on CCMModeFinite → ℂ without the explicit EuclideanSpace/WithLp wrapper.
Current smallest named gap after implementation:
SELECTED_KTRIAL_ASSOCIATED_WEIL_OPERATOR_DOMAIN_AND_COMPRESSION
Next cheapest decisive test:
Audit whether the literal kTrial_m_N has any source-backed regularity theorem strong enough to imply membership in the associated Weil operator domain, rather than merely the closed form domain.
YAMLiteration:
  target: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND
  status: OPEN
  failed_strategy: plain_Pi_coefficients_as_Hilbert_coefficient_space
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: EUCLIDEAN_CCM_COEFFICIENT_CARRIER_BIND
  invariant_learned: identical coordinates do not imply identical norms or operator categories
  forbidden_future_move: construct_ccmFiniteSynthesisEquiv_from_plain_Pi_sup_norm
  next_decisive_test: compile_the_repaired_Euclidean_carrier_child
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAMLOPERATIVE_CLASS:
  TRY_GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_REPAIRED

MODE:
  IMPLEMENT_EXACTLY_ONE_REPAIRED_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 1ba34ff53f80071c29018860ef826f636279de10
  require_origin_equal: true

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean

SOLE_IMPORT:
  - Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - ccmFiniteSynthesisEquiv
    - sourceCCMFiniteRieszOperator
  theorems:
    - sourceCCMFiniteRieszOperator_apply_sourceTrial
  total_public_declarations: 3

REQUIRED_TYPE_REPAIR:
  ccmFiniteSynthesisEquiv: |
    noncomputable def ccmFiniteSynthesisEquiv
        (i : PairIndex) :
        EuclideanSpace ℂ (CCMModeFinite i.N) ≃ₗᵢ[ℂ] E_m_N i :=
      (ccmFiniteModeOrthonormalBasis i).repr.symm

FORBIDDEN_TYPE:
  - "(CCMModeFinite i.N → ℂ) ≃ₗᵢ[ℂ] E_m_N i"

PRIVATE_HELPERS_ALLOWED:
  - exact_CCMModeFinite_to_modeSet_equivalence
  - ccmFiniteModeOrthonormalBasis
  - ccmFiniteSynthesisEquiv_apply_toLp
  - sourceCCMFiniteOperatorEuclidean
  - local carrier and reindex lemmas

PRIVATE_BASIS_ROUTE:
  - reuse V_n_m_orthonormal
  - reuse OrthonormalBasis.span
  - reuse LinearIsometryEquiv.ofEq for sourceCarrier = E_m_N
  - reindex by exact_CCMModeFinite_to_modeSet_equivalence.symm
  - define synthesis equivalence as basis.repr.symm
  - prove forward application with OrthonormalBasis.sum_repr_symm

PRIVATE_COEFFICIENT_OPERATOR:
  statement: |
    private noncomputable def sourceCCMFiniteOperatorEuclidean
        (i : PairIndex) :
        Module.End ℂ (EuclideanSpace ℂ (CCMModeFinite i.N)) :=
      (WithLp.linearEquiv 2 ℂ
          (CCMModeFinite i.N → ℂ)).symm.conj
        (sourceCCMFiniteOperator i)

PUBLIC_RIESZ_OPERATOR:
  statement: |
    noncomputable def sourceCCMFiniteRieszOperator
        (i : PairIndex) :
        Module.End ℂ (E_m_N i) :=
      (ccmFiniteSynthesisEquiv i).toLinearEquiv.conj
        (sourceCCMFiniteOperatorEuclidean i)

PUBLIC_THEOREM_EXACT:
  statement: |
    theorem sourceCCMFiniteRieszOperator_apply_sourceTrial
        (S : ProlateCanonicalSourceData)
        (i : PairIndex) :
        let xE : E_m_N i :=
          kTrial_m_N
            i
            (prolateCombination (S.source.pair i))
            (S.source.eStar_memLp i)
            (S.source.trialNonzero i)
        ((sourceCCMFiniteRieszOperator i xE : E_m_N i) : H_m i) =
          ccmFiniteSynthesis i
            (sourceCCMFiniteOperator i
              (sourceCCMComplexRow S i)) := by
      ...

PROOF_ROUTE:
  - define q as sourceCCMComplexRow S i
  - define q2 as WithLp.toLp 2 q
  - prove ccmFiniteSynthesisEquiv i q2 = xE by Subtype.ext
  - consume ccmFiniteSynthesis_sourceCCMComplexRow
  - unfold the two LinearEquiv conjugations
  - use LinearEquiv.conj_apply and apply_symm_apply
  - reduce the Euclidean operator to WithLp.toLp 2 of the plain matrix action
  - apply ccmFiniteSynthesisEquiv_apply_toLp
  - perform no form, domain, limit, or ambient-operator argument

MANDATORY_PLANTS:
  - id: P057_B2_0_PLAIN_PI_NORM
    mutation: use_plain_Pi_as_source_of_LinearIsometryEquiv
    witness: N_1_two_unit_coefficients
    expected: GOAL057_B2_PLAIN_PI_ISOMETRY_CARRIER_MISMATCH

  - id: P057_B2_1_FORM_COMPRESSION
    expected: SOURCE_WEIL_FORM_COMPRESSION_NOT_OPERATOR_COMPRESSION

  - id: P057_B2_2_DOMAIN_ERASURE
    expected: SOURCE_WEIL_OPERATOR_DOMAIN_ERASURE

  - id: P057_B2_3_PROJECTION_CODOMAIN
    expected: SOURCE_WEIL_PROJECTION_CODOMAIN_MISMATCH

  - id: P057_B2_4_CARRIER_ALIAS
    expected: SOURCE_WEIL_COEFFICIENT_VS_SUBSPACE_CARRIER_MISMATCH

  - id: P057_B2_5_MODE_ORDER
    expected: SOURCE_WEIL_MODE_ORDER_INTERTWINER_MISMATCH

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean
  - target lake build
  - full lake build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - scan forbidden imports for aristotle_output and ACTIVE RequestProject
  - verify exactly 2 public definitions and 1 public theorem
  - verify all other declarations are private
  - fire P057_B2_0 and all five inherited plants
  - remove mutation files
  - print axioms sourceCCMFiniteRieszOperator_apply_sourceTrial
  - require axiom set to be a subset of [propext, Classical.choice, Quot.sound]
  - strict Spine validation
  - proof database import
  - three SQLite integrity checks
  - git diff --check
  - exact git status report

CLOSEOUT_MUST_STATE:
  - FINITE_RIESZ_CARRIER_BIND_ONLY
  - NO_LEAN_FORM_CHARACTERIZATION
  - NO_Dom_A_m_MEMBERSHIP
  - NO_AMBIENT_OPERATOR_COMPRESSION
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_MISSING

SUCCESS:
  GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_PROVED

NEXT_GAP_AFTER_SUCCESS:
  SELECTED_KTRIAL_ASSOCIATED_WEIL_OPERATOR_DOMAIN_AND_COMPRESSION

FORBIDDEN:
  - use plain Pi as the Hilbert coefficient carrier
  - expand the public surface
  - modify B1 or earlier production files
  - name the finite operator A_m
  - assert selected trial membership in Dom_A_m
  - assert ambient operator compression
  - characterize a Lean Weil form not present in the file
  - call the finite residual the continuum numerator
  - close H4a1b
  - decrement the ten-checkpoint ledger
  - edit Q3.Main
  - create Bus_010
  - release Goal_055
  - submit Aristotle
  - promote Route_B
  - make PX or RH claim
  - open a fresh chat

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
