STATUS: OPEN — FINITE SOURCE-COMPLEX RESIDUAL BIND RATIFIED; EXACT UNIT-ROW PROOF SELECTED
YAML
STATUS: OPEN

PRIMARY: RATIFY_SOURCE_COMPLEX_FINITE_RESIDUAL_BIND_READY
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: dea558d9bb0c37c256a49397dec31a3f1568ff6e
  ORIGIN_HEAD_EQUALS_PIN: true

  CONTEXT_PACK:
    path: PROSHKA_CONTEXT_GOAL057_B1_RESIDUAL_PREFLIGHT_2026-08-08.md
    observed_sha256: 6bad3cc1a6eab3b126b74bffa5224157cebf10853da082e3ad268ace6e3e3f2f
    status: PASS_READABLE

  PRIOR_VERDICT:
    expected_sha256: 895388154c316a5dff6c1cde88a655565ba3ef5f66144d9bc11e3a9076bfc126
    observed_sha256: 895388154c316a5dff6c1cde88a655565ba3ef5f66144d9bc11e3a9076bfc126
    status: PASS

PREFLIGHT_CLASSIFICATION:
  reported: SOURCE_COMPLEX_FINITE_RESIDUAL_BIND_READY
  ruling: RATIFIED_FINITE_ONLY

  exact_source_row: PASS
  exact_finite_carrier: PASS
  exact_mode_order: PASS
  exact_parameter_lock: PASS
  exact_finite_matrix: PASS
  finite_complex_action_well_typed: PASS

  coefficient_row_unit_theorem_currently_named: false
  coefficient_row_unit_theorem_executable_now: true

  continuum_operator_compression: OPEN
  actual_continuum_numerator: OPEN
  projection_tail_identified_with_Weil_residual: false
  H4a1b_closed: false

NORMALIZATION_DECISION:
  quotient_normalization_in_production: REJECT
  prove_exact_unit_row_now: REQUIRED
  fallback_to_silent_renormalization: forbidden
  fallback_to_quotient_after_unit_proof_failure: forbidden

SELECTED_CHILD:
  name: GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND
  owned_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean
  namespace: Q3.RouteB.D0Pstar

  public_definitions: 6
  public_theorems: 6
  public_structures: 0
  public_axioms: 0

  progress_if_proved: PROOF_PROGRESS

STOP: GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND_MISSING
SUCCESS: GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND_PROVED

DIRECT_CONSUMER:
  node: H4a1b_ExactRouteBAmbientResidualCrosswalk
  authorized_in_this_transaction: false
  status_after_selected_child: OPEN_EXACT_COMPRESSION_ACTION_REQUIRED

DOWNSTREAM_LEAVES_TOUCHED_NOT_CLOSED:
  - H4a2b_ExactRouteBComponentRateInstantiation
  - H4a3b2_ExactRouteBSpectralResidualRateInstantiation
  - H3a2b_ExactSpectralProjectiveRateInstantiation
  - H3b2b_ExactWeightedProjectiveInstantiation

COARSE_CHECKPOINTS:
  delegated_mathematical_checkpoints: 10
  checkpoints_closed_by_selected_child: 0
  checkpoints_strictly_advanced: 1
  advanced_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  owner_gate: PX_RH_CLAIM
  current_total_including_owner_gate: 11

PHASE:
  same_six_field_key: true
  fresh_chat: false
  front_change: false

ARSENAL:
  mandate_accepted: true
  cards_applied:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
1. Source-lock and preflight audit

The current rh_clean branch resolves exactly to dea558d9bb0c37c256a49397dec31a3f1568ff6e, the commit that records the Goal-057 reviews and selects this residual preflight.

The attached context pack is internally consistent with that pin, and the embedded prior verdict rehashes exactly to the supplied 895388154c…fc126. 

PROSHKA_CONTEXT_GOAL057_A8_MAX_…

The source row is not a free coefficient selector. ProlateCanonicalSourceData.canonical_kTrial identifies it exactly with

lean
c_n i
  (prolateCombination (S.source.pair i))
  (S.source.eStar_memLp i)
  (S.source.trialNonzero i)
  n

and c_n itself is the conjugate-first coefficient

lean
inner ℂ (V_n_m i n) (kTrial_m_N ... : H_m i).

PROSHKA_REQUEST_GOAL057_A5_DEFE…

 

goal057_proshka_deferred_context

 [FINITE_CELL][LEAN]

The finite carrier and order are also literal:

CCMModeFinite N = Fin (2*N+1)
ccmModeFinite N j = j - N

so the array order is exactly

-N, -N+1, ..., 0, ..., N.

The matrix entry is the full source entry

lean
ccmWeilTauN1 i.m
  (ccmModeFinite i.N j)
  (ccmModeFinite i.N k),

and the real matrix is symmetric. [FINITE_CELL][LEAN]

Therefore the read-only classification is ratified:

SOURCE_COMPLEX_FINITE_RESIDUAL_BIND_READY.
	​


The scope qualifier is load-bearing:

finite source matrix residual:
  READY;

compressed continuum Weil-operator residual:
  NOT YET IDENTIFIED.

[FINITE_CELL][LEAN]

2. Unit-row decision
Ruling
Prove the exact coefficient-row unit theorem now.
	​


Do not retain quotient normalization in the production object.

The quotient was a correct preflight fallback while unit normalization was unverified. It is no longer the minimal production interface because two exact ingredients already exist:

The normalized projected source trial satisfies

lean
‖kTrial_m_N ...‖ = 1.

goal057_proshka_deferred_context

 [FINITE_CELL][LEAN]

The finite projection is reconstructed exactly in the literal modes:

lean
(P_m_N i f : H_m i) =
  ∑ n ∈ modeSet i,
    inner ℂ (V_n_m i n) f • V_n_m i n.

[FINITE_CELL][LEAN]

Since kTrial_m_N belongs to E_m_N, its projection is itself. Taking the inner product of the finite reconstruction with the same vector, using the already-proved orthonormality of V_n_m, gives finite Parseval:

n=−N
∑
N
	​

∣⟨V
n,m
	​

,kTrial
m,N
	​

⟩∣
2
=∥kTrial
m,N
	​

∥
2
=1.

The only new bookkeeping is the exact finite bijection between CCMModeFinite i.N and modeSet i. No global completeness theorem, limiting argument, or new analysis is required.

Keeping the quotient after this point would create two unnecessary normalizations:

source normalization:
  kTrial_m_N already has norm one;

new coordinate normalization:
  divide its exact coefficient row again.

That second normalization would obscure source identity and create a new C04/C10 risk.

If the exact finite reindex cannot be proved, the transaction stops with:

GOAL057_SOURCE_COMPLEX_ROW_UNIT_REINDEX_GAP

It must not silently revert to the quotient.

3. Selected production file
lean
import Q3.Proofs.RouteB.D0ProlateKTrialSource
import Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
import Q3.Proofs.RouteB.AmbientResidualSplit
lean
namespace Q3.RouteB.D0Pstar

No import from ACTIVE/, aristotle_output/, a numerical payload, or the Phase-1 surrogate is permitted.

3.1 Exact public definitions
lean
/-- Synthesis in the literal source mode order `-N,...,N`. -/
noncomputable def ccmFiniteSynthesis
    (i : PairIndex) :
    (CCMModeFinite i.N → ℂ) →ₗ[ℂ] H_m i where
  toFun q :=
    ∑ j, q j • V_n_m i (ccmModeFinite i.N j)
  map_add' := by
    intro q r
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c q
    simp [smul_smul, Finset.smul_sum]
lean
/-- Exact complex coefficient row of the normalized projected source trial. -/
noncomputable def sourceCCMComplexRow
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    CCMModeFinite i.N → ℂ :=
  fun j =>
    S.canonical.kTrial.kTrial i
      (ccmModeFinite i.N j)
lean
/-- Literal CCM source matrix, complexified entrywise without changing order. -/
noncomputable def sourceCCMFiniteMatrix
    (i : PairIndex) :
    Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
  fun j k =>
    (ccmWeilMatFinite i.m i.N j k : ℂ)
lean
/-- Finite source matrix action on the exact complex carrier. -/
noncomputable def sourceCCMFiniteOperator
    (i : PairIndex) :
    Module.End ℂ (CCMModeFinite i.N → ℂ) :=
  (sourceCCMFiniteMatrix i).mulVecLin
lean
/-- Real Rayleigh value of the exact unit source row. -/
noncomputable def sourceCCMFiniteRayleigh
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) : ℝ :=
  (star (sourceCCMComplexRow S i) ⬝ᵥ
    (sourceCCMFiniteMatrix i *ᵥ
      sourceCCMComplexRow S i)).re
lean
/-- Exact finite CCM Rayleigh residual of the source row. -/
noncomputable def sourceCCMFiniteResidual
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    CCMModeFinite i.N → ℂ :=
  ambientResidual
    (sourceCCMFiniteOperator i)
    (sourceCCMComplexRow S i)
    (sourceCCMFiniteRayleigh S i : ℂ)

These definitions introduce no fitted scalar, real-part projection, parity projection, independent coefficient family, or continuum operator claim.

4. Exact public theorem surface
4.1 Source provenance
lean
@[simp] theorem sourceCCMComplexRow_apply
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (j : CCMModeFinite i.N) :
    sourceCCMComplexRow S i j =
      c_n i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i)
        (ccmModeFinite i.N j) := by
  exact S.canonical_kTrial
    i (ccmModeFinite i.N j)

[FINITE_CELL][LEAN]

4.2 Exact source-vector reconstruction
lean
theorem ccmFiniteSynthesis_sourceCCMComplexRow
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    ccmFiniteSynthesis i (sourceCCMComplexRow S i) =
      (kTrial_m_N
        i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i) :
        H_m i) := by
  ...

This theorem is the anti-tautology core of the child. It proves that the finite row synthesizes the literal normalized projected source object.

4.3 Exact unit row
lean
theorem sourceCCMComplexRow_unit
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    star (sourceCCMComplexRow S i) ⬝ᵥ
      sourceCCMComplexRow S i = 1 := by
  ...

No quotient remains after this theorem.

4.4 Hermitian complexification
lean
theorem sourceCCMFiniteMatrix_isHermitian
    (i : PairIndex) :
    (sourceCCMFiniteMatrix i).IsHermitian := by
  ...

The proof must work entrywise from ccmWeilTauN1_symm i.m i.hm. It must not require 1 ≤ i.N; symmetry is meaningful also at N=0.

4.5 Rayleigh reality
lean
theorem sourceCCMFiniteRayleigh_coe
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    (sourceCCMFiniteRayleigh S i : ℂ) =
      star (sourceCCMComplexRow S i) ⬝ᵥ
        (sourceCCMFiniteMatrix i *ᵥ
          sourceCCMComplexRow S i) := by
  ...

The proof must derive zero imaginary part from Hermiticity. Taking .re and discarding the imaginary part without proving it zero is forbidden.

4.6 Residual orthogonality
lean
theorem sourceCCMComplexRow_inner_residual_eq_zero
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    star (sourceCCMComplexRow S i) ⬝ᵥ
      sourceCCMFiniteResidual S i = 0 := by
  ...

This uses the exact unit-row theorem and the exact Rayleigh equality. It is the first non-definitional mathematical consumer of the finite residual.

5. Proof route
Step 1 — private mode equivalence

Construct privately an equivalence

lean
CCMModeFinite i.N ≃ {n : ℤ // n ∈ modeSet i}

whose forward map is exactly ccmModeFinite i.N.

Use it to establish:

lean
∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)
  =
∑ n ∈ modeSet i, F n.

No reversal or reordered matrix is permitted.

Step 2 — exact synthesis

Apply coe_P_m_N_apply_eq_sum_inner_V_n_m_smul to the exact kTrial_m_N. Since that vector is in E_m_N, its orthogonal projection is itself. Reindex the resulting modeSet sum through the private equivalence and rewrite coefficients by canonical_kTrial.

Step 3 — finite Parseval

Prove privately that synthesis in the literal finite orthonormal family preserves the finite coordinate inner product:

⟨synth(q),synth(r)⟩=
j
∑
	​

q
j
	​

	​

r
j
	​

.

Apply this to the source row, rewrite its synthesis to kTrial_m_N, and use norm_kTrial_m_N = 1.

This uses only the finite span. It does not consume the global completeness of all V_n_m.

Step 4 — Hermitian matrix

Expand Matrix.IsHermitian pointwise. Use real-entry conjugation and ccmWeilTauN1_symm. No numerical symmetry check is admissible.

Step 5 — Rayleigh reality

Use the Hermitian quadratic-form reality lemma—equivalently the existing project use of qf_isHermitian_im—to prove the imaginary part is zero, then close by Complex.ext.

Step 6 — residual orthogonality

Expand ambientResidual, distribute the conjugate-first dot product, rewrite the quadratic term by sourceCCMFiniteRayleigh_coe, and rewrite the norm term by sourceCCMComplexRow_unit.

6. Exact H4a1b consumer shape

The selected child does not prove H4a1b. It gives H4a1b the exact finite object it must consume.

Let

lean
x : H_m i :=
  (kTrial_m_N
    i
    (prolateCombination (S.source.pair i))
    (S.source.eStar_memLp i)
    (S.source.trialNonzero i) :
    H_m i)

The direct downstream theorem must have the following shape:

lean
theorem exactRouteBAmbientResidualCrosswalk
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (A P : Module.End ℂ (H_m i))
    (hCompressedAction :
      P (A x) =
        ccmFiniteSynthesis i
          (sourceCCMFiniteOperator i
            (sourceCCMComplexRow S i))) :
    ambientResidual A x
        (sourceCCMFiniteRayleigh S i : ℂ) =
      ccmFiniteSynthesis i
          (sourceCCMFiniteResidual S i) +
        projectionLeakage A P x := by
  ...

The generic algebraic split already proves that ambient residual equals compressed residual plus leakage. [ABSTRACT][LEAN]

The missing load-bearing hypothesis is hCompressedAction:

P(Ax)=synth(K
C
q
src
).

That is the exact continuum/form-to-finite-operator compression theorem. This selected child does not manufacture it from definitions.

Therefore, after success:

finite source residual:
  PROVED;

H4a1b exact ambient crosswalk:
  OPEN on hCompressedAction.
7. K6 object precommit
YAML
K6_OBJECT_PRECOMMIT:
  source_structure:
    Q3.RouteB.D0Pstar.ProlateCanonicalSourceData

  source_trial:
    normalized projected kTrial_m_N

  finite_carrier:
    CCMModeFinite i.N -> Complex

  source_row:
    canonical.kTrial.kTrial i (ccmModeFinite i.N j)

  source_row_interpretation:
    inner Complex (V_n_m i n) kTrial_m_N

  mode_order:
    j maps to j - i.N

  matrix:
    entrywise complexification of ccmWeilMatFinite i.m i.N

  matrix_orientation:
    unchanged

  inner_product:
    conjugate-linear in first argument

  normalization:
    exact source unit normalization
    no quotient
    no post-hoc renormalization

  residual:
    Kq - a*q

  scope:
    FINITE_CELL_ONLY

  explicitly_not_claimed:
    - compressed continuum Weil action
    - projection leakage rate
    - true spectral gap
    - ground-state tracking
    - H4a1b closure
    - any H-slot

This object must be fixed before mutation tests.

8. Mandatory plants
P057-B1 — source-row surrogate

Mutation:

sourceCCMComplexRow
→ normalized J-even projection of Re(sourceCCMComplexRow).

Required result:

SOURCE_COMPLEX_ROW_SURROGATE_REJECTED

sourceCCMComplexRow_apply and the synthesis theorem must fail. [C04][C10]

P057-B2 — tiny norm is not equality

Attempt to import or use the approximately 1.7⋅10
−30
 Phase-1 distance as an exact rewrite.

Required result:

SMALL_NORM_NOT_EXACT_SOURCE_IDENTITY

No production theorem may depend on the Phase-1 numeric row.

P057-B3 — mode reversal

Mutation:

ccmModeFinite i.N j
→ -ccmModeFinite i.N j

without simultaneously conjugating the matrix by the exact reflection permutation.

Required result:

SOURCE_COMPLEX_MODE_ORDER_MISMATCH

The synthesis theorem must fail.

P057-B4 — conjugation deletion

Mutation:

star q ⬝ᵥ Kq
→ q ⬝ᵥ Kq.

Required result:

SOURCE_COMPLEX_RAYLEIGH_CONJUGATION_MISMATCH

Rayleigh reality or residual orthogonality must fail on a generic complex control.

P057-B5 — source normalizer deletion

Mutation:

kTrial_m_N
→ gTrial_m_N

or delete sTrial_m_N.

Required result:

SOURCE_COMPLEX_ROW_UNIT_NORMALIZATION_MISMATCH

The exact unit-row theorem must fail.

P057-B6 — ambient-action smuggling

Mutation:

declare sourceCCMFiniteOperator to be the compressed continuum Weil operator
by definitional equality.

Required result:

SOURCE_COMPLEX_AMBIENT_ACTION_CROSSWALK_MISSING

This plant is a source audit, not a numerical test. [C10]

9. Validation and axiom surface

Required:

Bash
cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean

lake build \
  Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual

lake build

cd ..

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean

Surface gate:

public definitions: exactly 6
public theorems: exactly 6
public structures: 0
public axioms: 0

Taint scan must reject:

sorry
admit
exact?
native_decide
axiom
opaque
Float
aristotle_output
ACTIVE/requests imports
Phase-1 numeric artifacts

Required axiom output for every public theorem:

[propext, Classical.choice, Quot.sound]

Also require:

all six plants fire;
temporary mutant files removed;
67/67 orchestration tests pass;
strict Spine passes;
proof database import passes;
three SQLite integrity checks pass;
git diff --check passes;
exact git status is reported.

Only the new owned file may be a mathematical source change. Phase 4A, Phase 4B, the finite matrix source, Goal 055, and Q3.Main remain untouched.

10. Coarse-checkpoint and fan-out ledger

The current project state still contains ten delegated mathematical checkpoints plus the sole PX/RH owner gate.

This child does not close any coarse checkpoint. It strictly advances one:

ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE

from:

source object and finite carrier unbound

to:

exact finite source row, unit normalization,
finite Hermitian action, Rayleigh scalar, and finite residual proved;
continuum compression still open.

The other nine delegated checkpoints remain unchanged:

PROLATE_CANONICAL_SOURCE_WITNESS
FINITE_QW_REAL_ZERO_SAME_FAMILY
DETREG_ZERO_FREE_GAUGE_NORMALIZATION_LOCK
JOINT_FINITE_TO_CONTINUUM_GROUND_TRANSFORM
TRUE_WEIL_GAP_OR_CLUSTER_DISCRIMINATOR
WEIGHTED_GROUND_TO_TRIAL_COMPACT_OPEN_TRANSFER
CCM_TRIAL_TO_XI_PROJECT_CROSSWALK
SELECTED_TRIAL_NORMALIZER_BOUNDED
SAME_FAMILY_ASSEMBLY_EXPORT

The four other exact-instantiation leaves remain touched but open. No rate, evaluation envelope, joint filter, gap, or compact-open theorem is bundled into this transaction.

11. Strongest attack

This child defines r=Kq−aq, proves elementary facts about it, and then advertises progress toward the actual numerator. Is that not the tautological wrapper previously forbidden?

It would be, without the synthesis and unit theorems.

The selected child must prove three non-definitional facts before its residual has route value:

the row is exactly the source coefficient row;

synthesis of that row is the literal normalized projected source trial;

the row has exact unit norm in the finite complex carrier.

Those facts rule out the Phase-1 surrogate and a second normalization.

The strongest surviving objection remains valid:

Why is the literal CCM matrix action the compression of the continuum Weil operator on that source trial?

It is not proved here.

That exact statement is isolated as hCompressedAction in the H4a1b consumer. The finite residual may be called:

the exact finite CCM source-matrix residual.

It may not yet be called:

the actual continuum Input-B numerator.
12. Final proposal and prediction score

Ratify the finite preflight and materialize the exact source object now.

Registered prediction fate:

P-A8-B1:
  CONFIRMED.
  Source row and CCM matrix share the exact finite carrier and order.

P-A8-B2:
  CONFIRMED.
  The remaining load-bearing statement is the compressed ambient
  operator-action identity, not the formal residual definition.

P-A8-B3:
  CONFIRMED.
  Real/J-even Phase-1 substitution fails exact source identity
  despite the tiny numerical distance.

The smallest gap after a successful child is:

SOURCE_COMPLEX_COMPRESSED_WEIL_ACTION_CROSSWALK

The cheapest next decisive test is a source audit of the exact statement

P
m,N
	​

(W
m
	​

kTrial
m,N
	​

)=synth(ccmWeilMatFinite
m,N
	​

q
m,N
src
	​

),

with the exact ambient operator, form domain, projection, and normalization named. That next transaction is not authorized here.

YAML
iteration:
  target: Goal057_source_complex_finite_residual_bind
  status: OPEN
  failed_strategy: quotient_normalization_after_exact_source_unit_data_became_available
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SOURCE_COMPLEX_COMPRESSED_WEIL_ACTION_CROSSWALK
  invariant_learned: exact source synthesis and unit normalization precede every residual or rate claim
  forbidden_future_move: call_the_finite_CCM_residual_the_continuum_numerator_without_hCompressedAction
  next_decisive_test: exact_compressed_Weil_action_source_crosswalk
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
OPERATIVE_CLASS:
  TRY_GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND

TRANSACTION:
  GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: dea558d9bb0c37c256a49397dec31a3f1568ff6e
  expected_prior_verdict_sha256: 895388154c316a5dff6c1cde88a655565ba3ef5f66144d9bc11e3a9076bfc126

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean

IMPORTS_EXACTLY:
  - Q3.Proofs.RouteB.D0ProlateKTrialSource
  - Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
  - Q3.Proofs.RouteB.AmbientResidualSplit

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_DEFINITIONS_EXACTLY:
  - ccmFiniteSynthesis
  - sourceCCMComplexRow
  - sourceCCMFiniteMatrix
  - sourceCCMFiniteOperator
  - sourceCCMFiniteRayleigh
  - sourceCCMFiniteResidual

PUBLIC_THEOREMS_EXACTLY:
  - sourceCCMComplexRow_apply
  - ccmFiniteSynthesis_sourceCCMComplexRow
  - sourceCCMComplexRow_unit
  - sourceCCMFiniteMatrix_isHermitian
  - sourceCCMFiniteRayleigh_coe
  - sourceCCMComplexRow_inner_residual_eq_zero

PRIVATE_HELPERS_ALLOWED:
  - exact_CCMModeFinite_to_modeSet_equivalence
  - finite_sum_reindex
  - finite_synthesis_inner_identity
  - Hermitian_quadratic_reality_helper

NORMALIZATION:
  prove_unit_row_now: true
  use_Rayleigh_quotient: false
  renormalize_source_row: forbidden
  fallback_to_quotient_if_proof_blocked: forbidden

OBJECT_PRECOMMIT:
  source_row: canonical_kTrial_composed_with_ccmModeFinite
  source_trial: exact_normalized_kTrial_m_N
  carrier: CCMModeFinite_iN_to_Complex
  mode_order: j_minus_N
  matrix: exact_entrywise_complexification_of_ccmWeilMatFinite
  inner_convention: conjugate_linear_first
  residual: Kq_minus_aq
  scope: FINITE_CELL

MANDATORY_PLANTS:
  - P057_B1_SOURCE_ROW_SURROGATE
  - P057_B2_SMALL_NORM_NOT_EQUALITY
  - P057_B3_MODE_ORDER_REVERSAL
  - P057_B4_CONJUGATION_DELETION
  - P057_B5_SOURCE_NORMALIZER_DELETION
  - P057_B6_AMBIENT_ACTION_SMUGGLE

STOP:
  GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND_MISSING

SUCCESS:
  GOAL057_SOURCE_COMPLEX_FINITE_RESIDUAL_PRODUCTION_BIND_PROVED

FAILURE_CODES:
  - GOAL057_SOURCE_COMPLEX_ROW_UNIT_REINDEX_GAP
  - SOURCE_COMPLEX_ROW_SURROGATE_REJECTED
  - SMALL_NORM_NOT_EXACT_SOURCE_IDENTITY
  - SOURCE_COMPLEX_MODE_ORDER_MISMATCH
  - SOURCE_COMPLEX_RAYLEIGH_CONJUGATION_MISMATCH
  - SOURCE_COMPLEX_ROW_UNIT_NORMALIZATION_MISMATCH
  - SOURCE_COMPLEX_MATRIX_HERMITIAN_GAP
  - SOURCE_COMPLEX_RAYLEIGH_REALITY_GAP
  - SOURCE_COMPLEX_AMBIENT_ACTION_CROSSWALK_MISSING
  - PUBLIC_SURFACE_MISMATCH
  - AXIOM_PROFILE_MISMATCH
  - LEAN_BUILD_FAIL

VALIDATION:
  - direct_Lean
  - target_build
  - full_build
  - q3_check
  - exact_public_surface_scan
  - taint_and_forbidden_import_scan
  - all_six_plants
  - remove_temporary_mutants
  - print_axioms_all_public_theorems
  - expected_axioms_exactly_standard_triple
  - orchestration_tests_67_of_67
  - strict_Spine
  - proof_database_import
  - three_SQLite_integrity_checks
  - git_diff_check
  - exact_git_status_report

DIRECT_CONSUMER_NOT_AUTHORIZED:
  node: H4a1b_ExactRouteBAmbientResidualCrosswalk
  remaining_exact_input: hCompressedAction
  required_statement: >-
    the exact ambient compression of the source Weil operator applied to
    kTrial_m_N equals ccmFiniteSynthesis of sourceCCMFiniteOperator applied
    to sourceCCMComplexRow

FORBIDDEN:
  - modify_existing_Lean_files
  - modify_Phase4A
  - modify_Phase4B
  - modify_CCMFiniteWeilSourceMatrix
  - import_Phase1_numeric_probe
  - use_Re_or_J_even_projection
  - use_small_norm_as_equality
  - reverse_mode_order
  - drop_first_slot_conjugation
  - renormalize_the_source_row
  - call_finite_residual_a_continuum_residual
  - assert_a_rate_or_limit
  - assert_true_gap
  - close_any_H_slot
  - edit_Q3_Main
  - edit_Goal_055
  - create_Bus_010
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_a_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
