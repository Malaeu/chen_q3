# Goal 058 G1/G3 analytic source wall — Proshka verdict

Captured: 2026-08-14

Natural reasoning time: 18m 51s

Transport: existing Proshka living chat, authoritative UTF-8 pasted-text
bundle SHA-256
`2644b307692d7ef279f624cc2f84c608bf16de0f4d74aa47e3819e3851e95251`,
repository HEAD `82617fd0`.

The verdict body below was extracted from the completed final assistant block
before any mathematical execution.

---

STATUS: OPEN — Ы · Q1 SOURCE-ANALYTIC CARRIER NOT READY; Q2 LOCAL ODD-CORRECTION LEAF READY, FULL FLOOR OPEN
YAML
PRIMARY: Q1_NOT_READY_Q2_CODEX_LOCAL_C1_SELECTED
PRIMARY_COUNT: 1


SOURCE_LOCK:
  BUNDLE_SHA256:
    expected: 2644b307692d7ef279f624cc2f84c608bf16de0f4d74aa47e3819e3851e95251
    observed: 2644b307692d7ef279f624cc2f84c608bf16de0f4d74aa47e3819e3851e95251
    status: PASS
  REPO: /Users/emalam/GitHub/rh_lean_01_2026
  BRANCH: rh_clean
  HEAD: 82617fd0
  WORKTREE: CLEAN_REPORTED
  ROUTE: CHALLENGER_NOT_RH


Q1:
  FRONT: G3
  DECISION: NOT_READY
  ARISTOTLE: NOT_READY
  SMALLEST_SOURCE_OBJECT:
    MODE4_CLASSICAL_EVEN_STURM_LIOUVILLE_SPECTRUM
  SUCCESS_CODE:
    G3_CLASSICAL_EVEN_SPECTRUM_SAME_INDEX_LIMIT_ENDPOINT_COUNTS_2_3_INDEX4_PROVED
  STOP_CODE:
    DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_PROVED_ORDERED_FINITE_TO_CLASSICAL_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING


Q2:
  FRONT: G1
  DECISION: REVISE_TO_C1_C2_C3
  FULL_FLOOR_STATUS: NOT_READY
  LOCAL_C1_LEAF: ACCEPT_CODEX_LOCAL
  ARISTOTLE: REJECT
  LOCAL_SUCCESS_CODE:
    G1_ODD_TAIL_INVERSE_WEIGHTED_CORRECTION_BOUND_PROVED
  FULL_SUCCESS_CODE:
    G1_COFINAL_COMPLEX_TRIAL_COMPLEMENT_FLOOR_PROVED
  STOP_CODE:
Q1 — G3 source-analytic carrier and same-index limit
Decision: NOT_READY

The finite algebra is no longer the wall. The current tree already fixes:

literal DLMF 30.16.1 finite matrix;
positive diagonal similarity;
full-carrier actual-to-source reindexing;
exact scalar shift H(G,Λ)=H(G,0)-ΛI;
zero-based ascending finite eigenvalue family;
finite block inertia;
finite Schur convergence;
nonsingular count stability;
finite-to-literal negative-count transport.

The full finite crosswalk therefore removes the matrix, orientation, shift, characteristic-polynomial, and finite-ordering ambiguities. It still does not contain the DLMF 30.16.3 same-index analytic limit, a classical ordered even spectral carrier, endpoint counts 2/3, or the degree-four identification.

Eingefügter Text

[FINITE_CELL][LEAN]

Smallest source-faithful carrier

The carrier must not be an arbitrary sequence with fields asserting the desired convergence.

The first honest object is the even singular Sturm–Liouville form

q
G
	​

(f)=∫
−1
1
	​

((1−x
2
)∣f
′
(x)∣
2
+Gx
2
∣f(x)∣
2
)dx

on its natural even form domain, with the regular zero-flux endpoint realization.

Its ordered min–max values define:

χ
p
even
	​

(G)=χ
2p
	​

(
G
	​

),

and the shifted project parameter is:

Λ
p
	​

(G)=χ
p
even
	​

(G)−G.

This definition fixes:

DLMF order m = 0;
Lean p = 0,1,2,...;
DLMF selector = p+1;
classical degree n = 2p;
project Lambda = chi - G.

Defining mode4ClassicalEvenChi as the limit of the project finite eigenvalues would make the same-index theorem tautological and would not identify the differential spectrum. That route is rejected by [C10].

Source-addressed theorem-head sequence

These are exact target contracts, not current-tree declarations.

lean
namespace Q3.RouteB


/-- The ordered even classical spheroidal characteristic values,
with zero-based even index `p`, so degree = `2*p`. -/
noncomputable def mode4ClassicalEvenChi
    (G : ℝ) (p : ℕ) : ℝ


noncomputable def mode4ClassicalEvenLambda
    (G : ℝ) (p : ℕ) : ℝ :=
  mode4ClassicalEvenChi G p - G
Q1.1 — strict ordering and escape

Primary-source facts: singular Sturm–Liouville spectrum, simplicity, parity, and ordering.

lean
theorem mode4ClassicalEvenChi_strictMono
    (G : ℝ) (hG : 0 < G) :
    StrictMono (mode4ClassicalEvenChi G)


theorem mode4ClassicalEvenChi_tendsto_atTop
    (G : ℝ) (hG : 0 < G) :
    Filter.Tendsto
      (mode4ClassicalEvenChi G)
      Filter.atTop
      Filter.atTop
Q1.2 — one-sided Galerkin control and same-index limit

Primary-source fact: DLMF 30.16.2–30.16.3 finite ordered spectral approximation.

lean
theorem mode4ClassicalEvenLambda_le_finiteEigenvalue
    (G : ℝ) (hG : 0 < G)
    (p d : ℕ) :
    mode4ClassicalEvenLambda G p ≤
      mode4DLMFEvenFiniteEigenvalue G (p + 1 + d)
        ⟨p, by omega⟩


theorem mode4DLMFEvenFiniteEigenvalue_tendsto_classicalEvenLambda
    (G : ℝ) (hG : 0 < G)
    (p : ℕ) :
    Filter.Tendsto
      (fun d : ℕ =>
        mode4DLMFEvenFiniteEigenvalue G (p + 1 + d)
          ⟨p, by omega⟩)
      Filter.atTop
      (𝓝 (mode4ClassicalEvenLambda G p))

The one-sided theorem is load-bearing. Pointwise convergence at each fixed p alone does not rule out a spurious low finite eigenvalue whose index drifts with the dimension.

Q1.3 — finite negative count as a finite spectral count

Generic Lean receiver:

lean
theorem mode4ForwardHermitianFinite_negativeCount_eq_card_eigenvalue_lt
    (G Λ : ℝ) (d : ℕ) :
    mode4HermitianNegativeEigenvalueCount
        (mode4ForwardHermitianFiniteMatrix G Λ d)
        (mode4ForwardHermitianFiniteMatrix_isHermitian G Λ d)
      =
    Finset.card
      (Finset.univ.filter
        (fun p : Fin d =>
          mode4DLMFEvenFiniteEigenvalue G d p < Λ))
Q1.4 — eventual classical count at a strict separator

Composition of primary-source spectral convergence with a generic finite-count receiver:

lean
theorem mode4DLMFEvenFinite_negativeCount_eventually_eq_classicalCount
    (G Λ : ℝ) (hG : 0 < G)
    (r : ℕ)
    (hbelow :
      ∀ p < r, mode4ClassicalEvenLambda G p < Λ)
    (habove :
      ∀ p, r ≤ p → Λ < mode4ClassicalEvenLambda G p) :
    ∀ᶠ d in Filter.atTop,
      mode4HermitianNegativeEigenvalueCount
          (mode4ForwardHermitianFiniteMatrix G Λ (r + d))
          (mode4ForwardHermitianFiniteMatrix_isHermitian
            G Λ (r + d))
        = r

This is a generic receiver. Production must derive hbelow and habove from a source endpoint theorem; it may not pass endpoint counts as hypotheses.

Q1.5 — Bonami–Karoui endpoints as outputs

Primary-source theorem to formalize:

lean
theorem exists_mode4BonamiKaroui_evenSeparators
    (G : ℝ) (hG : 0 < G) :
    ∃ ΛLower ΛUpper : ℝ,
      ΛLower < ΛUpper ∧
      ΛUpper ≤ 20 ∧
      mode4ClassicalEvenLambda G 1 < ΛLower ∧
      ΛLower < mode4ClassicalEvenLambda G 2 ∧
      mode4ClassicalEvenLambda G 2 < ΛUpper ∧
      ΛUpper < mode4ClassicalEvenLambda G 3

This produces, rather than assumes, the separators.

At ΛLower, exactly the degree 0 and degree 2 values lie below the endpoint, hence count 2. At ΛUpper, degrees 0,2,4 lie below, hence count 3.

Strict inequalities give endpoint nonsingularity.

Q1.6 — literal endpoint counts and degree-four crossing

Production composition:

lean
theorem exists_mode4LiteralSchur_endpoints_counts_two_three
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20) :
    ∃ ΛLower ΛUpper : ℝ,
      ΛLower < ΛUpper ∧
      ΛUpper ≤ 20 ∧
      (mode4HermitianSchurMatrix
        mProject ΛLower K).det ≠ 0 ∧
      (mode4HermitianSchurMatrix
        mProject ΛUpper K).det ≠ 0 ∧
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject ΛLower K)
          (mode4HermitianSchurMatrix_isHermitian
            mProject K ΛLower)
        = 2 ∧
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject ΛUpper K)
          (mode4HermitianSchurMatrix_isHermitian
            mProject K ΛUpper)
        = 3

The finite-split offset is now zero on the finite side because the full carrier begins at even degree 0, the exact reindexing and positive diagonal similarity preserve characteristic polynomial/inertia, and the eliminated finite tail is positive definite. The remaining missing input is the classical same-index source limit, not another finite offset lemma.

GOAL058_G3_CLASSICAL_SPECTRUM_T…



Eingefügter Text

[COFINAL_FAMILY][CONDITIONAL]

The existing root bracket and root-inertia label then give one crossing between these endpoints. Since the count below the crossing is 2, the crossing is the zero-based even index p=2, hence classical degree n=4.

Q1 Aristotle boundary
ARISTOTLE: NOT_READY

There is no current-tree definition of the classical ordered even Sturm–Liouville spectrum and no theorem head for DLMF 30.16.3 that does not insert the desired same-index convergence as a premise.

The finite matrix formalization is complete enough. The remaining theorem is source analysis, not bounded proof search.

Q2 — G1 full complex complement floor
Decision: REVISE_TO_C1_C2_C3

The exact production object remains:

K = sourceCCMFiniteMatrix i
q = sourceCCMComplexRow S i
a = sourceCCMFiniteRayleigh S i
Q = I - |q><q|

and the production predicate is:

lean
sourceCCMComplexTrialComplementFloor S i beta

The kernel-checked receiver consumes this floor and then yields a unit bottom eigenpair, a gap at least beta, and projective tracking. It does not construct beta or its certificate.

markdown.md eingefügt

[FINITE_CELL][LEAN]

Source-to-Lean dictionary
Layer	Exact source/Lean object	Status
Full finite trial-line complement	sourceCCMComplexTrialComplementFloor	Receiver only
Gram checker	CCMProposition59ComplexTrialComplementFloor.lean	Proved
Literal odd ambient tail	sourceWeilOddTailAmbientCoercive_explicit	Proved, floor 1/2
Shifted odd graph operator	sourceWeilShiftedOddTailOperator	Proved positive/invertible under source coercivity
Exact correction	oddTailInverseWeightedCorrection D = R† C⁻¹ R	Proved
Fixed m=13 corrected-head equivalence	sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy	Unsigned receiver
Even tail/head	No source supplier	Missing
Dynamic Rayleigh shift	sourceCCMFiniteRayleigh S i	Defined, no cofinal fixed-shift bound
Exact source-row evenness	Conditional phase-realification theorem only	Missing as production supplier

The odd-tail supplier is real and schedule-generic, but it does not specialize to the production floor. The mismatch is six-dimensional:

carrier;
operator;
shift;
sector;
schedule;
modality.

In particular, the odd lane is blind to q, says nothing about the even directions in q⊥, and the corrected-head theorem is fixed at m=13.

markdown.md eingefügt

[COFINAL_FAMILY][PAPER]

Noncircular carrier package
C1 — odd leg

Bound the exact inverse-weighted correction.

Generalize the corrected-head theorem from fixed m=13 to the actual schedule.

Prove a uniform corrected odd-head floor.

C2 — even leg

Prove an even-tail coercivity twin.

Prove a uniform even-head complement floor at one source-defined fixed shift a
∗
	​

, with β
∗
	​

>0.

C3 — shift and cofinal connector

Prove eventually:

∣sourceCCMFiniteRayleigh(S,i
j
	​

)−a
∗
	​

∣≤β
∗
	​

/2.

The exact shift identity then gives a floor at the literal Rayleigh shift of at least β
∗
	​

/2.

C1–C3 are noncircular only if the Rayleigh/residual rate is obtained independently from the source approximation side. G1 may consume that rate; it may not be used to prove the rate.

Exact row evenness remains a prerequisite for a clean parity split. Without it, an explicit odd-contamination budget must stay in the theorem.

markdown.md eingefügt

Exact first bounded Lean head

The full G1 supplier is not theorem-head ready. One exact C1 subleaf is ready:

lean
namespace Q3.RouteB.D0Pstar


theorem sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le
    {Head : Type*}
    [NormedAddCommGroup Head]
    [InnerProductSpace ℂ Head]
    [CompleteSpace Head]
    (i : PairIndex)
    (R : ℕ)
    (mu : ℝ)
    (hcoercive :
      SourceWeilOddTailAmbientCoercive i R mu)
    (residual :
      Head →L[ℂ] SourceWeilGraphOddTailCarrier i R)
    (x : Head) :
    min mu 1 *
        (inner ℂ
          (oddTailInverseWeightedCorrection
            (sourceWeilOddTailInverseWeightedData
              i R mu hcoercive residual) x)
          x).re
      ≤
    2 * ‖residual x‖ ^ 2

The exact graph lower bound is:

2
min(μ,1)
	​

∥y∥
2
≤Re⟨Cy,y⟩,

and the correction is R
∗
C
−1
R. The source operator and generic correction APIs are already materialized.

GOAL057_B3_0AK_PROSHKA_SOURCE_C…



PROSHKA_REQUEST_GOAL057_B3_0_PO…

[ABSTRACT][LEAN_CONDITIONAL]

This theorem proves only a correction budget. It does not prove the corrected-head sign, the even leg, the cofinal shift connector, or the full complement floor.

Q2 Aristotle boundary
ARISTOTLE: REJECT

The head is bounded, but the task is an internal infinite-dimensional project theorem over exact custom graph carriers and inverse APIs. Codex should prove it locally first.

Aristotle becomes appropriate only for a later, fully specified exact-rational finite corrected-head Gram/LDL certificate after the analytic tail and correction bounds are already in the tree. The source packet explicitly keeps that boundary closed.

markdown.md eingefügt

ROUTE MAP
Route	Kill-power	Cost	Verdict
Q1 min–max Sturm–Liouville carrier + DLMF same-index theorem	5/5	8/5	Source program, NOT_READY
Q1 define classical spectrum as finite limit	1/5	1/5	Killed [C10]
Q2 sector split C1–C3	5/5	6/5	Survives
Q2 full complex Schur/Gram factorization without parity	5/5	8/5	Backup
Q2 odd-tail floor alone → full floor	0/5	—	Killed [C04][C10]
FINAL PROPOSAL

Run one Codex-local theorem:

G1_ODD_TAIL_INVERSE_WEIGHTED_CORRECTION_BOUND

Registered prediction:

YAML
prediction:
  theorem_compiles_from_existing_graph_lower_and_exact_inverse_pairing: true
confidence: 0.90

Likeliest failure point:

rewriting the actual inverse pairing into the graph-lower orientation
inside Mathlib's conjugate-first inner-product API.

Required response to failure:

return the smallest missing local inner-product/inverse lemma;
do not weaken the constant;
do not replace C⁻¹ by the scalar floor;
do not open the even leg in the same transaction.
STRONGEST ATTACK

The selected Q2 leaf may compile and still produce almost no G1 progress.

That objection is correct.

It closes only the legal estimate:

R
∗
C
−1
R⪯
min(μ,1)
2
	​

R
∗
R.

It does not establish that the corrected head is positive. The source wall remains:

uniform corrected odd head
+
even tail/head
+
Rayleigh-shift transport
+
cofinal schedule.

The theorem must therefore be recorded as C1 correction control, not as a complement-floor theorem.

For Q1, the strongest objection is spectral pollution. A theorem proving only fixed-p convergence cannot by itself certify the total number of finite eigenvalues below an endpoint. The source import must retain the DLMF one-sided finite-eigenvalue ordering or an equivalent no-pollution theorem.

CODEX DIRECTIVE
TARGET:
  G1_ODD_TAIL_INVERSE_WEIGHTED_CORRECTION_BOUND


PIN:
  repo = /Users/emalam/GitHub/rh_lean_01_2026
  branch = rh_clean
  HEAD = origin/rh_clean = 82617fd0


MODE:
  one Lean file;
  one report;
  local Codex only;
  no Aristotle;
  no commit;
  no push;
  no Route/Bus/runtime edit.


OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    D0PstarSourceWeilOddTailCorrectionBound.lean


DIRECT_IMPORT:
  Q3.Proofs.RouteB.D0PstarSourceWeilOddTailGraphOperator


THEOREM:
  sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le


PROOF_ROUTE:
  1. Set D :=
       sourceWeilOddTailInverseWeightedData
         i R mu hcoercive residual.
  2. Rewrite with:
       inner_oddTailInverseWeightedCorrection.
  3. Set y := D.outerBlock.inverse (D.residual x).
  4. Rewrite:
       D.outerBlock y = D.residual x.
META CLOSEOUT

What became smaller?
Q1 is now one analytic carrier plus one no-pollution same-index theorem. Q2 is split into the exact C1/C2/C3 source package.

What was killed?
Defining the classical spectrum as the finite limit; using the odd-tail floor as the full complex complement floor; treating fixed m=13 as cofinal.

What must not be tried again?
Counts, convergence, offset, or the Rayleigh-shift floor may not be inserted as binders and relabelled as suppliers.

Current smallest named gaps:

G3:
  Mode4ClassicalEvenSpectrumSameIndexLimit


G1:
  SourceWeilOddTailInverseWeightedCorrectionBound

Next cheapest decisive test:
Kernel-check the Q2 correction bound.

Prediction fate:

finite matrix/orientation was the G3 wall:
  REFUTED — now closed.


analytic same-index limit is the G3 wall:
  CONFIRMED.


recovered odd-tail coercivity closes G1:
  REFUTED.


odd-tail correction bound is locally executable:
  REGISTERED, UNTESTED.
YAML
iteration:
  target: Goal058_G1_G3_analytic_source_wall
  status: OPEN
  failed_strategy: finite_algebra_or_odd_tail_relabelled_as_global_source_supplier
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SourceWeilOddTailInverseWeightedCorrectionBound
  invariant_learned: classical index/count and full complex complement floors require separate source carriers and may not be introduced as hypotheses
  forbidden_future_move: finite_limit_definition_tautology_or_odd_tail_to_full_floor_substitution
  next_decisive_test: kernel_check_C1_inverse_weighted_correction_bound
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
