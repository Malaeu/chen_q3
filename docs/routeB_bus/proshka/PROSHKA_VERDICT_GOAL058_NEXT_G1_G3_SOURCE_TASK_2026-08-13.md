# STATUS: OPEN — ARISTOTLE_NONSCALAR_SOURCE_OBSERVABLE
```yaml
PRIMARY: ARISTOTLE_NONSCALAR_SOURCE_OBSERVABLE
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_COMMIT: 695b3f8a0da9f4ee94af0a4e21e1cf0c256a6bc2
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_BRIEF_GOAL058_G1_G3_NEXT_SOURCE_TASK_2026-08-13.md
  REQUEST_SHA256_OWNER_SUPPLIED: af9994cffb9af65ba732a9e109f388aa68abf9639c7a606fa2078e0450fc1b8a
  RAW_SHA_REHASHED_BY_THIS_RUNTIME: false

CURRENT_BOUNDARY:
  COMPLEX_HERMITIAN_P59_CONNECTOR: PROVED_KERNEL_CHECKED
  G1: OPEN
  G3: OPEN
  ROUTE: CHALLENGER_NOT_RH
  ROUTE_PROMOTION: false
  RH_CLAIM: false
  BUS_010: VOID

SELECTED_TASK:
  ID: GOAL058_ARISTOTLE_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH
  CLASS: FINITE_SOURCE_EXACT_IDENTITY
  SCOPE: FINITE_CELL
  VERIFIER: LEAN
  PROGRESS_IF_PROVED: REPRESENTATION_PROGRESS

NONCIRCULARITY:
  ASSUMES_GAP: false
  ASSUMES_COMPLEMENT_COERCIVITY: false
  ASSUMES_SIMPLICITY: false
  ASSUMES_EIGENVECTOR: false
  ASSUMES_TRACKING: false
  ASSUMES_DECAY_OR_TENDSTO: false
  ASSUMES_RH_OR_GLOBAL_WEIL_POSITIVITY: false
  USES_SCALAR_COMMUTATOR: false
  USES_SOURCE_REALIFICATION_OR_PARITY: false
  FINITE_TO_COFINAL_PROMOTION: false

MATHEMATICAL_EFFECT:
  - identifies_the_exact_source_residual_as_the_full_off_diagonal_Feshbach_coupling
  - isolates_the_only_remaining_source_blocks_as_residual_and_shifted_complement
  - gives_one_literal_CCM_object_for_future_G1_and_G3_source_estimates
  - does_not_supply_floor_or_rate

SUCCESS: GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH_PROVED
STOP: GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH_TYPED_STOP

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C07_PROBABILITY_WEIGHTED_ESTIMATE
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
```

# AUTHORITATIVE ATTACHMENT-READY ARISTOTLE PROMPT

```yaml
TARGET_ID: GOAL058_ARISTOTLE_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH

PRIMARY_CLASS: ARISTOTLE_NONSCALAR_SOURCE_OBSERVABLE

PIN:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_COMMIT: 695b3f8a0da9f4ee94af0a4e21e1cf0c256a6bc2
  REQUEST_FILE: docs/routeB_bus/proshka/PROSHKA_BRIEF_GOAL058_G1_G3_NEXT_SOURCE_TASK_2026-08-13.md
  REQUEST_SHA256: af9994cffb9af65ba732a9e109f388aa68abf9639c7a606fa2078e0450fc1b8a

  RELOCK_POLICY: >-
    Before proof search, verify that the source commit exists and that the
    request file has the exact SHA-256 above. Work against the exact source
    declarations at that commit. If the execution checkout is later, compare
    every allowed input against SOURCE_COMMIT. Do not repair source drift by
    changing the theorem statement.

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean

ALLOWED_IMPORTS:
  - Q3.Proofs.RouteB.CCMProposition59ComplexHermitianConnector

FORBIDDEN_IMPORTS:
  - any additional direct Q3 import
  - Q3.Main
  - Q3.Proofs.RouteB.H2aPenaltyCoercivity
  - Q3.Proofs.RouteB.SimpleEvenGroundSectorCriterion
  - Q3.Proofs.RouteB.WeightedRayleighProjectiveDefect
  - Q3.Proofs.RouteB.TempleResidualGapEnvelopeTransfer
  - Q3.Proofs.RouteB.PerturbativeTrueGapLower
  - Q3.Proofs.RouteB.AmbientResidualEnvelopeTransfer
  - Q3.Proofs.RouteB.WeightedProjectiveEvaluationTransfer
  - Q3.Proofs.RouteB.CompactEvaluationRateTransfer
  - Q3.Proofs.RouteB.UniformDifferenceReferenceTransfer
  - any GLOWER, D0-mode-4, sectional-gap, continuum-gap, RH, or route-export module

EXACT_INPUT_OBJECTS:
  - Q3.RouteB.CCMModeFinite
  - Q3.RouteB.complexTrialLineProjection
  - Q3.RouteB.complexTrialLineProjection_isHermitian
  - Q3.RouteB.complexTrialLineProjection_sq_of_unit
  - Q3.RouteB.D0Pstar.ProlateCanonicalSourceData
  - Q3.RouteB.D0Pstar.PairIndex
  - Q3.RouteB.D0Pstar.sourceCCMComplexRow
  - Q3.RouteB.D0Pstar.sourceCCMComplexRow_unit
  - Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix
  - Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix_isHermitian
  - Q3.RouteB.D0Pstar.sourceCCMFiniteRayleigh
  - Q3.RouteB.D0Pstar.sourceCCMFiniteRayleigh_coe
  - Q3.RouteB.D0Pstar.sourceCCMFiniteResidual
  - Q3.RouteB.D0Pstar.sourceCCMComplexRow_inner_residual_eq_zero
  - Matrix.vecMulVec
  - Matrix.vecMulVec_mul_vecMulVec
  - Matrix.mulVec
  - Matrix.IsHermitian
  - Matrix.conjTranspose

EXACT_BINDERS:
  S: Q3.RouteB.D0Pstar.ProlateCanonicalSourceData
  i: Q3.RouteB.D0Pstar.PairIndex

EXACT_THEOREM_HEAD: |
  namespace Q3.RouteB

  noncomputable def complexTrialLineComplement
      {ι : Type*} [Fintype ι] [DecidableEq ι]
      (q : ι → ℂ) : Matrix ι ι ℂ :=
    1 - complexTrialLineProjection q

  noncomputable def sourceCCMComplexTrialComplementBlock
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex) :
      Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
    let q := D0Pstar.sourceCCMComplexRow S i
    let K := D0Pstar.sourceCCMFiniteMatrix i
    let a : ℂ := (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
    let Q := complexTrialLineComplement q
    Q * (K - a •
      (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) * Q

  theorem sourceCCMComplexTrialComplement_mulVec_Kq_eq_residual
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex) :
      let q := D0Pstar.sourceCCMComplexRow S i
      let K := D0Pstar.sourceCCMFiniteMatrix i
      let Q := complexTrialLineComplement q
      Q *ᵥ (K *ᵥ q) =
        D0Pstar.sourceCCMFiniteResidual S i := by
    -- proof

  theorem sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex) :
      let q := D0Pstar.sourceCCMComplexRow S i
      let K := D0Pstar.sourceCCMFiniteMatrix i
      let a : ℂ := (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
      let r := D0Pstar.sourceCCMFiniteResidual S i
      K - a •
          (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ) =
        Matrix.vecMulVec q (star r) +
          Matrix.vecMulVec r (star q) +
            sourceCCMComplexTrialComplementBlock S i := by
    -- proof

REQUIRED_AUXILIARY_LEMMAS:
  - name: complexTrialLineProjection_mulVec_self_of_unit
    visibility: private
    exact_role: >-
      From star q dot q = 1, prove
      complexTrialLineProjection q *ᵥ q = q.

  - name: complexTrialLineComplement_mulVec_self_of_unit
    visibility: private
    exact_role: >-
      From star q dot q = 1, prove
      complexTrialLineComplement q *ᵥ q = 0.

  - name: hermitian_trialLine_left_block_eq_residual_vecMulVec
    visibility: private
    exact_role: >-
      For Hermitian K, unit q, a = star q dot (K*q), and
      r = K*q - a*q, prove
      Q*K*P = vecMulVec r (star q).

  - name: hermitian_trialLine_right_block_eq_vecMulVec_residual
    visibility: private
    exact_role: >-
      Under the same hypotheses, prove
      P*K*Q = vecMulVec q (star r).
      Derive the conjugate orientation from Hermiticity; do not assert it
      by commutativity or transpose symmetry.

  - name: hermitian_trialLine_center_block_eq_rayleigh_projection
    visibility: private
    exact_role: >-
      Under the same hypotheses, prove
      P*K*P = a • P.

  - name: hermitian_unit_trialLine_shifted_feshbach
    visibility: private
    exact_role: >-
      Assemble the exact shifted matrix identity from the four blocks.
      This helper may be generic in K and q, but the public theorem must
      specialize to the literal Goal-058 source objects.

EXPECTED_OUTPUT:
  SUCCESS: >-
    Return the complete contents of OWNED_FILE. The file must contain exactly
    the two public definitions and two public theorems named in
    EXACT_THEOREM_HEAD, the private support lemmas, mandatory plants, and
    #print axioms commands. Do not edit or propose edits to any other file.

  TYPED_STOP: >-
    If the theorem is not derivable from ALLOWED_IMPORTS, return exactly one
    typed-stop code plus the smallest missing Lean lemma signature. Do not add
    a gap, floor, eigenvector, simplicity, tracking, parity, realification, or
    Tendsto binder. Do not weaken or genericize the public source theorem.

SUCCESS_CODE: GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH_PROVED

TYPED_STOP_CODES:
  - GOAL058_ARISTOTLE_SOURCE_RELOCK_MISMATCH
  - GOAL058_COMPLEX_TRIAL_PROJECTION_API_GAP
  - GOAL058_SOURCE_RESIDUAL_DEFINITION_ORIENTATION_MISMATCH
  - GOAL058_HERMITIAN_LEFT_BLOCK_ORIENTATION_GAP
  - GOAL058_HERMITIAN_RIGHT_BLOCK_CONJUGATION_GAP
  - GOAL058_RAYLEIGH_CENTER_BLOCK_GAP
  - GOAL058_SOURCE_FAMILY_OBJECT_MISMATCH
  - GOAL058_HIDDEN_REALIFICATION_OR_PARITY_ASSUMPTION
  - GOAL058_COMMUTATOR_TAUTOLOGY_REINTRODUCED
  - GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
  - GOAL058_FINITE_TO_COFINAL_SUBSTITUTION
  - GOAL058_RESIDUAL_SIGN_MUTATION_NOT_DETECTED
  - GOAL058_COMPLEX_PROJECTION_ORIENTATION_MISMATCH
  - GOAL058_PUBLIC_SURFACE_MISMATCH
  - GOAL058_AXIOM_GATE_FAILED
  - GOAL058_VALIDATION_FAILED

AXIOM_GATE:
  REQUIRED_PRINT_HEADS:
    - Q3.RouteB.complexTrialLineComplement
    - Q3.RouteB.sourceCCMComplexTrialComplementBlock
    - Q3.RouteB.sourceCCMComplexTrialComplement_mulVec_Kq_eq_residual
    - Q3.RouteB.sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach

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
    test "$(git rev-parse 695b3f8a0da9f4ee94af0a4e21e1cf0c256a6bc2^{commit})" = \
      "695b3f8a0da9f4ee94af0a4e21e1cf0c256a6bc2"

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    git show \
      695b3f8a0da9f4ee94af0a4e21e1cf0c256a6bc2:docs/routeB_bus/proshka/PROSHKA_BRIEF_GOAL058_G1_G3_NEXT_SOURCE_TASK_2026-08-13.md \
      | sha256sum \
      | grep '^af9994cffb9af65ba732a9e109f388aa68abf9639c7a606fa2078e0450fc1b8a  -$'

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake env lean \
      Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake build Q3.Proofs.RouteB.CCMProposition59ComplexTrialLineFeshbach

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake build

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    bash scripts/q3_check.sh \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    rg -n \
      '\bsorry\b|\badmit\b|exact\?|native_decide|^[[:space:]]*axiom\b|^[[:space:]]*opaque\b' \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    rg -n \
      'sourceCCMHasRealEvenPhase|phaseRealifies|ccmNegFinite|simpleEven|hbottom|hsimple|heig|Tendsto|Filter\.atTop|RH|WeilPositivity|lagCommutatorObservable|ccmWeilMatFinite_commutator' \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    git diff --check -- \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean

    test "$(
      git diff --name-only -- \
        q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean \
      | wc -l | tr -d ' '
    )" = "1"
```

# MATHEMATICAL INTERPRETATION

Let

\[
q=\texttt{sourceCCMComplexRow},\qquad
K=\texttt{sourceCCMFiniteMatrix},
\]

\[
a=\langle q,Kq\rangle,\qquad
r=Kq-aq,
\]

and let

\[
P=|q\rangle\langle q|,\qquad Q=I-P.
\]

The task proves the exact literal-source identity

\[
\boxed{
K-aI
=
|q\rangle\langle r|
+
|r\rangle\langle q|
+
Q(K-aI)Q.
}
\]

Thus the full off-diagonal **Schur/Feshbach coupling** is not an unnamed
quantity and not the killed scalar commutator. It is exactly the already
source-locked finite residual \(r\).

After success, the two remaining source obligations are explicit:

1. control the literal residual \(r\);
2. prove a lower floor for the literal shifted complement block
   \(Q(K-aI)Q\).

Those are the genuine future G3 and G1 source estimates.

# WHY THIS IS NOT G1 OR G3 IN DISGUISE

The theorem has no binder for:

```text
spectral gap
complement floor
positivity
bottom eigenvalue
eigenvector
simplicity
tracking
decay
cofinal schedule
compact-open convergence
RH
global Weil positivity
```

It proves no inequality and no limit.

It only identifies the exact finite source blocks.

The theorem therefore does not close G1 or G3. It removes an object mismatch
and forces every later Schur estimate to use the literal CCM source residual
and literal CCM complement block.

# EXACT EXISTING DECLARATIONS ARISTOTLE MAY CONSUME

```text
Q3.RouteB.complexTrialLineProjection
Q3.RouteB.complexTrialLineProjection_isHermitian
Q3.RouteB.complexTrialLineProjection_sq_of_unit

Q3.RouteB.D0Pstar.sourceCCMComplexRow
Q3.RouteB.D0Pstar.sourceCCMComplexRow_unit
Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix
Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix_isHermitian
Q3.RouteB.D0Pstar.sourceCCMFiniteRayleigh
Q3.RouteB.D0Pstar.sourceCCMFiniteRayleigh_coe
Q3.RouteB.D0Pstar.sourceCCMFiniteResidual
Q3.RouteB.D0Pstar.sourceCCMComplexRow_inner_residual_eq_zero
```

# MANDATORY FALSIFIERS

## P1 — Wrong-family proxy

Replace the public source row or source matrix by any arbitrary binder,
real-part row, symmetrized row, Phase-1 row, D0Pstar surrogate, GLOWER matrix,
mode-4 matrix, or independently optimized witness.

Required stop:

```text
GOAL058_SOURCE_FAMILY_OBJECT_MISMATCH
```

The public theorem must hard-code `sourceCCMComplexRow S i` and
`sourceCCMFiniteMatrix i`.

## P2 — Hidden realification or parity

Attempt to introduce:

```text
sourceCCMHasRealEvenPhase
phaseRealifies
reflection-evenness
a real source row
q -> Re(q)
q -> (q + Jq)/2
```

Required stop:

```text
GOAL058_HIDDEN_REALIFICATION_OR_PARITY_ASSUMPTION
```

The theorem is complex Hermitian and needs none of these.

## P3 — Scalar commutator tautology

Attempt to prove any block using:

```text
lagCommutatorObservable
ccmWeilMatFinite_commutator
q dot ((D*K-K*D)*q)
```

Required stop:

```text
GOAL058_COMMUTATOR_TAUTOLOGY_REINTRODUCED
```

The source residual must enter from its definition, not from the killed scalar
observable.

## P4 — Circular gap or tracking premise

Add any binder or imported theorem asserting:

```text
positive gap
complement coercivity
simple ground state
ground-to-trial tracking
residual decay
Tendsto
cofinal schedule
RH
global Weil positivity
```

Required stop:

```text
GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
```

## P5 — Projection orientation

On `Fin 2`, use the exact unit vector

\[
q=(3/5,\;4i/5).
\]

Mutate

```text
vecMulVec q (star q)
```

to

```text
vecMulVec (star q) q
```

or delete one conjugation.

The off-diagonal entry must change, and the mutant must fail.

Required stop:

```text
GOAL058_COMPLEX_PROJECTION_ORIENTATION_MISMATCH
```

## P6 — Residual-sign mutation

On `Fin 2`, use

\[
K=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix},
\qquad
q=(1,0).
\]

The exact source-shaped residual is \(Kq-aq=(0,1)\).

Replace it by \(aq-Kq\). The two off-diagonal blocks acquire the wrong sign
and the Feshbach identity must fail.

Required stop:

```text
GOAL058_RESIDUAL_SIGN_MUTATION_NOT_DETECTED
```

## P7 — Nonunit private helper

Try to remove `star q dot q = 1` from the generic private helper and instantiate
it with \(q=(2,0)\).

Required stop:

```text
GOAL058_COMPLEX_TRIAL_PROJECTION_API_GAP
```

The public source specialization discharges unit normalization through
`sourceCCMComplexRow_unit`; it must not silently renormalize.

## P8 — Zero-residual branch

Use a Hermitian diagonal matrix and a unit eigenvector, so \(r=0\).

The theorem must reduce to the exact block-diagonal identity without division
by \(\|r\|\), overlap, gap, or any nonzero assumption.

Any division-based proof fails with:

```text
GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
```

# EVIDENCE BOUNDARY

A successful file proves:

```text
[FINITE_CELL][LEAN]
exact literal CCM complex trial-line Feshbach decomposition
```

It does not prove:

```text
a complement floor
a spectral gap
simple-even ground existence
small residual
residual decay
projective-defect decay
a cofinal schedule
finite-to-continuum transport
G1
G3
Route B promotion
RH
```
