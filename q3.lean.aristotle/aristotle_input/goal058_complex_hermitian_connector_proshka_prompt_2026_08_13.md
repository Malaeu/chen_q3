# Goal 058 Aristotle proof pack — Proshka-authorized complex Hermitian connector

This file is the source-locked execution copy of the authoritative Proshka task archived at
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md`.

# AUTHORITATIVE ARISTOTLE PROMPT

```yaml
TARGET_ID: GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR

PRIMARY_CLASS: ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR

PIN:
  AUTHORITATIVE_REQUEST_COMMIT: fea0965e021ea4cbb65f7dc7ceacd67ab1b1be63
  CURRENT_ORIGIN_TIP_REPORTED: ad754cb5bd69d7eba06c7d904a21f08c1c233aec
  EXECUTION_POLICY: >-
    Work at the current clean rh_clean tip only after byte-relocking every
    listed source file. If any hash differs, do not adapt the theorem to the
    changed source. Return GOAL058_ARISTOTLE_SOURCE_RELOCK_MISMATCH.

  LOCKED_SHA256:
    docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md: f4eb768a71b3928d3a2310adc8499a14f8b58f7aebb04a08316d7c1c61b8dd57
    docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md: 0a8e2e0a1b9423003d3d62ed7964cc22e17fc43c2642f43c164ca71c634aaa68
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean: 0651ef147401f50510be301443236276f948179f0e7712a0e3500bbdadcf04bf
    q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md: 1ccf88965a7ef916c036695a100bce98c72753fb9bbeb9aee98064324fe23517
    q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md: 32cde7e7b179bc81680cbc305f3c7475144d7c8fcdb190d446b1c93fb760e554
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean: c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497
    q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean: 7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016
    q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean: bb9383bebfcd5d01423ff5e944a28545e835e2e03c8609ec69fde73dce5ab2c5
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean: d0bb820651c81ac6971985cb705bd3191584108f5d90ea19411e9a0884c11190
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean: a79c30cdc11cc936838e7963eff1a3de1f2c9290cf5ce5ca516b9bbf093b5f90

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean

ALLOWED_IMPORTS:
  - Q3.Proofs.RouteB.CCMProposition59SourceTrialFeshbachPreflight
  - >-
    No other Q3 project import is allowed. Mathlib declarations already
    available transitively through this import may be used.

FORBIDDEN_IMPORTS:
  - Q3.Main
  - Q3.Proofs.RouteB.H2aPenaltyCoercivity
  - Q3.Proofs.RouteB.WeightedProjectiveEvaluationTransfer
  - Q3.Proofs.RouteB.CompactEvaluationRateTransfer
  - Q3.Proofs.RouteB.UniformDifferenceReferenceTransfer
  - Q3.Proofs.RouteB.TempleResidualGapEnvelopeTransfer
  - Q3.Proofs.RouteB.PerturbativeTrueGapLower
  - Q3.Proofs.RouteB.AmbientResidualEnvelopeTransfer
  - any GLOWER module
  - any D0-mode-4 module
  - any sectional or continuum-gap module
  - any RH or route-export module

EXACT_INPUT_OBJECTS:
  - Q3.RouteB.D0Pstar.ProlateCanonicalSourceData
  - Q3.RouteB.D0Pstar.PairIndex
  - Q3.RouteB.CCMModeFinite
  - Q3.RouteB.D0Pstar.sourceCCMComplexRow
  - Q3.RouteB.D0Pstar.sourceCCMComplexRow_unit
  - Q3.RouteB.proposition59CCMTransform
  - Q3.RouteB.proposition59CCMTransform_eq_mode_sum
  - Q3.RouteB.proposition59CCMComplexTransform
  - Q3.RouteB.proposition59CCMComplexTransform_eq_mode_sum
  - Q3.RouteB.proposition59PoleKernel
  - Q3.RouteB.ccmModeFinite
  - Matrix.vecMulVec
  - Matrix.vecMulVec_mul_vecMulVec
  - Matrix.mulVec
  - Matrix.dotProduct
  - Complex.normSq

EXACT_BINDERS:
  S: Q3.RouteB.D0Pstar.ProlateCanonicalSourceData
  i: Q3.RouteB.D0Pstar.PairIndex
  L: Real
  hL: 0 < L
  xi: Q3.RouteB.CCMModeFinite i.N -> Real

EXACT_THEOREM_HEAD: |
  namespace Q3.RouteB

  noncomputable def complexTrialLineProjection
      {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ :=
    Matrix.vecMulVec q (star q)

  noncomputable def sourceCCMGroundProjectionScalar
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex)
      (xi : CCMModeFinite i.N → ℝ) : ℂ :=
    star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
      (fun j => (xi j : ℂ))

  noncomputable def sourceCCMGroundProjectionErrorSq
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex)
      (xi : CCMModeFinite i.N → ℝ) : ℝ :=
    xi ⬝ᵥ xi -
      Complex.normSq (sourceCCMGroundProjectionScalar S i xi)

  noncomputable def proposition59CCMKernelL2
      (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
    ‖((Real.sqrt L : ℂ)⁻¹)‖ *
      Real.sqrt
        (∑ j : CCMModeFinite N,
          Complex.normSq
            (proposition59PoleKernel L (-ccmModeFinite N j) z))

  theorem proposition59CCMTransform_sub_sourceProjection_le
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex)
      (L : ℝ) (hL : 0 < L)
      (xi : CCMModeFinite i.N → ℝ) :
      0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧
      ∀ z : ℂ,
        ‖proposition59CCMTransform L i.N xi z -
            sourceCCMGroundProjectionScalar S i xi *
              proposition59CCMComplexTransform L i.N
                (D0Pstar.sourceCCMComplexRow S i) z‖
          ≤ proposition59CCMKernelL2 L i.N z *
              Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi) := by
    -- proof

REQUIRED_AUXILIARY_LEMMAS:
  - name: complexTrialLineProjection_isHermitian
    exact_statement: |
      theorem complexTrialLineProjection_isHermitian
          {ι : Type*} (q : ι → ℂ) :
          (complexTrialLineProjection q).IsHermitian

  - name: complexTrialLineProjection_sq_of_unit
    exact_statement: |
      theorem complexTrialLineProjection_sq_of_unit
          {ι : Type*} [Fintype ι]
          (q : ι → ℂ)
          (hq : star q ⬝ᵥ q = 1) :
          complexTrialLineProjection q * complexTrialLineProjection q =
            complexTrialLineProjection q

  - name: sourceCCMGroundProjectionErrorSq_eq_sum_normSq
    exact_statement: |
      theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq
          (S : D0Pstar.ProlateCanonicalSourceData)
          (i : D0Pstar.PairIndex)
          (xi : CCMModeFinite i.N → ℝ) :
          sourceCCMGroundProjectionErrorSq S i xi =
            ∑ j,
              Complex.normSq
                ((xi j : ℂ) -
                  sourceCCMGroundProjectionScalar S i xi *
                    D0Pstar.sourceCCMComplexRow S i j)

  - name: proposition59CCM_mode_sum_cauchy_schwarz
    visibility: private
    required_role: >-
      Apply finite Cauchy-Schwarz to the exact source-locked mode sum after
      rewriting with proposition59CCMTransform_eq_mode_sum and
      proposition59CCMComplexTransform_eq_mode_sum.

EXPECTED_OUTPUT:
  SUCCESS: >-
    Return the complete contents of the single owned Lean file. It must contain
    the three support definitions, the three named public auxiliary theorems,
    the main theorem, the mandatory plants, and all required #print axioms
    commands. Do not return prose in place of code.

  TYPED_STOP: >-
    If the exact theorem cannot be proved from the allowed imports, return
    exactly one typed-stop code and the smallest missing Lean lemma signature.
    Do not weaken the theorem, add a binder, or import a gap/tracking module.

SUCCESS_CODE: GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED

TYPED_STOP_CODES:
  - GOAL058_ARISTOTLE_SOURCE_RELOCK_MISMATCH
  - GOAL058_COMPLEX_TRIAL_PROJECTION_API_GAP
  - GOAL058_COMPLEX_PROJECTIVE_ERROR_IDENTITY_GAP
  - GOAL058_FINITE_COMPLEX_CAUCHY_SCHWARZ_API_GAP
  - GOAL058_P59_SOURCE_MODE_SUM_CONNECTOR_GAP
  - GOAL058_SOURCE_FAMILY_OBJECT_MISMATCH
  - GOAL058_HIDDEN_REALIFICATION_OR_PARITY_ASSUMPTION
  - GOAL058_COMMUTATOR_TAUTOLOGY_REINTRODUCED
  - GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
  - GOAL058_P59_COORDINATE_CONVENTION_MISMATCH
  - GOAL058_ZERO_OVERLAP_BRANCH_MISSING
  - GOAL058_COMPLEX_PROJECTION_ORIENTATION_MISMATCH
  - GOAL058_AXIOM_GATE_FAILED
  - GOAL058_VALIDATION_FAILED

AXIOM_GATE:
  REQUIRED_PRINT_HEADS:
    - Q3.RouteB.complexTrialLineProjection_isHermitian
    - Q3.RouteB.complexTrialLineProjection_sq_of_unit
    - Q3.RouteB.sourceCCMGroundProjectionErrorSq_eq_sum_normSq
    - Q3.RouteB.proposition59CCMTransform_sub_sourceProjection_le

  ALLOWED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound

  FORBIDDEN:
    - sorryAx
    - any new project axiom
    - any opaque proof constant

VALIDATION_COMMANDS:
  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    test "$(git rev-parse origin/rh_clean)" = \
      "ad754cb5bd69d7eba06c7d904a21f08c1c233aec"

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    cat <<'SHA256' | sha256sum -c -
    f4eb768a71b3928d3a2310adc8499a14f8b58f7aebb04a08316d7c1c61b8dd57  docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md
    0a8e2e0a1b9423003d3d62ed7964cc22e17fc43c2642f43c164ca71c634aaa68  docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md
    0651ef147401f50510be301443236276f948179f0e7712a0e3500bbdadcf04bf  q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean
    1ccf88965a7ef916c036695a100bce98c72753fb9bbeb9aee98064324fe23517  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md
    32cde7e7b179bc81680cbc305f3c7475144d7c8fcdb190d446b1c93fb760e554  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md
    c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean
    7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016  q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
    bb9383bebfcd5d01423ff5e944a28545e835e2e03c8609ec69fde73dce5ab2c5  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean
    d0bb820651c81ac6971985cb705bd3191584108f5d90ea19411e9a0884c11190  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
    a79c30cdc11cc936838e7963eff1a3de1f2c9290cf5ce5ca516b9bbf093b5f90  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean
    SHA256

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
    lake env lean \
      Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean

  - |
    lake build Q3.Proofs.RouteB.CCMProposition59ComplexHermitianConnector

  - |
    lake build

  - |
    cd /Users/emalam/GitHub/rh_lean_01_2026
    bash scripts/q3_check.sh \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean

  - |
    rg -n \
      '\bsorry\b|\badmit\b|exact\?|native_decide|^[[:space:]]*axiom\b|^[[:space:]]*opaque\b' \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean

  - |
    rg -n \
      'sourceCCMHasRealEvenPhase|sourceCCMPhaseRealification|phaseRealifies|ccmLagCommutatorObservable|lagCommutatorObservable|H2aPenalty|Tendsto|RH|hbottom|hsimple|heig' \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean

  - |
    git diff --check -- \
      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean

    test "$(git diff --name-only | wc -l | tr -d ' ')" = "1"
```

## MATHEMATICAL INTERPRETATION

The literal CCM trial row is complex and unit. The Proposition-59 ground row is real. Do not force the complex row through a nonexistent common-phase realification.

Instead, use the **Hermitian rank-one projection** onto the complex source line.

For a real row `xi`:

```lean
sourceCCMGroundProjectionScalar S i xi
```

is the exact Hermitian projection coefficient of `xi` onto the literal complex source row.

The quantity:

```lean
sourceCCMGroundProjectionErrorSq S i xi
```

is the exact squared coefficient-space distance from `xi` to that complex source line.

The theorem proves that the difference between:

1. the exact real Proposition-59 transform of `xi`; and
2. the exact complex source transform multiplied by that projection scalar

is bounded by the exact P59 kernel norm times the square root of the projective error.

## WHY THIS IS NOT A RENAMED G1 OR G3 ASSUMPTION

The theorem assumes no:

```text
eigenvalue
eigenvector equation
bottomness
simplicity
spectral gap
complement coercivity
residual decay
tracking rate
cofinal schedule
convergence
RH
global Weil positivity
source realification
source parity
```

It proves only:

```text
finite Hermitian coefficient projection error
→ finite pointwise Proposition-59 transform error.
```

It does not assert that the error is small or tends to zero. A later source theorem must supply that decay.

Therefore the theorem removes the exact **complex-source / real-ground object mismatch** inside G3 without occupying the substantive G3 quantifier.

## EXACT EXISTING DECLARATIONS ARISTOTLE MAY CONSUME

```text
Q3.RouteB.D0Pstar.sourceCCMComplexRow
Q3.RouteB.D0Pstar.sourceCCMComplexRow_unit
Q3.RouteB.proposition59CCMTransform
Q3.RouteB.proposition59CCMTransform_eq_mode_sum
Q3.RouteB.proposition59CCMComplexTransform
Q3.RouteB.proposition59CCMComplexTransform_eq_mode_sum
Q3.RouteB.proposition59PoleKernel
Q3.RouteB.ccmModeFinite
Q3.RouteB.goal058Plant_lagCommutatorObservable_zero
Q3.RouteB.goal058PlantQ_not_eigenvector
```

The last two declarations are falsifiers only. They may not enter the main theorem proof.

## MANDATORY FALSIFIERS

### P1 — Wrong family

The public theorem must hard-code:

```lean
D0Pstar.sourceCCMComplexRow S i
```

It must not expose an arbitrary public `row` binder.

Generic private helper lemmas are allowed.

Any public substitution of a D0Pstar, GLOWER, mode-4, sectional, fitted, or independently optimized row returns:

```text
GOAL058_SOURCE_FAMILY_OBJECT_MISMATCH
```

### P2 — Hidden realification or parity

The proof must not consume:

```text
sourceCCMHasRealEvenPhase
sourceCCMPhaseRealification
phaseRealifies
source-row reflection-evenness
xi reflection-evenness
```

Add a finite two-coordinate plant with entries `1` and `Complex.I` showing that a common realifying phase is not generally available.

The main Hermitian connector must not require such a phase.

Failure:

```text
GOAL058_HIDDEN_REALIFICATION_OR_PARITY_ASSUMPTION
```

### P3 — Commutator tautology

Retain exact checks of:

```lean
goal058Plant_lagCommutatorObservable_zero
goal058PlantQ_not_eigenvector
```

The main theorem and all auxiliary proofs must be independent of:

```text
lagCommutatorObservable
ccmWeilMatFinite_commutator
```

Any use returns:

```text
GOAL058_COMMUTATOR_TAUTOLOGY_REINTRODUCED
```

### P4 — Circular gap or tracking premise

The public theorem and support lemmas may not bind or import:

```text
epsilon
heig
hbottom
hsimple
gap or complement floor
residual-decay hypothesis
Tendsto or cofinal schedule
ground-to-trial tracking
RH or global Weil positivity
```

Any such premise returns:

```text
GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
```

### P5 — Zero-overlap branch

Add a finite orthogonal-vector plant.

The theorem must remain valid when the projection scalar is zero.

No division by the overlap is allowed.

Failure:

```text
GOAL058_ZERO_OVERLAP_BRANCH_MISSING
```

### P6 — Phase-orientation plant

Add a one-coordinate plant with source row `Complex.I` and real row `1`.

Verify that the Hermitian projection scalar makes the coefficient error exactly zero.

This detects conjugation or orientation reversal.

Failure:

```text
GOAL058_COMPLEX_PROJECTION_ORIENTATION_MISMATCH
```

### P7 — Proposition-59 coordinate lock

The proof must rewrite through the existing exact mode-sum theorems and retain:

```text
source mode n → P59 pole -n
```

Do not define a sign-flipped coefficient transport.

Failure:

```text
GOAL058_P59_COORDINATE_CONVENTION_MISMATCH
```

## FORBIDDEN PROOF MOVES

```text
sorry
admit
exact?
native_decide
new axiom
opaque
phase fitting
real-part replacement of the source row
post-hoc symmetrization
numerical overlap or tolerance
spectral-gap assumption
tracking assumption
finite-to-cofinal inference
commutator scalar expectation
editing any file except OWNED_FILE
```

## EVIDENCE BOUNDARY

A successful theorem proves one exact finite connector only.

It does not prove:

```text
G1
G3
source-row realification
source-row parity
simple-even ground existence
spectral-gap lower bounds
projective-defect decay
cofinal convergence
Route B promotion
RH
```

[Download the byte-locked attachment-ready prompt](sandbox:/mnt/data/PROSHKA_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_PROMPT_2026-08-13.md)
