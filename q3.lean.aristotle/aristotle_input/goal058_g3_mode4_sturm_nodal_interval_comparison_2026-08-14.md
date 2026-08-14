# Goal 058 G3 — Aristotle request: mode-four Sturm nodal comparison

Transport boundary: extracted from the complete Proshka file preview after the browser download control failed to materialize a file. The literal theorem head, pins, gates, stop codes, and validation commands are preserved from the visible preview; this is not claimed byte-identical to the unavailable raw download.

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
