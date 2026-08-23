# SOURCE RECORD — dimensionless-to-physical source lift (Linux-тело за Codex)

```yaml
PRIMARY: REGULAR_EVEN_SPHEROIDAL_TO_SATZ9_SOURCE_DATA_PHYSICAL_LIFT
DATE: 2026-08-22
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 5cb885c2 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 3712bf6bc55205cb6f6b4c84bc1f0d0ea68cccd0

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"RegularEvenSpheroidalEigenvalue Satz9SourceData physical
  lift\" exited 0, four TEXT_CANDIDATE hits in the unrelated external zeta23
  base only (word 'lift' as a Lean tactic), no exact declaration or interface
  match anywhere in the six local stores — confirms no existing supplier."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SpheroidalSourcePhysicalLift.lean
LEAN_GIT_BLOB: 341622fa3e50c6160e44025a4bf484b880def679
LEAN_SHA256: 1f1e1362ab36fb8e95fb98c4b0bbb65859b1427a5abc55952e542e4991b80013
LEAN_LINES: 182

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_SOURCE_PHYSICAL_LIFT_2026-08-22.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.regularEvenSpheroidalEigenvalue_physicalSatz9SourceData

EXPECTED_AXIOM_PROFILE:
  Q3.RouteB.regularEvenSpheroidalEigenvalue_physicalSatz9SourceData:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - W13_8_9_DIMENSIONLESS_TO_PHYSICAL_SOURCE_LIFT
    - SATZ9_SOURCE_DATA_PHYSICAL_REALIZATION
  OPENS: []

EXACT_SHIFT_CHECK:
  theta_equals_Lambda_plus_gamma_squared: true
  theta_equals_Lambda_planted_failure: NOT_PRESENT
  key_identity: "G * (x/lambda)^2 = (2*pi*lambda*x)^2, from G = (2*pi*lambda^2)^2"

PROOF_ROUTE_AS_MANDATED:
  - "f, f1, f2 + all fields from spheroidal_normalized_witness h (source-only,
     no project object touched)"
  - "p x = Complex.ofReal (f (x/lambda)); dp x = Complex.ofReal (f1(x/lambda)/lambda)"
  - "hasDeriv: real chain rule (f∘(·/lambda)) via HasDerivAt.comp, lifted to
     ℂ via HasDerivAt.scomp against ofRealCLM.hasDerivAt"
  - "flux: product/chain rule on (lambda^2-y^2)*f1(y/lambda)/lambda, reduced to
     -2z*f1(z)+(1-z^2)*f2(z) (z=x/lambda) via field_simp, then the ODE hodez
     gives = G*z^2*f(z) - theta*f(z) via linear_combination, then
     G*z^2 = (2*pi*lambda*x)^2 via field_simp/ring — exactly the physical shift"
  - "even: source parity hev + neg_div"
  - "center_ne: f 0 = 1 (0/lambda=0, zero_div)"
  - "normalized_continuousOn: ContinuousOn f on Icc(-1,1) composed with the
     scaling map (MapsTo + ContinuousOn.comp), then continuous_ofReal.
     centerNormalized p = p pointwise since p 0 = 1 (div_one)"

DEVIATION_FROM_DIRECTIVE:
  - "PROOF_ROUTE names dp x = f1(x/lambda)/lambda literally (not through an
     intermediate normalized_witness field for f1); matches exactly, no
     deviation in substance."
  - "HasDerivAt.scomp in this Mathlib version takes the composition point `x`
     as an EXPLICIT leading argument (a `variable (x)` section convention in
     Mathlib's Deriv/Comp.lean, not implicit as in some other chain-rule
     lemmas) — several iterations were needed to get the exact invocation
     shape (HasDerivAt.scomp x hg hh, then rw the composed-function/smul
     normal forms via separate `have`s rather than direct ascription) before
     the term elaborated. No mathematical content changed; purely API shape."

FORBIDDEN_CHECK:
  project_Ferrers_mode_used_as_p: not_used
  mode4ClassicalEvenEigenvalue_or_V3_2_in_proof_term: not_used
  source_witness_defined_from_project_object: not_present
  Satz9_rate_hypothesis_added: not_added
  Satz9_asymptotic_claimed: not_claimed
  theta_replaced_by_Lambda: not_present (theta = Lambda + G throughout)
  global_Continuous_instead_of_ContinuousOn: not_used (ContinuousOn as required)
  selected_source_package_transport_bundled: not_bundled
  F72_1A_or_F72_1C_bundled: not_bundled
  paper_axiom_or_typed_hole: none
  sorry_or_admit: none
  theorem_weakening: none (TARGET_SHAPE дословно)

GATE:
  ROUNDS: 5 (гладкая цепочка HasDerivAt.scomp: explicit-x confusion, defeq
    ascription friction on ∘-composed lambda, `↑Wderiv * ↑(1:ℝ)` cast
    normalization — все чинились явными `have`+`rw` вместо прямой аскрипции
    типа на композиции)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SpheroidalSourcePhysicalLift.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SpheroidalSourcePhysicalLift — Build completed successfully (7847 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SpheroidalSourcePhysicalLift.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: SOURCE_PHYSICAL_SATZ9_DATA_LIFT_LEAN
NEXT_LOAD_BEARING_GAP: SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
