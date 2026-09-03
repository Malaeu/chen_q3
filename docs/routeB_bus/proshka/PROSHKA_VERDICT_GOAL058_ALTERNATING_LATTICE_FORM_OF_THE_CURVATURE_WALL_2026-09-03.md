# STATUS: OPEN — ALTERNATING LATTICE FORM EXACT; NORMALITY AND INPUT A REMAIN DISTINCT
```yaml
PRIMARY: TRY_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-03-LATTICEWALL
BOUNDARY_ID: GOAL058_ALTERNATING_LATTICE_FORM_OF_THE_CURVATURE_WALL
REQUEST_COMMIT: 2b78050265dfcc31d12680682bb22dde69c61ef6
REQUEST_GIT_BLOB: ecd1536add041b6fd43479ad061887f1af1e0cb0
REQUEST_SHA256: 2809978da5f05335bac4ee7c68207654429e6a8182b7fed5fd955086d7b56384
ATTACHMENT_MATCHES_COMMITTED_BYTES: true
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
Q1:
  identity: EXACT
  formula: kappa=2*sum_{n<=N}(-1)^n*(f_k(x_n)-1)/x_n^2-L^2/(2*pi^2)*sum_{n>N}(-1)^n/n^2
  tail: abs(T)<=L^2/(2*pi^2*(N+1)^2)
  bound: kappa<=S_XI+L^2/(2*pi^2)*W+abs(T)
  XI_head: bounded and tends to kappa_Xi by alternating half-cell quadrature
Q2:
  W_O_L_MINUS_TWO_CLOSES_NORMALITY: true
  W_IS_WEAKEST: false
  W_CLOSES_INPUT_A: false
  INPUT_A_NEEDS: for every X>0, sup_{n<=X*L/(2*pi)} abs(Delta_n) tends to zero
Q3:
  LEMMA_7_3_RATE: O(lambda^-1/2) plus outer tail, hence o(L^-2)
  DIRECT_PROJECT_IMPORT: false
  NODE_AMPLIFICATION: sqrt(L)
  weighted_transfer: W_ground_trial<=pi^2/(sqrt(45)*abs(centeredXi(0)))*abs(A)*sqrt(L*p)
  one_rate: abs(A)*L^(5/2)*sqrt(p)=O(1)
Q4:
  CURVATURE_GAP: P59_WEIGHTED_LATTICE_ERROR_SOURCE_BOUND
  FULL_ROUTE_GAP: P59_WEIGHTED_AND_COMPACT_LATTICE_PROFILE_SOURCE_BOUND
  attack: NORMALIZED_XI_LATTICE_EIGEN_EQUATION
  equation: R(y)_n=(K_tilde*y)_n-y_n*(K_tilde*y)_0=0
  success: P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY
  failure: P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
PREDICTION_FATES:
  P_C5_ODD_COBBOUNDARY_EXISTS: [0.45, CONFIRMED_WITH_ADVERSE_UTILITY]
  P_ODD_SECTOR_FLOOR_NONCOLLAPSING: [0.55, REFUTED]
  P_E_TERMS_NOT_GAP_INFLATED: [0.50, REFUTED]
  P_WEIGHTED_LATTICE_ERROR_POLYLOG: [0.65, CONFIRMED_FINITE]
  P_SUP_LATTICE_ERROR_POLYLOG: [0.45, CONFIRMED_FINITE]
  P_ALTERNATING_FORM_EXACT: [0.90, CONFIRMED]
  P_WEIGHTED_ERROR_IS_WEAKEST_SUFFICIENT: [0.60, REFUTED_AS_STATED]
  P_NODE_TRANSFER_EXACT_SQRT_L: [0.70, CONFIRMED_WITH_ANCHOR_REPAIR]
CANDIDATES:
  - [R_NORMALIZED_XI_LATTICE_EQUATION, 10/10, 2/10]
  - [R_COMMON_ANCHOR_PROJECTIVE_TWO_JET, 9/10, 8/10]
KILLS:
  - [W_AS_WEAKEST, THEOREM_SHAPE, EXACT_SIGNED_DECOMPOSITION]
  - [W_ALONE_AS_INPUT_A, THEOREM_SHAPE, MOVING_INDEX_COUNTERESTIMATE]
  - [C5_AS_NEW_BOUND, ATTEMPT, COBBOUNDARY_EQUALS_E]
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: same normalized family, normality, Xi identification
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
LEAN_READY:
  - alternating eta-two sum
  - normalized P59 sample
  - alternating curvature identity
  - alternating tail bound
  - weighted curvature inequality
  - projective weighted-node inequality
NEW_ANALYTIC_WORK:
  - P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY
  - P59_WEIGHTED_LATTICE_ERROR_SOURCE_BOUND
CHEAPEST_NEXT_ACTION:
  task: GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT
  mode: PAPER_AND_SOURCE_READ_ONLY
  prediction: [P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP, 0.40]
  falsifier: kill if stability pays a full inverse, collapsed gap, odd floor, or dense tail
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CURRENT_SMALLEST_GAP: P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY
```

## ROUTE MAP

P59 curvature is `[FINITE_CELL][LEAN]` proved. The alternating form is `[FINITE_CELL][PAPER]` exact. `W=O(L^-2)` supplies normality, not Input A.

## Q1-Q4

With `x_n=2*pi*n/L` and `f_k(x_n)=(-1)^n*xi_n/xi_0`, the proved curvature formula plus `sum (1+2*(-1)^n)/n^2=0` gives Q1. Alternating-series remainder gives the tail; triangle inequality gives the `W` bound. `[FINITE_CELL][PAPER]`

For `g(0)=f''(0)/2=-kappa_Xi`, `g(x)=(f(x)-1)/x^2`, adjacent-pair quadrature gives uniform boundedness from integrable `g'` and convergence to `kappa_Xi` from integrable `g''`, `2*pi/L -> 0`, and `2*pi*N/L -> infinity`. `[COFINAL_FAMILY][PAPER]`

`W=O(L^-2)` closes normality, not Input A: fixed modes approach only zero; fixed physical points need indices of order `L`. CCM Lemma 7.3 controls the continuum trial, not the finite project trial without its crosswalk. Exact P59 sampling gives the `sqrt(L)` transfer and Q3. `[COFINAL_FAMILY][PAPER]`

For Q4, use the center-normalized equation before any inverse. Accept only a source recurrence or one-sided bound; otherwise issue the registered failure and return to the projective two-jet route. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Preserve the representation. Run one source-only preflight for `P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY`, probability `0.40`. Fallback: `abs(A)*L^(5/2)*sqrt(p)=O(1)`.

## STRONGEST ATTACK

The dense CCM equation may hide the collapsed complement inverse. The route survives only if its dense tail is removed or independently bounded before any inverse norm. `[COFINAL_FAMILY][CONDITIONAL]`

## CODEX DIRECTIVE

No execution is authorized. A later transaction may formalize the six Lean-ready items in `Proposition59AlternatingLatticeCurvature.lean`; validate with `lake env lean`, `lake build`, and `scripts/q3_check.sh`. Expected axioms: `[propext, Classical.choice, Quot.sound]`.

## META CLOSEOUT

Curvature is Xi head plus signed error plus explicit tail. C5 as a bound, `W` as weakest, and `W` alone as Input A are killed. All eight probabilities are preserved and scored.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
