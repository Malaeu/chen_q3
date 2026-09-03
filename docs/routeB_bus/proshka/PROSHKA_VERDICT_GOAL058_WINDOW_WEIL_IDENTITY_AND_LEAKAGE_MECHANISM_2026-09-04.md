# STATUS: OPEN — CUTOFF-FREE WEIL ZERO-SUM IDENTITY CONFIRMED; LEAKAGE IS RH-CONDITIONAL AND SELECTED-DIAGONAL POSITIVITY IS NOT THE WEIL CRITERION WITHOUT EXHAUSTION
```yaml
PRIMARY: TRY_P59_ANCHORED_LOG_DERIVATIVE_FIXED_COMPACT_DIVISOR_CONTROL
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: REPRESENTATION_SHIFT_FROM_INDEFINITE_ZERO_ENERGY_TO_DIVISOR_COUNT

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-LEAKAGE
  BOUNDARY_ID: GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM
  REQUEST_COMMIT: 5fcf891b994407b693240424eda3cb12115c9a5c
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_WEIL_IDENTITY_LEAKAGE_2026-09-04.txt
  REQUEST_GIT_BLOB: b9df8f842de379d286c5e93691bfc87e774d3763
  REQUEST_SHA256: 2142b6adc46c609df84973f54ed6d9e426f4c7862ee870b2ca0c029e29be5929
  REQUEST_BYTES: 9432
  REQUEST_LINES: 94
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: 7fc903a3d4ba76d042d1c902d07529b1d778e53b
  PARENT_VERDICT_ZEROPIN: 1529837d895f531330acfa4d81d96c83779a75d7
  PARENT_VERDICT_QUASIEIGEN: 9b8226246adda225c10bca322d75782c8c98dd5e
  PARENT_VERDICT_SHELLSEARCH: 99927f01a210df283fce15b3e846f595ec1fd629

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

Q1_IDENTITY:
  VERDICT: CONFIRMED_WITH_REAL_EVEN_SECTOR_SCOPE_GUARD
  EXACT_FORM:
    quadratic: "<v, K_even(m,N) v> = sum_{z in ZetaCenteredZeros} F_v(z)^2"
    entry: "(K_even(m,N))_kl = sum_z E_k(z) * E_l(z)"
    zero_coordinate: "1/2 + i*z is a nontrivial zero of zeta"
    multiplicity: INCLUDED
    convergence: ABSOLUTE
  HYPOTHESES:
    - "m=c>1"
    - "N>=0"
    - "v is a real even Galerkin vector"
    - "K_even is the cutoff-free real-even contraction of the exact CCM matrix"
    - "F_v is the Proposition-5.9 transform in the locked normalization"
  SOURCE_CHAIN:
    - "Groskin arXiv:2607.02828, Lemma 2.1"
    - "Groskin arXiv:2607.02828, Lemma 2.2"
    - "Groskin arXiv:2607.02828, Theorem 2.5"
    - "CCM arXiv:2511.22755, Proposition 5.9, equation (5.25)"
  NO_TRUNCATION:
    zero_sum: true
    prime_remainder: false
    prime_reason: "support of the induced Fourier weight kills prime powers q>m exactly"
    archimedean_remainder: false
    archimedean_reason: "K uses the cutoff-free T->infinity entry limit, not a finite-T quadrature"
  SCOPE_GUARD:
    direct_theorem_scope: REAL_EVEN_SECTOR
    arbitrary_full_complex_mode_entries: NOT_CLAIMED_BY_THEOREM_AS_QUOTED
  LEAN:
    finite_polarization_and_matrix_packaging: LEAN_READY
    explicit_formula_zero_sum: NEW_ANALYTIC_IMPORT
    finite_dimensional_reformulation_eliminates_explicit_formula: false
  SCOPE: FINITE_CELL
  VERIFIER: PAPER

Q2_POSITIVITY:
  RAYLEIGH_IDENTITY:
    formula: "lambda1(m,N) = min_{v != 0} (sum_z F_v(z)^2) / ||v||^2"
    status: UNCONDITIONAL
  TOTAL_ZERO_SIDE_ENERGY_WORDING:
    unconditional: false
    valid_under_RH_for_real_even_v: true
    reason: "off-line quartets make the exact sum real but indefinite"
  OFFLINE_QUARTET:
    formula: "F(z0)^2 + F(conj z0)^2 + F(-z0)^2 + F(-conj z0)^2 = 2 Re(F(z0)^2) + 2 Re(F(-z0)^2)"
    even_reduction: "= 4 Re(F(z0)^2)"
    sign: INDEFINITE
  FIXED_WINDOW:
    all_N_nonnegative: "equivalent to QW_lambda >= 0 by the CCM form-core theorem"
    all_N_strictly_positive: "sufficient for QW_lambda >= 0 but not equivalent; the limit may be zero"
  GLOBAL_EQUIVALENCE:
    repaired_statement: "nonnegativity for every N on a cofinal family of windows, together with the exact restriction/form-core crosswalk, is equivalent to global Weil positivity and hence RH"
    selected_single_N_per_m: NOT_EQUIVALENT_WITHOUT_EXHAUSTION_THEOREM
    selected_single_N_per_m_implies: "positivity only on the selected finite subspaces"
  HONEST_POSITIVITY_ATOM: CCM_WINDOW_WEIL_POSITIVITY_ON_A_PROVED_FORM_CORE_EXHAUSTION
  POSITIVITY_ROUTE_CLASSIFICATION: RH_EQUIVALENT_RESTATEMENT
  SAME_FAMILY_REALZERO_ROUTE_CLASSIFICATION: NOT_KILLED_BY_THIS_RESTATEMENT
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

Q3_LEAKAGE:
  UNCONDITIONAL_LEAKAGE_NORM:
    status: REJECTED
    reason: "the zero-side pairing is indefinite off RH"
  UNDER_RH:
    interpretation: "K is a positive sampling Gram operator on the real zeta ordinates and lambda1 is the squared least singular value"
    inside_outside_split: POSITIVE
  OBSERVED_SQRT_LAMBDA1_SCALE:
    status: DIAGNOSTIC_ONLY
    theorem: NOT_DERIVED
  RECOGNIZED_ANALOGUES:
    exact_nearest: "Bombieri 2000 localized Weil quadratic-functional minimizer"
    signal_processing: "Slepian-Landau-Pollak time-band concentration"
    standard_name_for_zero_measure_problem: NONE_FOUND
    descriptive_name_only: WEIL_SLEPIAN_ZERO_SAMPLING_MINIMIZER
    beurling_selberg: "counting/majorant analogy only, not the same variational problem"
  FIXED_COMPACT_DIVISOR_REQUIREMENT:
    - "each target zero is matched with its multiplicity"
    - "no additional ground-transform zero occurs outside the target zero neighborhoods"
    - "the compact boundary is zero-free for both functions"
    - "the zero-count comparison is certified by Rouche or the argument principle"
  SMALL_VALUE_AT_TARGET_ZERO:
    sufficient_for_nearby_zero: false
    missing:
      - "boundary-uniform comparison or a local derivative/slope lower bound"
      - "multiplicity and separation control"
  GLOBAL_PRODUCT_IDENTIFICATION_ADDS:
    - "escape of excess zeros from every compact"
    - "reciprocal-square mass tightness or an equivalent tail ledger"
    - "second-jet/gauge pinning"
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL

Q4_NOT_RH:
  UNCONDITIONAL_SHAPE:
    statement: "not RH implies a compactly supported Weil test with negative quadratic value; hence some sufficiently large localized window and, by the form core, some finite compression have negative minimum"
    status: PAPER_THEOREM_SHAPE
  BOMBIERI_FINITE_NEGATIVE_INDEX:
    assumptions: "only finitely many off-line nontrivial zeros"
    conclusion: "large enough truncations have negative index equal to half the off-line-zero count"
  PARTICULAR_OFFLINE_QUARTET_FOR_GROUND:
    necessarily_negative: false
    necessarily_dominant: false
  WINDOW_THRESHOLD_FROM_DELTA_ONLY:
    available: false
    status: NO_VERIFIED_QUANTITATIVE_LOCATOR
    note: "the witness size also depends on height, separation, multiplicity and the chosen test class"
  PROPOSED_NONREAL_GROUND_ZERO_THEOREM:
    status: KILLED
    reason: "CCM Theorem 5.10 gives a real-rooted ground transform from simple-even bottom data independently of the sign of lambda1"
  CIRCULAR_LOOP:
    statement: "proving positivity on an exhaustive CCM form core already proves Weil positivity and RH; Theorem 5.10 and Hurwitz are not needed for that implication"
  NONCIRCULAR_COMPONENTS:
    - "the cutoff-free zero-sum identity"
    - "the simple-even real-zero theorem"
    - "not RH implies existence of a negative localized Weil direction"
  DOES_NOT_SUPPLY:
    - "ground-to-trial same-family convergence"
    - "a delta-only window threshold"
    - "a contradiction between negative lambda1 and real-rootedness"
  SCOPE: ABSTRACT
  VERIFIER: PAPER

DISCRIMINATOR:
  NAME: P59_FIXED_COMPACT_WINDING_NUMBER_DIFFERENCE
  FORMULA: "(1/(2*pi*i)) * integral_boundary_D ((F_ground'/F_ground) - (F_trial'/F_trial)) dz"
  PASS_CONDITION: "the certified integer is zero on every precommitted compact boundary"
  FAIL_CONDITION: "a nonzero integer certifies missing or extra zeros with multiplicity"
  BOUNDARY_GUARD: "both transforms are nonzero on the boundary"
  ZERO_CONSISTENT_RESULT: INCONCLUSIVE_WITHOUT_ANALYTIC_OR_INTERVAL_CERTIFICATE
  PLANTED_FAILURE:
    transform: "F_plant(z) = F_reference(z) * (1 - z^2/a^2), renormalized at the anchor"
    expected_count_change: 2
  SCOPE: FINITE_CELL
  VERIFIER: CONDITIONAL

CANDIDATE_REREPRESENTATIONS:
  - CODE: R1_ANCHORED_LOG_DERIVATIVE_ARGUMENT_PRINCIPLE
    RANK: PRIMARY
    TARGET: "cancel the common P59 lattice factor and compare finite numerator divisors on fixed compact boundaries"
    KILL_POWER: 9/10
    COST: 5/10
  - CODE: R2_PROJECTIVE_GROUND_TO_TRIAL_COMPACT_TRANSFER
    RANK: SECOND
    TARGET: "source residual/complement control -> projective coefficient error -> compact transform error -> trial-to-Xi"
    KILL_POWER: 10/10
    COST: 8/10
  - CODE: R3_ZERO_SAMPLING_CHRISTOFFEL_LEVERAGE
    RANK: DIAGNOSTIC_ONLY
    TARGET: "study K^{-1}E(z) as a leverage/Christoffel object at target zeros"
    KILL_POWER: 6/10
    COST: 4/10
    RH_SIGN_DEPENDENCE: "positive-Gram interpretation requires RH"

RANKED_NEXT_ACTION:
  CODE: PAPER_PREFLIGHT_P59_ANCHORED_LOG_DERIVATIVE_FIXED_COMPACT
  EXECUTION_AUTHORIZED: false
  EXACT_TARGET: P59_FIXED_COMPACT_LOG_DERIVATIVE_WINDING_LOCK
  SUFFICIENT_INTERFACE: "boundary nonvanishing plus length(boundary)/(2*pi) times the sup norm of the log-derivative difference < 1"
  CONSEQUENCE: "ground and trial transforms have the same zero count with multiplicity inside the boundary"
  FIRST_SOURCE_STEP: "prove the common Proposition-5.9 sine/lattice factor cancels exactly in the anchored logarithmic-derivative difference"
  FALSIFIER: P59_EXTRA_REAL_ROOT_PAIR_WINDING_PLANT
  SUCCESS_CODE: P59_FIXED_COMPACT_DIVISOR_COUNT_LOCKED
  FAILURE_CODE: P59_LOG_DERIVATIVE_SOURCE_BOUND_NOT_AVAILABLE

SCOPED_KILLS:
  UNCONDITIONAL_LEAKAGE_NORM:
    CODE: KILL_LEAKAGE_AS_UNCONDITIONAL_ZERO_SIDE_NORM
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_OFFLINE_QUARTET_INDEFINITENESS
    PINNED_EVIDENCE: "Groskin arXiv:2607.02828 Theorem 2.5 plus quartet algebra"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  SELECTED_DIAGONAL_POSITIVITY_EQ_RH:
    CODE: KILL_SELECTED_DIAGONAL_POSITIVITY_EQ_RH_WITHOUT_EXHAUSTION
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: QUANTIFIER_AND_FORM_CORE_MISMATCH
    PINNED_EVIDENCE: "CCM arXiv:2511.22755 Proposition 3.4"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_STATED
  OFFLINE_ZERO_FORCES_NONREAL_GROUND_ZERO:
    CODE: KILL_OFFLINE_ZERO_FORCES_NONREAL_P59_GROUND_ZERO
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: INCOMPATIBILITY_WITH_THEOREM_5_10
    PINNED_EVIDENCE: "CCM arXiv:2511.22755 Theorem 5.10"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD

PREDICTION_FATES:
  P_RANGE_IDENTITY_UNIFORM_IN_M:
    probability: 0.70
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_RANGE_IDENTITY_HIGHER_ZEROS:
    probability: 0.55
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_RANGE_IDENTITY_SEES_THE_LINE:
    probability: 0.60
    fate: CONFIRMED_WITH_SIGN_GUARD
    note: "the identity sees the line through positivity only when all centered zeros are real; it is not a selector by itself"
    scope: ABSTRACT
    verifier: PAPER
  OBSERVER_ZERO_SUM_SCALE_DOUBT:
    registered: false
    fate: REFUTED_BY_REPORTED_MOMENT_AND_TAIL_DATA
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_SOURCE_SPECIFIC_REALZERO_COMPONENT_IS_SELECTIVE:
    probability: 0.30
    fate: REFUTED_BY_EXPLICIT_REALROOTED_CONE_FALSIFIER
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_IDENTITY_UNCONDITIONAL_NO_TRUNCATION:
    probability: 0.75
    fate: CONFIRMED_WITH_REAL_EVEN_SECTOR_SCOPE_GUARD
    scope: FINITE_CELL
    verifier: PAPER
  P_LAMBDA1_POSITIVITY_IS_WEIL_CRITERION:
    probability: 0.60
    fate: REFUTED_AS_STATED_REPAIRED_FULL_FORM_CORE_EXHAUSTION_IS_EQUIVALENT
    scope: COFINAL_FAMILY
    verifier: PAPER
  P_LEAKAGE_PICTURE_HAS_A_NAME:
    probability: 0.50
    fate: PARTIALLY_CONFIRMED
    note: "Bombieri gives the exact localized variational analogue and Slepian gives the concentration analogy; no standard zeta-zero leakage name was found"
    scope: ABSTRACT
    verifier: PAPER
  P_NOTRH_BRANCH_HAS_UNCONDITIONAL_SHAPE:
    probability: 0.30
    fate: CONFIRMED_AFTER_REPAIR
    note: "the valid shape is eventual negative localized direction/finite compression, not a nonreal zero of the simple-even ground transform"
    scope: ABSTRACT
    verifier: PAPER

LEAN_READY_VS_ANALYTIC:
  LEAN_READY_OR_FINITE_ALGEBRA:
    - "Proposition-5.9 entire transform and finite Cauchy numerator infrastructure already in project"
    - "polarization from a quadratic identity to the real-even matrix identity"
    - "Rayleigh minimum consequences from an assumed exact matrix identity"
    - "offline-quartet conjugation/evenness algebra"
    - "abstract winding-number integer comparison after a Complex-analysis API preflight"
  NEW_ANALYTIC:
    - "Guinand-Weil explicit formula for the exact induced test class"
    - "absolute convergence of the zero sum in project formalization"
    - "exact project crosswalk from Groskin g_v to the locked F_v squared convention"
    - "selected-production-schedule form-core exhaustion, if the positivity route is pursued"
    - "source-specific fixed-compact logarithmic-derivative bound"
    - "any quantitative off-RH localization threshold"
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_RUN_PERFORMED: false
  JUDGE_KERNEL_RERUN: false

K8A:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: "the same normalized entire finite-ground family has only real zeros and converges locally uniformly to centeredXi"
  ORIGINAL_REQUESTED_OBJECT: "unconditional sqrt(lambda1) leakage norm and positivity of one selected finite cell per window"
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "projective ground-to-trial error times compact evaluation amplification tends to zero"
    - "fixed-compact divisor equality plus tail and second-jet control yields finite-product target identification"
  FAILURE_TYPE: INCOMPATIBILITY
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "exact finite zero-sampling dictionary for the source-locked ground family"

ROUTE_MAP:
  exact_zero_sum_dictionary: GREEN_PAPER
  unconditional_leakage_norm: KILLED
  selected_diagonal_positivity_eq_RH: KILLED_AS_STATED
  full_form_core_positivity: RH_EQUIVALENT
  fixed_compact_divisor_control: OPEN_PRIMARY
  direct_same_family_transform_tracking: OPEN_SECONDARY

NEW_REGISTERED_PREDICTIONS:
  P_COMMON_LATTICE_FACTOR_CANCELS_IN_LOG_DERIVATIVE:
    probability: 0.90
    test: PAPER_IDENTITY_PREFLIGHT
  P_FIXED_COMPACT_SOURCE_BOUND_CLOSES_WITHOUT_FULL_TRACKING:
    probability: 0.35
    test: FIRST_NONTRIVIAL_BOUNDARY_COMPACT

CODEX_DIRECTIVE:
  AUTHORIZED: false
  REASON: "request authorizes verdict document only and forbids Lean edit or numerical run"

META_CLOSEOUT:
  PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  BECAME_SMALLER: "the exact identity is no longer a hypothesis; the open issue is divisor control or same-family transform tracking, not matrix-to-zero provenance"
  KILLED:
    - "unconditional norm interpretation of leakage"
    - "RH equivalence of positivity on one selected finite cell per changing window"
    - "off-line zeta zero forces a nonreal zero of the simple-even ground transform"
  DO_NOT_REPEAT:
    - "use positive finite diagnostics as a universal quantifier"
    - "call an indefinite zero sum an energy off RH"
    - "use small values at target zeros as proof of nearby roots without a discriminator"
  CURRENT_SMALLEST_GAP: P59_FIXED_COMPACT_LOG_DERIVATIVE_SOURCE_BOUND
  NEXT_CHEAPEST_DECISIVE_TEST: "exact common-factor cancellation plus the planted extra-root winding test"
  MEMORY_ENTRY:
    target: WINDOW_WEIL_IDENTITY_AND_LEAKAGE
    status: OPEN
    failed_strategy: UNCONDITIONAL_LEAKAGE_NORM
    cognitive_operator_used: REPRESENTATION_SHIFT
    new_gap_name: P59_FIXED_COMPACT_LOG_DERIVATIVE_SOURCE_BOUND
    invariant_learned: "the zero-sum is positive only on the RH line; exact provenance does not supply positivity"
    forbidden_future_move: "do not infer RH from selected-cell positivity without a proved form-core exhaustion"
    next_decisive_test: "P59 common-factor log-derivative cancellation"
    
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## Q1 — exact status of the window identity

The identity is confirmed, with one scope correction. Groskin's `Q_infinity` is the cutoff-free CCM Galerkin form. Lemma 2.1 identifies its prime, pole and archimedean entries with the CCM assembly. Lemma 2.2 proves that the induced `g_v` is an admissible Guinand–Weil test function and that its zero sum is absolutely convergent. Theorem 2.5 then states, for fixed `c > 1`, `N >= 0`, and a real even Galerkin vector `v`,

\[
\langle v,Q_\infty v\rangle
=
\sum_{z:\,\zeta(1/2+iz)=0}^{*} g_v(z),
\]

with multiplicity. `[FINITE_CELL][PAPER]`

Under the locked real-even CCM convention, `g_v` is the autocorrelation test generated by the same finite window function whose Proposition-5.9 transform is `F_v`; therefore

\[
g_v(z)=F_v(z)F_v(-z)=F_v(z)^2.
\]

Polarization gives the even-sector matrix identity

\[
(K_{\mathrm{even}})_{k\ell}
=
\sum_z E_k(z)E_\ell(z).
\]

This is the correct meaning of the request's matrix formula. The theorem as quoted is directly a theorem on the real even contraction. It should not be silently promoted to arbitrary complex vectors or to every entry of the uncontracted full-mode matrix. `[FINITE_CELL][PAPER]`

There is no zero truncation. The zero sum is the full absolutely convergent sum over all nontrivial zeros. There is no prime remainder: the induced Fourier weight is supported in `[-log(c)/(2 pi), log(c)/(2 pi)]`, so prime powers `q > c` vanish exactly in the explicit formula. There is no archimedean remainder when `K` denotes the cutoff-free `T -> infinity` assembly; a finite-`T` quadrature would be a different object and would carry Groskin's tail budget. `[FINITE_CELL][PAPER]`

The locator chain is exact:

```text
Groskin, arXiv:2607.02828:
  Lemma 2.1  — entry identification;
  Lemma 2.2  — admissibility and absolute zero-sum convergence;
  Theorem 2.5 — finite Guinand–Weil dictionary;
  Remark 2.6 — the zero-sum step is the classical explicit formula.

Connes–Consani–Moscovici, arXiv:2511.22755:
  Proposition 5.9, equation (5.25) — the entire finite-window transform F_v.
```

`[FINITE_CELL][PAPER]`

A finite-dimensional reformulation can package the result after the analytic identity has been supplied: one can define a summable zero-indexed evaluation family, prove the matrix identity by polarization, and derive Rayleigh consequences in finite linear algebra. It cannot remove the Guinand–Weil explicit formula. The equality between the source matrix and the infinite zero sum is the analytic theorem. The project can formalize it, but it must import or prove the explicit formula and absolute convergence; no purely finite matrix argument creates the zeta-zero side. `[ABSTRACT][PAPER]`

## Q2 — what is unconditional, and where Weil positivity reappears

For a unit real-even vector `v`, the exact identity gives

\[
v^{T}Kv=\sum_z F_v(z)^2.
\]

Rayleigh–Ritz therefore gives unconditionally

\[
\lambda_1(m,N)
=
\min_{v\ne0}
\frac{\sum_z F_v(z)^2}{\|v\|_2^2}.
\]

The phrase "total zero-side energy" is not unconditional. It becomes literal only when all centered zeros `z` are real, because then `F_v(z)` is real and each summand is nonnegative. `[FINITE_CELL][PAPER]`

Let `z_0` be a genuinely nonreal centered zero. Reality of the coefficients gives
`F_v(conj z_0)=conj(F_v(z_0))`. The centered zero symmetries give the quartet
`z_0`, `conj z_0`, `-z_0`, `-conj z_0`. Its exact contribution is

\[
F_v(z_0)^2+F_v(\overline{z_0})^2
+F_v(-z_0)^2+F_v(-\overline{z_0})^2
=
2\Re(F_v(z_0)^2)+2\Re(F_v(-z_0)^2).
\]

For an even transform this is

\[
4\Re(F_v(z_0)^2),
\]

which can be negative. The full zero sum is real and absolutely convergent, but it is an indefinite Hermitian/real quadratic pairing off RH, not an `ell^2` norm. `[ABSTRACT][PAPER]`

The exact equivalence has two quantifiers, not one diagonal:

1. For a fixed window `lambda`, CCM Proposition 3.4 says the Fourier-mode span is a form core and the lower bound of `QW_lambda` is the limit of the smallest finite-section eigenvalues as `N -> infinity`. Hence
   \[
   \lambda_{\min}(QW_\lambda^N)\ge0\quad\forall N
   \]
   is equivalent to `QW_lambda >= 0`. Strict positivity for every finite `N` is sufficient, but not equivalent, because the decreasing minima may converge to zero. `[COFINAL_FAMILY][PAPER]`

2. Nonnegativity for every window in an unbounded cofinal window family gives global Weil positivity, since every compactly supported Weil test lies in some sufficiently large window. Together with Weil's criterion, that is equivalent to RH. `[ABSTRACT][PAPER]`

The production statement

\[
\lambda_1(m,N(m))>0\qquad\text{for one selected }N(m)\text{ at each }m
\]

does not contain either quantifier. Without a theorem that these changing finite spaces form a form-core exhaustion in the form topology, it proves only positivity on the selected finite subspaces. Therefore the registered claim "`lambda_1(m)>0` for all production cells is equivalent to RH" is refuted as stated. `[COFINAL_FAMILY][PAPER]`

If the missing exhaustion theorem is supplied and the sign is weakened to nonnegativity, the repaired statement is indeed Weil's criterion in CCM coordinates. The honest atom is:

```text
CCM_WINDOW_WEIL_POSITIVITY_ON_A_PROVED_FORM_CORE_EXHAUSTION.
```

That positivity program is a restatement of the RH-equivalent Weil criterion. The current Route-B same-family program is not thereby killed: it intends to use simple-even real-rooted finite ground transforms plus independently proved convergence of those same transforms to `Xi`, rather than assume positivity on every window. `[COFINAL_FAMILY][PAPER]`

A further correction is important. Theorem 5.10 does not require `lambda_1 > 0`. It uses the smallest eigenvalue, simplicity and evenness; after shifting by that smallest eigenvalue it produces a selfadjoint operator and a transform with only real zeros. A negative smallest Weil eigenvalue is compatible with a real-rooted ground transform. `[FINITE_CELL][PAPER]`

## Q3 — leakage as a variational object

The reported picture is useful as a finite diagnostic, but its norm language is conditional.

Under RH, the exact matrix can be read as a sampling Gram operator

\[
K=S^{*}S,\qquad
(Sv)_\gamma=F_v(\gamma),
\]

over the real zeta ordinates. Then `lambda_1` is the squared least singular value of this sampling map, and an inside/outside split of the zero ordinates is positive. In that regime, "leakage outside the window" is a legitimate concentration picture. `[FINITE_CELL][CONDITIONAL]`

Without RH, the same exact formula is an indefinite quartet pairing. There is no positive sampling norm, no unconditional Pythagorean split into inside and outside energy, and no theorem that the observed outside amplitude `sqrt(lambda_1)` is the source of `lambda_1`. The reported scale remains a strong diagnostic, not a quantifier-bearing identity. `[FINITE_CELL][PAPER]`

There is no standard established name for exactly this zeta-zero minimization problem. The closest exact locator is:

```text
E. Bombieri,
"Remarks on Weil's quadratic functional in the theory of prime numbers, I",
Rend. Lincei Mat. Appl. 11 (2000), 183–233.
```

Bombieri proves that the localized Weil functional attains a minimum on the unit ball of the `L^2` space supported in a fixed interval, and studies finite truncations and their eigenvalues. Yoshida's earlier locator is:

```text
H. Yoshida,
"On Hermitian forms attached to zeta functions",
Zeta Functions in Geometry, Adv. Stud. Pure Math. 21 (1992), 281–325.
```

The nearest signal-processing analogy is the Slepian–Landau–Pollak concentration problem, where the extremizer maximizes simultaneous time/frequency concentration. That analogy becomes operator-theoretically exact only after a positive sampling measure is available. Beurling–Selberg extremal functions optimize majorants/minorants for counting; they are not the same least-Rayleigh problem. `[ABSTRACT][PAPER]`

A descriptive phrase such as `Weil–Slepian zero-sampling minimizer` is acceptable in a research note, but it is not a standard theorem name and must not be presented as an imported result. `[ABSTRACT][PAPER]`

On a fixed compact, complete divisor tightness is stronger than the two numerical observations in the request. Choose disjoint small neighborhoods around every target zero and a compact boundary avoiding target zeros. One must prove, eventually:

1. each target neighborhood contains exactly the target multiplicity of ground-transform zeros;
2. the complement contains no ground-transform zero;
3. neither function vanishes on the comparison boundary;
4. the comparison is certified by Rouché or an argument-principle integer. `[COFINAL_FAMILY][PAPER]`

The bound `F_xi(gamma_j)=O(sqrt(lambda_1))`, even when available under RH, proves only a small value at the center of a target disk. A small value does not imply a nearby zero. It needs a derivative/slope lower bound with multiplicity control, or preferably a uniform boundary estimate for Rouché. Likewise, observing that all numerator roots below a moving threshold are tracked does not prove absence of spurious roots on an arbitrary fixed compact. `[COFINAL_FAMILY][PAPER]`

For global entire-function identification, fixed-compact divisor matching must be supplemented by escape/tightness of excess zeros and by a gauge pin such as reciprocal-square mass or the second jet. This is exactly why the ZEROPIN verdict did not close from low-zero tracking alone. `[COFINAL_FAMILY][PAPER]`

## Q4 — the not-RH branch without hand-waving

If RH is false, Weil's criterion gives a compactly supported test with negative Weil quadratic value. Put its support inside a sufficiently large multiplicative window. The corresponding localized form is negative on that test. By the CCM form-core theorem, some sufficiently large finite Fourier compression has a negative Rayleigh value and hence a negative smallest eigenvalue. This is an unconditional theorem shape. `[ABSTRACT][PAPER]`

Bombieri proves a stronger finite-index statement under the additional hypothesis that only finitely many nontrivial zeros are off the critical line: for a sufficiently large truncation, the number of negative eigenvalues is one-half of the number of off-line zeros. This is an existence theorem for a large enough truncation, not a source-verified formula for the threshold. `[COFINAL_FAMILY][PAPER]`

What does not follow is the request's pointwise story. Merely placing the real part `gamma_0` of one off-line zero inside the window does not force the ground minimizer's contribution from that particular quartet to be negative, dominant, or responsible for the sign of `lambda_1`. The minimizer is global and the exact sum has cancellation among quartets. `[COFINAL_FAMILY][PAPER]`

No verified locator supplies a universal window size depending only on `|delta|`. An explicit localization scale would also depend on the height, multiplicity, separation from other zeros, the test class and normalization. A heuristic resolution scale of order `1/|delta|` is not a theorem and is not entered in the ledger. `[ABSTRACT][PAPER]`

The proposed theorem shape

```text
a window contains an off-line zeta zero
-> the finite simple-even ground transform has a nonreal zero
```

is false. CCM Theorem 5.10 says the opposite: whenever the finite bottom eigenvalue is simple and its eigenvector is even and legally normalized, the ground transform has only real zeros, regardless of whether the bottom eigenvalue is positive or negative. `[FINITE_CELL][PAPER]`

Therefore the loop is:

```text
prove lambda_min >= 0 on a genuine form-core exhaustion
-> global Weil positivity
-> RH.
```

This already proves RH through Weil's criterion; Theorem 5.10 and Hurwitz add nothing to that implication. The noncircular Route-B alternative is:

```text
simple-even finite ground
-> real-rooted finite ground transform

plus

the same normalized finite ground transforms
-> Xi locally uniformly

-> Hurwitz / ZeroEscape
-> RH.
```

The zero-sum identity explains the matrix exactly, but it does not supply the second arrow. `[COFINAL_FAMILY][PAPER]`

## Route map

| Route | Decisive interface | Main risk | Status | Tags |
|---|---|---|---|---|
| Exact finite zero-sum dictionary | Groskin Theorem 2.5 plus CCM Proposition 5.9 crosswalk | real-even/full-sector scope confusion | **CLOSED ON PAPER** | `[FINITE_CELL][PAPER]` |
| Leakage as positive sampling norm | all centered zeta zeros real | this premise is RH | **KILLED UNCONDITIONALLY** | `[ABSTRACT][PAPER]` |
| Positivity of every selected production cell | selected spaces form a form-core exhaustion | missing quantifier/topology bridge | **OPEN; NOT RH-EQUIVALENT AS STATED** | `[COFINAL_FAMILY][PAPER]` |
| Full CCM-window positivity | all `N` at cofinal windows | exactly Weil positivity | **RH-EQUIVALENT RESTATEMENT** | `[ABSTRACT][PAPER]` |
| Anchored log-derivative divisor route | fixed-compact winding-number lock | source-specific boundary bound | **PRIMARY OPEN REPRESENTATION** | `[COFINAL_FAMILY][CONDITIONAL]` |
| Direct same-family tracking | projective error times compact amplification tends to zero | residual/gap or another source supplier | **OPEN** | `[COFINAL_FAMILY][CONDITIONAL]` |

## Final proposal

Do not formalize the full explicit formula next. It would certify an identity that is now understood but would not reduce the same-family convergence wall.

The selected paper preflight is:

```text
P59_FIXED_COMPACT_LOG_DERIVATIVE_WINDING_LOCK
```

For a precommitted compact domain `D` whose boundary is zero-free for the ground and trial transforms, prove the abstract implication

\[
\frac{\operatorname{length}(\partial D)}{2\pi}
\sup_{\partial D}
\left|
\frac{F_{\rm ground}'}{F_{\rm ground}}
-
\frac{F_{\rm trial}'}{F_{\rm trial}}
\right|
<1
\]

\[
\Longrightarrow
N_D(F_{\rm ground})=N_D(F_{\rm trial})
\]

with multiplicity. Then attack the source-specific bound after cancelling the common Proposition-5.9 sine/lattice factor. `[ABSTRACT][PAPER]`

This representation has the correct discriminator: the argument-principle difference is an integer. The plant

\[
F_{\rm plant}(z)
=
F_{\rm ref}(z)(1-z^2/a^2)
\]

adds the real pair `+a,-a`; the winding difference must report `2`. If the detector does not reject that plant, it is not a divisor certificate. `[FINITE_CELL][PAPER]`

The direct runner-up remains the already typed same-family route:

\[
\text{source residual/complement control}
\to
\text{projective ground-to-trial error}
\to
\text{compact transform difference}
\to
\Xi.
\]

It has greater direct closure power but higher cost and has already exposed a collapsed absolute-gap interface. `[COFINAL_FAMILY][CONDITIONAL]`

## Strongest attack

The strongest objection to the leakage narrative is one line:

\[
\sum_z F_v(z)^2
\quad\text{is not}\quad
\sum_z |F_v(z)|^2
\]

when the centered zeros are not real.

The exact identity is stronger provenance and weaker positivity than it first appears. It tells us exactly what the matrix measures; it does not make that measurement a norm. An off-line quartet can contribute a negative real number, while the finite ground transform itself remains real-rooted by Theorem 5.10. `[ABSTRACT][PAPER]`

The strongest objection to the production-positivity claim is the missing quantifier:

```text
one N(m) per changing window
```

is not

```text
all N for each window plus a proved form-core exhaustion.
```

No amount of positive finite-cell data repairs that logical difference. `[COFINAL_FAMILY][PAPER]`

## Lean-ready versus new analytic

The finite algebra is ready for Lean: the project already contains the Proposition-5.9 transform, finite Cauchy numerator and real-zero infrastructure. Given an analytic zero-sum theorem as an assumption, polarization, matrix equality, Rayleigh consequences and quartet algebra are ordinary finite formalization. `[FINITE_CELL][LEAN]`

The load-bearing new analytic imports are the Guinand–Weil explicit formula in the exact project normalization, absolute convergence of the zero sum, and the exact `g_v=F_v^2` crosswalk. If the positivity route is pursued, it additionally needs a selected-schedule form-core exhaustion. If the selected divisor route is pursued, it needs the fixed-compact logarithmic-derivative boundary bound. `[COFINAL_FAMILY][CONDITIONAL]`

No Lean source was edited. No numerical run was performed. No route promotion or RH claim is made. `[ABSTRACT][PAPER]`

## Meta closeout

**What became smaller?** Matrix-to-zero provenance is closed on paper. The live gap is no longer "why does the matrix know the zeros?" It is "how does the same ground family acquire the target divisor or the target function?" `[COFINAL_FAMILY][PAPER]`

**What was killed?** Unconditional leakage-as-norm, selected-diagonal positivity as RH-equivalent without exhaustion, and the proposed nonreal-ground-zero contradiction. `[ABSTRACT][PAPER]`

**What must not be tried again?** Do not use finite positive diagnostics as a quantifier. Do not call an indefinite zero sum an energy off RH. Do not infer a nearby root from a small point value without a winding/Rouché discriminator. `[ABSTRACT][PAPER]`

**Current smallest named gap:** `P59_FIXED_COMPACT_LOG_DERIVATIVE_SOURCE_BOUND`. `[COFINAL_FAMILY][CONDITIONAL]`

**Next cheapest decisive test:** exact cancellation of the common P59 lattice factor, followed by the planted extra-root winding test. `[FINITE_CELL][PAPER]`

**Prediction fate:** probabilities were not edited; their fates are recorded in the machine header. `[ABSTRACT][PAPER]`

**Memory entry:** exact zero-sum provenance is not positivity; positivity appears only after the real-line condition or a genuine form-core theorem. `[ABSTRACT][PAPER]`
