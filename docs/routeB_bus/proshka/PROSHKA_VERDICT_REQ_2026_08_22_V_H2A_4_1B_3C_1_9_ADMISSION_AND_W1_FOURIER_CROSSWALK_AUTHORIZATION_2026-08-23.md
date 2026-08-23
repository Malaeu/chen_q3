# STATUS: CONDITIONAL

```yaml
PRIMARY: ADMIT_W1_FOURIER_CROSSWALK_REPAIR_BV_ABEL_ROOT_ENERGY_OUTCOME
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: ff47f300e93fc6d5c6869b40b420cbea717fb125
  REPORT_PARENT: b3acb86b0f9276c65959b4aa71b4c844283eb857
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT_2026-08-23.md
  REPORT_GIT_BLOB: 9455fbca6b6177e4f3bb4f1bbb5c3d9ae0a3f54c
  RECEIPT: PASS
  MODE: READ_ONLY_MATH_AND_SOURCE
  LEAN_EDIT: false
  ARISTOTLE_USED: false
  NUMERICS_USED: false

REPORT:
  REPORTED_OUTCOME: ABEL_LIMIT_SHIFTED_FORM_DOMAIN_ROUTE_FOUND
  SEMANTIC_ADMISSION: CONDITIONAL_WITH_MAJOR_OBJECT_AND_SCALE_REPAIRS
  REPAIRED_OUTCOME: SOURCE_FOURIER_CROSSWALK_FOUND_SELECTED_BV_ABEL_AND_ROOT_ENERGY_OPEN

ADMITTED:
  FIXED_R_ABEL_ABSOLUTE_CONVERGENCE: true
  PRODUCTION_TSUM_NOT_VALID_FOR_CONDITIONAL_REFLECTION: true
  MIDPOINT_AND_FULL_ENDPOINT_OBJECTS_AGREE_AE_NOT_POINTWISE: true
  ZERO_MASS_SHADOW_SIGN: PLUS_ONE_HALF_F_ZERO_SQRT_U
  SOURCE_SCALED_CENTER_SHADOW_O_LAMBDA_MINUS_2: true
  W1_SOURCE_FOURIER_CROSSWALK_ROUTE: true
  W1_REQUIRES_NO_PLANCHEREL_BACKPORT: true
  HILBERT_DENSITY_NOT_FORM_CORE: true

REPAIRS:
  FOURIER_COORDINATE:
    correct_object: ADDITIVE_LOG_WINDOW_ZERO_EXTENSION_ON_Icc_0_Lm
    rejected_object: UNSPECIFIED_MULTIPLICATIVE_WINDOW_FOURIER_TRANSFORM
  L2_TO_L1_CONSTANT:
    exact_constant: sqrt_L_m
    warning: sqrt_abs_I_m_is_ambiguous_and_wrong_if_read_as_Lebesgue_length
  LIMIT_IDENTIFICATION:
    required: L2_SUBSEQUENCE_AE_OR_CONVERGENCE_IN_MEASURE_UNIQUENESS
    forbidden: UNIFORM_CONVERGENCE_IMPLIES_L2_ON_WHOLE_LINE
  SELECTED_PACKET_BV:
    status: OPEN
    rejected_shortcut: INTERIOR_ANALYTICITY_PLUS_ENDPOINT_CONTINUITY_IMPLIES_BV
  ABEL_ENVELOPE:
    partial_sum_bound: C_lambda_times_Wk
    reflected_object_bound: C_lambda_pow_three_halves_times_Wk
    missing_factor_in_report: u_pow_minus_one_half
  SHIFTED_FORM_MEMBERSHIP:
    status: OPEN
    depends_on:
      - W1_SOURCE_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
      - W2_SELECTED_PACKET_VARIATION_OR_PIECEWISE_AC_CERTIFICATE
      - W3_DIRICHLET_JORDAN_AND_SINE_HARMONIC_IMPORTS
      - W4_FINITE_JUMP_FOURIER_DECAY_ROOT_ENERGY
  COFINAL_ROOT_ENERGY_RATE:
    status: OPEN_LATER_STAGE

CLOSED_BY_THIS_ADJUDICATION:
  - PINNED_MATHLIB_PLANCHEREL_BACKPORT_AS_A_REQUIREMENT
  - ORDINARY_FOURIER_VS_SYNTHESIZED_ISOMETRY_AS_AN_UNMAPPED_OBJECT

STILL_OPEN:
  - W1_LEAN_FORMALIZATION
  - W2_SELECTED_PACKET_VARIATION_CERTIFICATE
  - W3_DIRICHLET_JORDAN_AND_SINE_HARMONIC_IMPORTS
  - W4_FINITE_JUMP_DECAY_AND_FIXED_K_ROOT_ENERGY
  - W5_COFINAL_QUANTITATIVE_ROOT_ENERGY
  - GLOBAL_WEIL_TO_PROJECT_SHIFTED_FORM_CROSSWALK
  - POLARIZED_FULL_WEIL_DEFECT_BOUND
  - WINDOW_PROJECTION_DEFECT_RATE
  - SELECTED_RAYLEIGH_SCALAR_BOUND

NEXT:
  CODE: H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN
  MODE: LEAN_SOURCE_TRANSACTION
  LEAN_EDIT: true
  NUMERICS: false
  ARISTOTLE_AUTHORIZED: false
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_INTEGRAL_CROSSWALK_2026-08-23.md

CANDIDATE_REPRESENTATIONS:
  R1:
    CODE: DENSE_MODE_L2_TO_L1_FOURIER_CROSSWALK
    ROLE: PRIMARY
    KILL_POWER: 10
    COST: 4
  R2:
    CODE: DIRECT_MODE_COEFFICIENT_WEIGHTED_ARCH_ENERGY
    ROLE: RUNNER_UP_NOT_AUTHORIZED
    KILL_POWER: 8
    COST: 7

ARSENAL_MANDATE:
  ACCEPTED: true
  HASH_STATUS: OWNER_RATIFIED_C13_DECK_SUPERSEDES_2026_08_04_12_CARD_HASH
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

QUEUE_AUDIT:
  REQ_2026_08_21_P: ALREADY_ANSWERED_BY_EXISTING_VERDICT_QUEUE_MARK_STALE
  CURRENT_RESPONSE: REQ_2026_08_22_V

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Node | Verdict | Exact boundary | Tags |
|---|---|---|---|
| **W1 actual-Fourier crosswalk** | **ADMITTED AS A THEOREM-SIZED ROUTE** | The synthesized `sourceLogWindowFourierL2Isometry` can be identified almost everywhere with the ordinary Fourier integral of the **additive log-window zero extension** of any `H_m` vector. Lean proof is still pending. | `[ABSTRACT][CONDITIONAL]` |
| **W2 selected packet variation** | **OPEN** | The selected zero-extended Ferrers packet has closed-window continuity and interior regularity, but the current source does not yet prove the global derivative integrability or total-variation estimate consumed by Dirichlet–Jordan. | `[COFINAL_FAMILY][CONDITIONAL]` |
| **W3 Abel `L²` construction** | **OPEN WITH A CLEAR CLASSICAL ROUTE** | Needs a midpoint/piecewise-AC theorem and the universal sine-harmonic bound. The report's reflected envelope must include the factor `u⁻¹/²`. | `[COFINAL_FAMILY][CONDITIONAL]` |
| **W4 fixed-`k` root energy** | **OPEN WITH A CLEAR ROUTE** | W1 plus a finite-jump/piecewise-AC certificate gives `O(1/|t|)` Fourier decay and hence finite logarithmically weighted energy. No theorem has yet instantiated this chain. | `[COFINAL_FAMILY][CONDITIONAL]` |
| **W5 cofinal rate** | **OPEN, LATER CONSUMER** | Fixed-`k` membership does not imply the `o(m^{1/4}/L^{3/2})` polarized rate. | `[COFINAL_FAMILY][CONDITIONAL]` |

The report's main structural discovery survives: no new Plancherel library is needed. The exact additive-window unitary `logWindowL2Equiv`, completeness of `V_n_m_hilbertBasis`, and modewise equality of the synthesized isometry with the ordinary Fourier images are already in the source tree. The missing statement is a continuity/uniqueness theorem, not new harmonic analysis. `[ABSTRACT][CONDITIONAL]`

## 1. W1 is mathematically sound

Fix `i : PairIndex` and `x : H_m i`. Let

```text
x_log := (logWindowL2Equiv i).symm x
```

and let `g_x` be its representative multiplied by the indicator of the **additive** interval

\[
[0,L_m(i)].
\]

The literal finite mode sums converge to `x` in `H_m` because `V_n_m_hilbertBasis` is complete. Pulling them back through `logWindowL2Equiv.symm` gives convergence in `L²([0,L_m])`. Since the measure of this interval is exactly `L_m`,

\[
\|g_N-g_x\|_{L^1(\mathbb R)}
\le
\sqrt{L_m}\,\|g_N-g_x\|_{L^2([0,L_m])}
\longrightarrow0.
\]

The pinned Fourier integral satisfies

\[
\sup_t|\mathcal Fg_N(t)-\mathcal Fg_x(t)|
\le
\|g_N-g_x\|_1,
\]

so the ordinary Fourier integrals converge uniformly on the whole frequency line. On every finite mode sum, the existing mode theorem and linearity identify this Fourier integral with `sourceLogWindowFourierL2Isometry`. Continuity of the isometry gives convergence in whole-line `L²` to the synthesized image of `x`.

The last step must be written correctly: uniform convergence on an infinite-measure space does **not** imply `L²` convergence. Instead, use either:

1. an almost-everywhere convergent subsequence extracted from the `L²` convergence; uniform convergence identifies its pointwise limit; or
2. convergence-in-measure uniqueness, since the uniform convergence gives convergence in measure and `L²` convergence also gives convergence in measure.

The conclusion is the required almost-everywhere equality. No Plancherel theorem is used. `[ABSTRACT][CONDITIONAL]`

### C04 coordinate firewall

The Fourier integral above acts on the additive log-window function `g_x`. It is not a Fourier transform of the original multiplicative representative on `I_m`. The two are connected by `logWindowL2Equiv`, and that map must remain explicit in the theorem statement or its defining object. **[C04]**

## 2. The BV claim in Test 1 is not yet proved

The report says that interior analyticity and finite endpoint values make the packet piecewise absolutely continuous and of bounded variation. That implication is false in general.

For example, with `t = 1-x`,

\[
f(x)=t\sin(t^{-2}),\qquad 0\le x<1,\qquad f(1)=0,
\]

is real analytic on `(0,1)` and continuous at `1`, but its derivative has nonintegrable absolute value near `1`; the function has infinite variation. Thus interior analyticity plus continuous endpoint extension is only a surrogate for the variation functional actually consumed by Dirichlet–Jordan. **[C10]**

The project has stronger source material—geometric tail splice and polynomially weighted coefficient summability—so W2 is likely theorem-sized. But the next proof must derive one of the following exact objects:

```text
BoundedVariationOn the closed physical window;
Piecewise absolutely continuous with integrable derivative;
or an explicit total-variation bound from a global Legendre derivative majorant.
```

The phrase `(1-z²)^{m/2} * entire` is not accepted as the current source lock for the literal `mode4FerrersSeries` unless a named theorem establishes that representation for this exact object.

## 3. Abel envelope scale repair

Let

\[
S_N(u)=\sum_{n=1}^N\widehat f(n/u).
\]

The Stieltjes/sine-harmonic argument may give

\[
\sup_{N,\,u\in[\lambda^{-1},\lambda]}|S_N(u)|
\le C\lambda W_k.
\]

But the reflected object is

\[
E_r^\vee(f)(u)=u^{-1/2}\sum_{n\ge1}r^n\widehat f(n/u).
\]

Since `u⁻¹/² ≤ √λ` on the window, the corresponding uniform envelope is

\[
\boxed{
|E_r^\vee(f)(u)|\le C\lambda^{3/2}W_k,
}
\]

not `C λ W_k`. This does not damage fixed-`k` dominated convergence, but it matters for every later cofinal rate ledger.

The exact C13 shadow remains

\[
E^\vee(f)(u)=E(f)(u)-\frac12\widehat f(0)u^{-1/2}+\frac12f(0)u^{1/2}.
\]

For the zero-mass packet the surviving sign is plus. **[C13]**

## 4. Repaired report conclusion

The strongest supported conclusion is:

```text
The ordinary-Fourier / synthesized-isometry object mismatch has a clean,
elementary source-specific solution.

The selected Abel limit and its shifted-form membership are not yet proved.
They reduce to W2 + W3 + W4 after W1 lands.
```

Therefore `ABEL_LIMIT_SHIFTED_FORM_DOMAIN_ROUTE_FOUND` is accepted only as a route classification. It is not accepted as a theorem or as a completed membership supplier.

## FINAL PROPOSAL

Formalize W1 first. It is generic, closes an old C04 boundary for the entire source architecture, consumes no paper input, and opens no new analytic supplier.

The target file is:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
D0PstarSourceLogWindowFourierIntegralCrosswalk.lean
```

Required public surface:

```lean
noncomputable def sourceLogWindowZeroExtension
    (i : PairIndex) (x : H_m i) : ℝ → ℂ

theorem sourceLogWindowZeroExtension_integrable
    (i : PairIndex) (x : H_m i) :
    Integrable (sourceLogWindowZeroExtension i x)

theorem coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
    (i : PairIndex) (x : H_m i) :
    ((sourceLogWindowFourierL2Isometry i x :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        (fun t : ℝ => 𝓕 (sourceLogWindowZeroExtension i x) t)
```

The definition must use `(logWindowL2Equiv i).symm x` and the indicator of `Icc 0 (L_m i)`. Equivalent repository notation is allowed; the mathematical object may not change.

## STRONGEST ATTACK

The strongest objection is:

> Agreement on each displayed mode does not identify two transforms on the whole Hilbert space.

Correct. The missing ingredient is not modewise algebra but completeness plus continuity. The proof must explicitly use the complete `V_n_m_hilbertBasis` and the finite-measure `L²→L¹` estimate. A modewise `simp` without the dense-limit argument is rejected.

Mandatory private plant:

```text
ONE_MODE_AGREEMENT_WITHOUT_COMPLETE_BASIS_DOES_NOT_IDENTIFY_MAPS
```

Use two linear maps on `Fin 2 → ℂ` which agree on the first coordinate vector and differ on the second. The plant guards the exact false shortcut above. It must compile on the standard axiom profile.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN

MODE:
  LEAN SOURCE TRANSACTION
  NO NUMERICS
  NO ARISTOTLE

PREFLIGHT:
  Run ./ask.sh for:
    sourceLogWindowFourierL2Isometry actual Fourier
    logWindowZeroExtension
    L2 finite measure L1
    tendstoInMeasure Lp uniqueness
  Reuse a supplier if the exact theorem already exists.

LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceLogWindowFourierIntegralCrosswalk.lean

SOURCE RECORD:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_INTEGRAL_CROSSWALK_2026-08-23.md

PUBLIC SURFACE:
  sourceLogWindowZeroExtension
  sourceLogWindowZeroExtension_integrable
  coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension

CLOSES:
  SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK

OPENS:
  []

PROOF ROUTE:
  1. Define the additive zero extension from `(logWindowL2Equiv i).symm x`.
  2. Prove integrability using finite measure and the exact interval measure `L_m i`.
  3. Approximate `x` by finite sums in the complete `V_n_m_hilbertBasis`.
  4. On each finite sum, use the public mode theorem plus Fourier linearity.
  5. Pull the approximation to the additive interval and prove L1 convergence with constant `sqrt (L_m i)`.
  6. Use `VectorFourier.norm_fourierIntegral_le_integral_norm` for uniform Fourier convergence.
  7. Use isometry continuity for whole-line L2 convergence.
  8. Identify the two limits by an a.e.-subsequence or convergence-in-measure uniqueness.
  9. Prove the mandatory Fin-2 plant.
  10. Print axioms for all three public declarations and the plant.

FORBIDDEN:
  - Plancherel or an unpinned Lp Fourier API;
  - selected Ferrers, Abel, BV, Dirichlet-Jordan or root-energy imports;
  - redefining `sourceLogWindowFourierL2Isometry`;
  - a pointwise equality instead of an a.e. equality;
  - Fourier transform of the multiplicative `I_m` representative;
  - Hilbert density relabeled as form-core density;
  - adding `Integrable g` as a new public hypothesis;
  - claiming shifted-form membership or a Gamma rate;
  - sorry, admit, native_decide, opaque project axiom, theorem weakening.

VALIDATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean
    lake build Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierIntegralCrosswalk
  WORKDIR repository root:
    scripts/q3_check.sh Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS CODE:
  H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN

FAILURE CODES:
  LOG_WINDOW_L2_TO_L1_API_GAP
  FINITE_SPAN_FOURIER_LINEARITY_NORMAL_FORM_GAP
  L2_UNIFORM_LIMIT_AE_UNIQUENESS_GAP
  SOURCE_LOG_WINDOW_FOURIER_CROSSWALK_OBJECT_MISMATCH

NEXT AFTER SEMANTIC ADMISSION ONLY:
  W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE
```

## META CLOSEOUT

### What became smaller?

The prior C04 wall

```text
synthesized Fourier isometry versus ordinary Fourier integral
```

is now one exact Lean theorem with no new harmonic-analysis import.

### What was killed?

- the need for a Plancherel backport;
- the use of an unspecified multiplicative Fourier object;
- `interior analytic + endpoint continuous ⇒ BV`;
- the report's missing `u⁻¹/²` scale factor;
- uniform convergence on the whole line relabeled as `L²` convergence.

### What must not be tried again?

Do not use ordinary Fourier decay against the shifted-form consumer before W1 is kernel-green. Do not use qualitative interior regularity as a variation certificate.

### Current smallest named gap

```text
SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
```

### Next cheapest decisive test

Compile W1 with the additive coordinate and exact `sqrt(L_m)` finite-measure constant.

### Prediction fates

```text
P_ABEL_ROOT_1 = 0.99:
  CONFIRMED.

P_ABEL_ROOT_2 = 0.84:
  PARTIAL. The route is plausible, but qualitative BV was not proved.

P_ABEL_ROOT_3 = 0.62:
  CONFIRMED IN STRENGTHENED FORM. No Plancherel layer is needed.

P_ABEL_ROOT_4 = 0.78:
  PARTIAL. Fixed-k membership has a route, not a theorem; cofinal growth remains open.

RETROACTIVE_REPAIR:
  false.
```

### New predictions

```text
P_W1_1 = 0.91:
  the exact crosswalk theorem is mathematically valid with no new paper input.

P_W1_2 = 0.76:
  the first Lean transaction compiles without changing the public statement.

P_W1_3 = 0.99:
  no Plancherel or selected-Ferrers import is needed.

LIKELIEST_FAILURE:
  LP_RESTRICTED_REPRESENTATIVE_OR_TENDSTO_IN_MEASURE_NORMAL_FORM.
```

### Memory entry

```yaml
iteration: H2A_4_1B_3C_1_9
target: Abel-limit shifted-form route
status: PROGRESS
failed_strategy: infer BV from interior analyticity and endpoint continuity
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
invariant_learned: Fourier estimates must target the additive log-window object consumed by the synthesized isometry
forbidden_future_move: do not use BV or root-energy before the literal Fourier crosswalk is kernel-green
next_decisive_test: formalize W1 by L2-to-L1 finite-window continuity and a.e. limit uniqueness
```
