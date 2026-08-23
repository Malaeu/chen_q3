# STATUS: CONDITIONAL — ABEL-ОБЪЕКТ ВЫЖИЛ, НО L2/FORMS CLAIM ТРЕБУЕТ MIDPOINT, BV И FOURIER-ISOMETRY РЕМОНТА

```yaml
PRIMARY: ADMIT_ABEL_OBJECT_CLASSIFICATION_WITH_MIDPOINT_BV_AND_PLANCHEREL_REPAIRS
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 4e4e456d7b893f4b1a770644fb2f188ed1bdd34c
  REPORT_PARENT: be71af51da5399aa78a15f13095e1158a74f2aca
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_3C_1_8_SELECTED_FERRERS_ABEL_POISSON_REFLECTION_OBJECT_PREFLIGHT_2026-08-23.md
  REPORT_GIT_BLOB: 944f34baf9d06d9d0f184b28c867b98689a23eb5
  MODE: READ_ONLY_MATH_AND_SOURCE
  LEAN_EDIT: false
  ARISTOTLE_USED: false
  NUMERICS_USED: false
  RECEIPT: PASS

REPORT_OUTCOME:
  REPORTED: ABEL_REFLECTED_L2_FOUND_SHIFTED_FORM_NORM_OPEN
  ADMISSION: CONDITIONAL_WITH_MAJOR_OBJECT_REPAIRS
  REPAIRED: ABEL_REFLECTED_CANONICAL_L2_CANDIDATE_FOUND_PLANCHEREL_ROOT_ENERGY_OPEN

ADMITTED:
  FIXED_R_ABEL_ABSOLUTE_CONVERGENCE: true
  PRODUCTION_TSUM_NOT_VALID_FOR_CONDITIONAL_REFLECTION: true
  ZERO_MASS_REMOVES_FOURIER_CENTER_SHADOW: true
  SOURCE_SCALED_CENTER_DEFECT_O_LAMBDA_MINUS_2: true
  HILBERT_DENSITY_NOT_FORM_CORE: true
  ABEL_AND_SYMMETRIC_SUM_AGREE_AFTER_ORDINARY_SERIES_CONVERGENCE: true

CONDITIONAL_NOT_YET_SOURCE_LOCKED:
  SELECTED_PACKET_BOUNDED_VARIATION: true
  DIRICHLET_JORDAN_APPLIES_TO_EXACT_SELECTED_PACKET: true
  UNIFORM_PARTIAL_SUM_BOUND_ON_MOVING_SCALE_WINDOW: true
  ABEL_LIMIT_CONVERGES_IN_L2: true

REPAIRS:
  MIDPOINT_REPRESENTATIVE:
    production_selected_mode: FULL_Icc_ENDPOINT_VALUES
    poisson_required_object: MIDPOINT_ENDPOINT_REPRESENTATIVE
    pointwise_equality_to_production_ESTAR: false_at_finite_seams
    ae_and_L2_equality: expected_true

  SHADOW_SIGN:
    general_formula: E_reflect = E(f) - 0.5*fhat(0)*u^(-1/2) + 0.5*f(0)*u^(1/2)
    zero_mass_formula: E_reflect = E(f) + 0.5*f(0)*u^(1/2)

  FOURIER_OBJECT:
    domain_consumer: sourceLogWindowFourierL2Isometry
    consumer_definition: COMPLETE_BASIS_SYNTHESIZED_L2_ISOMETRY
    pointwise_fourier_integral_crosswalk_for_arbitrary_H_m: ABSENT_BY_SOURCE_DOCSTRING
    bv_decay_directly_controls_consumer: false_until_crosswalk

  PINNED_MATHLIB:
    version: v4.26.0
    commit: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
    ready_Lp_fourierTransform_linear_isometry_file: absent
    implication: LOCAL_PLANCHEREL_EXTENSION_OR_SOURCE_SPECIFIC_PROOF_REQUIRED

CLOSED:
  - REFLECTED_CONDITIONAL_SERIES_IS_NOT_PRODUCTION_ESTAR
  - ABEL_REGULARIZATION_GIVES_UNCONDITIONAL_OBJECT_FOR_R_LT_1
  - CENTER_SHADOW_HAS_EXISTING_SOURCE_SCALED_C0_RATE
  - HILBERT_DENSITY_CANNOT_CLOSE_SHIFTED_FORM_DOMAIN

STILL_OPEN:
  - SELECTED_FERRERS_PACKET_BV_OR_PIECEWISE_AC_SOURCE_LOCK
  - MIDPOINT_TO_FULL_ENDPOINT_ESTAR_AE_CROSSWALK
  - UNIFORM_SINE_HARMONIC_PARTIAL_SUM_BOUND
  - ABEL_L2_LIMIT_SOURCE_LOCK
  - SOURCE_LOG_WINDOW_FOURIER_ISOMETRY_TO_ACTUAL_FOURIER_CROSSWALK
  - ABEL_LIMIT_SHIFTED_FORM_ROOT_ENERGY
  - GLOBAL_WEIL_TO_PROJECT_SHIFTED_FORM_CROSSWALK
  - POLARIZED_FULL_WEIL_DEFECT_BOUND
  - WINDOW_PROJECTION_DEFECT_RATE
  - SELECTED_RAYLEIGH_SCALAR_BOUND

DIRECT_LEAN_WRITE:
  AUTHORIZED: false
  REASON: the literal consumer Fourier object and the selected BV/midpoint object are not yet locked

NEXT:
  CODE: H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT
  MODE: READ_ONLY_MATH_AND_SOURCE
  LEAN_EDIT: false
  NUMERICS: false
  ARISTOTLE_AUTHORIZED: false
  OUTPUT: docs/routeB_bus/H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT_2026-08-23.md

CANDIDATE_REPRESENTATIONS:
  R1:
    CODE: LOCAL_PLANCHEREL_EXTENSION_PLUS_FINITE_JUMP_DECAY
    ROLE: PRIMARY
    KILL_POWER: 10
    COST: 6
    TARGET: construct/identify the actual whole-line L2 Fourier transform with sourceLogWindowFourierL2Isometry, then prove a 1/(1+|t|) bound from finite jumps and piecewise AC regularity
  R2:
    CODE: DIRECT_MODE_COEFFICIENT_WEIGHTED_ARCH_ENERGY
    ROLE: RUNNER_UP
    KILL_POWER: 9
    COST: 7
    TARGET: avoid a pointwise Fourier transform and bound the synthesized weighted image directly from selected mode coefficients and the exact archimedean matrix/form ledger

RETURN_EXACTLY_ONE:
  - ABEL_LIMIT_SHIFTED_FORM_DOMAIN_ROUTE_FOUND
  - ABEL_LIMIT_L2_FOUND_POINTWISE_FOURIER_CROSSWALK_OPEN
  - SELECTED_PACKET_BV_SOURCE_LOCK_OPEN
  - PINNED_MATHLIB_PLANCHEREL_BACKPORT_REQUIRED
  - ROOT_ENERGY_ROUTE_RATE_FATAL

SUCCESS: H2A_4_1B_3C_1_9_ABEL_LIMIT_ROOT_ENERGY_ROUTE_CLASSIFIED
FAILURE: H2A_4_1B_3C_1_9_MIDPOINT_BV_OR_FOURIER_OBJECT_UNMAPPED

ARSENAL_MANDATE:
  ACCEPTED: true
  HASH_STATUS: OWNER_RATIFIED_C13_DECK_SUPERSEDES_2026_08_04_12_CARD_HASH
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 4

PREDICTION_FATES:
  P_ABEL_OBJECT_1_0_97: CONFIRMED
  P_ABEL_OBJECT_2_0_84: PARTIALLY_CONFIRMED_NOT_SOURCE_LOCKED
  P_ABEL_OBJECT_3_0_58: UNRESOLVED_WITH_EARLIER_C04_BLOCKER
  P_ABEL_OBJECT_4_0_95: CONFIRMED
  RETROACTIVE_REPAIR: false

NEW_PREDICTIONS:
  P_ABEL_ROOT_1:
    probability: 0.99
    claim: production full-endpoint EStar and midpoint EStar differ at seams but agree almost everywhere
  P_ABEL_ROOT_2:
    probability: 0.84
    claim: selected Ferrers tail-splice data yields a quantitative finite-variation or piecewise-AC certificate
  P_ABEL_ROOT_3:
    probability: 0.62
    claim: the pinned project can build a local Plancherel crosswalk without upgrading Mathlib
  P_ABEL_ROOT_4:
    probability: 0.78
    claim: after the crosswalk, finite-jump decay proves shifted-form membership with a polynomial bound
  LIKELIEST_FAILURE: PINNED_MATHLIB_L2_FOURIER_OR_WEIGHTED_CROSSWALK_GAP

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Что действительно найдено

Для каждого фиксированного `0 < r < 1` ряд

\[
E^{\vee}_{r,k}(u)
=
 u^{-1/2}\sum_{n\ge1}r^n\widehat f_k(n/u)
\]

абсолютно сходится: `f_k` интегрируема, поэтому `|fhat_k|` ограничена её `L1`-нормой, а `r^n` даёт геометрическую мажоранту. Это честный новый объект, в отличие от применения production `tsum` к условно сходящемуся отражённому ряду.

`[ABSTRACT][PAPER]`

Plant с alternating harmonic series проходит: одинаковые слагаемые под conditional/Abel summation и под Mathlib `tsum` задают разные функционалы. Поэтому production `E_star` нельзя переиспользовать для отражённой Fourier-серии без отдельного theorem.

`[ABSTRACT][PAPER]` **[C04][C10]**

### 2. Midpoint-representative в report не source-locked

Concrete selected Ferrers mode определяется как `Icc.indicator` непрерывной closed-window функции. Следовательно, в точках `±lambda_k` он хранит полное внутреннее endpoint value, а не половинное Dirichlet–Jordan value.

Пусть `f_k^mid` отличается от production `f_k` только тем, что в `±lambda_k` принимает половину внутреннего значения. Тогда:

- Fourier integrals `f_k` и `f_k^mid` совпадают;
- их `L1`/`L2` классы совпадают;
- production `E_star f_k` и midpoint `E_star f_k^mid` различаются в конечных seam points `u=lambda_k/n`;
- они совпадают почти всюду на multiplicative window.

Поэтому report-фраза «pointwise at every window point and identical to production `E_star`» отклонена. `L2`-route выживает после `ae`-ремонта.

`[COFINAL_FAMILY][PAPER]` **[C04]**

Обязательный plant следующего preflight:

```text
FULL_ENDPOINT_VS_MIDPOINT_ESTAR_SEAM_PLANT

Take a compactly supported function with nonzero right endpoint value.
At u=lambda and n=1:
  full-endpoint EStar contribution = sqrt(lambda)*f(lambda),
  midpoint contribution = (1/2)*sqrt(lambda)*f(lambda).
They are unequal pointwise but equal as L2 classes after changing finitely many points.
```

### 3. Exact sign of the explicit shadow

With the fixed Fourier convention,

\[
E(f)(u)
=
E^{\vee}(f)(u)
+rac12\widehat f(0)u^{-1/2}
-rac12 f(0)u^{1/2}.
\]

Thus

\[
\boxed{
E^{\vee}(f)(u)
=
E(f)(u)
-rac12\widehat f(0)u^{-1/2}
+rac12f(0)u^{1/2}
}.
\]

For the zero-mass selected packet, `fhat_k(0)=0`, hence

\[
\boxed{
E^{\vee}(f_k)(u)
=
E(f_k)(u)+\frac12 f_k(0)\sqrt u.
}
\]

Any next source must carry this plus sign literally. An unspecified symbol `centerDefect` is no longer accepted. This is the exact C13 shadow.

`[ABSTRACT][PAPER]` **[C13]**

### 4. BV and the L2 limit are plausible, not yet source-locked

The report invokes bounded variation of the selected packet. The production structure stores closed-window continuity, interior `C2`, a tail splice, and enough polynomially weighted coefficient summability can plausibly be re-derived from that splice. This gives a clear route to a closed-window derivative/variation bound. But no named source theorem currently states `BoundedVariationOn` or the exact piecewise-AC substitute consumed by Dirichlet–Jordan.

The required uniform partial-sum estimate should be proved explicitly, not cited as a vague “Jordan uniform bound”. For an even BV packet one may integrate by parts in Stieltjes form and use the universal bound for

\[
\sum_{n=1}^{N}\frac{\sin(2\pi n y)}n.
\]

The intended bound is of the form

\[
\sup_{N,\,u\in[\lambda^{-1},\lambda]}
\left|\sum_{n=1}^{N}\widehat f(n/u)\right|
\le
C\lambda\bigl(|f(\lambda^-)|+\operatorname{Var}_{[0,\lambda]}f\bigr).
\]

This would give an `r`-uniform window envelope and dominated convergence of Abel means in `L2`. Until the variation theorem and this bound are source-locked, `L2 LIMIT FOUND` is classified as conditional, not proved.

`[COFINAL_FAMILY][CONDITIONAL]`

### 5. The earlier blocker is C04, before the numerical root energy

The shifted form domain is defined using

```text
sourceLogWindowFourierL2Isometry i x
```

which is synthesized from the complete `V_n_m` Hilbert basis and the Fourier images of those literal modes. Its source docstring explicitly makes no claim that an arbitrary `H_m` vector is represented by a separately defined pointwise Fourier integral.

Therefore a BV decay estimate for the ordinary Fourier transform of the log-window representative does not yet estimate the literal domain consumer. The missing identity is:

```text
SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
```

or a source-specific substitute for the selected Abel limit.

The pinned project uses Mathlib `v4.26.0` at commit `2df2f015...`; its Fourier directory has no ready `Mathlib.Analysis.Fourier.LpSpace`/`MeasureTheory.Lp.fourierTransformₗᵢ` layer. Hence the current source cannot close this by importing the later API. It must either build a local Plancherel extension or remain on the direct coefficient/form side.

`[ABSTRACT][PAPER]` **[C04][C10]**

Mandatory plant:

```text
L2_WITHOUT_SHIFTED_ROOT_ENERGY_PLANT

Choose ghat on |t|>=e with
  |ghat(t)|^2 = 1 / (|t| * (log |t|)^2).
Then ghat is L2, but
  integral log(2+|t|) * |ghat(t)|^2 dt = infinity.
By an L2 Fourier equivalence this gives an L2 vector outside the shifted form domain.
```

This kills every use of plain `L2` convergence as a form-domain certificate.

### 6. Why U1 is probably theorem-sized, not a new roof

Once the literal Fourier object is locked, the selected reflected limit is expected to be a finite-seam, piecewise-smooth function in log coordinates:

- production `E_star` is a finite dilation sum on each fixed window;
- seams occur at `u=lambda_k/n`, finitely many for fixed `k`;
- the explicit shadow `0.5*f_k(0)*sqrt u` is smooth;
- the zero extension of a finite-variation function has Fourier decay `O(1/|t|)`;
- the shifted arch weight grows only logarithmically.

Thus the root-energy tail is controlled by

\[
\int_{|t|\ge1}
\frac{1+\log(2+|t|)}{t^2}\,dt<\infty.
\]

This is not yet a theorem, but it compresses U1 to one exact finite-jump Fourier bound plus the C04 crosswalk.

`[ABSTRACT][CONDITIONAL]`

## FINAL PROPOSAL

Run one read-only preflight:

```text
H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT
```

### Mandatory test 1 — exact selected midpoint/BV object

Derive from the literal Ferrers tail splice:

```text
selected packet on [-lambda,lambda]:
  finite variation / piecewise AC;
  explicit variation bound V_k;
  midpoint representative f_k^mid;
  Fourier(f_k^mid) = Fourier(f_k);
  midpoint EStar = production EStar almost everywhere;
  exact finite seam correction pointwise.
```

### Mandatory test 2 — exact Abel L2 bound

Do not invoke a generic phrase. Derive the uniform partial-sum estimate through the sine harmonic kernel and return an explicit envelope in `lambda_k`, `V_k`, and the endpoint value.

### Mandatory test 3 — literal Fourier-isometry crosswalk

Audit the pinned Mathlib and exact project maps. Return either:

```text
A. a local Plancherel extension and a basis-uniqueness proof identifying it with sourceLogWindowFourierL2Isometry;

B. a source-specific theorem identifying the synthesized image of the selected Abel limit with its ordinary Fourier integral;

C. a proof that neither is available without backporting a new L2 Fourier layer.
```

### Mandatory test 4 — root-energy inequality

Produce the exact bound

\[
\left\|
\sqrt{\mu_{\rm arch}+c_{\rm shift}}\,
\mathcal F_{L^2}(x_k)
\right\|_2^2
\le B_k<\infty
\]

for the literal reflected-limit `H_m` object `x_k`. Separate mere finiteness from cofinal growth.

### Mandatory test 5 — downstream sufficiency

State whether the radical/window route requires only `B_k<infinity` for each fixed `k`, or a uniform/cofinal rate. Do not prove a stronger bound than the consumer needs.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The report estimates the ordinary Fourier transform of a BV representative, while the project form domain is defined through a separately synthesized Hilbert-space isometry. Why should those be the same object?

At the current pin there is no theorem saying they are the same for arbitrary `H_m` vectors. Therefore the form-domain claim cannot be admitted from BV decay alone. This kill instantiates **C04** and **C10**.

A second objection is exact and local:

> The concrete selected Ferrers zero extension stores full endpoint values, not midpoint half-values.

This does not kill the `L2` representation because the difference is finite and null almost everywhere. It does kill every pointwise identity that silently calls the production object a midpoint representative.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT

MODE:
  READ_ONLY_MATH_AND_SOURCE
  NO LEAN EDIT
  NO NUMERICS
  NO ARISTOTLE

BASE_HEAD:
  use live `git rev-parse HEAD`; paste the full output verbatim

READ:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersRegularEvenProlateSolution.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalNormalizedZeroExtension.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0ModeZeroFourFerrersProductionProlatePair.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierL2Isometry.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchFormDomain.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchClosedForm.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
  q3.lean.aristotle/lake-manifest.json
  pinned Mathlib Fourier directory at rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

MANDATORY PLANTS:
  FULL_ENDPOINT_VS_MIDPOINT_ESTAR_SEAM_PLANT
  L2_WITHOUT_SHIFTED_ROOT_ENERGY_PLANT
  CONDITIONAL_SERIES_VS_TSUM_PLANT

FORBIDDEN:
  calling the production selected packet a midpoint representative;
  pointwise equality where only ae equality holds;
  using Hilbert density as a form core;
  using lower semicontinuity as equality;
  estimating an ordinary Fourier integral without identifying the literal source isometry;
  importing an API absent from the pinned Mathlib;
  differentiating a C0 rate;
  calling form-domain membership a Gamma source rate;
  Lean edits, numerics, Aristotle, route promotion, RH claim.

RETURN EXACTLY ONE:
  ABEL_LIMIT_SHIFTED_FORM_DOMAIN_ROUTE_FOUND
  ABEL_LIMIT_L2_FOUND_POINTWISE_FOURIER_CROSSWALK_OPEN
  SELECTED_PACKET_BV_SOURCE_LOCK_OPEN
  PINNED_MATHLIB_PLANCHEREL_BACKPORT_REQUIRED
  ROOT_ENERGY_ROUTE_RATE_FATAL
```

## META CLOSEOUT

**Что стало меньше?**

```text
conditional reflected Fourier series
→ canonical Abel family at r<1
→ one midpoint/ae repair
→ one literal Fourier-isometry crosswalk
→ one finite-jump root-energy bound.
```

**Что убито?**

- production `tsum` as the reflected conditional series;
- pointwise equality between full-endpoint and midpoint `E_star` at seams;
- ambiguous sign of the center shadow;
- plain `L2` membership as a shifted-form-domain proof;
- BV decay applied to the wrong Fourier object;
- Hilbert density as form-core density.

**Что нельзя пробовать снова?**

Do not call two summation methods or two Fourier isometries the same because they have the same displayed summands or agree on a few modes. Name the exact functional and prove the crosswalk.

**Текущий smallest named gap:**

```text
SELECTED_ABEL_LIMIT_ACTUAL_FOURIER_CROSSWALK_AND_ROOT_ENERGY
```

**Следующий самый дешёвый решающий тест:**

```text
Can the pinned project identify sourceLogWindowFourierL2Isometry with the actual Fourier transform on the selected finite-jump object and obtain a 1/(1+|t|) bound?
```

**Fate старых predictions:** recorded in the machine header; no retroactive repair.

**Memory entry:**

```yaml
iteration: H2A_4_1B_3C_1_8
target: selected Abel-reflected object in shifted form domain
status: PROGRESS
failed_strategy: BV-decay applied directly to an un-crosswalked Fourier isometry
cognitive_operator_used: UNIT_AUDIT
new_gap_name: SELECTED_ABEL_LIMIT_ACTUAL_FOURIER_CROSSWALK_AND_ROOT_ENERGY
invariant_learned: midpoint/full endpoint equality is ae only; form domain uses the synthesized source isometry
forbidden_future_move: L2 or ordinary Fourier decay relabeled as source root-energy
next_decisive_test: local Plancherel/source-specific Fourier crosswalk plus finite-jump tail bound
```
