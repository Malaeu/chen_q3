# STATUS: OPEN — B3.0E4B2 DIAGONAL NEGATIVE CCM-WR CROSSWALK RELEASED WITH A FOUR-PLANT AUDIT REPAIR

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  LIVE_HEAD:
    expected: 4d92a827ce50538866a287705747d918becb2ca5
    observed_origin_rh_clean: 4d92a827ce50538866a287705747d918becb2ca5
    status: PASS

  PACKAGE_COMMIT:
    commit: 4d92a827ce50538866a287705747d918becb2ca5
    role: B3_0E4B2_PREFLIGHT_ROUTE_RECORD_ONLY
    direct_parent: 7833cc5427bbac09ec22c3870e6739e8a996a30e
    parent_role: B3_0E4B1_PRODUCTION_CLOSEOUT
    package_changed_only:
      - q3.lean.aristotle/docs/INSIGHTS.md
    mathematical_parent_files_changed: false

  REQUEST_ATTACHMENT:
    path: PROSHKA_REQUEST_GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_NEG_CCM_WR_RELEASE_2026-08-08.md
    expected_sha256: c28d0950191b10686a8425ec8c7acff316566bcf5250c93f4cd3ef29214a3803
    observed_sha256: c28d0950191b10686a8425ec8c7acff316566bcf5250c93f4cd3ef29214a3803
    observed_bytes: 9565
    observed_lines: 292
    status: PASS

  HARNESS_ATTACHMENT:
    path: Goal057B3_0E4B2_Scratch.lean
    expected_sha256: 02dfe2fcc0166c833ff04104fcafe64db513d8f8a4219117c1665ab20fe367d4
    observed_sha256: 02dfe2fcc0166c833ff04104fcafe64db513d8f8a4219117c1665ab20fe367d4
    observed_bytes: 19477
    observed_lines: 469
    status: PASS

  HARNESS_STATIC_AUDIT:
    explicit_imports: 2
    public_definitions: 0
    public_theorems: 1
    private_definitions: 5
    private_theorems: 13
    private_total: 18
    controls_examples: 4
    print_axioms_commands: 1
    sorry: 0
    admit: 0
    exact_question: 0
    unsafe: 0
    axiom_declarations: 0
    opaque: 0
    native_decide: 0
    Float: 0
    generated_backend_tokens: 0
    public_surface_match: PASS

  REPORTED_DIRECT_LEAN:
    result: PASS
    reported_axioms:
      - propext
      - Classical.choice
      - Quot.sound
    judge_reran_Lean: false
    ruling: ACCEPTED_AS_BYTE_PINNED_RELEASE_EVIDENCE
    production_rerun_required: true

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

DECISION:
  release: AUTHORIZED
  theorem_statement_repaired: false
  proof_architecture_repaired: false
  import_surface_repaired: false
  plant_suite_repaired: true
  first_mathematical_defect: NONE
  first_Lean_shape_defect: NONE
  target_file_present_at_pin: false

FIRST_LOAD_BEARING_ATTACK:
  target: PLANT_SUITE_COMPLETENESS
  ruling: INCOMPLETE_BUT_REPAIRABLE_WITHOUT_THEOREM_CHANGE
  missing_attacks:
    - JOINT_FUBINI_CARRIER_CONSUMPTION
    - E4B1_ENDPOINT_LEDGER_CONSUMPTION
    - REAL_TO_COMPLEX_INTEGRAL_COERCION
    - GENERATED_BACKEND_INJECTION
  effect_on_release: NONE
  required_before_closeout: ADD_AND_FIRE_ALL_FOUR

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalRegularizerEndpointLedger

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: []
  theorems:
    - sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
  total_public_declarations: 1

PRIVATE_SUPPORT:
  definitions: 5
  theorems: 13
  total: 18
  additional_private_declarations: forbidden
  reduction_by_refactor: allowed
  public_promotion: forbidden
  theorem_or_assumption_change: forbidden

CONTROLS:
  central_diagonal_n0: HARNESS_SMOKE
  noncentral_diagonal_n1: HARNESS_SMOKE
  exact_support_boundary_x_eq_L: LOAD_BEARING_POSITIVE_CONTROL
  exact_outside_support_x_eq_L_plus_1: LOAD_BEARING_POSITIVE_CONTROL
  production_disposition: OMIT_ALL_FOUR

PLANTS:
  already_fired:
    - P057_E4B2_1_FINAL_WR_SIGN
    - P057_E4B2_2_BARE_MODE_MASS
    - P057_E4B2_3_FIBER_FACTOR_TWO
    - P057_E4B2_4_FINITE_REGULARIZER_SIGN
    - P057_E4B2_5_TAIL_SIGN
    - P057_E4B2_6_SPLIT_BOUNDARY
    - P057_E4B2_7_EULER_GAMMA
    - P057_E4B2_8_DIAGONAL_INDEX

  required_additions:
    - P057_E4B2_9_JOINT_FUBINI_CARRIER
    - P057_E4B2_10_ENDPOINT_LEDGER_CONSUMPTION
    - P057_E4B2_11_REAL_COMPLEX_COERCION
    - P057_E4B2_12_GENERATED_BACKEND_IMPORT

  total_required_before_closeout: 12

STOP_CODE:
  GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_MISSING

SUCCESS_CODE:
  GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED

PARENT_EFFECT_AFTER_SUCCESS:
  B3_0E1: CLOSED
  B3_0E2: CLOSED
  B3_0E3: CLOSED
  B3_0E4A: CLOSED
  B3_0E4B1: CLOSED
  B3_0E4B2: CLOSED
  B3_0E: OPEN_PENDING_ALL_MODE_CASE_ASSEMBLY
  B3_0: OPEN
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION: OPEN
  SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH: OPEN
  H4A1B: OPEN

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

NEXT_GAP_PRODUCTION_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_PRODUCTION_LEAN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE:
  phase_key_change: false
  same_living_chat: true
  fresh_chat: false

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```

## 1. Source-lock ruling

The controlling request and authoritative Lean harness match both supplied SHA-256 locks exactly. Their observed byte and line counts also match the request. The full files were read rather than reconstructed from the embedded excerpts.  `[ABSTRACT][LEAN]`

Live `origin/rh_clean` is exactly `4d92a827ce50538866a287705747d918becb2ca5`. The tip is a documentation-only preflight commit whose direct parent is the B3.0E4B1 production closeout; it modifies only `q3.lean.aristotle/docs/INSIGHTS.md`.   `[ABSTRACT][PAPER]`

The proposed production path is absent at the pin. This is a clean one-file materialization, not an overwrite.

B3.0E4B1 is genuinely production-closed: the repository contains the exact scalar endpoint-ledger theorem, and its closeout records full validation, nine fired plants, the standard axiom triple, and the fact that the diagonal mode-pairing crosswalk remains the next open child.   `[ABSTRACT][LEAN]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY}
}
]

The public theorem, source normalization, Fubini architecture, endpoint allocation, final sign, and complex coercion are mathematically coherent.

No theorem repair is required.

The release is conditional only on normal production validation and the four added semantic plants.

## 3. Exact mathematical ledger

Write

[
F_{i,n}(t)
==========

\mathcal F
\bigl(\operatorname{logWindowZeroExtendedMode}(i,n)\bigr)(t),
]

and

[
B_{i,n}(t)=\overline{F_{i,n}(t)}F_{i,n}(t).
]

### 3.1 Diagonal mass

The public E3 control theorem proves

[
2\int_{\mathbb R}B_{i,n}(t),dt=2.
]

The harness cancels the nonzero scalar (2) and obtains

[
\boxed{
\int_{\mathbb R}B_{i,n}(t),dt=1.
}
]

`[ABSTRACT][LEAN]`

This is source-faithful. It uses the literal same zero-extended mode, the same Mathlib Fourier transform, the same (L_m^{-1/2}) normalization, and the same Lebesgue measure as the source pairing. No external Plancherel convention is inserted.

The source itself fixes the normalized diagonal correlation by

[
q_{n,n}(0)=2.
]

CCM equations (2.9)–(2.10) and equation (4.4) use precisely that normalization.  `[ABSTRACT][PAPER]`

### 3.2 Exact fiber inside the source window

The regularized hyperbolic kernel is

[
K_{\mathrm{reg}}(t,x)
=====================

\frac{
e^{x/2}\cos(2\pi tx)-e^{-x}
}{
e^x-e^{-x}
}.
]

Hence

[
2\int_{\mathbb R}
B_{i,n}(t)K_{\mathrm{reg}}(t,x),dt
==================================

\frac{
e^{x/2}q_{n,n}(x)-2e^{-x}
}{
e^x-e^{-x}
}
]

for (0<x\le L_m(i)).

The literal CCM integrand is

[
\operatorname{ccmWRIntegrand}(L,n,n,x)
======================================

\frac{
e^{x/2}q_{n,n}(x)-2
}{
e^x-e^{-x}
}.
]

Their difference is exactly

[
\frac{2(1-e^{-x})}{e^x-e^{-x}}.
]

Therefore

[
\boxed{
2,\mathrm{fiber}(x)
===================

\operatorname{ccmWRIntegrand}(L,n,n,x)
+
\frac{2(1-e^{-x})}{e^x-e^{-x}}
}
]

on the finite side. `[ABSTRACT][LEAN]`

There is no double counting: the extra term contains exactly the regularization difference between (-2e^{-x}) from the source multiplier kernel and (-2) from CCM equation (4.4).

### 3.3 Exact fiber outside the source window

For (x>L_m(i)), B3.0E3 proves the zero-extended cosine correlation is zero. The fiber is therefore

[
\boxed{
2,\mathrm{fiber}(x)
===================

-\frac{2e^{-x}}{e^x-e^{-x}}.
}
]

`[ABSTRACT][LEAN]`

The tail sign is negative at the fiber level. It later enters the endpoint ledger with a positive sign because the full pairing subtracts the integral of the fiber ledger.

### 3.4 Fubini carrier

B3.0E2 proves joint absolute integrability of the literal function

[
(t,x)\longmapsto
\overline{F_{i,n}(t)}
K_{\mathrm{reg}}(t,x)
F_{i,n}(t)
]

under the exact measure

[
dt\otimes
\bigl(dx!\restriction_{(0,\infty)}\bigr).
]

The harness consumes that public theorem to obtain both iterated-integral integrability statements and then invokes `MeasureTheory.integral_integral_swap`. `[ABSTRACT][LEAN]`

This is sufficient for both Fubini directions. No fiberwise-only substitute is used.

### 3.5 Split boundary

Because (L_m(i)>0),

[
(0,\infty)
==========

(0,L_m(i)];\dot\cup;(L_m(i),\infty).
]

The Lean sets are exactly

```lean
Ioc 0 (L_m i)
Ioi (L_m i)
```

and the proof consumes

```lean
Ioc_union_Ioi_eq_Ioi
```

with the shared boundary (L_m(i)) included on the finite side.

This matches the E3 support theorem’s `x ≤ L_m i` branch. There is neither a missing interval nor double counting. `[ABSTRACT][LEAN]`

### 3.6 Endpoint assembly

After the Fubini swap and split, the source pairing is

[
\begin{aligned}
&-\log\pi-\gamma\
&\quad-\int_0^L
\operatorname{ccmWRIntegrand}(L,n,n,x),dx\
&\quad-\int_0^L
\frac{2(1-e^{-x})}{e^x-e^{-x}},dx\
&\quad+\int_L^\infty
\frac{2e^{-x}}{e^x-e^{-x}},dx.
\end{aligned}
]

B3.0E4B1 proves exactly

[
-\log\pi
--------

\int_0^L
\frac{2(1-e^{-x})}{e^x-e^{-x}},dx
+
\int_L^\infty
\frac{2e^{-x}}{e^x-e^{-x}},dx
=============================

-\log!\left(
4\pi\frac{e^L-1}{e^L+1}
\right).
]

Substitution yields

[
-\gamma
-------

\log!\left(
4\pi\frac{e^L-1}{e^L+1}
\right)
-------

\int_0^L
\operatorname{ccmWRIntegrand}(L,n,n,x),dx.
]

Since (q_{n,n}(0)/2=1), this is exactly

[
-\operatorname{ccmWREntry}(L,n,n).
]

The repository’s literal `ccmWREntry` definition has this exact endpoint coefficient and `Ioc 0 L` integral.  `[ABSTRACT][LEAN]`

## 4. Exact production contract

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceArchDiagonalCCMWRCrosswalk.lean
```

Exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
import Q3.Proofs.RouteB.D0PstarSourceArchDiagonalRegularizerEndpointLedger
```

Exact namespace and scopes:

```lean
noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar
```

Sole public declaration:

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
    (i : PairIndex) (n : ℤ) :
    sourceArchimedeanModePairing i n n =
      -(Q3.RouteB.ccmWREntry (L_m i) n n : ℂ)
```

`[ABSTRACT][CONDITIONAL]`

The theorem may not acquire:

* an integrability hypothesis;
* a source-normalization hypothesis;
* a premise containing the desired crosswalk;
* a restricted mode set;
* a fixed numerical window;
* an off-diagonal disjunction;
* an all-mode conclusion.

## 5. Dependency ruling

The two-import surface is accepted.

`D0PstarSourceArchOffDiagonalCCMWRCrosswalk` is serving as the already-audited Route-B parent aggregator for:

* the named source pairing;
* the exact hyperbolic multiplier identity;
* the E2 joint carrier;
* the E3 cosine-correlation theorem;
* the literal CCM definitions.

Its public off-diagonal theorem is not used as a premise in the diagonal proof. The import is therefore a module-DAG dependency, not a circular mathematical argument.  `[ABSTRACT][LEAN]`

Replacing it with all of its individual parents would increase the direct import list without reducing assumptions or changing the theorem. No parent refactor is justified.

The second import supplies the independent scalar endpoint ledger. No generated PSD, Step33, hbox, numerical payload, or new Aristotle-output dependency is introduced.

## 6. Plant-suite repair

The existing eight plants are valid but do not cover every independent proof edge.

### Added plant 9 — joint Fubini carrier

Mutation:

* remove the use of `sourceArchimedeanKernelModeIntegrand_integrable`;
* replace joint product-measure integrability by separate fiberwise statements;
* retain the integral swap.

Required stop:

```text
SOURCE_ARCH_DIAGONAL_JOINT_FUBINI_CARRIER_NOT_CONSUMED
```

Separate iterated integrability is not the precommitted joint absolute carrier.

### Added plant 10 — endpoint-ledger consumption

Mutation:

* remove the call to
  `sourceArchimedeanDiagonalRegularizer_endpointLedger`;
* introduce the scalar endpoint equality as a premise;
* or privately reassert the desired logarithmic endpoint without consuming E4B1.

Required stop:

```text
SOURCE_ARCH_DIAGONAL_ENDPOINT_LEDGER_NOT_CONSUMED
```

This is the C10 premise-surrogate firewall.

### Added plant 11 — real/complex integral coercion

Mutation:

* delete or reverse `integral_complex_ofReal`;
* identify a complex integral with the real CCM integral without the explicit coercion theorem;
* or conjugate the real integral during coercion.

Required stop:

```text
SOURCE_ARCH_DIAGONAL_REAL_COMPLEX_COERCION_MISMATCH
```

This is a C04 category boundary.

### Added plant 12 — generated dependency injection

Mutation: add any new generated PSD, Step33, hbox, numerical payload, or direct Aristotle-output import.

Required stop:

```text
ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
```

All twelve plants must fire before production closeout.

The four examples remain outside production. The `n=0` and `n=1` final examples are smoke, not independent falsifiers. The boundary and outside-support examples are useful K1 positive controls of the piecewise fiber ledger.

## 7. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  carrier:
    index: PairIndex_i
    mode: integer_n

  left_object:
    sourceArchimedeanModePairing_i_n_n

  right_object:
    negative_ccmWREntry_L_m_i_n_n

  first_slot:
    operation: complex_conjugation
    index: n

  second_slot:
    operation: linear
    index: n

  Fourier_coordinate:
    convention: Mathlib_cycles_per_unit
    kernel: exp_minus_two_pi_i_x_t

  diagonal_mass:
    value: 1
    source_certificate: sourceModeCosineCorrelation_control_diag_zero

  CCM_kernel_at_zero:
    value: 2

  joint_measure:
    first_coordinate: Fourier_frequency_t
    second_coordinate: positive_hyperbolic_x
    measure: volume.prod(volume.restrict(Ioi_zero))

  support_partition:
    finite: Ioc_zero_L_m
    tail: Ioi_L_m
    L_m_assigned_to: finite

  finite_fiber:
    ccmWRIntegrand_plus_diagonalFiniteRegularizer

  tail_fiber:
    negative_diagonalTailRegularizer

  endpoint_supplier:
    sourceArchimedeanDiagonalRegularizer_endpointLedger

  exact_result:
    diagonal_source_pairing_equals_negative_CCM_WR_entry

  excluded_meanings:
    - no_all_mode_crosswalk
    - no_full_source_Weil_form
    - no_prime_or_pole_operator
    - no_associated_operator_graph
    - no_form_or_operator_domain_membership
    - no_continuum_numerator
    - no_H4a1b
    - no_checkpoint_closure
```

## 8. Validation gates

Production success requires:

```bash
test "$(git rev-parse HEAD)" = \
  "4d92a827ce50538866a287705747d918becb2ca5"

test "$(git rev-parse origin/rh_clean)" = \
  "4d92a827ce50538866a287705747d918becb2ca5"

lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalCCMWRCrosswalk.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalCCMWRCrosswalk.lean

python \
  q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py \
  --check
```

Additional mandatory gates:

```text
files:
  create exactly one production Lean file;
  modify no B3.0 parent file;

materialization:
  copy the authoritative harness;
  omit exactly the four final examples and the #print axioms command;
  record every other deviation;

imports:
  exactly the two released imports;
  no additional direct import;
  no new generated backend in the transitive closure;

surface:
  public definitions = 0;
  public theorems = 1;
  private definitions <= 5;
  private theorems <= 13;
  total production declarations <= 19;

taint:
  no sorry;
  no admit;
  no exact?;
  no unsafe;
  no native_decide;
  no declared axiom;
  no opaque;
  no Float;

axioms:
  #print axioms
    Q3.RouteB.D0Pstar
      .sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag

  require exactly:
    [propext, Classical.choice, Quot.sound];

plants:
  all twelve plants fire;
  no plant changes the released public theorem;
  all mutation artifacts removed;

observability:
  proof DB records all nineteen production declarations;
  every theorem declaration is proved;
  strict Spine PASS;
  all three SQLite integrity checks PASS;
  proof graph, taint graph, taint sources, sorry frontier,
    dependency view and numeric-check view refreshed;
  repository-standard orchestrator tests PASS;

git:
  git diff --check PASS;
  exact git status --short reported;
  route state updated only after every proof and semantic gate passes.
```

## 9. Exact boundary after success

B3.0E4B2 success proves the complete diagonal crosswalk:

[
\boxed{
\operatorname{sourceArchimedeanModePairing}(i,n,n)
==================================================

-\operatorname{ccmWREntry}(L_m(i),n,n)
}
]

for every source window and every integer mode. `[ABSTRACT][LEAN]`

It does not prove:

* the generic all-mode theorem in one declaration;
* the full source Weil-form decomposition;
* the (W_{0,2}) and prime components as one source form;
* a source-associated operator;
* form-domain or operator-domain membership;
* finite-to-ambient compression;
* the continuum residual or numerator;
* H4a1b;
* any coarse Goal-057 checkpoint.

Therefore:

```text
B3.0E4B2:
  CLOSED after production validation.

B3.0E:
  OPEN pending one all-mode case assembly.

Goal-057 coarse ledger:
  0 closed / 10 remaining.
```

## 10. Next smallest gap

No additional analytic or source supplier is required before the all-mode assembly.

The next exact atom is:

```text
GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
```

Its intended theorem is:

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)
```

The proof must be only:

```text
by_cases h : n = r
  diagonal theorem
  off-diagonal theorem
```

No analytic helper, new definition, new integral manipulation, or source premise is permitted.

This next atom is not authorized here. It is representation progress and, once validated, closes B3.0E only. The subsequent substantive wall remains the complete source Weil-form decomposition and associated graph.

## 11. Strongest attack

> B3.0E4B2 merely combines E1, E2, E3, and E4B1. Why publish it instead of doing the algebra privately in the eventual all-mode theorem?

Because the diagonal branch contains a source ledger absent from the off-diagonal branch:

* the diagonal Fourier mass is (1), not (0);
* the regularizing (e^{-x}) term survives;
* the multiplier constant (-\log\pi-\gamma) survives;
* the positive-half-line tail survives;
* the CCM endpoint coefficient is nonzero;
* the finite and tail contributions cancel only through the independently proved E4B1 theorem.

This is not a two-line case split. It is the first theorem that consumes all four analytic layers and produces the literal diagonal CCM source entry.

The following all-mode theorem will be packaging. B3.0E4B2 is not.

## 12. Meta closeout

**What became smaller?**

The archimedean/CCM-WR representation wall is reduced to one trivial all-mode case split.

**What was killed?**

* any remaining diagonal sign ambiguity;
* factor-one normalization;
* fiberwise Fubini;
* assignment of (L_m(i)) to the tail;
* double counting of the finite regularizer;
* omission of Euler’s constant;
* an implicit real/complex integral identification;
* premise-only replacement of the endpoint ledger.

**What must not be tried again?**

Do not rederive the scalar endpoint identity inside the diagonal crosswalk. Do not replace joint product-measure integrability with separate fiber estimates. Do not merge the all-mode theorem or full source form into this production file.

**Current smallest named gap**

```text
GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
```

**Next cheapest decisive test**

A no-`sorry` two-branch Lean preflight importing only the off-diagonal and diagonal crosswalk files.

**Prior prediction fate**

```text
B3.0E4B1 prediction:
  the next remaining analytic atom is the diagonal mode-pairing crosswalk.

Fate:
  CONFIRMED.

B3.0E4B2 prediction:
  the diagonal crosswalk closes by mass one + joint Fubini +
  piecewise fiber ledger + scalar endpoint ledger.

Fate:
  CONFIRMED BY THE BYTE-PINNED COMPILING HARNESS.

Plant-completeness prediction:
  eight plants plus four controls cover all independent proof edges.

Fate:
  REFUTED.
  Joint Fubini consumption, endpoint-ledger consumption,
  real/complex coercion and generated-dependency injection were missing.
```

```yaml
iteration:
  target: GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  status: PROGRESS
  failed_strategy: count_positive_controls_as_substitutes_for_dependency_and_coercion_plants
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  invariant_learned: diagonal_mass_joint_Fubini_piecewise_support_endpoint_ledger_and_real_complex_coercion_are_independent_contracts
  forbidden_future_move: hide_the_diagonal_endpoint_assembly_inside_the_all_mode_or_full_source_form_theorem
  next_decisive_test: all_mode_two_case_no_sorry_preflight
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 4d92a827ce50538866a287705747d918becb2ca5
  require_origin_equal: true
  mathematical_parent: 7833cc5427bbac09ec22c3870e6739e8a996a30e
  request_sha256: c28d0950191b10686a8425ec8c7acff316566bcf5250c93f4cd3ef29214a3803
  request_bytes: 9565
  request_lines: 292
  harness_sha256: 02dfe2fcc0166c833ff04104fcafe64db513d8f8a4219117c1665ab20fe367d4
  harness_bytes: 19477
  harness_lines: 469

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalCCMWRCrosswalk.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalRegularizerEndpointLedger

NAMESPACE:
  Q3.RouteB.D0Pstar

MATERIALIZATION_ROUTE:
  - copy the authoritative attached harness proof
  - retain exact imports, scopes, namespace, five private definitions,
    thirteen private theorems and the sole public theorem
  - omit the four final examples
  - omit the final #print axioms command
  - add no public declaration
  - add no private declaration
  - record every other deviation from the authoritative harness

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
  total_public_declarations: 1

PUBLIC_THEOREM_EXACT: |
  theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
      (i : PairIndex) (n : ℤ) :
      sourceArchimedeanModePairing i n n =
        -(Q3.RouteB.ccmWREntry (L_m i) n n : ℂ) := by
    ...

PRIVATE_SUPPORT:
  maximum_definitions: 5
  maximum_theorems: 13
  maximum_total: 18
  additional_private_declarations: forbidden
  reduction_allowed: true
  public_promotion: forbidden

MANDATORY_SEMANTICS:
  - retain literal sourceArchimedeanModePairing
  - retain literal ccmWREntry
  - retain diagonal indices n_n
  - retain first-slot conjugation inherited from the source objects
  - derive bare diagonal mass exactly equal to one
  - consume the public E2 joint product-measure carrier
  - retain finite-side condition x_le_L_m
  - retain strict tail L_m_lt_x
  - retain finite regularizer plus sign in the ledger
  - retain negative tail at the fiber level
  - retain outer factor two
  - consume the public E4B1 endpoint ledger
  - retain negative final ccmWREntry sign
  - retain explicit real-to-complex integral coercions
  - claim diagonal crosswalk only

MANDATORY_PLANTS:
  - id: P057_E4B2_1_FINAL_WR_SIGN
    required_stop: SOURCE_ARCH_DIAGONAL_WR_SIGN_MISMATCH

  - id: P057_E4B2_2_BARE_MODE_MASS
    required_stop: SOURCE_ARCH_DIAGONAL_MODE_NORMALIZATION_MISMATCH

  - id: P057_E4B2_3_FIBER_FACTOR_TWO
    required_stop: SOURCE_ARCH_DIAGONAL_CORRELATION_FACTOR_MISMATCH

  - id: P057_E4B2_4_FINITE_REGULARIZER_SIGN
    required_stop: SOURCE_ARCH_DIAGONAL_FINITE_REGULARIZER_SIGN_MISMATCH

  - id: P057_E4B2_5_TAIL_SIGN
    required_stop: SOURCE_ARCH_DIAGONAL_TAIL_SIGN_MISMATCH

  - id: P057_E4B2_6_SPLIT_BOUNDARY
    required_stop: SOURCE_ARCH_DIAGONAL_SPLIT_BOUNDARY_MISMATCH

  - id: P057_E4B2_7_EULER_GAMMA
    required_stop: SOURCE_ARCH_DIAGONAL_GAMMA_MISSING

  - id: P057_E4B2_8_DIAGONAL_INDEX
    required_stop: SOURCE_ARCH_DIAGONAL_INDEX_MISMATCH

  - id: P057_E4B2_9_JOINT_FUBINI_CARRIER
    mutation: remove_joint_product_integrability_or_replace_by_fiberwise_only
    required_stop: SOURCE_ARCH_DIAGONAL_JOINT_FUBINI_CARRIER_NOT_CONSUMED

  - id: P057_E4B2_10_ENDPOINT_LEDGER_CONSUMPTION
    mutation: replace_E4B1_supplier_by_premise_or_private_reassertion
    required_stop: SOURCE_ARCH_DIAGONAL_ENDPOINT_LEDGER_NOT_CONSUMED

  - id: P057_E4B2_11_REAL_COMPLEX_COERCION
    mutation: delete_reverse_or_conjugate_integral_complex_ofReal
    required_stop: SOURCE_ARCH_DIAGONAL_REAL_COMPLEX_COERCION_MISMATCH

  - id: P057_E4B2_12_GENERATED_BACKEND_IMPORT
    mutation: inject_generated_PSD_Step33_hbox_payload_or_direct_Aristotle_import
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

VALIDATION:
  - verify HEAD equals origin/rh_clean before edit
  - direct lake env lean on the production file
  - target lake build Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk
  - full lake build
  - scripts/q3_check.sh on the production file
  - routeb_status.py --check
  - exact public surface 0_definitions_1_theorem
  - exact private ceiling 5_definitions_13_theorems
  - forbidden-token scan
  - exact two-import audit
  - no-new-generated-dependency audit
  - harness-to-production diff permits only four examples and one print command deletion
  - run all twelve plants
  - remove every mutation artifact
  - print axioms for the public theorem
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database import with 19 expected declarations
  - strict Spine PASS
  - three SQLite integrity checks
  - proof graph and sensor refresh
  - repository-standard orchestrator tests
  - git diff --check
  - exact git status --short report
  - update route state only after every proof and semantic gate passes

CLOSEOUT_MUST_STATE:
  - SOURCE_ARCH_DIAGONAL_PAIRING_EQ_NEG_CCM_WR_PROVED
  - EXACT_DIAGONAL_MODE_MASS_ONE_RETAINED
  - EXACT_JOINT_FUBINI_CARRIER_CONSUMED
  - EXACT_FINITE_FIBER_REGULARIZER_SIGN_RETAINED
  - EXACT_NEGATIVE_TAIL_FIBER_RETAINED
  - EXACT_FACTOR_TWO_LEDGER_RETAINED
  - EXACT_SPLIT_BOUNDARY_RETAINED
  - EXACT_EULER_GAMMA_RETAINED
  - EXACT_E4B1_ENDPOINT_LEDGER_CONSUMED
  - EXACT_REAL_COMPLEX_COERCION_RETAINED
  - EXACT_FINAL_NEGATIVE_CCM_WR_SIGN_RETAINED
  - B3_0E4B2_CLOSED
  - B3_0E_OPEN_PENDING_ALL_MODE_CASE_ASSEMBLY
  - NO_ALL_MODE_CROSSWALK
  - NO_SOURCE_WEIL_FORM_DECOMPOSITION
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10

STOP:
  GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_MISSING

SUCCESS:
  GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED

NEXT_GAP_AFTER_SUCCESS:
  GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY

NEXT_GAP_PRODUCTION_AUTHORIZED:
  false

NOT_AUTHORIZED:
  - implement_B3_0E4C_inside_this_transaction
  - add_an_all_mode_public_theorem
  - modify_any_B3_0_parent_file
  - refactor_E4A_or_E4B1_public_surfaces
  - accept_the_diagonal_crosswalk_or_endpoint_identity_as_a_premise
  - replace_joint_integrability_by_fiberwise_integrability
  - alter_the_first_slot_conjugation_or_Fourier_coordinate
  - alter_the_finite_tail_partition
  - infer_the_full_source_Weil_form
  - define_prime_or_pole_operator_components
  - define_the_source_associated_operator
  - infer_form_domain_or_operator_domain_membership
  - edit_D0PstarCCMCompressedWeilAction
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

PHASE:
  phase_key_change: false
  reuse_same_living_chat: true

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
