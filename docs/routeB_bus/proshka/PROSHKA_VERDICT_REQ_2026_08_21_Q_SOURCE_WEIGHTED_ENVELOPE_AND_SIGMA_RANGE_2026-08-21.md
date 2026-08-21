# STATUS: CONDITIONAL — INPUT A REUSES THE EXISTING L73.2 SOURCE-RATE WALL; EDGE CONSTANT BLOW-UP IS ALLOWED; DO NOT SWITCH YET
```yaml
PRIMARY: KEEP_G5_PRIMARY_AND_REUSE_L73_SOURCE_RATE
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-21-Q
  STATUS_AT_REVIEW: OPEN
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_GIT_BLOB: 6777ef2402176aff3363e30048c831160c1ee3bd
  QUEUE_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 7737bfff6b889878a7479b66da7244102c764cc9
  PRIOR_G5_VERDICT_COMMIT: 2794daa06834ea46ad128dc5ac7c02790c11a4ad
  PRIOR_G5_VERDICT_BLOB: b3c9f087c815732ed172e36d5349a42118cd4b7f
  MOMENT_RATIO_EQUIVALENCE_COMMIT: 2fa5b68918d69daed9bcb398c368779f5f4cc35e
  MOMENT_RATIO_EQUIVALENCE_BLOB: 2307e8c386bbd1ad566fe432c72096d62f51527b
  DIAGONAL_EXTENSION_COMMIT: ceac4f729d9f6a2b475c767a9259b34f005f32fc
  DIAGONAL_EXTENSION_BLOB: ecd8e3f3c93ccb99cf1386ce1a47f9a1ef9cd166
  FIXED_WINDOW_BOUND_COMMIT: fab2ac73f4a71c31e6847ebc5e32106b90cbf032
  FIXED_WINDOW_BOUND_BLOB: 0124a5fa00cc313836fd757152ee05cf525eb7e4

ARSENAL_MANDATE:
  accepted: true
  deck_sha256_expected: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  deck_sha256_verified: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  cards_applied:
    - C01_SIGN_MASS_LOCALIZATION
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

QUESTION_1:
  SUPPORT_AND_L2_NORMALIZATION_ALONE_IMPLY_INPUT_A: KILLED
  PROLATE_LABEL_ALONE_IMPLIES_INPUT_A: REJECTED
  SEPARATE_SUM_OVER_N_ESTIMATE_REQUIRED: true
  NEW_INDEPENDENT_ANALYTIC_HYPOTHESIS_REQUIRED: false_if_existing_L73_floors_are_proved
  EXISTING_SUPPLIER_CHAIN:
    - F72_1_CENTER_ANCHORED_FIXED_MODE_RATE
    - F72_3_FINITE_FOURIER_EIGENVALUE_DEFECT_RATE
    - L73_2_SELECTED_FERRERS_LEMMA72_RATE
    - L73_3_ESTAR_WINDOW_MAIN_ERROR
    - L73_4_EXPLICIT_LIMIT_BEYOND_SOURCE_WINDOW_TAIL
    - L73_6_EXPLICIT_LIMIT_CLOSED_SUBSTRIP_OUTER_TAIL
  CLASSIFICATION: EXISTING_GAP_REUSE_NOT_NEW_SHELF_GAP

QUESTION_2:
  REQUIRED_QUANTIFIER: FOR_EACH_FIXED_SIGMA_LT_HALF_EXISTS_C_SIGMA_UNIFORM_IN_K
  C_SIGMA_UNIFORM_AS_SIGMA_TENDS_TO_HALF: NOT_REQUIRED
  C_SIGMA_BLOWUP_AS_SIGMA_TENDS_TO_HALF: ALLOWED
  FAILURE_ONLY_AT_SIGMA_EQ_HALF: IRRELEVANT_TO_CURRENT_CONSUMER
  FAILURE_AT_ONE_FIXED_SIGMA_LT_HALF: KILLS_PRIMARY_G5_MOMENT_REPRESENTATION
  KILLS_WHOLE_ROUTE_B: false
  FIXED_NARROWER_RANGE_SIGMA_LE_SIGMA_STAR_LT_HALF: INSUFFICIENT_FOR_CURRENT_FULL_STRIP_CONSUMER
  ALL_FIXED_SIGMA_LT_HALF_WITH_DIVERGING_C_SIGMA: SUFFICIENT

QUESTION_3:
  SWITCH_TO_DIRECT_STRIP_BOUND_NOW: NO
  PRIMARY_ROUTE_STATUS: RETAIN
  FALLBACK_STATUS: HELD_AS_MANDATORY_REPRESENTATION
  REASON: FALLBACK_SHARES_THE_SOURCE_LOCALIZATION_WALL_OR_USES_THE_STRONGER_L73_7_CONVERGENCE_THEOREM
  SWITCH_TRIGGER:
    - PROVED_DIVERGENCE_OF_NORMALIZED_ABSOLUTE_SOURCE_MOMENT_AT_ONE_FIXED_INTERIOR_SIGMA
    - SOURCE_NORMALIZATION_OR_ZERO_EXTENSION_OBSTRUCTION_BLOCKS_THE_ABSOLUTE_L1_ROUTE_WHILE_TRANSFORM_CANCELLATION_SURVIVES

DERIVED_MAIN_ERROR_RATE:
  assumptions:
    - delta_k_le_C_lambda_k_pow_minus_two
    - u_eq_exp_t
    - t_in_minus_log_lambda_to_log_lambda
  pointwise_main_error: C_times_lambda_inverse_times_exp_minus_t_over_two
  weighted_integral_upper_bound: >-
    C * (lambda^(-1/2+sigma)/(1/2+sigma)
         + lambda^(-1)/(1/2-sigma))
  tends_to_zero_for_each_fixed_sigma_lt_half: true
  uniform_in_sigma_up_to_half: false

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_NORMALIZED_ESTAR_WEIGHTED_ENVELOPE
  statement: >-
    For every fixed real sigma with 0 <= sigma < 1/2, the exact source-scaled
    selected Ferrers prolate combination has a uniformly bounded normalized
    E_star weighted L1 moment on the moving window, with one constant depending
    on sigma but not on the cofinal index.
  exact_route: >-
    L73.2 source rate + active-term counting + explicit target E_star weighted
    envelope + literal zero-extension target-tail repair + exact source zero-mode
    preservation.
  not_a_new_input: true

CANDIDATE_REPRESENTATIONS:
  R1_LEMMA72_TO_WEIGHTED_ESTAR_ENVELOPE:
    rank: PRIMARY
    kill_power: 10/10
    cost: 4/10_after_L73_2
    preserves:
      - exact_selected_Ferrers_source
      - exact_sourceScale
      - exact_moving_window
      - one_precommitted_cofinal_schedule
      - absolute_weighted_L1_functional
  R2_DIRECT_CLOSED_SUBSTRIP_GWIN_BOUND:
    rank: FALLBACK_HELD
    kill_power: 10/10
    cost: 6/10
    preserves:
      - exact_selected_family
      - exact_anchor
      - full_open_centered_critical_strip
    warning: may_use_cancellation_and_therefore_does_not_prove_R1

DISCRIMINATOR:
  name: ABSOLUTE_SOURCE_ENVELOPE_VS_TRANSFORM_CANCELLATION
  R1_PASS: strict_upper_envelope_for_every_fixed_sigma_lt_half
  R1_KILL: proved_lower_envelope_tending_to_infinity_for_some_fixed_sigma_lt_half
  R2_TRIGGER: R1_killed_but_direct_compact_strip_bound_remains_plausible
  zero_consistent_numerics: INCONCLUSIVE

PRIOR_REGISTERED_PREDICTIONS_FATE:
  P_P_G5_1:
    prior: unprojected_source_has_uniform_weighted_L1_ratio_for_every_fixed_sigma_lt_half
    fate: SUPPORTED_CONDITIONALLY_NOT_CONFIRMED
  P_P_G5_2:
    prior: one_diagonal_absorbs_fixed_window_Galerkin_error_without_uniform_rate
    fate: ORDER_THEORY_CONFIRMED_ANALYTIC_EVENTUALITY_PENDING
  P_P_G5_3:
    prior: first_failure_if_any_near_sigma_to_half_not_central_normalization
    fate: SUPPORTED_BY_THRESHOLD_CALCULATION_STILL_PENDING

NEW_REGISTERED_PREDICTIONS:
  P_Q_1:
    statement: L73.2_plus_target_tail_floors_close_Input_A_for_every_fixed_sigma_lt_half
    probability: 0.84
    fate: PENDING
  P_Q_2:
    statement: any_proved_constants_C_sigma_will_deteriorate_as_sigma_tends_to_half_without_harming_the_consumer
    probability: 0.93
    fate: PENDING
  P_Q_3:
    statement: direct_strip_fallback_will_not_remove_the_selected_Ferrers_source_rate_wall
    probability: 0.81
    fate: PENDING

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. The three new kernel nodes are correctly scoped

The ratio equivalence proves that the G5 contract is exactly a uniform bound on
`centeredMomentLeakage`; it supplies no estimate. The diagonal node proves pure
order theory; it does not prove that any analytic requirement is satisfiable.
The fixed-window node proves

\[
 e^{\sigma |t|}\le e^{\sigma L/2}
 \qquad (|t|\le L/2),
\]

with a constant depending on the fixed window. Since \(L=\log m\), that constant
is \(m^{\sigma/2}\) and cannot be transported as a uniform cofinal constant.
The request states this boundary correctly. `[COFINAL_FAMILY][LEAN]`

The current G5 consumer has the quantifier order

\[
\forall\sigma\in[0,1/2),\quad
\exists C_\sigma,\quad
\forall k,\quad R_k(\sigma)\le C_\sigma.
\]

It does **not** ask for one constant uniform in both \(k\) and \(\sigma\).
`[COFINAL_FAMILY][LEAN]`

### 2. Answer to question 1: support makes the sum finite; it does not bound it

The fact that the selected prolate mode is zero-extended outside
\([ -\lambda_k,\lambda_k]\) implies only that, for \(u>0\), the starred sum has at
most about \(\lambda_k/u\) active terms. It supplies no location or cancellation
information for their absolute values. Support and \(L^2\) normalization alone
therefore do not imply the required normalized weighted \(L^1\) envelope.
`[COFINAL_FAMILY][PAPER]` **[C01]**

The needed estimate is nevertheless not a new independent hypothesis. It is a
consequence of the already catalogued selected-Ferrers Lemma-7.2 source rate,
combined with an exact sum-over-\(n\) count and the explicit target tail. Let

\[
\delta_k=
 \sup_{|x|\le\lambda_k}
 |a_kh_k(x)-h(x)|,
\qquad
\delta_k\le C\lambda_k^{-2},
\]

where \(a_k\) is the source-derived normalization and \(h\) is the repaired
explicit CCM limiting packet. For \(u=e^t\in[\lambda_k^{-1},\lambda_k]\), the
active part of the starred-sum difference satisfies

\[
\left|
 u^{1/2}\sum_{nu\le\lambda_k}
   (a_kh_k(nu)-h(nu))
\right|
\le
 \delta_k\lambda_k u^{-1/2}
\le
 C\lambda_k^{-1}e^{-t/2}.
\]

This is the separate **sum-over-\(n\)** theorem the request asks about. It follows
from the source rate and active-term counting; it does not follow from the word
“prolate” or from compact support by itself. `[COFINAL_FAMILY][PAPER]`

For fixed \(0\le\sigma<1/2\), integration on the centered log-window gives

\[
\begin{aligned}
I^{\rm main}_{k,\sigma}
&\le
 C\lambda_k^{-1}
 \int_{-\log\lambda_k}^{\log\lambda_k}
      e^{-t/2}e^{\sigma|t|}\,dt\\
&\le C\left(
 \frac{\lambda_k^{-1/2+\sigma}}{1/2+\sigma}
 +\frac{\lambda_k^{-1}}{1/2-\sigma}
 \right)
 \longrightarrow0.
\end{aligned}
\]

The remaining pieces are exactly existing L73 floors, not new shelf inputs:

```text
L73.4:
  the explicit target terms with n*u > lambda_k caused by literal zero extension;

L73.6:
  the explicit target outer-tail / weighted integrability on strict substrips;

G6N1 pre-anchor zero-mode crosswalk:
  the exact source zero mode and its preservation by the Galerkin projection.
```

After the source-scaled zero mode converges to the already fixed nonzero target
anchor, it has an eventual lower bound. The finitely many earlier indices are
absorbed into \(C_\sigma\). This does not reintroduce
`SelectedCentralFloor` as an independent G5 premise. `[COFINAL_FAMILY][CONDITIONAL]`

Therefore the correct classification is:

```text
INPUT_A:
  not implied by support alone;
  not a new independent analytic axiom;
  a downstream corollary of the existing L73.2/L73.4/L73.6 source chain.
```

### 3. Answer to question 2: edge deterioration is allowed

The estimate naturally exposes the threshold \(1/2\). For every **fixed**
\(\sigma<1/2\), the exponent \(-1/2+\sigma\) is negative and the main source
error tends to zero. As \(\sigma\uparrow1/2\), the decay becomes arbitrarily slow
and the displayed constants deteriorate. That is compatible with the exact
consumer. `[COFINAL_FAMILY][PAPER]`

Three different statements must not be conflated:

```text
A. C_sigma grows as sigma -> 1/2:
   ALLOWED.

B. The estimate fails only at sigma = 1/2:
   IRRELEVANT; the boundary is not consumed.

C. The estimate fails for one fixed sigma_0 < 1/2:
   PRIMARY G5 MOMENT REPRESENTATION KILLED.
```

A proof only on one fixed narrower range

\[
0\le\sigma\le\sigma_*<1/2
\]

is not sufficient for the existing full-strip Montel consumer. Every compact in
the open centered critical strip lies inside **some** strict substrip, but those
substrips can approach \(1/2\) arbitrarily closely. One fixed
\(\sigma_*<1/2\) leaves part of the strip uncovered. `[ABSTRACT][LEAN]`

What is sufficient is precisely the current quantifier: one common cofinal path,
and for each fixed \(\sigma<1/2\) its own constant \(C_\sigma\). The diagonal and
rational-to-real nodes were built for this exact purpose. `[COFINAL_FAMILY][LEAN]`

If case C occurs, it kills `CenteredTrialCriticalMomentRatio`, not Route B as a
whole. The weaker direct strip-local representation remains available.

### 4. Answer to question 3: do not switch before testing the shared source wall

An immediate switch to
`SelectedLocallyBoundedOnCenteredCriticalStrip` is not justified. The fallback
is weaker at the consumer, but it does not magically remove the source
asymptotic:

1. proving it through the current moment route uses L73.2 plus the absolute
   `E_star` envelope;
2. proving it through direct CCM Lemma-7.3 convergence uses L73.2 plus the
   stronger closed-substrip convergence assembly;
3. a crude fixed-window transform bound still suffers from the moving window
   and post-anchor normalization.

Thus both representations share the selected-Ferrers source-rate wall. Opening
a second proof front now would duplicate the hard input rather than avoid it.
`[COFINAL_FAMILY][PAPER]` **[C09]**

Keep the primary representation because, once L73.2 exists, the calculation
above makes Input A a bounded corollary. Keep the direct strip route registered
as the fallback because absolute values may destroy a cancellation that is
still available at transform level. `[COFINAL_FAMILY][CONDITIONAL]`

The switch trigger is exact:

```text
prove that the normalized absolute source moment diverges
for some fixed sigma_0 < 1/2,
while a direct compact-strip transform bound remains viable.
```

Finite probes or a constant that merely grows as \(\sigma\uparrow1/2\) do not
trigger the switch.

## FINAL PROPOSAL

### Route decision

Keep the registered primary chain:

```text
selected Ferrers source object
→ source-derived center normalization
→ fixed-mode Satz-9 rate
→ finite-Fourier defect rate
→ selected Lemma-7.2 combination rate
→ E_star active-sum estimate
→ explicit target tail repair
→ normalized weighted source envelope
→ fixed-window Galerkin convergence
→ one precommitted diagonal
→ CenteredTrialCriticalMomentRatio.
```

Do not add `INPUT_A` as a fresh analytic assumption or a second independent
shelf gap. Attach it as a consumer of the existing L73.2/L73.4/L73.6 chain.

### Registered next test

After the selected Lemma-7.2 rate is available, prove the explicit weighted
error inequality above. The registered expectation is that it closes Input A
for every fixed \(\sigma<1/2\), with constants deteriorating toward the boundary.

### Likeliest failure point

The strongest remaining risk is not the factor
\(e^{\sigma L/2}\) by itself. It is an object/normalization mismatch in the
source-rate port or an unclosed absolute target-tail theorem. If either blocks
absolute \(L^1\) while the transform-level cancellation survives, activate the
direct strip fallback.

## STRONGEST ATTACK

The strongest reviewer objection is:

> CCM Lemma 7.3 controls a Mellin transform difference. Why should that imply an
> absolute weighted \(L^1\) bound on the source? Absolute values destroy
> cancellation.

Correct. Locally uniform transform convergence alone does **not** imply Input A.
The primary route survives only because it attacks the difference before the
Mellin integral, through the uniform whole-window Lemma-7.2 source estimate and
an explicit count of active summands. The explicit target itself must then have
a separately proved absolute weighted envelope, including the literal
zero-extension tail. `[COFINAL_FAMILY][PAPER]` **[C10]**

Those source theorems are not yet all kernel-green. Therefore this verdict does
not mark Input A proved. It only establishes that the requested envelope is a
correct downstream theorem shape and that it reuses the existing analytic wall.

If the target absolute envelope cannot be proved, the weakest repaired theorem
is direct closed-substrip boundedness of the selected transform. That repair
must preserve the exact family, anchor, domain and one cofinal schedule; it may
not be obtained by cutting the window or fitting a scalar.

## CODEX DIRECTIVE

```text
DO NOT OPEN A PARALLEL G5-SPECIFIC ASYMPTOTIC FRONT.
DO NOT SWITCH TO THE DIRECT-STRIP FALLBACK YET.

Current exact source task remains the existing F72/L73 chain.
The next load-bearing source obligation is:

  SATZ9_FIXED_MODE_SOURCE_DATA_INHABITANT

followed by:

  F72_1A_CENTER_NORMALIZED_SATZ9_FIXED_MODE_RATE
  F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE
  L73_2_SELECTED_FERRERS_LEMMA72_RATE

Only after L73.2 is kernel-green, open one bridge transaction:

  G5_WEIGHTED_ESTAR_ENVELOPE_FROM_LEMMA72

Required theorem content:
  for every fixed 0 <= sigma < 1/2, derive the exact weighted-window
  E_star source error bound from L73.2, active-term counting, the explicit
  target tail, and the exact source zero mode; then conclude the uniform
  normalized source ratio.

Forbidden:
  - carrying exp(sigma*L/2) as a cofinal constant;
  - requiring one C uniform in sigma;
  - adding Input A as an axiom or structure field;
  - replacing the selected Ferrers source;
  - using locally uniform transform convergence as absolute L1 control;
  - cutting the moving window;
  - fitting the source normalization;
  - opening a second cofinal schedule;
  - claiming G5, S1, Route B or RH closure.

Validation when the bridge becomes executable:
  lake env lean <exact touched file>
  lake build <exact module>
  scripts/q3_check.sh <exact touched file>

Expected public axiom profile:
  [propext, Classical.choice, Quot.sound]

Success code:
  G5_SELECTED_FERRERS_WEIGHTED_ESTAR_ENVELOPE_LEAN

Failure codes:
  G5_LEMMA72_SOURCE_RATE_NOT_AVAILABLE
  G5_ESTAR_ACTIVE_SUM_COUNTING_GAP
  G5_EXPLICIT_TARGET_WEIGHTED_ENVELOPE_GAP
  G5_SOURCE_ZERO_MODE_NORMALIZATION_GAP
  G5_FIXED_INTERIOR_SIGMA_ABSOLUTE_ENVELOPE_FATAL
```

## META CLOSEOUT

**What became smaller?**

```text
INPUT_A as an apparently new analytic wall
→ a corollary target consuming the already catalogued L73.2/L73.4/L73.6 chain.
```

**What was killed?**

- compact support alone as a proof of the weighted source envelope;
- the need for one constant uniform as \(\sigma\uparrow1/2\);
- the claim that a fixed narrower strip closes the current consumer;
- an immediate fallback switch before the source-rate discriminator;
- locally uniform transform convergence as a substitute for absolute \(L^1\).

**What must not be tried again?**

Do not carry the fixed-window factor \(e^{\sigma L/2}\) across the cofinal path.
Do not treat “finite sum” as “uniformly bounded sum.” Do not duplicate L73.2
under a new G5 name.

**Current smallest named gaps:**

```text
source-object predecessor:
  SATZ9_FIXED_MODE_SOURCE_DATA_INHABITANT;

analytic rate:
  F72_1A_CENTER_NORMALIZED_SATZ9_FIXED_MODE_RATE;

G5 downstream bridge after that:
  SELECTED_FERRERS_NORMALIZED_ESTAR_WEIGHTED_ENVELOPE.
```

**Next cheapest decisive test:**

Derive and formalize the displayed weighted active-sum error from the actual
L73.2 theorem. If it fails because of a proved fixed-interior-\(\sigma\)
absolute-moment divergence, kill R1 and activate direct strip boundedness.

**Fate of prior predictions:**

Recorded in the machine block. None is upgraded to confirmed without the
source-rate and target-tail theorems.

```yaml
iteration:
  target: REQ-2026-08-21-Q uniform unprojected source envelope
  status: PROGRESS
  failed_strategy: support_or_fixed_window_constant_as_uniform_source_control
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_NORMALIZED_ESTAR_WEIGHTED_ENVELOPE
  invariant_learned: constants_may_depend_on_fixed_sigma_but_not_on_the_cofinal_index
  forbidden_future_move: carry_fixed_window_endpoint_weight_cofinally_or_duplicate_L73_2
  next_decisive_test: weighted_Estar_error_from_selected_Lemma72_rate
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
