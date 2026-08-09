# STATUS: OPEN — B3.0L EXACT BASIS-SYNTHESIZED WHOLE-LINE FOURIER L² ISOMETRY RELEASED FOR PRODUCTION

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY
OPERATIVE_CLASS_COUNT: 1

BINARY_RULING: PRODUCTION_CANDIDATE_RELEASED
PRODUCTION_AUTHORIZED: true
PRODUCTION_ALREADY_PROVED: false
AUTHORIZED_CHILDREN: 1
NEXT_CHILD_SELECTED: false
NEXT_CHILD_AUTHORIZED: false

TRANSACTION:
  ID: GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY
  MODE: IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD
  SAME_LIVING_CHAT: true
  PHASE_KEY_CHANGE: false
  ARISTOTLE_SUBMISSION: NONE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  CONTROLLING_REQUEST:
    expected_sha256: c4fd87beb227ee624eb4ed12e7d9236f21122a318e41afb1fb0a6347938912af
    observed_sha256: c4fd87beb227ee624eb4ed12e7d9236f21122a318e41afb1fb0a6347938912af
    expected_bytes: 13548
    observed_bytes: 13548
    expected_wc_lines: 344
    observed_wc_lines: 344
    final_LF: true
    read_byte_for_byte: true
    status: PASS

  HEAD:
    expected: f5b46e5bc724238f64f85dbf085241d4f4a79a90
    observed_repository_pin: f5b46e5bc724238f64f85dbf085241d4f4a79a90
    status: PASS

  STAGED_PATCH:
    expected_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b
    preservation_required: true

CURRENT_STATE:
  stage: RB-GOAL-057-B3-0K-CLOSED
  B3_0K: CLOSED
  B3_0L: PREFLIGHT_ONLY
  B3_0: OPEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

PREFLIGHT_HARNESS:
  sha256: d7351abafce845efde05b05502061a9067e967d7e0c87987ef7e4cf1c81e28af
  bytes: 4904
  wc_lines: 122
  final_LF: true
  direct_Lean_exit: 0
  reported_axioms:
    - propext
    - Classical.choice
    - Quot.sound
  semantic_plants: PASS_5_OF_5
  forbidden_tokens: ZERO
  judge_reran_Lean: false
  status: ACCEPTED_AS_EXACT_PREFLIGHT_EVIDENCE

RULING:
  whole_line_L2_carrier: PASS
  complex_linear_isometry: PASS
  domain_all_of_H_m: PASS
  complete_literal_input_basis: PASS
  exact_forward_Fourier_mode_images: PASS
  exact_2pi_convention: PASS
  exact_mode_index: PASS
  arbitrary_vector_pointwise_Fourier_claim: NOT_MADE
  surjectivity_onto_whole_line_L2: NOT_CLAIMED
  ambient_source_Weil_form: NOT_DEFINED
  associated_operator_graph: NOT_DEFINED
  operator_domain: NOT_DEFINED
  compression_identity: NOT_CLAIMED
  continuum_numerator: NOT_CLAIMED
  premise_surrogate: ABSENT
  finite_Riesz_lift: ABSENT
  first_mathematical_defect: NONE
  first_API_defect: NONE
  first_category_defect: NONE

PRODUCTION_SURFACE_REPAIR:
  reason: MINIMAL_LEMMA_AND_PRIVATE_API_FIREWALL
  proof_bodies_changed: false
  mathematical_statement_changed: false
  changes_from_tested_harness:
    - sourceLogWindowFourierL2Isometry_apply_mode_made_private
    - anonymous_example_removed
    - public_nonclaim_docstrings_added
    - axiom_prints_retargeted_to_public_surface
  exact_candidate_requires_direct_byte_identical_Lean_gate: true

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierL2Isometry.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

NAMESPACE:
  Q3.RouteB.D0Pstar

PRODUCTION_CANDIDATE:
  filename: GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_CANDIDATE_2026-08-09.lean
  sha256: f67325b9b853fcc1d10bc9769152cf11e7afc59a57b1648256027c6cffa946d8
  bytes: 4846
  wc_lines: 118
  final_LF: true
  forbidden_token_scan: PASS
  direct_Lean_status: MUST_BE_RERUN_BYTE_IDENTICALLY_BEFORE_CLOSEOUT
  materialization_method: BYTE_FOR_BYTE_COPY

PUBLIC_SURFACE:
  definitions:
    - sourceLogWindowFourierL2Isometry
  theorems:
    - coeFn_sourceLogWindowFourierL2Isometry_apply_mode
  total_public_declarations: 2

PRIVATE_SURFACE:
  definitions:
    - fourierLogWindowModeLp
  theorems:
    - fourierLogWindowMode_memLp
    - coeFn_fourierLogWindowModeLp
    - fourierLogWindowModeLp_orthonormal
    - sourceLogWindowFourierL2Isometry_apply_mode
  total_private_declarations: 5

TOTAL_NAMED_DECLARATIONS: 7

STOP:
  GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_STILL_MISSING

SUCCESS:
  GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION_MISSING

POST_SUCCESS_BOUNDARY:
  B3_0L: CLOSED
  SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY: CLOSED
  B3_0: OPEN
  AMBIENT_SOURCE_WEIL_FORM: OPEN
  FORM_DOMAIN: OPEN
  ASSOCIATED_OPERATOR_GRAPH: OPEN
  OPERATOR_DOMAIN: OPEN
  SELECTED_KTRIAL_OPERATOR_DOMAIN: OPEN
  COMPRESSION_IDENTITY: OPEN
  CONTINUUM_NUMERATOR: OPEN
  H4A1B: OPEN
  CHECKPOINT_EFFECT: STRICTLY_ADVANCED_NOT_CLOSED
  COARSE_CHECKPOINTS_CLOSED: 0
  COARSE_CHECKPOINTS_REMAINING: 10

ARSENAL:
  MANDATE_ACCEPTED: true
  ADDITIONAL_PENDING_MANDATE_SURFACED: false
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_EXACT_PRODUCTION_LEAN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

FINAL_BOUNDARY:
  ROUTE: CHALLENGER_NOT_RH
  ACTIVE_BUS_GOAL: 057
  BUS_010: VOID
  GOAL_055: HOLD
  G2_CCM: FROZEN
  ARISTOTLE_SUBMISSION: NONE
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  SOLE_OWNER_GATE: PX_RH_CLAIM
```

## 1. Source-lock and preflight audit

The controlling request passes its exact SHA-256, byte-count, `wc -l` count, UTF-8, and final-LF locks. Its supplied scratch harness, direct Lean output, dependency boundary, five mutation results, and hard nonclaims are the controlling evidence.  `[ABSTRACT][LEAN]`

The repository pin is live and carries the declared state: B3.0K is closed, B3.0 remains open, the current checkpoint is only advanced, and the coarse ledger remains `0 closed / 10 remaining`.  `[ABSTRACT][PAPER]`

The input-side completeness is genuine. Production defines `V_n_m_hilbertBasis` as a Hilbert basis of the literal carrier `H_m i`, and proves its values are exactly the existing source-locked `V_n_m i n` modes. It is not a finite basis, a fitted family, or a new mode convention.  `[ABSTRACT][LEAN]`

The target-side orthonormality is also genuine. The public source-mode controls prove, under the exact forward Mathlib Fourier convention,

[
2\int_{\mathbb R}
\overline{\widehat V_n(t)}\widehat V_r(t),dt
============================================

\begin{cases}
2,&n=r,\
0,&n\ne r.
\end{cases}
]

Cancelling the explicit nonzero factor (2) gives the required Kronecker inner products in whole-line `Lp ℂ 2 volume`. The controls retain the literal first-slot conjugation, mode order, and `2π` scale.  `[ABSTRACT][LEAN]`

## 2. Binary ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY}
}
]

The construction satisfies the exact discriminator.

It composes two lawful isometries:

[
H_m(i)
\xrightarrow{;\operatorname{repr}*{V};}
\ell^2(\mathbb Z)
\xrightarrow{;\operatorname{synthesis}*{\widehat V};}
L^2(\mathbb R).
]

The first arrow exists because the literal `V_n_m` family is a complete Hilbert basis. The second exists because the literal forward-Fourier images form an orthonormal family. Their composition is therefore a complex linear isometry defined on **all** of `H_m i`. `[ABSTRACT][LEAN]`

Surjectivity onto all of (L^2(\mathbb R)) is neither needed nor claimed. The expected range is the closed Fourier image of the zero-extended log-window carrier, generally a proper closed subspace of whole-line (L^2). `[ABSTRACT][PAPER]`

## 3. Strongest attack

> This is not Mathlib’s general Plancherel completion. It synthesizes an isometry by declaring the Fourier images of the basis vectors. Is that merely a Fourier surrogate built to satisfy the desired basis law?

No.

A surrogate would choose an arbitrary orthonormal target family and merely call it Fourier. This construction instead fixes every target basis vector as

```lean
MemLp.toLp
  (fun t => 𝓕 (logWindowZeroExtendedMode i n) t)
```

and publicly proves the almost-everywhere representative law for the literal forward Fourier integral.

The substantive theorem is not the final basis rewrite. It is:

```lean
fourierLogWindowModeLp_orthonormal
```

which consumes the independently proved source-mode correlation controls. Thus the target family’s normalization, Fourier sign, `2π` scale, conjugate-first orientation, and literal integer index are all externally pinned before synthesis. `[ABSTRACT][LEAN]`

Because the input basis is complete, a continuous linear map out of `H_m i` is uniquely determined by these basis values. A phase-twisted, reindexed, inverse-Fourier, or rescaled family cannot satisfy the released public mode-image theorem. `[ABSTRACT][PAPER]`

This is the exact Hilbert-space extension requested by the discriminator. It does **not** claim the stronger statement that, for an arbitrary `Lp` equivalence class (f), the image is pointwise the classical integral Fourier transform of a separately selected representative. That stronger representative theorem remains unnecessary here and is explicitly excluded from the public contract.

C10 therefore does not kill the construction. Defining the continuous extension by basis synthesis is the canonical construction of the requested operator; the nontrivial source content lies in completeness and orthonormality, not in accepting the result as a premise. The applicable Arsenal safeguards are C04, C09, and C10.

## 4. Production-surface repair

The supplied 4,904-byte harness is mathematically accepted, but its production surface should not be copied literally.

Its theorem

```lean
sourceLogWindowFourierL2Isometry_apply_mode
```

mentions the private helper `fourierLogWindowModeLp` in its conclusion. Publishing that theorem would expose a private implementation object in a public type. It is not false, but it is a poor and unnecessary downstream interface.

The repaired candidate therefore:

1. keeps `sourceLogWindowFourierL2Isometry` public;
2. keeps the source-faithful a.e. mode-image theorem public;
3. makes the implementation-level `Lp` equality private;
4. removes the anonymous discriminator `example`;
5. adds explicit nonclaim documentation;
6. changes no mathematical proof body.

The exact public contract becomes:

```lean
sourceLogWindowFourierL2Isometry
    (i : PairIndex) :
    H_m i →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 volume
```

and

```lean
coeFn_sourceLogWindowFourierL2Isometry_apply_mode
    (i : PairIndex) (n : ℤ) :
    ((sourceLogWindowFourierL2Isometry i (V_n_m i n) :
        MeasureTheory.Lp ℂ 2 volume) : ℝ → ℂ)
      =ᵐ[volume]
        fun t => 𝓕 (logWindowZeroExtendedMode i n) t
```

`[ABSTRACT][CONDITIONAL]`

## 5. Exact production candidate

Exact lock:

```text
SHA-256:
  f67325b9b853fcc1d10bc9769152cf11e7afc59a57b1648256027c6cffa946d8

bytes:
  4846

wc -l:
  118

final LF:
  true
```

[Exact byte-pinned Lean candidate](sandbox:/mnt/data/GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_CANDIDATE_2026-08-09.lean)

```lean
import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Q3.RouteB.D0Pstar

private theorem fourierLogWindowMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · have hfi : Integrable (logWindowZeroExtendedMode i n) := by
      apply IntegrableOn.integrable_indicator
      · apply Continuous.integrableOn_Icc
        fun_prop
      · exact measurableSet_Icc
    exact (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hfi).aestronglyMeasurable
  · filter_upwards [] with t
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) henv)]
    nlinarith [norm_nonneg (𝓕 (logWindowZeroExtendedMode i n) t)]

private noncomputable def fourierLogWindowModeLp
    (i : PairIndex) (n : ℤ) :
    MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  (fourierLogWindowMode_memLp i n).toLp
    (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t)

private theorem coeFn_fourierLogWindowModeLp
    (i : PairIndex) (n : ℤ) :
    (fourierLogWindowModeLp i n : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) := by
  exact MemLp.coeFn_toLp (fourierLogWindowMode_memLp i n)

private theorem fourierLogWindowModeLp_orthonormal
    (i : PairIndex) :
    Orthonormal ℂ (fourierLogWindowModeLp i) := by
  rw [orthonormal_iff_ite]
  intro n r
  rw [MeasureTheory.L2.inner_def]
  have hn := coeFn_fourierLogWindowModeLp i n
  have hr := coeFn_fourierLogWindowModeLp i r
  calc
    _ = ∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            𝓕 (logWindowZeroExtendedMode i r) t := by
      apply integral_congr_ae
      filter_upwards [hn, hr] with t hnt hrt
      rw [hnt, hrt]
      simp only [RCLike.inner_apply']
    _ = if n = r then 1 else 0 := by
      by_cases hnr : n = r
      · subst r
        rw [if_pos rfl]
        have h := sourceModeCosineCorrelation_control_diag_zero i n
        simp only [mul_zero, Real.cos_zero,
          Complex.ofReal_one, mul_one] at h
        exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (by simpa using h)
      · rw [if_neg hnr]
        have h := sourceModeCosineCorrelation_control_offdiag_zero i hnr
        simp only [mul_zero, Real.cos_zero,
          Complex.ofReal_one, mul_one] at h
        exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (by simpa using h)

/-- The whole-line `L²` isometry synthesized from the complete literal
`V_n_m` basis and the exact forward Fourier images of those modes.

This declaration makes no claim that the image of an arbitrary `H_m` vector
is represented by a separately defined pointwise Fourier integral. -/
noncomputable def sourceLogWindowFourierL2Isometry
    (i : PairIndex) :
    H_m i →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  (fourierLogWindowModeLp_orthonormal i).orthogonalFamily.linearIsometry.comp
    (V_n_m_hilbertBasis i).repr.toLinearIsometry

private theorem sourceLogWindowFourierL2Isometry_apply_mode
    (i : PairIndex) (n : ℤ) :
    sourceLogWindowFourierL2Isometry i (V_n_m i n) =
      fourierLogWindowModeLp i n := by
  change
    (fourierLogWindowModeLp_orthonormal i).orthogonalFamily.linearIsometry
        ((V_n_m_hilbertBasis i).repr (V_n_m i n)) =
      fourierLogWindowModeLp i n
  rw [← V_n_m_hilbertBasis_apply]
  rw [(V_n_m_hilbertBasis i).repr_self]
  rw [OrthogonalFamily.linearIsometry_apply_single]
  rw [LinearIsometry.toSpanSingleton_apply]
  simp

/-- On every literal production mode, the synthesized isometry agrees almost
everywhere with the existing forward Fourier transform of the zero extension. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_apply_mode
    (i : PairIndex) (n : ℤ) :
    ((sourceLogWindowFourierL2Isometry i (V_n_m i n) :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)]
        (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) := by
  rw [sourceLogWindowFourierL2Isometry_apply_mode]
  exact coeFn_fourierLogWindowModeLp i n


#print axioms sourceLogWindowFourierL2Isometry
#print axioms coeFn_sourceLogWindowFourierL2Isometry_apply_mode

end Q3.RouteB.D0Pstar
```

## 6. Mandatory production judges

The five successful preflight mutations must be rerun against the exact production candidate.

| ID                                               | Mutation                                                                  | Required result                                    |
| ------------------------------------------------ | ------------------------------------------------------------------------- | -------------------------------------------------- |
| `P057_B3_0L_1_RESTRICTED_MEASURE_NOT_WHOLE_LINE` | Replace whole-line `volume` codomain by `volume.restrict (Icc 0 (L_m i))` | `SOURCE_LOG_WINDOW_ZERO_EXTENSION_CARRIER_MISSING` |
| `P057_B3_0L_2_FOURIER_SIGN`                      | Replace forward `𝓕` target by inverse `𝓕⁻`                              | `SOURCE_LOG_WINDOW_FOURIER_SIGN_MISMATCH`          |
| `P057_B3_0L_3_TWO_PI`                            | Replace target frequency `t` by `2*t`                                     | `SOURCE_LOG_WINDOW_FOURIER_SCALE_MISMATCH`         |
| `P057_B3_0L_4_ISOMETRY`                          | Weaken `LinearIsometry` to `LinearMap`                                    | `SOURCE_LOG_WINDOW_PLANCHEREL_ISOMETRY_MISSING`    |
| `P057_B3_0L_5_MODE_FAMILY`                       | Replace literal mode `n` by `n+1`                                         | `SOURCE_LOG_WINDOW_LITERAL_V_N_M_IMAGE_MISMATCH`   |

Three production-surface gates are added:

| ID                                           | Attack                                                                                                         | Required result                                   |
| -------------------------------------------- | -------------------------------------------------------------------------------------------------------------- | ------------------------------------------------- |
| `P057_B3_0L_6_PRIVATE_HELPER_FIREWALL`       | Expose a public declaration whose type mentions `fourierLogWindowModeLp`                                       | `B3_0L_PRIVATE_IMPLEMENTATION_ESCAPED_PUBLIC_API` |
| `P057_B3_0L_7_NO_ARBITRARY_VECTOR_OVERCLAIM` | Add an arbitrary-vector pointwise classical-Fourier theorem without a separate representative/Plancherel proof | `B3_0L_ARBITRARY_VECTOR_FOURIER_OVERCLAIM`        |
| `P057_B3_0L_8_DEPENDENCY`                    | Add generated PSD, Step33, hbox, payload, or direct Aristotle-output support                                   | `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`            |

The phase-twisted/reindexed-family attack instantiates C04. The exact object was precommitted before synthesis, satisfying C09. The construction acts on the requested Hilbert-space functional itself rather than a finite or premise-only proxy, satisfying C10.

## 7. Production validation

Production success requires all of the following:

```text
source lock:
  HEAD = origin/rh_clean
       = f5b46e5bc724238f64f85dbf085241d4f4a79a90

staged patch:
  SHA-256 unchanged at
  291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

production file:
  SHA-256 f67325b9b853fcc1d10bc9769152cf11e7afc59a57b1648256027c6cffa946d8
  bytes 4846
  wc-lines 118
  final LF true

imports:
  exactly 2, in the pinned order

public surface:
  1 definition
  1 theorem

private surface:
  1 definition
  4 theorems

total named declarations:
  7
```

Required commands:

```bash
cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierL2Isometry.lean

lake build \
  Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

lake build

./scripts/q3_check.sh
```

Then require:

```text
forbidden-token scan:
  zero sorry
  zero exact?
  zero admit
  zero unsafe
  zero native_decide
  zero project axiom
  zero opaque
  zero Float

public axioms:
  exactly [propext, Classical.choice, Quot.sound]

proof DB:
  7 declarations
  7 proven
  repeat import idempotent

all current orchestration tests:
  PASS, observed count recorded

strict Spine:
  PASS

semantic index:
  PASS

SQLite integrity:
  knowledge.db = ok
  aristotle_proofs.db = ok
  observability.db = ok

routeb_status.py --check:
  PASS

git diff --check:
  PASS

temporary mutation files:
  zero

route state:
  updated last
```

## 8. Exact semantic boundary after success

A green transaction proves:

[
\boxed{
\exists,
\Phi_i:H_m(i)\longrightarrow L^2(\mathbb R)
\text{ a complex linear isometry,}
}
]

with

[
\boxed{
\Phi_i(V_{n,m})
===============

\widehat{\operatorname{zeroExt}(V_{n,m})}
\quad\text{a.e. for every }n\in\mathbb Z.
}
]

`[ABSTRACT][LEAN]`

It does not prove an ambient Weil form, a closed form domain, a Fourier-multiplier decomposition of that form, an associated operator, selected-trial domain membership, compression, the continuum numerator, H4a1b, or a coarse checkpoint.

The next named wall is:

```text
SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION_MISSING
```

No post-B3.0L child is selected or authorized by this verdict.

## 9. Meta closeout

**What became smaller?**

The whole-line Fourier carrier is no longer blocked on a general Mathlib Plancherel API. It is reduced to an exact basis-synthesized Hilbert-space isometry with the literal source mode images.

**What was killed?**

* the claim that a ready-made all-`Lp` Mathlib Fourier unitary is required;
* restricted-window `Lp` as the Fourier codomain;
* inverse-Fourier and `2π`-rescaled conventions;
* a merely linear, non-isometric extension;
* phase-twisted or reindexed target families;
* a public theorem exposing a private implementation object.

**What must not be tried again?**

Do not restart the general Plancherel-library search before using this exact source-specific isometry. Do not infer a pointwise arbitrary-vector Fourier formula from the released mode law. Do not name this isometry as the source Weil form or its associated operator.

**Current smallest named gap**

```text
SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION_MISSING
```

**Next cheapest decisive test**

Not authorized here: test whether the exact three-component source form can be represented on a source-locked dense core through this isometry and the already proved modewise archimedean, W02, and prime components.

**Prediction fate**

```text
Prediction:
  absence of a ready-made pinned-Mathlib all-Lp Plancherel isometry
  blocks the source-specific whole-line carrier.

Fate:
  REFUTED.
  Complete-basis synthesis supplies the exact requested carrier.

Prediction:
  the literal Fourier-mode family must be proved orthonormal under the
  existing 2π convention before synthesis.

Fate:
  CONFIRMED.
  The diagonal/off-diagonal source correlation controls discharge it.

Prediction:
  a stronger arbitrary-vector pointwise classical-Fourier theorem is
  required for B3.0L itself.

Fate:
  REFUTED.
  It is a separate stronger theorem and remains unclaimed.
```

```yaml
iteration:
  target: GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY
  status: PROGRESS
  failed_strategy: require_a_ready_made_general_Lp_Plancherel_operator_before_source_specific_synthesis
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION_MISSING
  invariant_learned: complete_literal_input_basis_plus_exact_orthonormal_forward_Fourier_images_determines_the_required_all_H_m_isometry
  forbidden_future_move: infer_arbitrary_vector_pointwise_Fourier_or_associated_operator_claims_from_the_mode_image_law
  next_decisive_test: exact_source_form_Fourier_multiplier_decomposition_on_a_source_locked_core
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY

MODE:
  IMPLEMENT_EXACTLY_ONE_PRODUCTION_CHILD

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: f5b46e5bc724238f64f85dbf085241d4f4a79a90
  require_origin_equal: true
  controlling_request_sha256: c4fd87beb227ee624eb4ed12e7d9236f21122a318e41afb1fb0a6347938912af
  controlling_request_bytes: 13548
  controlling_request_wc_lines: 344
  preserve_staged_patch_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

CREATE_ONLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierL2Isometry.lean

EXACT_CANDIDATE:
  source: GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_CANDIDATE_2026-08-09.lean
  method: BYTE_FOR_BYTE_COPY
  sha256: f67325b9b853fcc1d10bc9769152cf11e7afc59a57b1648256027c6cffa946d8
  bytes: 4846
  wc_lines: 118
  final_LF: true
  any_byte_change: STOP_AND_RETURN_NEW_RELEASE_PACKET

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
  - Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceLogWindowFourierL2Isometry
  theorems:
    - coeFn_sourceLogWindowFourierL2Isometry_apply_mode
  total: 2

PRIVATE_SURFACE_EXACT:
  definitions:
    - fourierLogWindowModeLp
  theorems:
    - fourierLogWindowMode_memLp
    - coeFn_fourierLogWindowModeLp
    - fourierLogWindowModeLp_orthonormal
    - sourceLogWindowFourierL2Isometry_apply_mode
  total: 5

MANDATORY_SEMANTICS:
  - codomain_is_whole_line_Lp_Complex_2_volume
  - source_map_is_Complex_LinearIsometry
  - domain_is_all_H_m_i
  - input_coordinates_use_complete_literal_V_n_m_hilbertBasis
  - target_family_is_exact_forward_Fourier_of_logWindowZeroExtendedMode
  - target_orthonormality_consumes_public_diag_and_offdiag_source_controls
  - exact_2pi_scale_retained
  - exact_literal_integer_mode_index_retained
  - no_surjectivity_claim
  - no_arbitrary_vector_pointwise_Fourier_claim
  - no_source_form_graph_domain_compression_or_numerator_claim

MANDATORY_JUDGES:
  - P057_B3_0L_1_RESTRICTED_MEASURE_NOT_WHOLE_LINE
  - P057_B3_0L_2_FOURIER_SIGN
  - P057_B3_0L_3_TWO_PI
  - P057_B3_0L_4_ISOMETRY
  - P057_B3_0L_5_MODE_FAMILY
  - P057_B3_0L_6_PRIVATE_HELPER_FIREWALL
  - P057_B3_0L_7_NO_ARBITRARY_VECTOR_OVERCLAIM
  - P057_B3_0L_8_DEPENDENCY

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_staged_patch_SHA256_unchanged
  - verify_exact_candidate_SHA256_bytes_wc_lines_and_final_LF
  - forbidden_token_scan
  - direct_lake_env_lean
  - target_lake_build
  - full_lake_build
  - scripts_q3_check
  - exact_two_import_audit
  - exact_public_surface_1_definition_1_theorem
  - exact_private_surface_1_definition_4_theorems
  - exact_total_named_declarations_7
  - print_axioms_for_both_public_declarations
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - rerun_all_eight_production_judges
  - remove_all_mutation_artifacts
  - proof_DB_import_7_declarations_7_proven
  - proof_DB_repeat_import_idempotence
  - run_all_current_orchestration_tests
  - strict_Spine_PASS
  - semantic_index_validation_PASS
  - three_SQLite_integrity_checks_PASS
  - routeb_status_check
  - git_diff_check
  - exact_git_status_report
  - update_route_state_last
  - commit_and_push_only_owned_child_and_required_closeout_state_artifacts

CLOSEOUT_MUST_STATE:
  - GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_PROVED
  - WHOLE_LINE_L2_CARRIER_PROVED
  - COMPLEX_LINEAR_ISOMETRY_PROVED
  - ALL_H_M_DOMAIN_PROVED
  - COMPLETE_LITERAL_V_N_M_BASIS_CONSUMED
  - EXACT_FORWARD_FOURIER_MODE_IMAGE_PROVED
  - EXACT_2PI_CONVENTION_RETAINED
  - NO_ARBITRARY_VECTOR_POINTWISE_FOURIER_CLAIM
  - NO_AMBIENT_SOURCE_WEIL_FORM
  - NO_FORM_DOMAIN
  - NO_ASSOCIATED_OPERATOR_GRAPH
  - NO_OPERATOR_DOMAIN
  - NO_SELECTED_KTRIAL_DOMAIN
  - NO_COMPRESSION_IDENTITY
  - NO_CONTINUUM_NUMERATOR
  - H4A1B_OPEN
  - B3_0L_CLOSED
  - B3_0_OPEN
  - CHECKPOINTS_CLOSED_0
  - CHECKPOINTS_REMAINING_10
  - NO_SUCCESSOR_SELECTED_OR_AUTHORIZED

STOP:
  GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_STILL_MISSING

SUCCESS:
  GOAL057_B3_0L_SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION_MISSING

NOT_AUTHORIZED:
  - change_any_candidate_byte
  - select_or_authorize_any_post_B3_0L_child
  - define_ambient_sourceWeilSesquilinearForm
  - define_SourceWeilFormDomain
  - define_SourceWeilAssociatedGraph
  - define_SourceWeilOperatorDomain
  - define_sourceWeilAssociatedOperator
  - claim_arbitrary_vector_pointwise_classical_Fourier_identity
  - assert_selected_kTrial_operator_domain_membership
  - assert_projection_equals_finite_Riesz_action
  - assert_E_m_N_invariance
  - claim_compression_or_continuum_numerator
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
