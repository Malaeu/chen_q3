# Step33A.1-A Omega Closed-Form Endpoint Contract

- Schema: `q3_psdpd_step33_a_omega_closed_form_endpoint_contract.v14`
- Status: `blocked_missing_closed_form_proof_rows_not_lean`
- Worklist: `q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21`
- Endpoint mode: `closed_form_shape_value_deriv_endpoint`
- Target theorem: `rawOmegaEndpointClosedFormBounds_generated`
- Next theorem: `rawOmegaEndpointValueDerivIntervalCert_generated`
- Receiver: `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc`
- Absolute-tail fallback receiver: `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc`
- Derivative sub-receiver: `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert.of_direct_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc`
- Tail majorant lemma: `RawOmegaATaylorModelCertificate.abs_trigammaImSeriesTermClosedForm_le_etaUpper_cubic`
- Tail majorant summable lemma: `RawOmegaATaylorModelCertificate.summable_trigammaImSeriesTermClosedForm_cubic_majorant`
- Anchor re-series lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_bounds_from_re_series_prefix_tail_abs`
- Anchor signed-tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval`
- Anchor accelerated-tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_model_abs_error`
- Generic accelerated-tail lemma: `RawOmegaATaylorModelCertificate.tsum_shifted_tail_bounds_of_model_abs_error`
- Generic nonnegative prefix/tail lemma: `RawOmegaATaylorModelCertificate.nonneg_tsum_bounds_of_sum_range_tail_upper`
- Anchor leading quadratic tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_model_error`
- Anchor positive p-series tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_positive_series_bounds`
- Anchor leading quadratic error lemma: `RawOmegaATaylorModelCertificate.abs_step22OmegaArchWeightReSeriesTerm_sub_leading_quadratic_model_le_cubic`
- Anchor q2 closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_one_div_nat_add_quarter_sq_le_inv_pred`
- Anchor q3 closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_const_mul_one_div_nat_add_quarter_cubic_le`
- Anchor q2 shifted closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_anchor_q2_shifted_tail_le_closed_form`
- Anchor q3 shifted closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_anchor_q3_shifted_tail_le_closed_form`
- Anchor prefix/tail closed-form tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form`
- Rows: `110`
- Families: `primary_finite`

## Closed-Form Term

```text
trigammaImSeriesTermClosedForm eta n = -((2 * (n + 1/4) * (eta/2)) / (((n + 1/4)^2 + (eta/2)^2)^2))
```

## Cubic Tail Series

```text
g n = etaUpper / ((((n + derivN : Nat) : Real) + 1/4)^3)
```

## Anchor Re-Series Term

```text
1/(n+1) - (n+1/4)/((n+1/4)^2 + (eta/2)^2)
```

## Anchor Leading Tail Model

```text
model n = -(3/4) / ((((n + anchorN : Nat) : Real) + 1/4)^2)
g n = ((3/4)^2 + (etaUpper/2)^2) / ((((n + anchorN : Nat) : Real) + 1/4)^3)
q2 n = 1 / ((((n + anchorN : Nat) : Real) + 1/4)^2)
g n = ((3/4)^2 + (etaUpper/2)^2) / ((((n + anchorN : Nat) : Real) + 1/4)^3)
1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)
((3/4)^2 + (etaUpper/2)^2) * (1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))
```

## Required Generated Fields

- `derivN`
- `anchorN`
- `etaUpper`
- `termLower`
- `termUpper`
- `imPrefixLower`
- `imPrefixUpper`
- `tailRadius`
- `hANonneg`
- `hBUpper`
- `hTermLower over trigammaImSeriesTermClosedForm on [a,b]`
- `hTermUpper over trigammaImSeriesTermClosedForm on [a,b]`
- `hPrefixLower`
- `hPrefixUpper`
- `hCubicTailSum`
- `hDerivLower`
- `hDerivUpper`
- `anchorConstLower`
- `anchorConstUpper`
- `anchorPrefixLower`
- `anchorPrefixUpper`
- `anchorTailLower`
- `anchorTailUpper`
- `anchorQ2Lower`
- `anchorQ2Upper`
- `anchorQ3Upper`
- `anchorQ2PrefixN`
- `anchorQ2PrefixLower`
- `anchorQ2PrefixUpper`
- `anchorQ2TailUpper`
- `anchorQ2TailIndex`
- `anchorQ2TailClosedFormUpper`
- `anchorQ3PrefixN`
- `anchorQ3PrefixUpper`
- `anchorQ3TailUpper`
- `anchorQ3TailIndex`
- `anchorQ3TailCoeff`
- `anchorQ3TailClosedFormUpper`
- `hAnchorConstLower`
- `hAnchorConstUpper`
- `hAnchorPrefixLower`
- `hAnchorPrefixUpper`
- `hAnchorQ2Lower`
- `hAnchorQ2Upper`
- `hAnchorQ3Upper`
- `hAnchorQ2PrefixLower`
- `hAnchorQ2PrefixUpper`
- `hAnchorQ2TailIndexEq`
- `hAnchorQ2TailIndexGeOne`
- `hAnchorQ2TailClosedFormUpper`
- `hAnchorQ2TailUpperFromClosedForm`
- `hAnchorQ2TailUpper`
- `hAnchorQ3PrefixUpper`
- `hAnchorQ3TailIndexEq`
- `hAnchorQ3TailIndexGeOne`
- `hAnchorQ3TailCoeffNonneg`
- `hAnchorQ3TailClosedFormUpper`
- `hAnchorQ3TailUpperFromClosedForm`
- `hAnchorQ3TailUpper`
- `hAnchorTailLowerFromPositiveSeries`
- `hAnchorTailUpperFromPositiveSeries`
- `hAnchorLowerFromReSeries`
- `hAnchorUpperFromReSeries`

## Candidate Status Counts

- `candidate_interval_generated_not_lean_proof`: `440`

## First Row Proof-Data Request

- Status: `ready_for_first_row_proof_data_generation_or_aristotle_after_user_ok`
- Row: `primary_finite row=0 parent=0 split=100 sub=0`
- Target Lean file: `q3.lean.aristotle/aristotle_input/step33_endpoint_v18_first_row_pilot.lean`
- Proof pack: `q3.lean.aristotle/aristotle_input/step33_endpoint_v18_first_row_proof_pack.md`
- Context bundle script: `q3.lean.aristotle/scripts/q3_psdpd_step33_endpoint_first_row_context_bundle.py`
- Aristotle submit requires explicit user OK: `True`
- Omega target theorem: `primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_aristotle_v18`
- ShapeSq target theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18`
- Checked combiner: `primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_aristotle_v18`
- Interval: `[499999999999999999999/10000000000000000000000, 1/20]`, anchor `1/20`
- Parameters: `k=11`, `ell=0.3`, `distance=0.00`

### First Row Omega Endpoint Targets

| endpoint | field | status | candidate decimal |
| --- | --- | --- | ---: |
| omegaDerivLower | `hOmegaDerivLower` | `candidate_interval_generated_not_lean_proof` | `0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000E+90` |
| omegaDerivUpper | `hOmegaDerivUpper` | `candidate_interval_generated_not_lean_proof` | `2.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000E+0` |
| omegaAnchorLower | `hOmegaAnchorLower` | `candidate_interval_generated_not_lean_proof` | `-5.332164676365227629591616356352554217022087394632457926284822676923938394647490561593897312E+0` |
| omegaAnchorUpper | `hOmegaAnchorUpper` | `candidate_interval_generated_not_lean_proof` | `-5.332164676365227629590512382843586537477340567741576008170879715536683602673645148956338388E+0` |

### First Row Proof-Data Groups

| group | status | receiver | fields |
| --- | --- | --- | ---: |
| derivative_trigamma_prefix_tail | `missing_lean_proof_data` | `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert.of_direct_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc` | 15 |
| anchor_re_series_prefix_signed_tail | `missing_lean_proof_data` | `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval` | 15 |
| anchor_re_series_positive_pseries_tail | `missing_positive_pseries_sum_rows` | `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_positive_series_bounds` | 12 |
| anchor_re_series_positive_pseries_prefix_tail | `missing_positive_pseries_prefix_rows_and_closed_tail_comparisons` | `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form` | 28 |
| anchor_re_series_prefix_abs_tail_fallback | `available_not_active` | `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_bounds_from_re_series_prefix_tail_abs` | 13 |
| endpoint_rational_containment | `already_generated_checked_after_endpoint_packages` | `primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated` | 6 |

## Sample Rows

| row | interval | available endpoint candidates |
| --- | --- | ---: |
| primary_finite row=0 parent=0 split=100 sub=0 | [499999999999999999999/10000000000000000000000, 1/20] anchor=1/20 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=1 | [149999999999999999999999/1000000000000000000000000, 3/20] anchor=3/20 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=2 | [2499999999999999999999/10000000000000000000000, 1/4] anchor=1/4 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=3 | [3499999999999999999999/10000000000000000000000, 7/20] anchor=7/20 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=4 | [4499999999999999999999/10000000000000000000000, 9/20] anchor=9/20 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=5 | [5499999999999999999999/10000000000000000000000, 11/20] anchor=11/20 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=6 | [6499999999999999999999/10000000000000000000000, 13/20] anchor=13/20 | 4/4 |
| primary_finite row=0 parent=0 split=100 sub=7 | [7499999999999999999999/10000000000000000000000, 3/4] anchor=3/4 | 4/4 |

## Route Guard

- do not emit rawOmegaEndpointClosedFormBounds_generated until each row has proof data
- candidate endpoint rationals are not Lean proofs
- do not route tight direct anchors through Stieltjes main/error
- prefer signed/accelerated anchor-tail intervals over absolute anchor tails
- do not call Step33A.1-A or A hbox closed from this contract
- do not edit A CSV, ARadius, radius-floor, or LDL
- do not touch Q3.Main, H1, or PO3
