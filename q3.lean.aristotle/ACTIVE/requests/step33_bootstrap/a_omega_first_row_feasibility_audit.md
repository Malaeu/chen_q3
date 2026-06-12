# Step33A.1-A Omega First-Row Feasibility Audit

- Schema: `q3_psdpd_step33_a_omega_first_row_feasibility_audit.v11`
- Status: `route_feasibility_audit_not_lean_proof`
- Row: `primary_finite row=0 parent=0 split=100 sub=0`
- Interval: `[499999999999999999999/10000000000000000000000, 1/20]`, anchor `1/20`
- Lean proof emitted: `False`

## Current Containment

- omega radius: `2.487199989833435045049250024048093261896941186250842292793095E-21`
- derivative abs slope: `2`
- anchor center error: `6.312397263819157279290096877252160909824991053686543320249760436616125E-22`
- consumed: `8.312397263819157279290096877252160909824991053686543320249760436616125E-22`
- margin: `1.6559602634515193171202403363228771709144420808821879607681189563383875E-21`
- passes: `True`

## Relaxed Derivative Candidate

- derivative interval: `[1, 2]`
- consumed with current anchor proof: `8.312397263819157279290096877252160909824991053686543320249760436616125E-22`
- margin with current anchor proof: `1.6559602634515193171202403363228771709144420808821879607681189563383875E-21`
- allowed anchor center error: `2.287199989833435045049250024048093261896941186250842292793095E-21`
- passes containment: `True`

## Direct Anchor Proof Target

- status: `direct_anchor_wrapper_checked_anchor_inequalities_open`
- wrapper: `primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_of_direct_anchor_generated`
- proof pad: `44158940358707181789873075635276724557718455490191678953816505502357/80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000`
- proof pad decimal: `5.519867544838397723734134454410E-22`
- proof interval width: `1.103973508967679544746826890882E-21`
- lower statement: `omegaAnchorLower <= step22OmegaArchWeight anchor`
- upper statement: `step22OmegaArchWeight anchor <= omegaAnchorUpper`
- meaning: The active v21 endpoint receiver asks for the two direct anchor inequalities around step22OmegaArchWeight (1/20).  This is below the checked Route A subchunk wrapper; it is not a request to regenerate A data or replay a full row.

## Derivative Prefix/Tail Candidate

- derivN: `4`
- cubic tail bound: `0.002035416242621616120496641563199674333401180541420720537349888052106655811113372684714024017911662935`
- produced derivative interval: `[1.583168162267358111492732592751884929923939121160538598144958846977130190177741507685257177263004580, 1.585203578509979727616273327094471293405784979545900876967308180266222300710421182021876094465952822]`
- passes current tight derivative targets: `True`
- passes relaxed derivative targets: `True`
- rough min N for current tight width via cubic tail: `0.1118033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137`

## Anchor Real-Series Abs-Tail Feasibility

- status: `plain_abs_tail_impractical_for_current_direct_anchor_budget`
- allowed anchor center error after relaxed derivative: `2.287199989833435045049250024048093261896941186250842292793095E-21`
- rough min anchorN for plain abs tail: `327911858750322320515.8216735665100622226299027967217482697189767497450361735355251771627194185021048`
- implication: The direct real-series prefix/absolute-tail receiver is not a good first proof route for the v21 direct anchor endpoint.  Use a sharper high-order/asymptotic bridge or a certified constant backend before trying to materialize anchorN rows.

## Anchor Signed-Tail Route

- status: `checked_combined_prefix_tail_receiver_available_but_simple_prefix_tail_width_impractical`
- receiver: `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc`
- anchor lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval`
- accelerated-tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_model_abs_error`
- generic accelerated-tail lemma: `RawOmegaATaylorModelCertificate.tsum_shifted_tail_bounds_of_model_abs_error`
- generic nonnegative prefix/tail lemma: `RawOmegaATaylorModelCertificate.nonneg_tsum_bounds_of_sum_range_tail_upper`
- leading quadratic tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_model_error`
- positive p-series tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_positive_series_bounds`
- prefix/tail closed-form tail lemma: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form`
- leading quadratic error lemma: `RawOmegaATaylorModelCertificate.abs_step22OmegaArchWeightReSeriesTerm_sub_leading_quadratic_model_le_cubic`
- q2 closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_one_div_nat_add_quarter_sq_le_inv_pred`
- q3 closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_const_mul_one_div_nat_add_quarter_cubic_le`
- q2 shifted closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_anchor_q2_shifted_tail_le_closed_form`
- q3 shifted closed tail lemma: `RawOmegaATaylorModelCertificate.tsum_anchor_q3_shifted_tail_le_closed_form`
- meaning: The Lean receiver no longer requires |tail| <= radius.  The remaining proof-producing task is now localized to finite prefix sums and rational comparisons against checked closed-form shifted-tail bounds for the positive q2/q3 p-series; the combined Lean receiver now splits the nonnegative tsums and performs the negative-model sign flip.  However, using this receiver with only the current integral closed tails still leaves a first-order q2 tail-width constraint, so it is not a practical row-generation route for the v21 direct anchor interval.

```text
model n = -(3/4) / ((((n + anchorN : Nat) : Real) + 1/4)^2)
g n = ((3/4)^2 + (etaUpper/2)^2) / ((((n + anchorN : Nat) : Real) + 1/4)^3)
q2 n = 1 / ((((n + anchorN : Nat) : Real) + 1/4)^2)
g n = ((3/4)^2 + (etaUpper/2)^2) / ((((n + anchorN : Nat) : Real) + 1/4)^3)
1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)
((3/4)^2 + (etaUpper/2)^2) * (1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))
```

### Accelerated Model Tail Facts

- `anchorQ2Lower <= tsum (fun n => 1/(n+anchorN+1/4)^2)`
- `tsum (fun n => 1/(n+anchorN+1/4)^2) <= anchorQ2Upper`
- `tsum (fun n => ((3/4)^2 + (etaUpper/2)^2)/(n+anchorN+1/4)^3) <= anchorQ3Upper`
- `anchorTailLower <= -(3/4) * anchorQ2Upper - anchorQ3Upper`
- `-(3/4) * anchorQ2Lower + anchorQ3Upper <= anchorTailUpper`

### Positive P-Series Prefix/Tail Facts

- `anchorQ2PrefixLower <= sum range anchorQ2PrefixN q2`
- `tsum (fun n => q2 (n + anchorQ2PrefixN)) <= 1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)`
- `1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1) <= anchorQ2TailUpper`
- `sum range anchorQ2PrefixN q2 + anchorQ2TailUpper <= anchorQ2Upper`
- `tsum (fun n => q3 (n + anchorQ3PrefixN)) <= ((3/4)^2 + (etaUpper/2)^2) * (1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))`
- `((3/4)^2 + (etaUpper/2)^2) * (1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2)) <= anchorQ3TailUpper`
- `sum range anchorQ3PrefixN q3 + anchorQ3TailUpper <= anchorQ3Upper`

## Anchor Signed-Tail Prefix Feasibility

- status: `current_simple_q2_q3_prefix_tail_receiver_impractical_for_v21_direct_anchor_interval`
- anchor interval width: `1.1039735089676795447468268908819181139429613872547919738454126375589250E-21`
- q2 tail width model: `width contains roughly (3/4) / (anchorN + anchorQ2PrefixN - 3/4)`
- min combined q2 tail index for anchor width: `679364127769081602024`
- rough q2 index decimal: `679364127769081602023.2959782840584692524335362851483467752701163081966017537304196549869897516461828`
- q3 tail width model: `width contains roughly 2*((3/4)^2 + (etaUpper/2)^2) / (anchorN + anchorQ3PrefixN - 3/4)^2`
- q3 tail coefficient: `0.563125`
- min combined q3 tail index for anchor width: `31940232705`
- rough q3 index decimal: `31940232704.97280761414152815346441526295811672241960046958471658070566521342648191582598642089014664`
- verdict: Do not treat the remaining anchor task as finite-prefix row crawl.  Under the current simple closed-tail receiver, the q2 tail alone asks for an astronomically large combined anchorN+prefixN index.  The next proof route should introduce a sharper analytic/asymptotic tail bridge, a certified special-function constant backend, or an equivalent route chosen by Pro/Louise.

## Recommendation

- Do not try to prove the current tight derivative endpoint interval with cubic absolute tail.
- Keep the derivative-side wrapper that closes the first endpoint with relaxed derivative interval [0,2].
- Use the v21 direct-anchor wrapper and prove only the two anchor inequalities for step22OmegaArchWeight (1/20).
- Do not route the anchor side back to the old q2/q3 finite-prefix crawl under the current closed-tail receiver.
- Ask Pro/Louise only for the canonical direct-anchor theorem shape: certified special-function constant backend, high-order/asymptotic digamma bridge, or another semantic rewrite.
- Do not widen A radius/CSV/radius-floor/LDL.
- Do not use the plain absolute-tail anchor receiver as the active tight-row target.
