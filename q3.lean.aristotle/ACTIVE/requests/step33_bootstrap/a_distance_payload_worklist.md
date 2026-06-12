# Step33A.1-A Distance Payload Worklist

This file is generated worklist data, not a Lean proof object.
It names the exact distance-compressed payloads still missing for the
Arch-side A finite-tail analytic cert gate.

## Lean receiver

- payload row type: `RawOmegaAChunkTaylorPayload.PayloadFin`
- compatibility payload row type: `RawOmegaAChunkTaylorPayload.Payload`
- Fin-to-Nat chunk adapter: `RawOmegaAChunkTaylorPayload.chunkValueFromFin26`
- Taylor/model certificate: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate`
- Taylor/model validity proof: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid`
- Taylor value bounds: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ValueBounds`
- Taylor polynomial term bounds: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.PolynomialTermBounds`
- polynomial value-bound helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_term_bounds`
- value bounds from raw/term helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ValueBounds.of_raw_and_polynomial_term_bounds`
- raw integrand component bounds: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.RawIntegrandComponentBounds`
- raw component abs-cos product helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds`
- raw value bounds from component helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.rawOmegaAIntegrand_value_bounds_of_component_bounds`
- value bounds from raw component/term helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ValueBounds.of_raw_component_abs_cos_and_polynomial_term_bounds`
- abs-cos component/term record: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.AbsCosComponentTermBounds`
- abs-cos component/term record value helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.AbsCosComponentTermBounds.toValueBounds`
- abs-cos chunk proof-data record: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.AbsCosChunkProofData`
- abs-cos chunk proof-data valid helper: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.AbsCosChunkProofData.valid`
- lower model integral: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.lowerModelIntegral`
- upper model integral: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.upperModelIntegral`
- generic validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.of_diff_bounds_model_integral_bounds`
- primary validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_of_diff_bounds_model_integral_bounds`
- control validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_of_diff_bounds_model_integral_bounds`
- primary finite chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_diff_bounds_model_integral_bounds`
- primary tail chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_diff_bounds_model_integral_bounds`
- control finite chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_diff_bounds_model_integral_bounds`
- control tail chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_diff_bounds_model_integral_bounds`
- generic value-bound constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.of_value_bounds_model_integral_bounds`
- primary value-bound constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_of_value_bounds_model_integral_bounds`
- control value-bound constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_of_value_bounds_model_integral_bounds`
- primary finite value-bound chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_value_bounds_model_integral_bounds`
- primary tail value-bound chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_value_bounds_model_integral_bounds`
- control finite value-bound chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_value_bounds_model_integral_bounds`
- control tail value-bound chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_value_bounds_model_integral_bounds`
- primary finite raw/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
- primary tail raw/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
- control finite raw/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
- control tail raw/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
- primary finite raw component abs-cos/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- primary tail raw component abs-cos/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- control finite raw component abs-cos/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- control tail raw component abs-cos/term chunk constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- exact-integrand row helper: `RawOmegaAChunkIntegral.WindowPartBoundsCert`
- distance assembler: `RawOmegaAChunkTaylorPayload.PayloadFin.toChunkedRangePayload`
- chunked-range payload: `RawOmegaAChunkedRangePayload`
- chunked-range assembler: `RawOmegaAChunkedRangePayload.toChunkIntegralBoundsCert`
- Step33A wrapper: `RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs`
- Step33B wrapper: `psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs`
- Step33C wrapper: `psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs`

## Totals

- families: `4`
- distance rows: `92`
- distance/chunk cells: `2392`
- local target refresh rows: `71`

## Current missing layer

- radius/nonnegativity checks for every Taylor chunk
- structural finite/tail endpoint checks are discharged by chunk constructors
- Omega/shape-squared/cos component enclosures on every chunk
- component product comparisons producing raw integrand value enclosures
- Taylor polynomial term enclosures and summed polynomial value bounds
- raw/term constructor comparisons implying the Taylor diff enclosure
- explicit Taylor model integral endpoint comparisons for every chunk
- distance-level sum comparisons against generated targets

## Route guard

- global A radius update
- CSV rewrite
- radius-floor regeneration
- 23x23 entry crawl
- Q3.Main or H1/PO3 reroute

## Families

| family | k | domain | target lower | target upper | distances | chunks | target signs |
| --- | ---: | --- | --- | --- | ---: | ---: | --- |
| primary_finite | 11 | (0,260] | `primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower` | `primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper` | 23 | 26 | +1/-22/x0/z0 |
| primary_tail | 11 | (260,520] | `primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower` | `primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper` | 23 | 26 | +10/-13/x0/z0 |
| control_finite | 9 | (0,260] | `controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower` | `controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper` | 23 | 26 | +1/-22/x0/z0 |
| control_tail | 9 | (260,520] | `controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower` | `controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper` | 23 | 26 | +11/-12/x0/z0 |

## primary_finite

- collection name: `primaryFinite`
- validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- Lean L: `fun i => 0 + (10 : Real) * (i : Real)`
- Lean U: `fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real)`

| idx | d | target sign | route tail sign | target lower | target upper | tail slack | tail excess | priority |
| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.00 | positive | positive | 1.233644453639219465E-1 | 1.233644453639219559E-1 | 1.326048519512948610E-18 | 0.000000000000000000E+0 | 2 |
| 1 | 0.25 | negative | negative | -4.374817834937379660E-1 | -4.374817834937379380E-1 | 1.329518998967055565E-18 | 0.000000000000000000E+0 | 0 |
| 2 | 0.50 | negative | negative | -2.235303949220050502E-1 | -2.235303949220050478E-1 | 1.329644710709809283E-18 | 0.000000000000000000E+0 | 0 |
| 3 | 0.75 | negative | negative | -1.588643857122144599E-1 | -1.588643857122144421E-1 | 1.329645110003003917E-18 | 0.000000000000000000E+0 | 0 |
| 4 | 1.00 | negative | positive | -1.255555459045882929E-1 | -1.255555459045882747E-1 | 1.329645110004382962E-18 | 0.000000000000000000E+0 | 0 |
| 5 | 1.25 | negative | positive | -1.042320657664256335E-1 | -1.042320657664256264E-1 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 6 | 1.50 | negative | positive | -8.879834253975839552E-2 | -8.879834253975839068E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 7 | 1.75 | negative | positive | -7.675380274770543894E-2 | -7.675380274770543146E-2 | 1.329645110004383090E-18 | 0.000000000000000000E+0 | 0 |
| 8 | 2.00 | negative | negative | -6.690167682234596462E-2 | -6.690167682234596018E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 9 | 2.25 | negative | negative | -5.860341194405480949E-2 | -5.860341194405480581E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 10 | 2.50 | negative | positive | -5.148618820286358405E-2 | -5.148618820286358048E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 11 | 2.75 | negative | negative | -4.531358455175713209E-2 | -4.531358455175712804E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 12 | 3.00 | negative | negative | -3.992364956689390739E-2 | -3.992364956689390341E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 13 | 3.25 | negative | positive | -3.519755893762420596E-2 | -3.519755893762420260E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 14 | 3.50 | negative | negative | -3.104306607661829972E-2 | -3.104306607661829952E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 15 | 3.75 | negative | negative | -2.738542581476614256E-2 | -2.738542581476614024E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 16 | 4.00 | negative | positive | -2.416221268183482035E-2 | -2.416221268183481990E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 17 | 4.25 | negative | negative | -2.132022017537525370E-2 | -2.132022017537525310E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 18 | 4.50 | negative | negative | -1.881349899943884700E-2 | -1.881349899943884422E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 19 | 4.75 | negative | positive | -1.660203614477936783E-2 | -1.660203614477936457E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 20 | 5.00 | negative | negative | -1.465080742557569843E-2 | -1.465080742557569760E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 21 | 5.25 | negative | negative | -1.292905771430244334E-2 | -1.292905771430244184E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 22 | 5.50 | negative | positive | -1.140972789300954143E-2 | -1.140972789300954062E-2 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |

| refreshed idx | guard | needed slack | slack after |
| ---: | ---: | ---: | ---: |
| 0 | 1.233644453639219558E-19 | 4.133133388000000000E-19 | 9.127351807129486100E-19 |
| 4 | 1.255555459045882929E-19 | 3.710079837000000000E-19 | 9.586371263043829620E-19 |
| 5 | 1.042320657664256335E-19 | 1.313937555950802589E-19 | 1.198251354409302830E-18 |
| 9 | 5.860341194405480943E-20 | 9.984700854726072310E-20 | 1.229798101457122366E-18 |
| 10 | 5.148618820286358405E-20 | 7.160946989717132467E-20 | 1.258035640107211764E-18 |
| 11 | 4.531358455175713209E-20 | 7.334752263000000000E-20 | 1.256297587374383089E-18 |
| 13 | 3.519755893762420596E-20 | 4.401713260943235596E-20 | 1.285627977394950733E-18 |
| 14 | 3.104306607661829969E-20 | 4.223533297131342487E-20 | 1.287409777033069664E-18 |
| 16 | 2.416221268183482033E-20 | 5.475894577996509063E-20 | 1.274886164224417998E-18 |
| 18 | 1.881349899943884698E-20 | 2.040778679522295726E-20 | 1.309237323209160132E-18 |
| 20 | 1.465080742557569841E-20 | 2.888621277000000000E-20 | 1.300758897234383089E-18 |
| 21 | 1.292905771430244334E-20 | 2.342487395578269511E-20 | 1.306220236048600394E-18 |
| 22 | 1.140972789300954141E-20 | 4.597728480000000000E-20 | 1.283667825204383089E-18 |

## primary_tail

- collection name: `primaryTail`
- validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- Lean L: `fun i => rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real)`
- Lean U: `fun i => rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real)`

| idx | d | target sign | route tail sign | target lower | target upper | tail slack | tail excess | priority |
| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.00 | positive | positive | 1.798295245717239885E-21 | 1.798295245717239886E-21 | 1.326048519512948610E-18 | 0.000000000000000000E+0 | 1 |
| 1 | 0.25 | negative | negative | -6.305551866376207189E-23 | -6.305551866376207087E-23 | 1.329518998967055565E-18 | 0.000000000000000000E+0 | 0 |
| 2 | 0.50 | negative | negative | -1.996472869034854930E-25 | -1.996472869034848130E-25 | 1.329644710709809283E-18 | 0.000000000000000000E+0 | 0 |
| 3 | 0.75 | negative | negative | -6.895864347001253940E-31 | -6.895864340443257689E-31 | 1.329645110003003917E-18 | 0.000000000000000000E+0 | 0 |
| 4 | 1.00 | positive | positive | 6.401079035162446847E-35 | 6.401160321134446965E-35 | 1.329645110004382962E-18 | 0.000000000000000000E+0 | 1 |
| 5 | 1.25 | positive | positive | 2.763713814090063621E-37 | 2.765434525216832360E-37 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |
| 6 | 1.50 | positive | positive | 1.601969433701131396E-38 | 1.636634569504751816E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |
| 7 | 1.75 | positive | positive | 9.729055166241254325E-39 | 1.033393651689044580E-38 | 1.329645110004383090E-18 | 0.000000000000000000E+0 | 1 |
| 8 | 2.00 | negative | negative | -1.814020884951004928E-38 | -1.760240619106856281E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 9 | 2.25 | negative | negative | -2.175142380199614396E-38 | -2.143920573751077708E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 10 | 2.50 | positive | positive | 6.473483476136563255E-38 | 6.495885617702951180E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |
| 11 | 2.75 | negative | negative | -4.054245808317083294E-38 | -4.049949548971988508E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 12 | 3.00 | negative | negative | -4.998461426049225854E-38 | -4.979430741976423300E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 13 | 3.25 | positive | positive | 1.104979223614212926E-37 | 1.105298281018955597E-37 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |
| 14 | 3.50 | negative | negative | -5.579641763480666301E-38 | -5.567555740781065146E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 15 | 3.75 | negative | negative | -7.547160862263315632E-38 | -7.527573355200720725E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 16 | 4.00 | positive | positive | 1.428235690884327907E-37 | 1.431037884303337226E-37 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |
| 17 | 4.25 | negative | negative | -6.017701436619444538E-38 | -5.998501807296401262E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 18 | 4.50 | negative | negative | -9.715450123528218917E-38 | -9.689472673015302558E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 19 | 4.75 | positive | positive | 1.603265278771680276E-37 | 1.604706731390971483E-37 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |
| 20 | 5.00 | negative | negative | -5.498545248477549621E-38 | -5.471530306837159073E-38 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 21 | 5.25 | negative | negative | -1.122040070429504374E-37 | -1.119924116223486288E-37 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 0 |
| 22 | 5.50 | positive | positive | 1.627623055066903689E-37 | 1.629227873897282337E-37 | 1.329645110004383089E-18 | 0.000000000000000000E+0 | 1 |

| refreshed idx | guard | needed slack | slack after |
| ---: | ---: | ---: | ---: |
| 1 | 6.305551866376207189E-41 | 7.000000000000000000E-41 | 1.329518998967055565E-18 |
| 2 | 1.996472869034854928E-43 | 2.212419645743594406E-43 | 1.329644710709809283E-18 |
| 3 | 1.000000000000000000E-45 | 1.405900120000000000E-41 | 1.329645110003003917E-18 |
| 4 | 1.000000000000000000E-45 | 4.442578102112000000E-41 | 1.329645110004382962E-18 |
| 5 | 1.000000000000000000E-45 | 1.655003048110800000E-42 | 1.329645110004383089E-18 |
| 6 | 1.000000000000000000E-45 | 4.298860632388730000E-42 | 1.329645110004383089E-18 |
| 7 | 1.000000000000000000E-45 | 7.777736809214690000E-42 | 1.329645110004383090E-18 |
| 8 | 1.000000000000000000E-45 | 2.752630425027680000E-42 | 1.329645110004383089E-18 |
| 9 | 1.000000000000000000E-45 | 3.814968664579560000E-42 | 1.329645110004383089E-18 |
| 10 | 1.000000000000000000E-45 | 8.456440262713200000E-42 | 1.329645110004383089E-18 |
| 11 | 1.000000000000000000E-45 | 5.714503551836440000E-42 | 1.329645110004383089E-18 |
| 12 | 1.000000000000000000E-45 | 2.396520284217560000E-42 | 1.329645110004383089E-18 |
| 13 | 1.000000000000000000E-45 | 2.392108254685900000E-42 | 1.329645110004383089E-18 |
| 14 | 1.000000000000000000E-45 | 3.569150246099700000E-43 | 1.329645110004383089E-18 |
| 15 | 1.000000000000000000E-45 | 2.964033163328800000E-43 | 1.329645110004383089E-18 |
| 17 | 1.000000000000000000E-45 | 6.095374065872100000E-43 | 1.329645110004383089E-18 |
| 18 | 1.000000000000000000E-45 | 4.081499760747130000E-42 | 1.329645110004383089E-18 |
| 19 | 1.000000000000000000E-45 | 2.924801939126300000E-42 | 1.329645110004383089E-18 |
| 20 | 1.000000000000000000E-45 | 3.390989973399290000E-42 | 1.329645110004383089E-18 |
| 21 | 1.000000000000000000E-45 | 2.035644083641000000E-42 | 1.329645110004383089E-18 |
| 22 | 1.000000000000000000E-45 | 4.510209844050500000E-42 | 1.329645110004383089E-18 |

## control_finite

- collection name: `controlFinite`
- validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- Lean L: `fun i => 0 + (10 : Real) * (i : Real)`
- Lean U: `fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real)`

| idx | d | target sign | route tail sign | target lower | target upper | tail slack | tail excess | priority |
| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.00 | positive | positive | 2.624890365877484281E-2 | 2.624890365877484551E-2 | 7.753281601564634378E-17 | 0.000000000000000000E+0 | 2 |
| 1 | 0.25 | negative | negative | -4.873092439847854368E-1 | -4.873092439847854092E-1 | 7.932058134337893153E-17 | 0.000000000000000000E+0 | 0 |
| 2 | 0.50 | negative | positive | -2.460736057093875349E-1 | -2.460736057093875091E-1 | 8.107005357470637650E-17 | 0.000000000000000000E+0 | 0 |
| 3 | 0.75 | negative | negative | -1.744899965879780170E-1 | -1.744899965879779987E-1 | 8.217220306228191775E-17 | 0.000000000000000000E+0 | 0 |
| 4 | 1.00 | negative | negative | -1.378119062369357636E-1 | -1.378119062369357584E-1 | 8.184143370488495385E-17 | 0.000000000000000000E+0 | 0 |
| 5 | 1.25 | negative | positive | -1.143748439686752181E-1 | -1.143748439686752083E-1 | 8.179860802762412739E-17 | 0.000000000000000000E+0 | 0 |
| 6 | 1.50 | negative | negative | -9.742597050289207721E-2 | -9.742597050289207452E-2 | 8.213860896224260190E-17 | 0.000000000000000000E+0 | 0 |
| 7 | 1.75 | negative | negative | -8.420506225936439190E-2 | -8.420506225936438458E-2 | 8.211678661821574861E-17 | 0.000000000000000000E+0 | 0 |
| 8 | 2.00 | negative | positive | -7.339349733534717080E-2 | -7.339349733534716652E-2 | 8.198825799171174629E-17 | 0.000000000000000000E+0 | 0 |
| 9 | 2.25 | negative | negative | -6.428849036841745951E-2 | -6.428849036841744649E-2 | 8.213977319370804181E-17 | 0.000000000000000000E+0 | 0 |
| 10 | 2.50 | negative | negative | -5.648004324873016381E-2 | -5.648004324873016032E-2 | 8.222982967446280534E-17 | 0.000000000000000000E+0 | 0 |
| 11 | 2.75 | negative | positive | -4.970832111898410805E-2 | -4.970832111898410595E-2 | 8.208583544880007810E-17 | 0.000000000000000000E+0 | 0 |
| 12 | 3.00 | negative | negative | -4.379542530481586225E-2 | -4.379542530481585575E-2 | 8.214786877323590880E-17 | 0.000000000000000000E+0 | 0 |
| 13 | 3.25 | negative | negative | -3.861088483096191087E-2 | -3.861088483096190608E-2 | 8.229305928762822990E-17 | 0.000000000000000000E+0 | 0 |
| 14 | 3.50 | negative | positive | -3.405344322235764996E-2 | -3.405344322235764777E-2 | 8.215032554431188459E-17 | 0.000000000000000000E+0 | 0 |
| 15 | 3.75 | negative | negative | -3.004107317037790859E-2 | -3.004107317037790684E-2 | 8.215957801186835121E-17 | 0.000000000000000000E+0 | 0 |
| 16 | 4.00 | negative | positive | -2.650527771460507803E-2 | -2.650527771460507640E-2 | 8.229363701843752903E-17 | 0.000000000000000000E+0 | 0 |
| 17 | 4.25 | negative | positive | -2.338768127103869603E-2 | -2.338768127103869477E-2 | 8.219860605887889937E-17 | 0.000000000000000000E+0 | 0 |
| 18 | 4.50 | negative | negative | -2.063787367594900365E-2 | -2.063787367594900175E-2 | 8.217381000230125219E-17 | 0.000000000000000000E+0 | 0 |
| 19 | 4.75 | negative | positive | -1.821195908254563434E-2 | -1.821195908254563229E-2 | 8.226719744121181584E-17 | 0.000000000000000000E+0 | 0 |
| 20 | 5.00 | negative | positive | -1.607151550999931542E-2 | -1.607151550999931480E-2 | 8.223715240731351752E-17 | 0.000000000000000000E+0 | 0 |
| 21 | 5.25 | negative | negative | -1.418280469000953240E-2 | -1.418280469000953238E-2 | 8.218989930328400653E-17 | 0.000000000000000000E+0 | 0 |
| 22 | 5.50 | negative | positive | -1.251614313302646556E-2 | -1.251614313302646504E-2 | 8.224999760778144645E-17 | 0.000000000000000000E+0 | 0 |

| refreshed idx | guard | needed slack | slack after |
| ---: | ---: | ---: | ---: |
| 0 | 2.624890365877484551E-20 | 7.871040821000000000E-20 | 7.745410560743634378E-17 |
| 3 | 1.744899965879780170E-19 | 2.999260996548954281E-19 | 8.187227696262702232E-17 |
| 5 | 1.143748439686752180E-19 | 4.436193179000000000E-19 | 8.135498870972412739E-17 |
| 6 | 9.742597050289207711E-20 | 1.293861289231118764E-19 | 8.200922283331949002E-17 |
| 7 | 8.420506225936439190E-20 | 1.184214119300000000E-19 | 8.199836520628574861E-17 |
| 8 | 7.339349733534717080E-20 | 8.281286319000000000E-20 | 8.190544512852174629E-17 |
| 10 | 5.648004324873016381E-20 | 7.377475379167231150E-20 | 8.215605492067113303E-17 |
| 13 | 3.861088483096191087E-20 | 5.245849960000000000E-20 | 8.224060078802822990E-17 |
| 14 | 3.405344322235764996E-20 | 6.867059509742294709E-20 | 8.208165494921446164E-17 |
| 15 | 3.004107317037790856E-20 | 3.466967739749186773E-20 | 8.212490833447085934E-17 |
| 16 | 2.650527771460507800E-20 | 3.004652483338881679E-20 | 8.226359049360414021E-17 |
| 19 | 1.821195908254563432E-20 | 3.213194305000000000E-20 | 8.223506549816181584E-17 |
| 20 | 1.607151550999931541E-20 | 2.460993939572176161E-20 | 8.221254246791779576E-17 |
| 21 | 1.418280469000953240E-20 | 2.342558602912224961E-20 | 8.216647371725488428E-17 |

## control_tail

- collection name: `controlTail`
- validity constructor: `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds`
- Lean L: `fun i => rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real)`
- Lean U: `fun i => rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real)`

| idx | d | target sign | route tail sign | target lower | target upper | tail slack | tail excess | priority |
| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.00 | positive | positive | 2.390275099671697075E-18 | 2.390275099671697078E-18 | 7.753281601564634378E-17 | 0.000000000000000000E+0 | 1 |
| 1 | 0.25 | negative | negative | -1.496392435805403197E-18 | -1.496392435805403195E-18 | 7.932058134337893153E-17 | 0.000000000000000000E+0 | 0 |
| 2 | 0.50 | positive | positive | 6.216563201416807164E-19 | 6.216563201416807170E-19 | 8.107005357470637650E-17 | 0.000000000000000000E+0 | 1 |
| 3 | 0.75 | negative | negative | -7.058157635391009113E-20 | -7.058157635391009106E-20 | 8.217220306228191775E-17 | 0.000000000000000000E+0 | 0 |
| 4 | 1.00 | negative | negative | -2.359662550523920397E-19 | -2.359662550523920394E-19 | 8.184143370488495385E-17 | 0.000000000000000000E+0 | 0 |
| 5 | 1.25 | positive | positive | 2.573790936828052663E-19 | 2.573790936828052666E-19 | 8.179860802762412739E-17 | 0.000000000000000000E+0 | 1 |
| 6 | 1.50 | negative | negative | -8.737862637356801490E-20 | -8.737862637356801472E-20 | 8.213860896224260190E-17 | 0.000000000000000000E+0 | 0 |
| 7 | 1.75 | negative | negative | -9.828979838699466054E-20 | -9.828979838699466044E-20 | 8.211678661821574861E-17 | 0.000000000000000000E+0 | 0 |
| 8 | 2.00 | positive | positive | 1.625541116389958198E-19 | 1.625541116389958200E-19 | 8.198825799171174629E-17 | 0.000000000000000000E+0 | 1 |
| 9 | 2.25 | negative | negative | -8.679651064084806076E-20 | -8.679651064084806056E-20 | 8.213977319370804181E-17 | 0.000000000000000000E+0 | 0 |
| 10 | 2.50 | negative | negative | -4.176827026346629406E-20 | -4.176827026346629398E-20 | 8.222982967446280534E-17 | 0.000000000000000000E+0 | 0 |
| 11 | 2.75 | positive | positive | 1.137653830948299150E-19 | 1.137653830948299151E-19 | 8.208583544880007810E-17 | 0.000000000000000000E+0 | 1 |
| 12 | 3.00 | negative | negative | -8.274872087691456304E-20 | -8.274872087691456295E-20 | 8.214786877323590880E-17 | 0.000000000000000000E+0 | 0 |
| 13 | 3.25 | negative | negative | -1.015346368075401225E-20 | -1.015346368075401224E-20 | 8.229305928762822990E-17 | 0.000000000000000000E+0 | 0 |
| 14 | 3.50 | positive | positive | 8.152033533892666785E-20 | 8.152033533892666794E-20 | 8.215032554431188459E-17 | 0.000000000000000000E+0 | 1 |
| 15 | 3.75 | negative | negative | -7.689410156069335997E-20 | -7.689410156069335989E-20 | 8.215957801186835121E-17 | 0.000000000000000000E+0 | 0 |
| 16 | 4.00 | positive | positive | 9.864598276104447565E-21 | 9.864598276104447585E-21 | 8.229363701843752903E-17 | 0.000000000000000000E+0 | 1 |
| 17 | 4.25 | positive | positive | 5.738007805541927632E-20 | 5.738007805541927644E-20 | 8.219860605887889937E-17 | 0.000000000000000000E+0 | 1 |
| 18 | 4.50 | negative | negative | -6.977810634424286923E-20 | -6.977810634424286916E-20 | 8.217381000230125219E-17 | 0.000000000000000000E+0 | 0 |
| 19 | 4.75 | positive | positive | 2.308438688896104384E-20 | 2.308438688896104387E-20 | 8.226719744121181584E-17 | 0.000000000000000000E+0 | 1 |
| 20 | 5.00 | positive | positive | 3.810690383811020539E-20 | 3.810690383811020543E-20 | 8.223715240731351752E-17 | 0.000000000000000000E+0 | 1 |
| 21 | 5.25 | negative | negative | -6.173345585286570038E-20 | -6.173345585286570032E-20 | 8.218989930328400653E-17 | 0.000000000000000000E+0 | 0 |
| 22 | 5.50 | positive | positive | 3.168430360414573664E-20 | 3.168430360414573668E-20 | 8.224999760778144645E-17 | 0.000000000000000000E+0 | 1 |

| refreshed idx | guard | needed slack | slack after |
| ---: | ---: | ---: | ---: |
| 0 | 2.390275099671697075E-36 | 3.000000000000000000E-36 | 7.753281601564634378E-17 |
| 1 | 1.496392435805403197E-36 | 2.000000000000000000E-36 | 7.932058134337893153E-17 |
| 2 | 6.216563201416807164E-37 | 6.408907738680580430E-37 | 8.107005357470637650E-17 |
| 3 | 7.058157635391009113E-38 | 7.494231519917738765E-38 | 8.217220306228191775E-17 |
| 4 | 2.359662550523920397E-37 | 3.000000000000000000E-37 | 8.184143370488495385E-17 |
| 5 | 2.573790936828052663E-37 | 3.065962955685168656E-37 | 8.179860802762412739E-17 |
| 6 | 8.737862637356801481E-38 | 9.000000000000000000E-38 | 8.213860896224260190E-17 |
| 7 | 9.828979838699466044E-38 | 1.000000000000000000E-37 | 8.211678661821574861E-17 |
| 8 | 1.625541116389958198E-37 | 2.010523543812138414E-37 | 8.198825799171174629E-17 |
| 9 | 8.679651064084806076E-38 | 1.100000000000000000E-37 | 8.213977319370804181E-17 |
| 10 | 4.176827026346629406E-38 | 4.319404227353360501E-38 | 8.222982967446280534E-17 |
| 11 | 1.137653830948299151E-37 | 1.453452623121257540E-37 | 8.208583544880007810E-17 |
| 12 | 8.274872087691456295E-38 | 9.000000000000000000E-38 | 8.214786877323590880E-17 |
| 13 | 1.015346368075401224E-38 | 1.029028488608094973E-38 | 8.229305928762822990E-17 |
| 14 | 8.152033533892666785E-38 | 9.000000000000000000E-38 | 8.215032554431188459E-17 |
| 15 | 7.689410156069335989E-38 | 8.000585966680690784E-38 | 8.215957801186835121E-17 |
| 16 | 9.864598276104447575E-39 | 1.034936414070181042E-38 | 8.229363701843752903E-17 |
| 17 | 5.738007805541927644E-38 | 6.000000000000000000E-38 | 8.219860605887889937E-17 |
| 18 | 6.977810634424286916E-38 | 7.272819446269481098E-38 | 8.217381000230125219E-17 |
| 19 | 2.308438688896104387E-38 | 3.000000000000000000E-38 | 8.226719744121181584E-17 |
| 20 | 3.810690383811020543E-38 | 4.000000000000000000E-38 | 8.223715240731351752E-17 |
| 21 | 6.173345585286570032E-38 | 6.489168930937340774E-38 | 8.218989930328400653E-17 |
| 22 | 3.168430360414573664E-38 | 4.000000000000000000E-38 | 8.224999760778144645E-17 |
