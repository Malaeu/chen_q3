# Step33A.1-A Refined Subchunk Pilot Overlay

Fail-closed pilot overlay for `primary_finite` row 0 parent chunk 0.

## Verdict

- schema: `q3_psdpd_step33_a_refined_subchunk_pilot_overlay.v3`
- status: `pilot_overlay_blocked_jet_envelope_failed`
- source audit status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.ResidualAnchorRefinedPayloadFin`
- active subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData`
- subchunks: `0`
- blocked subchunks: `100`
- seeded fields: `0`
- remaining analytic fields: `0`

## Seeded Fields

- `remainder`
- `sampleRadius`
- `slope`
- `mesh`
- `anchor`
- `derivCellCount`
- `derivCellLeft`
- `derivCellRight`
- `derivLower`
- `derivUpper`
- `derivAnchor`
- `derivAnchorLower`
- `derivAnchorUpper`
- `derivMesh`
- `derivSlope`
- `hSlopeNonneg`
- `hAnchorIn`
- `hLeftMesh`
- `hRightMesh`
- `hDerivSlopeNonneg`
- `hDerivAnchorIn`
- `hDerivLeftMesh`
- `hDerivRightMesh`
- `hDerivLowerFromAnchor`
- `hDerivUpperFromAnchor`
- `hDerivLowerAbs`
- `hDerivUpperAbs`
- `hEnvelope`

## Still Missing Per Subchunk

- `coeff`
- `hAnchorResidual`
- `hResidualDifferentiable`
- `hDerivCoverCells`
- `hDerivAnchorLower`
- `hDerivAnchorUpper`
- `hResidualDerivDifferentiableOnCell`
- `hResidualSecondDerivBoundOnCell`
- `hIntegralLower`
- `hIntegralUpper`

## First Blockers

| subchunk | reason | split | cells | cover slope | envelope excess | sampled excess |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | `subchunk 0: jet envelope fails` | `64` | `64` | `1.179008903933595908E-5` | `5.895044519659269725E-7` | `-6.843206600623000000E-19` |
| 1 | `subchunk 1: jet envelope fails` | `64` | `64` | `1.380394893227744701E-5` | `6.901974466128984266E-7` | `-8.936788528616000000E-19` |
| 2 | `subchunk 2: jet envelope fails` | `64` | `64` | `1.300901266440272401E-5` | `6.504506332192528159E-7` | `-8.580742717972500000E-19` |
| 3 | `subchunk 3: jet envelope fails` | `64` | `64` | `8.479385426786311507E-6` | `4.239692713385530449E-7` | `-7.523618491780000000E-19` |
| 4 | `subchunk 4: jet envelope fails` | `64` | `64` | `4.830155147563297397E-6` | `2.415077573777087589E-7` | `-4.498344250769000000E-19` |
| 5 | `subchunk 5: jet envelope fails` | `64` | `64` | `2.988832919798042351E-6` | `1.494416459893138469E-7` | `-5.722565854644500000E-19` |
| 6 | `subchunk 6: jet envelope fails` | `64` | `64` | `2.393497425868751155E-6` | `1.196748712926589556E-7` | `-7.629646773941000000E-19` |
| 7 | `subchunk 7: jet envelope fails` | `64` | `64` | `1.854891767944511975E-6` | `9.274458839648554112E-8` | `-7.292860025512500000E-19` |
| 8 | `subchunk 8: jet envelope fails` | `64` | `64` | `1.398997145522886625E-6` | `6.994985727556368696E-8` | `-5.576289419374000000E-19` |
| 9 | `subchunk 9: jet envelope fails` | `64` | `64` | `1.033321033309986068E-6` | `5.166605166461704682E-8` | `-8.637736378320500000E-19` |
| 10 | `subchunk 10: jet envelope fails` | `64` | `64` | `7.553312921810803233E-7` | `3.776656460823801375E-8` | `-8.048160895762500000E-19` |
| 11 | `subchunk 11: jet envelope fails` | `64` | `64` | `5.554842890579450273E-7` | `2.777421445193072053E-8` | `-9.450335815809500000E-19` |
| 12 | `subchunk 12: jet envelope fails` | `64` | `64` | `4.142528048337168950E-7` | `2.071264024077263232E-8` | `-9.072787109573500000E-19` |
| 13 | `subchunk 13: jet envelope fails` | `64` | `64` | `3.136336848643917820E-7` | `1.568168424245633930E-8` | `-7.402829901816000000E-19` |
| 14 | `subchunk 14: jet envelope fails` | `64` | `64` | `2.417832302306976159E-7` | `1.208916151076352701E-8` | `-7.640272888465500000E-19` |
| 15 | `subchunk 15: jet envelope fails` | `64` | `64` | `1.911186103034304909E-7` | `9.555930514436401672E-9` | `-7.330308427191000000E-19` |
| 16 | `subchunk 16: jet envelope fails` | `64` | `64` | `1.530192594487832144E-7` | `7.650962971896982900E-9` | `-5.344965594153000000E-19` |
| 17 | `subchunk 17: jet envelope fails` | `64` | `64` | `1.224283021537878480E-7` | `6.121415106731829555E-9` | `-9.542109109580500000E-19` |
| 18 | `subchunk 18: jet envelope fails` | `64` | `64` | `9.692679195092700807E-8` | `4.846339596830006631E-9` | `-6.903284971370000000E-19` |
| 19 | `subchunk 19: jet envelope fails` | `64` | `64` | `8.372060936250318958E-8` | `4.186030467599122224E-9` | `-5.107524821414500000E-19` |

## Exact Next Lean Target

- `hResidualDerivLowerOnCell` / `hResidualDerivUpperOnCell`
- via `hDerivAnchorLower` / `hDerivAnchorUpper`
- via `hResidualSecondDerivBoundOnCell`
- via `hDerivLowerFromAnchor` / `hDerivUpperFromAnchor`

## Guard

- not Lean proof data
- do not emit PayloadFin from this overlay alone
- sampled derivative lower/upper values are candidates only
- anchor-to-cell scalar comparisons are rational checks, not analytic proofs
- next Lean work must prove derivative-anchor intervals and second-derivative cell bounds
- do not mutate CSV, ARadius, radius-floor, or LDL data
- do not route to H1/PO3 or Q3.Main from this layer
