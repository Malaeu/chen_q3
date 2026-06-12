# Step33A.1-A Refined Subchunk Derivative Bound Audit

Diagnostic derivative audit.  This is not Lean proof data.

## Verdict

- status: `derivative_envelope_candidate_failed`
- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- degree: `16`
- split: `10`

## Counts

| item | count |
| --- | ---: |
| `candidateSubchunks` | `10` |
| `secondDerivativeEnvelopePasses` | `0` |
| `secondDerivativeEnvelopeFails` | `10` |
| `sampledEnvelopePasses` | `9` |
| `sampledEnvelopeFails` | `1` |
| `rawPolyEnvelopePasses` | `0` |
| `rawPolyEnvelopeFails` | `10` |
| `intervalEnvelopePasses` | `0` |
| `intervalEnvelopeFails` | `10` |
| `jetFiniteCoverEnvelopePasses` | `0` |
| `jetFiniteCoverEnvelopeFails` | `10` |
| `proofSafeClosedFields` | `0` |
| `candidateFieldsForDerivativeIntervalFiniteCover` | `140` |
| `candidateFieldsForDerivativeSecondDerivativeSingleCover` | `120` |
| `candidateFieldsForDerivativeRawPolyIntervalSingleCover` | `150` |
| `candidateFieldsForResidualJetFiniteCover` | `9600` |

## Worst Envelope

- subchunk: `0`
- mesh: `5.000000000000000000E-1`
- sample radius: `6.244175561580000000E-19`
- sampled derivative lower: `-8.632248343720000000E-19`
- sampled derivative upper: `1.496707919400000000E-19`
- interval finite-cover cells: `1`
- residual-jet finite-cover cells: `64`
- residual-jet split: `64`
- anchor derivative residual: `2.139760444269051268E-19`
- deriv sample radius: `2.353736488700000000E-19`
- second derivative residual sampled max: `3.205691955046852706E-18`
- residual-jet cover slope: `7.497408868047512194E-7`
- residual-jet envelope excess: `3.748704434020000273E-7`
- residual-jet max second derivative residual: `7.931143265370764442E-5`
- deriv slope: `8.724257591907840886E-5`
- second-derivative-derived slope: `4.362128795953943981E-5`
- best second derivative split: `64`
- second derivative envelope excess: `2.181064397976934432E-5`
- raw/poly derivative lower: `-1.466979845678868209E-3`
- raw/poly derivative upper: `1.466979845678867653E-3`
- sampled slope: `8.632248343720000000E-19`
- raw/poly slope: `1.613677830246755030E-3`
- interval slope: `1.888698284462069806E-3`
- best split: `64`
- sampled envelope excess: `5.602997334400000000E-20`
- raw/poly envelope excess: `8.068389151233771395E-4`
- interval envelope excess: `9.443491422310345276E-4`

## Worst Active Candidate Cell

| cell | left | right | deriv lower | deriv upper | lower abs | upper abs |
| ---: | ---: | ---: | ---: | ---: | :---: | :---: |
| 0 | `1.000000000000000000E+1` | `1.100000000000000000E+1` | `-8.632248343720000000E-19` | `1.496707919400000000E-19` | `True` | `True` |

## Worst Residual-Jet Candidate Cells

| cell | left | right | anchor | deriv lower | deriv upper | deriv slope | lower abs | upper abs |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :---: |
| 0 | `1.000000000000000000E+1` | `1.001562500000000000E+1` | `1.000781250000000000E+1` | `-6.113843195380266977E-7` | `6.113843195382810703E-7` | `7.825719290088206917E-5` | `True` | `True` |
| 1 | `1.001562500000000000E+1` | `1.003125000000000000E+1` | `1.002343750000000000E+1` | `-5.955519822290943203E-7` | `5.955519822293155831E-7` | `7.623065372533681773E-5` | `True` | `True` |
| 2 | `1.003125000000000000E+1` | `1.004687500000000000E+1` | `1.003906250000000000E+1` | `-5.797459210833430803E-7` | `5.797459210835339667E-7` | `7.420747789867890933E-5` | `True` | `True` |
| 3 | `1.004687500000000000E+1` | `1.006250000000000000E+1` | `1.005468750000000000E+1` | `-5.639578016322170681E-7` | `5.639578016323798211E-7` | `7.218659860893315929E-5` | `True` | `True` |
| 4 | `1.006250000000000000E+1` | `1.007812500000000000E+1` | `1.007031250000000000E+1` | `-5.601746357922728812E-7` | `5.601746357924093266E-7` | `7.170235338141878805E-5` | `True` | `True` |
| 5 | `1.007812500000000000E+1` | `1.009375000000000000E+1` | `1.008593750000000000E+1` | `-5.707352732375147124E-7` | `5.707352732376263231E-7` | `7.305411497440831196E-5` | `True` | `True` |
| 6 | `1.009375000000000000E+1` | `1.010937500000000000E+1` | `1.010156250000000000E+1` | `-5.809974494839350901E-7` | `5.809974494840230411E-7` | `7.436767353394875751E-5` | `True` | `True` |
| 7 | `1.010937500000000000E+1` | `1.012500000000000000E+1` | `1.011718750000000000E+1` | `-5.910624334425903654E-7` | `5.910624334426555824E-7` | `7.565599148065532327E-5` | `True` | `True` |

## First Residual-Jet Finite-Cover Failures

| subchunk | cells | cover slope | envelope excess |
| ---: | ---: | ---: | ---: |
| 0 | `64` | `7.497408868047512194E-7` | `3.748704434020000273E-7` |
| 1 | `64` | `6.210816748771816630E-7` | `3.105408374382687250E-7` |
| 2 | `64` | `4.133719082872473833E-7` | `2.066859541432291340E-7` |
| 3 | `64` | `2.164796057153595554E-7` | `1.082398028572381361E-7` |
| 4 | `64` | `1.036197948987245497E-7` | `5.180989744855882672E-8` |
| 5 | `64` | `1.837513245359604931E-7` | `9.187566226726375238E-8` |
| 6 | `64` | `2.257300562368359593E-7` | `1.128650281175681977E-7` |
| 7 | `64` | `2.959566975210704663E-7` | `1.479783487602304546E-7` |
| 8 | `64` | `3.962563402734263725E-7` | `1.981281701361322601E-7` |
| 9 | `64` | `4.411382864814999132E-7` | `2.205691432401767454E-7` |

## First Second-Derivative Failures

| subchunk | deriv sample radius | deriv slope | derived slope | envelope excess | best split |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | `2.353736488700000000E-19` | `8.724257591907840886E-5` | `4.362128795953943981E-5` | `2.181064397976934432E-5` | `64` |
| 1 | `2.956177785730000000E-19` | `7.227132216746514066E-5` | `3.613566108373286595E-5` | `1.806783054186611087E-5` | `64` |
| 2 | `2.334660611990000000E-19` | `4.810145841887042717E-5` | `2.405072920943544705E-5` | `1.202536460471732897E-5` | `64` |
| 3 | `7.526578516200000000E-20` | `2.519035411954685634E-5` | `1.259517705977350343E-5` | `6.297588529886310075E-6` | `64` |
| 4 | `2.710746718370000000E-19` | `1.205757613360435790E-5` | `6.028788066802450025E-6` | `3.014394033400421565E-6` | `64` |
| 5 | `7.466184519000000000E-20` | `2.138197230959212910E-5` | `1.069098615479613921E-5` | `5.345493077397353111E-6` | `64` |
| 6 | `1.796216054750000000E-19` | `2.626677018025094835E-5` | `1.313338509012565380E-5` | `6.566692545061977116E-6` | `64` |
| 7 | `3.448574814590000000E-19` | `3.443859752968380574E-5` | `1.721929876484224773E-5` | `8.609649382420819086E-6` | `64` |
| 8 | `2.886915154530000000E-19` | `4.610982868630815447E-5` | `2.305491434315436592E-5` | `1.152745717157660204E-5` | `64` |
| 9 | `8.684453006700000000E-20` | `5.133245515417981627E-5` | `2.566622757708999498E-5` | `1.283311378854442428E-5` | `64` |

## First Sampled Failures

| subchunk | sample radius | sampled slope | sampled envelope excess |
| ---: | ---: | ---: | ---: |
| 0 | `6.244175561580000000E-19` | `8.632248343720000000E-19` | `5.602997334400000000E-20` |

## First Raw/Poly Failures

| subchunk | sample radius | raw/poly slope | raw/poly envelope excess |
| ---: | ---: | ---: | ---: |
| 0 | `6.244175561580000000E-19` | `1.613677830246755030E-3` | `8.068389151233771395E-4` |
| 1 | `6.778935083060000000E-19` | `1.308316497851998968E-3` | `6.541582489259991617E-4` |
| 2 | `6.054423277480000000E-19` | `1.042222491033471143E-3` | `5.211112455167351769E-4` |
| 3 | `5.583583945920000000E-19` | `8.079183434235511905E-4` | `4.039591717117751536E-4` |
| 4 | `1.965518510090000000E-19` | `6.007283516108795919E-4` | `3.003641758054389925E-4` |
| 5 | `2.835058206020000000E-19` | `5.033150918162246916E-4` | `2.516575459081116293E-4` |
| 6 | `1.502180901320000000E-19` | `5.040340264907223660E-4` | `2.520170132453603332E-4` |
| 7 | `6.952213961820000000E-19` | `5.014250242730660972E-4` | `2.507125121365327438E-4` |
| 8 | `4.190738463940000000E-19` | `4.907315552725744192E-4` | `2.453657776362866287E-4` |
| 9 | `4.267888158240000000E-19` | `4.731555942794137599E-4` | `2.365777971397063067E-4` |

## First Interval Failures

| subchunk | sample radius | interval slope | interval envelope excess | best split |
| ---: | ---: | ---: | ---: | ---: |
| 0 | `6.244175561580000000E-19` | `1.888698284462069806E-3` | `9.443491422310345276E-4` | `64` |
| 1 | `6.778935083060000000E-19` | `1.930411219918016179E-3` | `9.652056099590077675E-4` | `64` |
| 2 | `6.054423277480000000E-19` | `1.930105292145992102E-3` | `9.650526460729956562E-4` | `64` |
| 3 | `5.583583945920000000E-19` | `1.792747682743737641E-3` | `8.963738413718683790E-4` | `64` |
| 4 | `1.965518510090000000E-19` | `1.500680764160231193E-3` | `7.503403820801147933E-4` | `64` |
| 5 | `2.835058206020000000E-19` | `1.271706546591322185E-3` | `6.358532732956603760E-4` | `64` |
| 6 | `1.502180901320000000E-19` | `1.119529199574384945E-3` | `5.597645997871916228E-4` | `64` |
| 7 | `6.952213961820000000E-19` | `9.787620019346999202E-4` | `4.893810009673496553E-4` | `64` |
| 8 | `4.190738463940000000E-19` | `1.105149165655512785E-3` | `5.525745828277558114E-4` | `64` |
| 9 | `4.267888158240000000E-19` | `1.029925750995784821E-3` | `5.149628754978918371E-4` | `64` |

## Guard

- do not emit Lean from derivative audit alone
- active route is the residual-jet derivative finite-cover receiver
- second-derivative interval candidates are rejected route-comparison data
- sampled derivative cells are candidates, not Lean proofs
- proof-producing emitters should target hDerivAnchorLower/hDerivAnchorUpper and hResidualSecondDerivBoundOnCell
- raw/poly derivative diagnostics are route comparison only
- if envelope fails, reduce mesh/increase degree/recompute remainder before payload generation
- if sampled feasibility holds, next target is a proof-producing local derivative-residual emitter
