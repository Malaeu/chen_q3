# Step33A.1-A Refined Subchunk Derivative Bound Audit

Diagnostic derivative audit.  This is not Lean proof data.

## Verdict

- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
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
| `sampledEnvelopePasses` | `10` |
| `sampledEnvelopeFails` | `0` |
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
- sample radius: `1.430000000000000000E-28`
- sampled derivative lower: `-4.331000000000000000E-27`
- sampled derivative upper: `2.248200000000000000E-26`
- interval finite-cover cells: `1`
- residual-jet finite-cover cells: `64`
- residual-jet split: `64`
- anchor derivative residual: `1.094873170602930519E-30`
- deriv sample radius: `2.000000000000000000E-30`
- second derivative residual sampled max: `2.215199839610626668E-24`
- residual-jet cover slope: `7.497408868045860860E-7`
- residual-jet envelope excess: `3.748704434022930430E-7`
- residual-jet max second derivative residual: `7.931143265370828018E-5`
- deriv slope: `8.724257591907910819E-5`
- second-derivative-derived slope: `4.362128795953955410E-5`
- best second derivative split: `64`
- second derivative envelope excess: `2.181064397976977705E-5`
- raw/poly derivative lower: `-1.466979845678868359E-3`
- raw/poly derivative upper: `1.466979845678868359E-3`
- sampled slope: `2.248200000000000000E-26`
- raw/poly slope: `1.613677830246755195E-3`
- interval slope: `1.888698284462070026E-3`
- best split: `64`
- sampled envelope excess: `0.000000000000000000E-29`
- raw/poly envelope excess: `8.068389151233775974E-4`
- interval envelope excess: `9.443491422310350130E-4`

## Worst Active Candidate Cell

| cell | left | right | deriv lower | deriv upper | lower abs | upper abs |
| ---: | ---: | ---: | ---: | ---: | :---: | :---: |
| 0 | `1.000000000000000000E+1` | `1.100000000000000000E+1` | `-4.331000000000000000E-27` | `2.248200000000000000E-26` | `True` | `True` |

## Worst Residual-Jet Candidate Cells

| cell | left | right | anchor | deriv lower | deriv upper | deriv slope | lower abs | upper abs |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :---: |
| 0 | `1.000000000000000000E+1` | `1.001562500000000000E+1` | `1.000781250000000000E+1` | `-6.113843195381506971E-7` | `6.113843195381506971E-7` | `7.825719290088328922E-5` | `True` | `True` |
| 1 | `1.001562500000000000E+1` | `1.003125000000000000E+1` | `1.002343750000000000E+1` | `-5.955519822292025936E-7` | `5.955519822292025936E-7` | `7.623065372533793198E-5` | `True` | `True` |
| 2 | `1.003125000000000000E+1` | `1.004687500000000000E+1` | `1.003906250000000000E+1` | `-5.797459220604332652E-7` | `5.797459220604332652E-7` | `7.420747802373545795E-5` | `True` | `True` |
| 3 | `1.004687500000000000E+1` | `1.006250000000000000E+1` | `1.005468750000000000E+1` | `-5.639578016322977750E-7` | `5.639578016322977750E-7` | `7.218659860893411520E-5` | `True` | `True` |
| 4 | `1.006250000000000000E+1` | `1.007812500000000000E+1` | `1.007031250000000000E+1` | `-5.601746357923412989E-7` | `5.601746357923412989E-7` | `7.170235338141968625E-5` | `True` | `True` |
| 5 | `1.007812500000000000E+1` | `1.009375000000000000E+1` | `1.008593750000000000E+1` | `-5.707352732375715927E-7` | `5.707352732375715927E-7` | `7.305411497440916387E-5` | `True` | `True` |
| 6 | `1.009375000000000000E+1` | `1.010937500000000000E+1` | `1.010156250000000000E+1` | `-5.809974494839810368E-7` | `5.809974494839810368E-7` | `7.436767353394957271E-5` | `True` | `True` |
| 7 | `1.010937500000000000E+1` | `1.012500000000000000E+1` | `1.011718750000000000E+1` | `-5.910624334426258575E-7` | `5.910624334426258575E-7` | `7.565599148065610976E-5` | `True` | `True` |

## First Residual-Jet Finite-Cover Failures

| subchunk | cells | cover slope | envelope excess |
| ---: | ---: | ---: | ---: |
| 0 | `64` | `7.497408868045860860E-7` | `3.748704434022930430E-7` |
| 1 | `64` | `6.210816748766588284E-7` | `3.105408374383294142E-7` |
| 2 | `64` | `4.133719082871748797E-7` | `2.066859541435874398E-7` |
| 3 | `64` | `2.164796057148410152E-7` | `1.082398028574205076E-7` |
| 4 | `64` | `1.036197948981550548E-7` | `5.180989744907752738E-8` |
| 5 | `64` | `1.837513248042498249E-7` | `9.187566240212491246E-8` |
| 6 | `64` | `2.257300565052132292E-7` | `1.128650282526066146E-7` |
| 7 | `64` | `2.959566980580765990E-7` | `1.479783490290382995E-7` |
| 8 | `64` | `3.962563402729657102E-7` | `1.981281701364828551E-7` |
| 9 | `64` | `4.411382864812308020E-7` | `2.205691432406154010E-7` |

## First Second-Derivative Failures

| subchunk | deriv sample radius | deriv slope | derived slope | envelope excess | best split |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | `2.000000000000000000E-30` | `8.724257591907910819E-5` | `4.362128795953955410E-5` | `2.181064397976977705E-5` | `64` |
| 1 | `1.000000000000000000E-30` | `7.227132216746575458E-5` | `3.613566108373287729E-5` | `1.806783054186643865E-5` | `64` |
| 2 | `1.000000000000000000E-30` | `4.810145841887125873E-5` | `2.405072920943562936E-5` | `1.202536460471781468E-5` | `64` |
| 3 | `1.000000000000000000E-30` | `2.519035411954513631E-5` | `1.259517705977256815E-5` | `6.297588529886284077E-6` | `64` |
| 4 | `1.000000000000000000E-30` | `1.205757613360349728E-5` | `6.028788066801748640E-6` | `3.014394033400874320E-6` | `64` |
| 5 | `1.000000000000000000E-30` | `2.138197234085816144E-5` | `1.069098617042908072E-5` | `5.345493085214540361E-6` | `64` |
| 6 | `1.000000000000000000E-30` | `2.626677021151572122E-5` | `1.313338510575786061E-5` | `6.566692552878930305E-6` | `64` |
| 7 | `1.000000000000000000E-30` | `3.443859759221254970E-5` | `1.721929879610627485E-5` | `8.609649398053137425E-6` | `64` |
| 8 | `1.000000000000000000E-30` | `4.610982868630873718E-5` | `2.305491434315436859E-5` | `1.152745717157718430E-5` | `64` |
| 9 | `1.000000000000000000E-30` | `5.133245515417958423E-5` | `2.566622757708979211E-5` | `1.283311378854489606E-5` | `64` |

## First Raw/Poly Failures

| subchunk | sample radius | raw/poly slope | raw/poly envelope excess |
| ---: | ---: | ---: | ---: |
| 0 | `1.430000000000000000E-28` | `1.613677830246755195E-3` | `8.068389151233775974E-4` |
| 1 | `2.900000000000000000E-29` | `1.308316497851998709E-3` | `6.541582489259993546E-4` |
| 2 | `8.000000000000000000E-30` | `1.042222491033471071E-3` | `5.211112455167355353E-4` |
| 3 | `2.000000000000000000E-30` | `8.079183434235506717E-4` | `4.039591717117753359E-4` |
| 4 | `1.000000000000000000E-30` | `6.007283516108791258E-4` | `3.003641758054395629E-4` |
| 5 | `1.000000000000000000E-30` | `5.033150918162248270E-4` | `2.516575459081124135E-4` |
| 6 | `1.000000000000000000E-30` | `5.040340264907216888E-4` | `2.520170132453608444E-4` |
| 7 | `1.000000000000000000E-30` | `5.014250242730664388E-4` | `2.507125121365332194E-4` |
| 8 | `1.000000000000000000E-30` | `4.907315552725743369E-4` | `2.453657776362871685E-4` |
| 9 | `1.000000000000000000E-30` | `4.731555942794139470E-4` | `2.365777971397069735E-4` |

## First Interval Failures

| subchunk | sample radius | interval slope | interval envelope excess | best split |
| ---: | ---: | ---: | ---: | ---: |
| 0 | `1.430000000000000000E-28` | `1.888698284462070026E-3` | `9.443491422310350130E-4` | `64` |
| 1 | `2.900000000000000000E-29` | `1.930411219918015747E-3` | `9.652056099590078737E-4` | `64` |
| 2 | `8.000000000000000000E-30` | `1.930105292145992427E-3` | `9.650526460729962137E-4` | `64` |
| 3 | `2.000000000000000000E-30` | `1.792747682743738099E-3` | `8.963738413718690497E-4` | `64` |
| 4 | `1.000000000000000000E-30` | `1.500680764160230893E-3` | `7.503403820801154466E-4` | `64` |
| 5 | `1.000000000000000000E-30` | `1.271706546591322210E-3` | `6.358532732956611051E-4` | `64` |
| 6 | `1.000000000000000000E-30` | `1.119529199574385032E-3` | `5.597645997871925162E-4` | `64` |
| 7 | `1.000000000000000000E-30` | `9.787620029351445054E-4` | `4.893810014675722527E-4` | `64` |
| 8 | `1.000000000000000000E-30` | `1.105149165655513152E-3` | `5.525745828277565760E-4` | `64` |
| 9 | `1.000000000000000000E-30` | `1.029925750995784862E-3` | `5.149628754978924308E-4` | `64` |

## Guard

- do not emit Lean from derivative audit alone
- active route is the residual-jet derivative finite-cover receiver
- second-derivative interval candidates are rejected route-comparison data
- sampled derivative cells are candidates, not Lean proofs
- proof-producing emitters should target hDerivAnchorLower/hDerivAnchorUpper and hResidualSecondDerivBoundOnCell
- raw/poly derivative diagnostics are route comparison only
- if envelope fails, reduce mesh/increase degree/recompute remainder before payload generation
- if sampled feasibility holds, next target is a proof-producing local derivative-residual emitter
