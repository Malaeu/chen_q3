# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 26
- cells with sampled feasible degree: 8
- degrees: `12,16`
- fit samples: 25
- check samples: 81

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 12 | `2.026612037330755698e-32` | `8.469858707133606145e-36` | 4 |
| 16 | `1.491302718882754577e-35` | `1.271109954575304252e-35` | 4 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_tail` | 0 | `0.00` | 0 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 1 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 2 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 3 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 4 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 5 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 6 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 7 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 8 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 9 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 10 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 11 | `12,16` | 12 |
| `primary_tail` | 0 | `0.00` | 12 | `16` | 16 |
| `primary_tail` | 0 | `0.00` | 13 | `16` | 16 |
| `primary_tail` | 0 | `0.00` | 14 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 15 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 16 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 17 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 18 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 19 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 20 | `-` | 16 |
| `primary_tail` | 0 | `0.00` | 21 | `16` | 16 |
| `primary_tail` | 0 | `0.00` | 22 | `16` | 16 |
| `primary_tail` | 0 | `0.00` | 23 | `16` | 16 |
| `primary_tail` | 0 | `0.00` | 24 | `12,16` | 12 |
| `primary_tail` | 0 | `0.00` | 25 | `16` | 16 |

## Best Degree Details

### primary_tail row 0 chunk 0

- chunk interval: `[1.088613911944200701E-29, 1.088613911944221150E-29]`
- degree: `16`
- sampled max residual: `6.246091722942866619e-40`
- remainder candidate: `6.870710895237153830e-40`
- lower model integral: `1.088613911260945625e-29`
- upper model integral: `1.088613912635087766e-29`
- current chunk width: `2.044899999999999842e-43`
- model interval width: `1.374142140865280711e-38`
- extra chunk width needed: `1.374121691865280689e-38`
- lower margin: `-6.832550544545910136e-39`
- upper margin: `-6.908666274531105550e-39`
- required remainder cap: `-3.795557020470199391e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.809089250273719496e-44` | `0.000000000000000000e+00` | `2.242077542919707313e-44` | `sampled_feasible` |
| 16 | 10 | `9.388699710976274375e-44` | `0.000000000000000000e+00` | `2.242077542919707313e-44` | `sampled_feasible` |

### primary_tail row 0 chunk 1

- chunk interval: `[7.162922067052422385E-26, 7.162922067052422487E-26]`
- degree: `16`
- sampled max residual: `1.107765672405768989e-39`
- remainder candidate: `1.218543239646345878e-39`
- lower model integral: `7.162922067051234715e-26`
- upper model integral: `7.162922067053672947e-26`
- current chunk width: `1.019999999999999940e-42`
- model interval width: `2.438232422994666667e-38`
- extra chunk width needed: `2.438130422994666876e-38`
- lower margin: `-1.188121731544011300e-38`
- upper margin: `-1.250110691450655367e-38`
- required remainder cap: `-3.099447995332203594e-41`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.362186067504582549e-40` | `4.351986067504582266e-40` | `8.609577764811676084e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.739718509874450723e-40` | `5.729518509874450440e-40` | `1.090546516876145637e-40` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 2

- chunk interval: `[1.174784504455502726E-23, 1.174784504455502726E-23]`
- degree: `16`
- sampled max residual: `1.348833849820495920e-38`
- remainder candidate: `1.483717334802545455e-38`
- lower model integral: `1.174784504455488192e-23`
- upper model integral: `1.174784504455517873e-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.968123235826275958e-37`
- extra chunk width needed: `2.968123235826275958e-37`
- lower margin: `-1.454674259142580791e-37`
- upper margin: `-1.513448976683695167e-37`
- required remainder cap: `-2.938735877055718933e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `5.142787784847507847e-38` | `5.142787784847507847e-38` | `6.612155723375367232e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `9.257018012725514125e-38` | `9.257018012725514125e-38` | `1.836709923159824231e-38` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 3

- chunk interval: `[2.109279318875671532E-22, 2.109279318875671532E-22]`
- degree: `16`
- sampled max residual: `8.228460455756012556e-38`
- remainder candidate: `9.051306601331614747e-38`
- lower model integral: `2.109279318875662764e-22`
- upper model integral: `2.109279318875681101e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.833771187282768512e-36`
- extra chunk width needed: `1.833771187282768512e-36`
- lower margin: `-8.698658196084927559e-37`
- upper margin: `-9.639053676742757565e-37`
- required remainder cap: `-4.701977403289150293e-39`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.639053676742757565e-37` | `9.639053676742757565e-37` | `7.052966104933725048e-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.551652543085419511e-36` | `1.551652543085419511e-36` | `1.469367938527859385e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 4

- chunk interval: `[7.464841416472772846E-22, 7.464841416472772846E-22]`
- degree: `16`
- sampled max residual: `2.292213984103460641e-37`
- remainder candidate: `2.521435392513807111e-37`
- lower model integral: `7.464841416472748329e-22`
- upper model integral: `7.464841416472799110e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.078135595552282034e-36`
- extra chunk width needed: `5.078135595552282034e-36`
- lower margin: `-2.445028249710358017e-36`
- upper margin: `-2.633107345841924018e-36`
- required remainder cap: `-9.403954806578300586e-39`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.385423730368188023e-36` | `3.385423730368188023e-36` | `2.233439266562346265e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.078135595552282034e-36` | `5.078135595552282034e-36` | `3.056285312137947521e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 5

- chunk interval: `[6.632731636340872877E-22, 6.632731636340872877E-22]`
- degree: `16`
- sampled max residual: `2.233439266562346265e-37`
- remainder candidate: `2.456783203218581215e-37`
- lower model integral: `6.632731636340848289e-22`
- upper model integral: `6.632731636340897190e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.890056499420716033e-36`
- extra chunk width needed: `4.890056499420716033e-36`
- lower margin: `-2.445028249710358017e-36`
- upper margin: `-2.445028249710358017e-36`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.385423730368188023e-36` | `3.385423730368188023e-36` | `2.233439266562346265e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.701977403289150032e-36` | `4.701977403289150032e-36` | `3.408933617384633773e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 6

- chunk interval: `[1.562922755943454187E-22, 1.562922755943454187E-22]`
- degree: `16`
- sampled max residual: `1.175494350822287508e-37`
- remainder candidate: `1.293043795904516331e-37`
- lower model integral: `1.562922755943442331e-22`
- upper model integral: `1.562922755943468192e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.586087571809032518e-36`
- extra chunk width needed: `2.586087571809032518e-36`
- lower margin: `-1.175494350822287508e-36`
- upper margin: `-1.410593220986745010e-36`
- required remainder cap: `-1.175494350822287508e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.347669494440352543e-37` | `6.347669494440352543e-37` | `7.052966104933725048e-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.222514124855179008e-36` | `1.222514124855179008e-36` | `1.057944915740058757e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 7

- chunk interval: `[8.856206616415421738E-24, 8.856206616415421738E-24]`
- degree: `16`
- sampled max residual: `7.714181677271261771e-39`
- remainder candidate: `8.485600844998387905e-39`
- lower model integral: `8.856206616415339567e-24`
- upper model integral: `8.856206616415510014e-24`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.704466808692316887e-37`
- extra chunk width needed: `1.704466808692316887e-37`
- lower margin: `-8.228460455756012556e-38`
- upper margin: `-8.816207631167156310e-38`
- required remainder cap: `-2.938735877055718933e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.555040609436364093e-38` | `4.555040609436364093e-38` | `6.979497708007332079e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.877471754111437540e-38` | `5.877471754111437540e-38` | `1.212228549285483993e-38` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 8

- chunk interval: `[8.959177851417245136E-26, 8.959177851417245137E-26]`
- degree: `16`
- sampled max residual: `6.737218808719428506e-40`
- remainder candidate: `7.410950689591370927e-40`
- lower model integral: `8.959177851416514162e-26`
- upper model integral: `8.959177851417997306e-26`
- current chunk width: `9.999999999999999530e-45`
- model interval width: `1.483143262951558067e-38`
- extra chunk width needed: `1.483142262951558110e-38`
- lower margin: `-7.312401381580050220e-39`
- upper margin: `-7.519031247935530446e-39`
- required remainder cap: `-1.033149331777401156e-41`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.476980437702071564e-40` | `4.476880437702071785e-40` | `8.035605913824231012e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.920811543626741997e-40` | `7.920711543626741403e-40` | `1.664518367863590710e-40` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 9

- chunk interval: `[8.140234144392528233E-29, 8.140234144400148171E-29]`
- degree: `16`
- sampled max residual: `8.316986645460654279e-41`
- remainder candidate: `9.148785310006719894e-41`
- lower model integral: `8.140234144305185446e-29`
- upper model integral: `8.140234144488161394e-29`
- current chunk width: `7.619937999999999770e-41`
- model interval width: `1.829759482776773139e-39`
- extra chunk width needed: `1.753560102776773069e-39`
- lower margin: `-8.734237276198011810e-40`
- upper margin: `-8.801275394731311059e-40`
- required remainder cap: `3.475220191525546336e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.596258962985399993e-43` | `0.000000000000000000e+00` | `1.008934894313868291e-43` | `sampled_feasible` |
| 16 | 10 | `6.838336505905107306e-43` | `0.000000000000000000e+00` | `2.017869788627736582e-43` | `sampled_feasible` |

### primary_tail row 0 chunk 10

- chunk interval: `[1.140827387352955264E-33, 1.140827387524570999E-33]`
- degree: `16`
- sampled max residual: `5.577400626066248784e-43`
- remainder candidate: `6.145140688672874011e-43`
- lower model integral: `1.140827381196888040e-33`
- upper model integral: `1.140827393487169516e-33`
- current chunk width: `1.716157350000000034e-43`
- model interval width: `1.229028147570464199e-41`
- extra chunk width needed: `1.211866574070464210e-41`
- lower margin: `-6.156067171044119336e-42`
- upper margin: `-5.962598520186918374e-42`
- required remainder cap: `-1.092643319179834232e-45`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000784621316120038e-44` | `0.000000000000000000e+00` | `2.736911063134408342e-48` | `sampled_feasible` |
| 16 | 10 | `2.000647775762963318e-44` | `0.000000000000000000e+00` | `2.052683297350806256e-48` | `sampled_feasible` |

### primary_tail row 0 chunk 11

- chunk interval: `[-8.837748021078401890E-42, 8.837748021079727269E-42]`
- degree: `12`
- sampled max residual: `5.818054961928663096e-45`
- remainder candidate: `7.399860458121529234e-45`
- lower model integral: `1.703830119809496630e-43`
- upper model integral: `3.183802211433802328e-43`
- current chunk width: `1.767549604215812916e-41`
- model interval width: `1.479972091624305697e-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `9.008131033059352034e-42`
- upper margin: `8.519367799936347591e-42`
- required remainder cap: `8.593366404517562039e-43`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000000000267761069e-44` | `0.000000000000000000e+00` | `1.033757341133848283e-54` | `sampled_feasible` |
| 16 | 10 | `2.000000000000320765e-44` | `0.000000000000000000e+00` | `1.433782720019207049e-57` | `sampled_feasible` |

### primary_tail row 0 chunk 12

- chunk interval: `[3.059912354327532428E-37, 3.060735573364219415E-37]`
- degree: `16`
- sampled max residual: `3.846778363002033582e-45`
- remainder candidate: `5.231456199302236893e-45`
- lower model integral: `3.060323433328028319e-37`
- upper model integral: `3.060324479619267962e-37`
- current chunk width: `8.232190366869870071e-41`
- model interval width: `1.046291239643038748e-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.110790004960740529e-41`
- upper margin: `4.110937449512698135e-41`
- required remainder cap: `4.116021461158955978e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000000227516630871e-44` | `0.000000000000000000e+00` | `8.352389719038111394e-52` | `sampled_feasible` |
| 16 | 10 | `2.000000256749994888e-44` | `0.000000000000000000e+00` | `1.002286766284573367e-51` | `sampled_feasible` |

### primary_tail row 0 chunk 13

- chunk interval: `[1.154864319132177578E-31, 1.154864321102527489E-31]`
- degree: `16`
- sampled max residual: `1.898885281320803316e-43`
- remainder candidate: `2.098773809452883918e-43`
- lower model integral: `1.154864320096257290e-31`
- upper model integral: `1.154864320138232747e-31`
- current chunk width: `1.970349911000000179e-40`
- model interval width: `4.197545759307979385e-42`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `9.640797683766009981e-41`
- upper margin: `9.642947801097208372e-41`
- required remainder cap: `9.850674971731408696e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.064725706028597653e-44` | `0.000000000000000000e+00` | `1.751623080406021339e-46` | `sampled_feasible` |
| 16 | 10 | `2.073483821430627760e-44` | `0.000000000000000000e+00` | `1.423193752829892338e-46` | `sampled_feasible` |

### primary_tail row 0 chunk 14

- chunk interval: `[1.466836656785285560E-28, 1.466836656785516390E-28]`
- degree: `16`
- sampled max residual: `2.242077542919707313e-42`
- remainder candidate: `2.467285297211678255e-42`
- lower model integral: `1.466836656785155361e-28`
- upper model integral: `1.466836656785648618e-28`
- current chunk width: `2.308299999999999999e-41`
- model interval width: `4.932570594423356090e-41`
- extra chunk width needed: `2.624270594423356091e-41`
- lower margin: `-1.302647052436349949e-41`
- upper margin: `-1.322825750322627315e-41`
- required remainder cap: `1.143459546889050730e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.968310171678829254e-43` | `0.000000000000000000e+00` | `1.793662034335765851e-43` | `sampled_feasible` |
| 16 | 10 | `9.865141188846712179e-43` | `0.000000000000000000e+00` | `1.681558157189780485e-43` | `sampled_feasible` |

### primary_tail row 0 chunk 15

- chunk interval: `[1.039353807274181180E-26, 1.039353807274190931E-26]`
- degree: `16`
- sampled max residual: `4.394471984122626334e-42`
- remainder candidate: `4.834919182534889688e-42`
- lower model integral: `1.039353807274181422e-26`
- upper model integral: `1.039353807274191180e-26`
- current chunk width: `9.750999999999999342e-41`
- model interval width: `9.757521466786566228e-41`
- extra chunk width needed: `6.521466786566885910e-44`
- lower margin: `2.869859254937225361e-42`
- upper margin: `-2.869859254937225361e-42`
- required remainder cap: `4.591774807899560833e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `5.452732584380728186e-41` | `0.000000000000000000e+00` | `6.457183323608757063e-42` | `sampled_feasible` |
| 16 | 10 | `7.605127025583647207e-41` | `0.000000000000000000e+00` | `1.147943701974890145e-41` | `sampled_feasible` |

### primary_tail row 0 chunk 16

- chunk interval: `[1.088964554058981853E-25, 1.088964554058983101E-25]`
- degree: `16`
- sampled max residual: `3.156845180430947897e-41`
- remainder candidate: `3.472629698474043180e-41`
- lower model integral: `1.088964554058978920e-25`
- upper model integral: `1.088964554058985808e-25`
- current chunk width: `1.248000000000000052e-40`
- model interval width: `6.887662211849340867e-40`
- extra chunk width needed: `5.639662211849340407e-40`
- lower margin: `-2.984653625134714376e-40`
- upper margin: `-2.755064884739736347e-40`
- required remainder cap: `4.591774807899560833e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.362186067504582549e-40` | `3.114186067504582497e-40` | `4.017802956912115506e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.117250952244318896e-40` | `5.869250952244318436e-40` | `6.313690360861895795e-41` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 17

- chunk interval: `[2.540430612489620270E-25, 2.540430612489620418E-25]`
- degree: `16`
- sampled max residual: `2.582873329443502825e-41`
- remainder candidate: `2.841260662387853294e-41`
- lower model integral: `2.540430612489615970e-25`
- upper model integral: `2.540430612489621480e-25`
- current chunk width: `1.480000000000000075e-41`
- model interval width: `5.510129769479472694e-40`
- extra chunk width needed: `5.362129769479472890e-40`
- lower margin: `-4.132597327109604520e-40`
- upper margin: `-9.183549615799121156e-41`
- required remainder cap: `-1.377532442369868122e-41`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.147943701974890145e-39` | `1.133143701974890083e-39` | `7.174648137343063403e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.066298663554802260e-39` | `2.051498663554802361e-39` | `1.234039479623006905e-40` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 18

- chunk interval: `[1.540147041358927228E-25, 1.540147041358927315E-25]`
- degree: `16`
- sampled max residual: `5.165746658887005650e-41`
- remainder candidate: `5.682421324775705994e-41`
- lower model integral: `1.540147041358921912e-25`
- upper model integral: `1.540147041358933391e-25`
- current chunk width: `8.699999999999999579e-42`
- model interval width: `1.147943701974890145e-39`
- extra chunk width needed: `1.139243701974890133e-39`
- lower margin: `-5.280541029084494665e-40`
- upper margin: `-5.969307250269428751e-40`
- required remainder cap: `-2.295887403949780416e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.346839692639296925e-40` | `7.259839692639296814e-40` | `5.739718509874450723e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.056108205816898933e-39` | `1.047408205816898922e-39` | `9.757521466786566228e-41` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 19

- chunk interval: `[2.405481629996556414E-26, 2.405481629996558583E-26]`
- degree: `16`
- sampled max residual: `1.506676108842043315e-41`
- remainder candidate: `1.657443719726247833e-41`
- lower model integral: `2.405481629996542602e-26`
- upper model integral: `2.405481629996575892e-26`
- current chunk width: `2.168999999999999972e-41`
- model interval width: `3.329036735727181419e-40`
- extra chunk width needed: `3.112136735727181447e-40`
- lower margin: `-1.377532442369868173e-40`
- upper margin: `-1.721915552962335217e-40`
- required remainder cap: `-5.739718509874451041e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.757521466786566228e-41` | `7.588521466786566511e-41` | `1.004450739228028876e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.894107108258568738e-40` | `1.677207108258568767e-40` | `2.295887403949780289e-41` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_tail row 0 chunk 20

- chunk interval: `[8.147318881491188501E-28, 8.147318881491492156E-28]`
- degree: `16`
- sampled max residual: `2.017869788627736582e-42`
- remainder candidate: `2.220656767490510451e-42`
- lower model integral: `8.147318881491122630e-28`
- upper model integral: `8.147318881491567458e-28`
- current chunk width: `3.036550000000000020e-41`
- model interval width: `4.448281845152699310e-41`
- extra chunk width needed: `1.411731845152699290e-41`
- lower margin: `-6.636549527042333648e-42`
- upper margin: `-7.533380544210216573e-42`
- required remainder cap: `1.470802868155327870e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.125422678972261457e-42` | `0.000000000000000000e+00` | `6.277817120175180478e-43` | `sampled_feasible` |
| 16 | 10 | `7.354014340776639988e-42` | `0.000000000000000000e+00` | `1.345246525751824388e-42` | `sampled_feasible` |

### primary_tail row 0 chunk 21

- chunk interval: `[3.897019935837682468E-30, 3.897019935848419416E-30]`
- degree: `16`
- sampled max residual: `1.607989987812727589e-43`
- remainder candidate: `1.778788986594000378e-43`
- lower model integral: `3.897019935841269008e-30`
- upper model integral: `3.897019935844826905e-30`
- current chunk width: `1.073694800000000012e-41`
- model interval width: `3.557896800920710543e-42`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `3.586623419439369293e-42`
- upper margin: `3.592228613296668561e-42`
- required remainder cap: `5.365571819899724246e-43`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.923635700109487799e-44` | `0.000000000000000000e+00` | `4.203895392974451213e-45` | `sampled_feasible` |
| 16 | 10 | `5.535128934083027430e-44` | `0.000000000000000000e+00` | `8.057466169867698158e-45` | `sampled_feasible` |

### primary_tail row 0 chunk 22

- chunk interval: `[9.619205939759073932E-34, 9.619207532651919918E-34]`
- degree: `16`
- sampled max residual: `5.300090410645313046e-45`
- remainder candidate: `6.830099451709844926e-45`
- lower model integral: `9.619206735526519236e-34`
- upper model integral: `9.619206736892538917e-34`
- current chunk width: `1.592892845985999954e-40`
- model interval width: `1.366019680721014547e-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `7.957674458196164374e-41`
- upper margin: `7.957593804848272632e-41`
- required remainder cap: `7.964423903251877195e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000510930209806597e-44` | `0.000000000000000000e+00` | `1.710569414459005214e-48` | `sampled_feasible` |
| 16 | 10 | `2.000989889645855119e-44` | `0.000000000000000000e+00` | `2.736911063134408342e-48` | `sampled_feasible` |

### primary_tail row 0 chunk 23

- chunk interval: `[6.535489503380224650E-40, 6.536662018235220400E-40]`
- degree: `16`
- sampled max residual: `2.536957128960569169e-46`
- remainder candidate: `1.279065284185662593e-45`
- lower model integral: `6.535947971831946880e-40`
- upper model integral: `6.536203784888783570e-40`
- current chunk width: `1.172514854995750051e-43`
- model interval width: `2.558130568366902551e-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.584684517225526645e-44`
- upper margin: `4.582333464365063345e-44`
- required remainder cap: `5.861398748548515118e-45`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000000000591011366e-44` | `0.000000000000000000e+00` | `2.120723952099520471e-54` | `sampled_feasible` |
| 16 | 10 | `2.000000000582854736e-44` | `0.000000000000000000e+00` | `2.120723952099520471e-54` | `sampled_feasible` |

### primary_tail row 0 chunk 24

- chunk interval: `[-2.225337606182590454E-44, 2.225337606187822005E-44]`
- degree: `12`
- sampled max residual: `5.601500252776712470e-48`
- remainder candidate: `1.006161650278054321e-45`
- lower model integral: `-9.644725448522664946e-45`
- upper model integral: `1.047850755703842210e-44`
- current chunk width: `4.450675212370412459e-44`
- model interval width: `2.012323300556108705e-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `1.260865061330324077e-44`
- upper margin: `1.177486850483979677e-44`
- required remainder cap: `2.183648500762033905e-45`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000000000000106942e-44` | `0.000000000000000000e+00` | `3.833377411162463292e-58` | `sampled_feasible` |
| 16 | 10 | `2.000000000000000404e-44` | `0.000000000000000000e+00` | `2.022479965304871055e-60` | `sampled_feasible` |

### primary_tail row 0 chunk 25

- chunk interval: `[3.214914812559243507E-37, 3.214930332717216431E-37]`
- degree: `16`
- sampled max residual: `8.363256352391858571e-47`
- remainder candidate: `1.091995819876310491e-45`
- lower model integral: `3.214922463453629822e-37`
- upper model integral: `3.214922681852794031e-37`
- current chunk width: `1.552015797292399841e-42`
- model interval width: `2.183991642095680076e-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `7.650894386456208410e-43`
- upper margin: `7.650864422258091361e-43`
- required remainder cap: `7.760064004362875166e-44`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000000177402292557e-44` | `0.000000000000000000e+00` | `5.846672803326677976e-52` | `sampled_feasible` |
| 16 | 10 | `2.000000315216722921e-44` | `0.000000000000000000e+00` | `1.169334560665335595e-51` | `sampled_feasible` |

