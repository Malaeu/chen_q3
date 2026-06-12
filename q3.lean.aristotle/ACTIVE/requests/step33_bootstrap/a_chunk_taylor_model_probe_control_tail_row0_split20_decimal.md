# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 26
- cells with sampled feasible degree: 3
- degrees: `16,20`
- fit samples: 17
- check samples: 61

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 16 | `5.035246596083676968E-32` | `1.685848112880366661E-59` | 5 |
| 20 | `3.101712866979793125E-36` | `3.902846429759990000E-68` | 5 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_tail` | 0 | `0.00` | 0 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 1 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 2 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 3 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 4 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 5 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 6 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 7 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 8 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 9 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 10 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 11 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 12 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 13 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 14 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 15 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 16 | `20` | 20 |
| `control_tail` | 0 | `0.00` | 17 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 18 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 19 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 20 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 21 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 22 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 23 | `-` | 20 |
| `control_tail` | 0 | `0.00` | 24 | `20` | 20 |
| `control_tail` | 0 | `0.00` | 25 | `20` | 20 |

## Best Degree Details

### control_tail row 0 chunk 0

- chunk interval: `[2.079648243339560946E-18, 2.079648243339560946E-18]`
- degree: `20`
- sampled max residual: `1.044461907137900615E-37`
- remainder candidate: `1.148908097851690677E-37`
- lower model integral: `2.079648243339560944E-18`
- upper model integral: `2.079648243339560947E-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.297816195703381353E-36`
- extra chunk width needed: `2.297816195703381488e-36`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-20` | `0.000000000000000000E+18` | `1.684824900828422678E-55` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-20` | `0.000000000000000000E+18` | `5.265335997036289281E-65` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 1

- chunk interval: `[2.960968324589733858E-19, 2.960968324589733858E-19]`
- degree: `20`
- sampled max residual: `2.004127316531724456E-38`
- remainder candidate: `2.204540048184896901E-38`
- lower model integral: `2.960968324589733856E-19`
- upper model integral: `2.960968324589733860E-19`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.409080096369793803E-37`
- extra chunk width needed: `4.409080096369793774e-37`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-21` | `0.000000000000000000E+18` | `7.971519145485459055E-56` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-21` | `0.000000000000000000E+18` | `3.363114162923598226E-65` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 2

- chunk interval: `[6.872538926676278071E-21, 6.872538926676278071E-21]`
- degree: `20`
- sampled max residual: `1.278887069454363126E-38`
- remainder candidate: `1.406775776399799438E-38`
- lower model integral: `6.872538926676277931E-21`
- upper model integral: `6.872538926676278212E-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.813551552799598877E-37`
- extra chunk width needed: `2.813551552799598763e-37`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-24` | `0.000000000000000000E+18` | `3.034181004338268406E-56` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-24` | `0.000000000000000000E+18` | `9.269870676823761174E-66` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 3

- chunk interval: `[1.303993024244406343E-23, 1.303993024244406344E-23]`
- degree: `20`
- sampled max residual: `2.861114539093040295E-39`
- remainder candidate: `3.147225993002344324E-39`
- lower model integral: `1.303993024244403196E-23`
- upper model integral: `1.303993024244409490E-23`
- current chunk width: `1.000000000000000006e-41`
- model interval width: `6.294451986004688649E-38`
- extra chunk width needed: `6.293451986004689087e-38`
- lower margin: `-3.232609464761290647e-38`
- upper margin: `-3.085672670908504708e-38`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `4.891801555516405100E-57` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `3.330960145626717515E-66` | `sampled_feasible` |

### control_tail row 0 chunk 4

- chunk interval: `[2.695195050932686757E-28, 2.695195050932694713E-28]`
- degree: `20`
- sampled max residual: `2.080592316770173779E-40`
- remainder candidate: `2.288651548447191156E-40`
- lower model integral: `2.695195050909654619E-28`
- upper model integral: `2.695195050955427650E-28`
- current chunk width: `7.955999999999999656e-43`
- model interval width: `4.577303096894382313E-39`
- extra chunk width needed: `4.576507496894381923e-39`
- lower margin: `-2.303196576739698535e-39`
- upper margin: `-2.273287262317149639e-39`
- required remainder cap: `-1.457350402897809754e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-38` | `0.000000000000000000E+18` | `5.001953546500017587E-58` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-38` | `0.000000000000000000E+18` | `4.658166131445038650E-67` | `sampled_feasible` |

### control_tail row 0 chunk 5

- chunk interval: `[1.063214457388278042E-36, 1.063230481870625028E-36]`
- degree: `20`
- sampled max residual: `1.487225205254090967E-41`
- remainder candidate: `1.635947725779500064E-41`
- lower model integral: `1.063059660584604076E-36`
- upper model integral: `1.063386850129759976E-36`
- current chunk width: `1.602448234698600069e-41`
- model interval width: `3.271895451559000128E-40`
- extra chunk width needed: `3.111650628089139995e-40`
- lower margin: `-1.547968036740356010e-40`
- upper margin: `-1.563682591348712614e-40`
- required remainder cap: `7.226513443075105148e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `1.679233281872527470E-59` | `0.000000000000000000E+18` | `1.349134667658014333E-59` | `sampled_feasible` |
| 20 | 20 | `3.893969414509000000E-68` | `0.000000000000000000E+18` | `3.116481188258514191E-68` | `sampled_feasible` |

### control_tail row 0 chunk 6

- chunk interval: `[4.125328007045974063E-28, 4.125328007045977064E-28]`
- degree: `20`
- sampled max residual: `3.708888815603135273E-41`
- remainder candidate: `4.079777697163448800E-41`
- lower model integral: `4.125328007041915599E-28`
- upper model integral: `4.125328007050075154E-28`
- current chunk width: `3.001000000000000164e-43`
- model interval width: `8.159555394326897600E-40`
- extra chunk width needed: `8.156554394326898287e-40`
- lower margin: `-4.059057183701838120e-40`
- upper margin: `-4.097620917440057086e-40`
- required remainder cap: `-1.793662034335765851e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-36` | `0.000000000000000000E+18` | `3.365051436449069586E-59` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-36` | `0.000000000000000000E+18` | `2.848423792562075162E-68` | `sampled_feasible` |

### control_tail row 0 chunk 7

- chunk interval: `[2.164182963227018159E-24, 2.164182963227018160E-24]`
- degree: `20`
- sampled max residual: `9.645528803111275370E-41`
- remainder candidate: `1.061008168342240291E-40`
- lower model integral: `2.164182963227017103E-24`
- upper model integral: `2.164182963227019225E-24`
- current chunk width: `1.000000000000000038e-42`
- model interval width: `2.122016336684480581E-39`
- extra chunk width needed: `2.121016336684480391e-39`
- lower margin: `-1.102025953895894539e-39`
- upper margin: `-7.346839692639296925e-40`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `1.141421455098627918E-58` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `5.642775141754581291E-68` | `sampled_feasible` |

### control_tail row 0 chunk 8

- chunk interval: `[2.160279114650519470E-22, 2.160279114650519470E-22]`
- degree: `20`
- sampled max residual: `8.777364495852932112E-41`
- remainder candidate: `9.655100945438225323E-41`
- lower model integral: `2.160279114650519460E-22`
- upper model integral: `2.160279114650519480E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.931020189087645065E-39`
- extra chunk width needed: `1.931020189087645001e-39`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `1.989242041732889041E-58` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `9.560336898808460952E-68` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 9

- chunk interval: `[2.145889300808625518E-21, 2.145889300808625518E-21]`
- degree: `20`
- sampled max residual: `1.314906974947482459E-40`
- remainder candidate: `1.446397672442230704E-40`
- lower model integral: `2.145889300808625517E-21`
- upper model integral: `2.145889300808625519E-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.892795344884461409E-39`
- extra chunk width needed: `2.892795344884461289e-39`
- lower margin: `0.000000000000000000e+00`
- upper margin: `-3.761581922631320025e-37`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `2.624791399201142020E-58` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `1.048094845527346230E-67` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 10

- chunk interval: `[3.762292826279725866E-21, 3.762292826279725866E-21]`
- degree: `20`
- sampled max residual: `1.761803472948164147E-40`
- remainder candidate: `1.937983820242980562E-40`
- lower model integral: `3.762292826279725864E-21`
- upper model integral: `3.762292826279725868E-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.875967640485961123E-39`
- extra chunk width needed: `3.875967640485961091e-39`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-22` | `0.000000000000000000E+18` | `2.321637448447886461E-58` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-22` | `0.000000000000000000E+18` | `8.877532152470269056E-68` | `sampled_feasible` |

### control_tail row 0 chunk 11

- chunk interval: `[1.371845339436552877E-21, 1.371845339436552877E-21]`
- degree: `20`
- sampled max residual: `3.847907685888587784E-41`
- remainder candidate: `4.232698454477446562E-41`
- lower model integral: `1.371845339436552876E-21`
- upper model integral: `1.371845339436552877E-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.465396908954893124E-40`
- extra chunk width needed: `8.465396908954893033e-40`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `1.723027912213233370E-58` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `6.818747378461422277E-68` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 12

- chunk interval: `[9.419131701293495199E-23, 9.419131701293495199E-23]`
- degree: `20`
- sampled max residual: `4.123288977331094589E-41`
- remainder candidate: `4.535617875064204047E-41`
- lower model integral: `9.419131701293495154E-23`
- upper model integral: `9.419131701293495245E-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.071235750128408095E-40`
- extra chunk width needed: `9.071235750128408551e-40`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `7.497363571600692192E-59` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `2.733979298818724614E-68` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 13

- chunk interval: `[7.920862092127684826E-25, 7.920862092127684826E-25]`
- degree: `20`
- sampled max residual: `1.264938074867949073E-41`
- remainder candidate: `1.391431882354743980E-41`
- lower model integral: `7.920862092127683436E-25`
- upper model integral: `7.920862092127686219E-25`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.782863764709487960E-40`
- extra chunk width needed: `2.782863764709488092e-40`
- lower margin: `-9.183549615799121156e-41`
- upper margin: `-1.836709923159824231e-40`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `2.297685039195878353E-59` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `1.268466208133372587E-68` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 14

- chunk interval: `[2.504588245519127762E-28, 2.504588245519127808E-28]`
- degree: `20`
- sampled max residual: `1.119186586424248519E-42`
- remainder candidate: `1.231105245066673370E-42`
- lower model integral: `2.504588245519005961E-28`
- upper model integral: `2.504588245519252182E-28`
- current chunk width: `4.599999999999999834e-45`
- model interval width: `2.462210490133346741E-41`
- extra chunk width needed: `2.461750490133346810e-41`
- lower margin: `-1.219690183348320779e-41`
- upper margin: `-1.242110958777517852e-41`
- required remainder cap: `-1.345246525751824338e-44`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-35` | `0.000000000000000000E+18` | `2.563571559879228106E-60` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-35` | `0.000000000000000000E+18` | `2.527735428233892733E-69` | `sampled_feasible` |

### control_tail row 0 chunk 15

- chunk interval: `[4.473385859449875341E-35, 4.473385938834443383E-35]`
- degree: `20`
- sampled max residual: `1.041624446130973842E-43`
- remainder candidate: `1.145786890744071227E-43`
- lower model integral: `4.473385785758498173E-35`
- upper model integral: `4.473386014915876321E-35`
- current chunk width: `7.938456804199999390e-43`
- model interval width: `2.291573781488142453E-42`
- extra chunk width needed: `1.497728101068142614e-42`
- lower margin: `-7.369137688099990020e-43`
- upper margin: `-7.608143311119974597e-43`
- required remainder cap: `3.849725630670719809e-44`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `5.731967007839191218E-62` | `0.000000000000000000E+18` | `2.818524112302229824E-61` | `sampled_feasible` |
| 20 | 20 | `8.877015250990000000E-71` | `0.000000000000000000E+18` | `2.599787415176527133E-70` | `sampled_feasible` |

### control_tail row 0 chunk 16

- chunk interval: `[1.822673907663800974E-33, 1.822673910477328425E-33]`
- degree: `20`
- sampled max residual: `4.563195362508992437E-44`
- remainder candidate: `5.019514898759891681E-44`
- lower model integral: `1.822673908560759194E-33`
- upper model integral: `1.822673909564662174E-33`
- current chunk width: `2.813527450999999932e-42`
- model interval width: `1.003902979751978336E-42`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `8.969582835323186754e-43`
- upper margin: `9.126661003514128285e-43`
- required remainder cap: `1.398909825194466476e-43`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `8.828640000000000000E-63` | `0.000000000000000000E+18` | `6.470687857519058254E-62` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-50` | `0.000000000000000000E+18` | `6.056712133925909542E-71` | `sampled_feasible` |

### control_tail row 0 chunk 17

- chunk interval: `[3.443824611212247714E-28, 3.443824611212247729E-28]`
- degree: `20`
- sampled max residual: `2.974957828717933190E-43`
- remainder candidate: `3.272453611589726510E-43`
- lower model integral: `3.443824611212214813E-28`
- upper model integral: `3.443824611212280262E-28`
- current chunk width: `1.500000000000000054e-45`
- model interval width: `6.544907223179453019E-42`
- extra chunk width needed: `6.543407223179453264e-42`
- lower margin: `-3.273433212662772678e-42`
- upper margin: `-3.273433212662772678e-42`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `3.923527518030075250E-61` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `1.988589868531183743E-70` | `sampled_feasible` |

### control_tail row 0 chunk 18

- chunk interval: `[1.810675948549916763E-25, 1.810675948549916763E-25]`
- degree: `20`
- sampled max residual: `4.314498213203929303E-43`
- remainder candidate: `4.745948034524322234E-43`
- lower model integral: `1.810675948549916715E-25`
- upper model integral: `1.810675948549916810E-25`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.491896069048644467E-42`
- extra chunk width needed: `9.491896069048643893e-42`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `8.028153660661811518E-61` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `4.583004556744578969E-70` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 19

- chunk interval: `[5.374673041837326970E-24, 5.374673041837326970E-24]`
- degree: `20`
- sampled max residual: `6.191571827731197493E-43`
- remainder candidate: `6.810729010504317242E-43`
- lower model integral: `5.374673041837326964E-24`
- upper model integral: `5.374673041837326977E-24`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.362145802100863448E-41`
- extra chunk width needed: `1.362145802100863548e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `1.598419310863056689E-60` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `6.698592683411032501E-70` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 20

- chunk interval: `[2.289422842939743189E-23, 2.289422842939743189E-23]`
- degree: `20`
- sampled max residual: `1.342484365912974416E-42`
- remainder candidate: `1.476732802504271858E-42`
- lower model integral: `2.289422842939743187E-23`
- upper model integral: `2.289422842939743190E-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.953465605008543715E-41`
- extra chunk width needed: `2.953465605008543782e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `1.738184310219173837E-60` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `6.778358553765718321E-70` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 21

- chunk interval: `[1.936774980581608310E-23, 1.936774980581608310E-23]`
- degree: `20`
- sampled max residual: `6.020902655434675421E-43`
- remainder candidate: `6.622992920978142963E-43`
- lower model integral: `1.936774980581608309E-23`
- upper model integral: `1.936774980581608311E-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.324598584195628593E-41`
- extra chunk width needed: `1.324598584195628495e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `1.584645445136563294E-60` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `6.067461317048260123E-70` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 22

- chunk interval: `[3.332128614305462003E-24, 3.332128614305462003E-24]`
- degree: `20`
- sampled max residual: `4.080992248060238335E-43`
- remainder candidate: `4.489091472866262168E-43`
- lower model integral: `3.332128614305461999E-24`
- upper model integral: `3.332128614305462008E-24`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.978182945732524337E-42`
- extra chunk width needed: `8.978182945732524018e-42`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `7.690615607709737060E-61` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `3.331319165236151724E-70` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 23

- chunk interval: `[9.073920193491404915E-26, 9.073920193491404915E-26]`
- degree: `20`
- sampled max residual: `2.157678468070286031E-43`
- remainder candidate: `2.373446314877314634E-43`
- lower model integral: `9.073920193491404677E-26`
- upper model integral: `9.073920193491405152E-26`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.746892629754629268E-42`
- extra chunk width needed: `4.746892629754629257e-42`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-29` | `0.000000000000000000E+18` | `4.033786399441046925E-61` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-29` | `0.000000000000000000E+18` | `1.622603732725024878E-70` | `split_integral_center_mismatch` |

### control_tail row 0 chunk 24

- chunk interval: `[1.884816502101221078E-28, 1.884816502101831719E-28]`
- degree: `20`
- sampled max residual: `3.040386262099781002E-44`
- remainder candidate: `3.344424888309759102E-44`
- lower model integral: `1.884816502101523029E-28`
- upper model integral: `1.884816502101529717E-28`
- current chunk width: `6.106409999999999668e-41`
- model interval width: `6.688849776619518205E-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `3.020078450312845751e-41`
- upper margin: `3.020078450312845751e-41`
- required remainder cap: `3.053709613456641106e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `5.947872425242606096E-62` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `5.153102815632882256E-71` | `sampled_feasible` |

### control_tail row 0 chunk 25

- chunk interval: `[3.434543160105999872E-33, 3.434543248006916193E-33]`
- degree: `20`
- sampled max residual: `1.759954537128853254E-45`
- remainder candidate: `1.935949990841738579E-45`
- lower model integral: `3.434543204036584478E-33`
- upper model integral: `3.434543204075303478E-33`
- current chunk width: `8.790091632099999516e-41`
- model interval width: `3.871899981683477159E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.393058506404070569e-41`
- upper margin: `4.393161277414491266e-41`
- required remainder cap: `4.394994460444578438e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-44` | `0.000000000000000000E+18` | `1.124630064963477429E-62` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-44` | `0.000000000000000000E+18` | `7.532414882263133356E-72` | `sampled_feasible` |

