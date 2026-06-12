# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 26
- cells with sampled feasible degree: 0
- degrees: `12,16`
- fit samples: 25
- check samples: 81

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_tail` | 0 | `0.00` | 0 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 1 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 2 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 3 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 4 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 5 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 6 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 7 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 8 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 9 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 10 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 11 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 12 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 13 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 14 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 15 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 16 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 17 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 18 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 19 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 20 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 21 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 22 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 23 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 24 | `-` | 16 |
| `control_tail` | 0 | `0.00` | 25 | `-` | 16 |

## Best Degree Details

### control_tail row 0 chunk 0

- chunk interval: `[2.079648243339560946E-18, 2.079648243339560946E-18]`
- degree: `16`
- sampled max residual: `4.814824860968089633e-34`
- remainder candidate: `5.296307347074898585e-34`
- lower model integral: `2.079648243339556119e-18`
- upper model integral: `2.079648243339566904e-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.078520768856852078e-32`
- extra chunk width needed: `1.078520768856852078e-32`
- lower margin: `-5.007417855406813218e-33`
- upper margin: `-5.777789833161707559e-33`
- required remainder cap: `-3.851859888774471920e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.040002169969107361e-32` | `1.040002169969107361e-32` | `7.222237291452134449e-34` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.463706757734299248e-32` | `1.463706757734299248e-32` | `1.348150961071065097e-33` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 1

- chunk interval: `[2.960968324589733858E-19, 2.960968324589733858E-19]`
- degree: `16`
- sampled max residual: `4.212971753347078429e-34`
- remainder candidate: `4.634268928691786260e-34`
- lower model integral: `2.960968324589688229e-19`
- upper model integral: `2.960968324589780674e-19`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.244463733058732095e-33`
- extra chunk width needed: `9.244463733058732095e-33`
- lower margin: `-4.574083617919685151e-33`
- upper margin: `-4.670380115139046944e-33`
- required remainder cap: `-4.814824860968089900e-36`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.348150961071065097e-33` | `1.348150961071065097e-33` | `1.685188701338831371e-34` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.407412430484044816e-33` | `2.407412430484044816e-33` | `2.648153673532449298e-34` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 2

- chunk interval: `[6.872538926676278071E-21, 6.872538926676278071E-21]`
- degree: `16`
- sampled max residual: `4.777209041741776432e-35`
- remainder candidate: `5.254929946015954605e-35`
- lower model integral: `6.872538926675754455e-21`
- upper model integral: `6.872538926676804689e-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.050233672798664551e-33`
- extra chunk width needed: `1.050233672798664551e-33`
- lower margin: `-5.236122036302797475e-34`
- upper margin: `-5.266214691683848036e-34`
- required remainder cap: `-1.504632769052528094e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.761581922631320025e-35` | `3.761581922631320025e-35` | `8.275480229788904056e-36` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.717604522399606439e-35` | `5.717604522399606439e-35` | `1.090858757563082807e-35` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 3

- chunk interval: `[1.303993024244406343E-23, 1.303993024244406344E-23]`
- degree: `16`
- sampled max residual: `2.950490820563941645e-36`
- remainder candidate: `3.245539903620336293e-36`
- lower model integral: `1.303993024241131460e-23`
- upper model integral: `1.303993024247622540e-23`
- current chunk width: `1.000000000000000006e-41`
- model interval width: `6.491079805240671619e-35`
- extra chunk width needed: `6.491078805240671503e-35`
- lower margin: `-3.274927261390892997e-35`
- upper margin: `-3.216152543849778622e-35`
- required remainder cap: `-2.938735877055718770e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.640713280344868802e-38` | `7.639713280344868990e-38` | `2.204051907791789077e-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.204881709592844696e-37` | `1.204781709592844610e-37` | `3.085672670908504708e-38` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 4

- chunk interval: `[2.695195050932686757E-28, 2.695195050932694713E-28]`
- degree: `16`
- sampled max residual: `3.809793764452231076e-37`
- remainder candidate: `4.190773150897454005e-37`
- lower model integral: `2.695195008908325053e-28`
- upper model integral: `2.695195092723787871e-28`
- current chunk width: `7.955999999999999656e-43`
- model interval width: `8.381546281794908367e-36`
- extra chunk width needed: `8.381545486194908049e-36`
- lower margin: `-4.202436159226417350e-36`
- upper margin: `-4.179109315420575565e-36`
- required remainder cap: `-1.166301832896316773e-39`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.569454280043795119e-42` | `7.738542800437951538e-43` | `4.484155085839414627e-43` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.376602195494889752e-42` | `1.581002195494889627e-42` | `8.519894663094887791e-43` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 5

- chunk interval: `[1.063214457388278042E-36, 1.063230481870625028E-36]`
- degree: `16`
- sampled max residual: `4.710979355555981236e-40`
- remainder candidate: `5.182087291111580234e-40`
- lower model integral: `1.058090183666966675e-36`
- upper model integral: `1.068454358249189812e-36`
- current chunk width: `1.602448234698600069e-41`
- model interval width: `1.036417458222313698e-38`
- extra chunk width needed: `1.034815009987615111e-38`
- lower margin: `-5.124273721311426771e-39`
- upper margin: `-5.223876378564724336e-39`
- required remainder cap: `-4.178908745315584466e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000219849428098119e-44` | `0.000000000000000000e+00` | `4.978024272546714391e-49` | `sampled_feasible` |
| 16 | 10 | `2.000001233979592016e-44` | `0.000000000000000000e+00` | `5.533458188862748799e-51` | `sampled_feasible` |

### control_tail row 0 chunk 6

- chunk interval: `[4.125328007045974063E-28, 4.125328007045977064E-28]`
- degree: `16`
- sampled max residual: `2.607345038655113464e-38`
- remainder candidate: `2.868079642520625014e-38`
- lower model integral: `4.125328004172410414e-28`
- upper model integral: `4.125328009908570298e-28`
- current chunk width: `3.001000000000000164e-43`
- model interval width: `5.736159884398328563e-37`
- extra chunk width needed: `5.736156883398328601e-37`
- lower margin: `-2.873564063869145886e-37`
- upper margin: `-2.862593130036131174e-37`
- required remainder cap: `-5.484121669981604089e-41`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.421443746353283899e-42` | `2.121343746353283723e-42` | `7.174648137343063403e-43` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.766690272105108287e-42` | `3.466590272105108111e-42` | `1.255563424035036096e-42` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 7

- chunk interval: `[2.164182963227018159E-24, 2.164182963227018160E-24]`
- degree: `16`
- sampled max residual: `1.675079449921759699e-37`
- remainder candidate: `1.842587404913935825e-37`
- lower model integral: `2.164182963225175742e-24`
- upper model integral: `2.164182963228860917e-24`
- current chunk width: `1.000000000000000038e-42`
- model interval width: `3.685174789827871337e-36`
- extra chunk width needed: `3.685173789827871088e-36`
- lower margin: `-1.842587394913935669e-36`
- upper margin: `-1.842587394913935669e-36`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.175494350822287508e-38` | `1.175394350822287501e-38` | `2.571393892423753924e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.542836335454252354e-38` | `1.542736335454252477e-38` | `3.122406869371701193e-39` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 8

- chunk interval: `[2.160279114650519470E-22, 2.160279114650519470E-22]`
- degree: `16`
- sampled max residual: `3.855254128712471061e-37`
- remainder candidate: `4.240779551583717990e-37`
- lower model integral: `2.160279114650477632e-22`
- upper model integral: `2.160279114650562267e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.463559325920470057e-36`
- extra chunk width needed: `8.463559325920470057e-36`
- lower margin: `-4.184759888927343528e-36`
- upper margin: `-4.278799436993126529e-36`
- required remainder cap: `-4.701977403289150293e-39`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.034435028723613007e-36` | `1.034435028723613007e-36` | `1.410593220986745010e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.786751413249877012e-36` | `1.786751413249877012e-36` | `2.586087571809032518e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 9

- chunk interval: `[2.145889300808625518E-21, 2.145889300808625518E-21]`
- degree: `16`
- sampled max residual: `6.347669494440352543e-37`
- remainder candidate: `6.982436453884388121e-37`
- lower model integral: `2.145889300808617431e-21`
- upper model integral: `2.145889300808631725e-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.429401130599901610e-35`
- extra chunk width needed: `1.429401130599901610e-35`
- lower margin: `-7.899322037525772054e-36`
- upper margin: `-6.394689268473244043e-36`
- required remainder cap: `-7.523163845262640469e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.780112998841432066e-36` | `9.780112998841432066e-36` | `7.993361585591555054e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.542248588278841210e-35` | `1.542248588278841210e-35` | `1.034435028723613007e-36` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 10

- chunk interval: `[3.762292826279725866E-21, 3.762292826279725866E-21]`
- degree: `16`
- sampled max residual: `9.403954806578300064e-37`
- remainder candidate: `1.034435029723613056e-36`
- lower model integral: `3.762292826279713317e-21`
- upper model integral: `3.762292826279734382e-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.106485876673539214e-35`
- extra chunk width needed: `2.106485876673539214e-35`
- lower margin: `-1.278937853694648809e-35`
- upper margin: `-8.275480229788904056e-36`
- required remainder cap: `-2.256949153578791932e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.504632769052528010e-35` | `1.504632769052528010e-35` | `9.874152546907215067e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.858802261199803219e-35` | `2.858802261199803219e-35` | `1.880790961315660013e-36` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 11

- chunk interval: `[1.371845339436552877E-21, 1.371845339436552877E-21]`
- degree: `16`
- sampled max residual: `5.642372883946980038e-37`
- remainder candidate: `6.206610182341678198e-37`
- lower model integral: `1.371845339436547391e-21`
- upper model integral: `1.371845339436559804e-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.241322034468335608e-35`
- extra chunk width needed: `1.241322034468335608e-35`
- lower margin: `-5.454293787815414037e-36`
- upper margin: `-6.958926556867942047e-36`
- required remainder cap: `-7.523163845262640469e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.206610172341678042e-36` | `6.206610172341678042e-36` | `6.112570624275895041e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.147282486402552608e-35` | `1.147282486402552608e-35` | `1.034435028723613007e-36` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 12

- chunk interval: `[9.419131701293495199E-23, 9.419131701293495199E-23]`
- degree: `16`
- sampled max residual: `1.483143262951558067e-37`
- remainder candidate: `1.631457599246714155e-37`
- lower model integral: `9.419131701293333913e-23`
- upper model integral: `9.419131701293660700e-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.267874295285959272e-36`
- extra chunk width needed: `3.267874295285959272e-36`
- lower margin: `-1.610427260626533886e-36`
- upper margin: `-1.657447034659425386e-36`
- required remainder cap: `-2.350988701644575146e-39`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `5.172175143618065035e-37` | `5.172175143618065035e-37` | `7.640713280344868802e-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `8.110911020673783805e-37` | `8.110911020673783805e-37` | `1.175494350822287508e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 13

- chunk interval: `[7.920862092127684826E-25, 7.920862092127684826E-25]`
- degree: `16`
- sampled max residual: `9.275385111957112368e-39`
- remainder candidate: `1.020292462315282382e-38`
- lower model integral: `7.920862092126688944e-25`
- upper model integral: `7.920862092128729529e-25`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.040584724630564721e-37`
- extra chunk width needed: `2.040584724630564721e-37`
- lower margin: `-9.954967783526247333e-38`
- upper margin: `-1.045087946277939988e-37`
- required remainder cap: `-2.479558396265762875e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.040761830951613309e-39` | `4.040761830951613309e-39` | `1.010190457737903327e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `8.357030150377200252e-39` | `8.357030150377200252e-39` | `2.112216411633797866e-39` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 14

- chunk interval: `[2.504588245519127762E-28, 2.504588245519127808E-28]`
- degree: `16`
- sampled max residual: `3.634273172420270373e-39`
- remainder candidate: `3.997701489662298020e-39`
- lower model integral: `2.504588245120560546e-28`
- upper model integral: `2.504588245920100643e-28`
- current chunk width: `4.599999999999999834e-45`
- model interval width: `7.995400979324594820e-38`
- extra chunk width needed: `7.995400519324594819e-38`
- lower margin: `-3.985673985722076100e-38`
- upper margin: `-4.009726993602518720e-38`
- required remainder cap: `-1.202650394022130952e-41`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.524612729185400973e-42` | `1.520012729185401090e-42` | `4.932570594423356090e-43` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.376602195494889752e-42` | `2.372002195494889869e-42` | `8.071479154510946329e-43` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 15

- chunk interval: `[4.473385859449875341E-35, 4.473385938834443383E-35]`
- degree: `16`
- sampled max residual: `7.092149612122320871e-41`
- remainder candidate: `7.801464573334552737e-41`
- lower model integral: `4.473308027197547394e-35`
- upper model integral: `4.473464056489013983e-35`
- current chunk width: `7.938456804199999390e-43`
- model interval width: `1.560292914665886564e-39`
- extra chunk width needed: `1.559499068985466432e-39`
- lower margin: `-7.783225232768424232e-40`
- upper margin: `-7.811765457059535277e-40`
- required remainder cap: `-1.030088373010245769e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000060302079685053e-44` | `0.000000000000000000e+00` | `1.496748237651629562e-49` | `sampled_feasible` |
| 16 | 10 | `2.000060302079685053e-44` | `0.000000000000000000e+00` | `2.565854121688507820e-49` | `sampled_feasible` |

### control_tail row 0 chunk 16

- chunk interval: `[1.822673907663800974E-33, 1.822673910477328425E-33]`
- degree: `16`
- sampled max residual: `3.442498127602759109e-41`
- remainder candidate: `3.786847940363035513e-41`
- lower model integral: `1.822673530004775157e-33`
- upper model integral: `1.822674287374363207e-33`
- current chunk width: `2.813527450999999932e-42`
- model interval width: `7.573695880502008587e-40`
- extra chunk width needed: `7.545560605992008721e-40`
- lower margin: `-3.776590257592927529e-40`
- upper margin: `-3.768970348237000786e-40`
- required remainder cap: `1.025768265807676549e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.001126735199011839e-44` | `0.000000000000000000e+00` | `3.848781182532761730e-48` | `sampled_feasible` |
| 16 | 10 | `2.001708328799927901e-44` | `0.000000000000000000e+00` | `6.842277657836020854e-48` | `sampled_feasible` |

### control_tail row 0 chunk 17

- chunk interval: `[3.443824611212247714E-28, 3.443824611212247729E-28]`
- degree: `16`
- sampled max residual: `4.183328204247317233e-40`
- remainder candidate: `4.601671024672049342e-40`
- lower model integral: `3.443824611166241933e-28`
- upper model integral: `3.443824611258275629e-28`
- current chunk width: `1.500000000000000054e-45`
- model interval width: `9.203369581278531369e-39`
- extra chunk width needed: `9.203368081278530911e-39`
- lower margin: `-4.600563751867805831e-39`
- upper margin: `-4.602805829410725538e-39`
- required remainder cap: `-1.121038771459853657e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.242077542919707313e-42` | `2.240577542919707317e-42` | `6.277817120175180478e-43` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.363116314379560970e-42` | `3.361616314379560974e-42` | `9.416725680262770717e-43` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 18

- chunk interval: `[1.810675948549916763E-25, 1.810675948549916763E-25]`
- degree: `16`
- sampled max residual: `1.515285686606854991e-39`
- remainder candidate: `1.666815255267540773e-39`
- lower model integral: `1.810675948549751066e-25`
- upper model integral: `1.810675948550084429e-25`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.333628510535080980e-38`
- extra chunk width needed: `3.333628510535080980e-38`
- lower margin: `-1.657630705651741369e-38`
- upper margin: `-1.675997804883339611e-38`
- required remainder cap: `-9.183549615799121666e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.724372135009165098e-40` | `8.724372135009165098e-40` | `1.836709923159824231e-40` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.354573568330370371e-39` | `1.354573568330370371e-39` | `2.640270514542247332e-40` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 19

- chunk interval: `[5.374673041837326970E-24, 5.374673041837326970E-24]`
- degree: `16`
- sampled max residual: `2.215531344811537979e-39`
- remainder candidate: `2.437085479292691995e-39`
- lower model integral: `5.374673041837299812e-24`
- upper model integral: `5.374673041837348302e-24`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.848914197141935970e-38`
- extra chunk width needed: `4.848914197141935970e-38`
- lower margin: `-2.718330686276539862e-38`
- upper margin: `-2.130583510865396108e-38`
- required remainder cap: `-2.938735877055718933e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.644862289350146893e-38` | `2.644862289350146893e-38` | `3.122406869371701193e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.261167021730792216e-38` | `4.261167021730792216e-38` | `4.591774807899560578e-39` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 20

- chunk interval: `[2.289422842939743189E-23, 2.289422842939743189E-23]`
- degree: `16`
- sampled max residual: `8.081523661903226617e-39`
- remainder candidate: `8.889677028093549758e-39`
- lower model integral: `2.289422842939734482e-23`
- upper model integral: `2.289422842939752114e-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.763241526233431262e-37`
- extra chunk width needed: `1.763241526233431262e-37`
- lower margin: `-8.816207631167156310e-38`
- upper margin: `-8.816207631167156310e-38`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.110081218872728187e-38` | `9.110081218872728187e-38` | `6.244813738743402386e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.704466808692316887e-37` | `1.704466808692316887e-37` | `1.102025953895894539e-38` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 21

- chunk interval: `[1.936774980581608310E-23, 1.936774980581608310E-23]`
- degree: `16`
- sampled max residual: `4.775445800215543001e-39`
- remainder candidate: `5.252991380237097650e-39`
- lower model integral: `1.936774980581602413e-23`
- upper model integral: `1.936774980581612993e-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.057944915740058757e-37`
- extra chunk width needed: `1.057944915740058757e-37`
- lower margin: `-5.877471754111437540e-38`
- upper margin: `-4.701977403289150032e-38`
- required remainder cap: `-5.877471754111437866e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.522334043461584433e-38` | `8.522334043461584433e-38` | `7.346839692639296925e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.616304732380645323e-37` | `1.616304732380645323e-37` | `9.918233585063050848e-39` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 22

- chunk interval: `[3.332128614305462003E-24, 3.332128614305462003E-24]`
- degree: `16`
- sampled max residual: `5.326458777163490270e-39`
- remainder candidate: `5.859105654879839777e-39`
- lower model integral: `3.332128614305404806e-24`
- upper model integral: `3.332128614305522355e-24`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.175494350822287508e-37`
- extra chunk width needed: `1.175494350822287508e-37`
- lower margin: `-5.730534960258651601e-38`
- upper margin: `-6.024408547964223478e-38`
- required remainder cap: `-1.469367938527859467e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.616304732380645323e-38` | `1.616304732380645323e-38` | `1.653038930843841808e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.497925495497360954e-38` | `2.497925495497360954e-38` | `2.755064884739736347e-39` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 23

- chunk interval: `[9.073920193491404915E-26, 9.073920193491404915E-26]`
- degree: `16`
- sampled max residual: `3.214242365529692405e-40`
- remainder candidate: `3.535676602082662194e-40`
- lower model integral: `9.073920193491054476e-26`
- upper model integral: `9.073920193491761609e-26`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.071333204165323290e-39`
- extra chunk width needed: `7.071333204165323290e-39`
- lower margin: `-3.501228291023414941e-39`
- upper margin: `-3.570104913141908349e-39`
- required remainder cap: `-3.443831105924670306e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `5.165746658887005650e-40` | `5.165746658887005650e-40` | `1.033149331777401130e-40` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.576428433034274954e-40` | `7.576428433034274954e-40` | `1.320135257271123666e-40` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_tail row 0 chunk 24

- chunk interval: `[1.884816502101221078E-28, 1.884816502101831719E-28]`
- degree: `16`
- sampled max residual: `8.788943968245252669e-41`
- remainder candidate: `9.667938365069778530e-41`
- lower model integral: `1.884816502091817799e-28`
- upper model integral: `1.884816502111153476e-28`
- current chunk width: `6.106409999999999668e-41`
- model interval width: `1.933567673013955587e-39`
- extra chunk width needed: `1.872503573013955733e-39`
- lower margin: `-9.403273215005252473e-40`
- upper margin: `-9.321661592442975127e-40`
- required remainder cap: `2.645651500645254630e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.416725680262770717e-43` | `0.000000000000000000e+00` | `2.242077542919707313e-43` | `sampled_feasible` |
| 16 | 10 | `1.838503585194159997e-42` | `0.000000000000000000e+00` | `5.156778348715326821e-43` | `sampled_feasible` |

### control_tail row 0 chunk 25

- chunk interval: `[3.434543160105999872E-33, 3.434543248006916193E-33]`
- degree: `16`
- sampled max residual: `6.260212623989334180e-42`
- remainder candidate: `6.887233886388268190e-42`
- lower model integral: `3.434543135077299714e-33`
- upper model integral: `3.434543272821977420e-33`
- current chunk width: `8.790091632099999516e-41`
- model interval width: `1.377446777053592066e-40`
- extra chunk width needed: `4.984376138435921148e-41`
- lower margin: `-2.502869997929255151e-41`
- upper margin: `-2.481506149129864008e-41`
- required remainder cap: `4.384363887338705181e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.002803093225181664e-44` | `0.000000000000000000e+00` | `1.094764425253763337e-47` | `sampled_feasible` |
| 16 | 10 | `2.003145207108073465e-44` | `0.000000000000000000e+00` | `1.094764425253763337e-47` | `sampled_feasible` |

