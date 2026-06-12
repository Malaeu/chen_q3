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

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 12 | `2.409833118956304365e-01` | `1.411731795397261419e-06` | 0 |
| 16 | `5.515999432004376618e-02` | `1.374827069038886639e-07` | 0 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_finite` | 0 | `0.00` | 0 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 1 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 2 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 3 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 4 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 5 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 6 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 7 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 8 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 9 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 10 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 11 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 12 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 13 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 14 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 15 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 16 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 17 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 18 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 19 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 20 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 21 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 22 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 23 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 24 | `-` | 16 |
| `primary_finite` | 0 | `0.00` | 25 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `16`
- sampled max residual: `2.507272469082610922e-03`
- remainder candidate: `2.757999715990872187e-03`
- lower model integral: `-3.807376479739739694e-01`
- upper model integral: `-3.255776536541565291e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.515999431981744028e-02`
- extra chunk width needed: `5.515999431981744028e-02`
- lower margin: `-2.720295777408765492e-02`
- upper margin: `-2.795703654572978536e-02`
- required remainder cap: `-3.770393858210652069e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.411731793077297681e-06` | `1.411731793077297681e-06` | `6.416695496613833427e-07` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.374827032218917111e-07` | `1.374827032218917111e-07` | `6.249212380904367592e-08` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 1

- chunk interval: `[2.615058139399545823E-1, 2.615058139399545823E-1]`
- degree: `16`
- sampled max residual: `1.021752127350339379e-14`
- remainder candidate: `1.123927340085373474e-14`
- lower model integral: `2.615058139398412362e-01`
- upper model integral: `2.615058139400660564e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.248201624865941994e-13`
- extra chunk width needed: `2.248201624865941994e-13`
- lower margin: `-1.133537708142284828e-13`
- upper margin: `-1.114663916723657167e-13`
- required remainder cap: `-9.436895709313830347e-17`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.276756478318930021e-15` | `1.276756478318930021e-15` | `6.938893903907228378e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.053912595556539600e-15` | `2.053912595556539600e-15` | `1.214306433183764966e-16` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 2

- chunk interval: `[1.623500002662727337E-1, 1.623500002662727337E-1]`
- degree: `16`
- sampled max residual: `3.469446951953614189e-17`
- remainder candidate: `3.816391647148975608e-17`
- lower model integral: `1.623500002662723041e-01`
- upper model integral: `1.623500002662730812e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.771561172376095783e-16`
- extra chunk width needed: `7.771561172376095783e-16`
- lower margin: `-4.163336342344337027e-16`
- upper margin: `-3.608224830031758756e-16`
- required remainder cap: `-2.775557561562891505e-18`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.049116928532384918e-16` | `8.049116928532384918e-16` | `6.245004513516505540e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.165734175856414367e-15` | `1.165734175856414367e-15` | `9.714451465470119729e-17` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 3

- chunk interval: `[4.574132198443945260E-2, 4.574132198443945260E-2]`
- degree: `16`
- sampled max residual: `2.775557561562891351e-17`
- remainder candidate: `3.053113317719180733e-17`
- lower model integral: `4.574132198443915664e-02`
- upper model integral: `4.574132198443976727e-02`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.106226635438360972e-16`
- extra chunk width needed: `6.106226635438360972e-16`
- lower margin: `-2.983724378680108202e-16`
- upper margin: `-3.122502256758252770e-16`
- required remainder cap: `-6.938893903907228763e-19`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.012279232133096230e-16` | `2.012279232133096230e-16` | `2.255140518769849223e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.024558464266192459e-16` | `4.024558464266192459e-16` | `3.556183125752454544e-17` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 4

- chunk interval: `[6.765808406913482313E-3, 6.765808406913482313E-3]`
- degree: `16`
- sampled max residual: `5.204170427930421283e-18`
- remainder candidate: `5.724587470723463874e-18`
- lower model integral: `6.765808406913428191e-03`
- upper model integral: `6.765808406913542683e-03`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.144917494144692682e-16`
- extra chunk width needed: `1.144917494144692682e-16`
- lower margin: `-5.377642775528101993e-17`
- upper margin: `-6.071532165918824830e-17`
- required remainder cap: `-3.469446951953614381e-19`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.469446951953614189e-17` | `3.469446951953614189e-17` | `3.035766082959412415e-18` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.551115123125782702e-17` | `5.551115123125782702e-17` | `8.023096076392732812e-18` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 5

- chunk interval: `[5.169774839176038619E-4, 5.169774839176038619E-4]`
- degree: `16`
- sampled max residual: `4.065758146820641628e-19`
- remainder candidate: `4.472333961502705790e-19`
- lower model integral: `5.169774839175994129e-04`
- upper model integral: `5.169774839176083034e-04`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.890457814381136359e-18`
- extra chunk width needed: `8.890457814381136359e-18`
- lower margin: `-4.445228907190568179e-18`
- upper margin: `-4.445228907190568179e-18`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.276824562219559311e-18` | `2.276824562219559311e-18` | `3.252606517456513302e-19` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.228388472693467293e-18` | `4.228388472693467293e-18` | `4.201283418381329682e-19` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 6

- chunk interval: `[1.892225314469768391E-5, 1.892225314469768391E-5]`
- degree: `16`
- sampled max residual: `2.286988957586610915e-20`
- remainder candidate: `2.515687853345272248e-20`
- lower model integral: `1.892225314469744390e-05`
- upper model integral: `1.892225314469794535e-05`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.014435047745458007e-19`
- extra chunk width needed: `5.014435047745458007e-19`
- lower margin: `-2.405573570202212963e-19`
- upper margin: `-2.608861477543245044e-19`
- required remainder cap: `-1.016439536705160369e-21`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.486769009248163798e-20` | `9.486769009248163798e-20` | `1.609362599783170644e-20` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.524659305057740610e-19` | `1.524659305057740610e-19` | `2.032879073410320814e-20` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 7

- chunk interval: `[2.897508287881122299E-7, 2.897508287881122299E-7]`
- degree: `16`
- sampled max residual: `5.558653716356345975e-22`
- remainder candidate: `6.114519087991980949e-22`
- lower model integral: `2.897508287881063439e-07`
- upper model integral: `2.897508287881186259e-07`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.228197773518735492e-20`
- extra chunk width needed: `1.228197773518735492e-20`
- lower margin: `-5.876291071576708602e-21`
- upper margin: `-6.405686663610646314e-21`
- required remainder cap: `-2.646977960169688560e-23`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.482307657695025593e-21` | `1.482307657695025593e-21` | `2.382280164152719704e-22` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.329340604949325932e-21` | `2.329340604949325932e-21` | `3.705769144237563983e-22` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 8

- chunk interval: `[1.476670460523115116E-9, 1.476670460523115116E-9]`
- degree: `16`
- sampled max residual: `3.174426769707285650e-24`
- remainder candidate: `3.491869446678014509e-24`
- lower model integral: `1.476670460523081113e-09`
- upper model integral: `1.476670460523151010e-09`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.989676176073083853e-23`
- extra chunk width needed: `6.989676176073083853e-23`
- lower margin: `-3.391440511467413467e-23`
- upper margin: `-3.598235664605670386e-23`
- required remainder cap: `-1.033975765691284594e-25`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.824240053562478318e-24` | `6.824240053562478318e-24` | `1.344168495398669972e-24` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.199411888201890129e-23` | `1.199411888201890129e-23` | `3.308722450212110699e-24` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 9

- chunk interval: `[1.665838345718554951E-12, 1.665838345718554951E-12]`
- degree: `16`
- sampled max residual: `6.906634997391002559e-26`
- remainder candidate: `7.597298497130103733e-26`
- lower model integral: `1.665838345717786696e-12`
- upper model integral: `1.665838345719306155e-12`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.519459699426020563e-24`
- extra chunk width needed: `1.519459699426020563e-24`
- lower margin: `-7.682116821659466004e-25`
- upper margin: `-7.512480172600739625e-25`
- required remainder cap: `-8.481832452936319291e-28`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.279884061199739910e-27` | `8.279884061199739910e-27` | `2.423380700838948266e-27` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.292469707114105742e-26` | `1.292469707114105742e-26` | `2.625329092575527288e-27` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 10

- chunk interval: `[1.829338978707496745E-16, 1.829338978707496745E-16]`
- degree: `16`
- sampled max residual: `2.331687946558649722e-26`
- remainder candidate: `2.564856741214514981e-26`
- lower model integral: `1.829338976150336298e-16`
- upper model integral: `1.829338981280049780e-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.129713482429029389e-25`
- extra chunk width needed: `5.129713482429029389e-25`
- lower margin: `-2.557160417007952198e-25`
- upper margin: `-2.572553065421077191e-25`
- required remainder cap: `-7.696324206562496427e-29`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.084683744678891232e-30` | `1.084683744678891232e-30` | `2.958228394578794270e-31` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.651677520306493468e-30` | `1.651677520306493468e-30` | `5.176899690512889973e-31` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 11

- chunk interval: `[2.451698236335648757E-22, 2.451698236335648757E-22]`
- degree: `16`
- sampled max residual: `5.670110130767626932e-29`
- remainder candidate: `6.237121143844389625e-29`
- lower model integral: `2.451692036801282917e-22`
- upper model integral: `2.451704511043570606e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.247424228768877925e-27`
- extra chunk width needed: `1.247424228768877925e-27`
- lower margin: `-6.199534365911310100e-28`
- upper margin: `-6.274707921777469150e-28`
- required remainder cap: `-3.758677793307952340e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.551652543085419511e-36` | `1.551652543085419511e-36` | `5.172175143618065035e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.150324860203730521e-36` | `3.150324860203730521e-36` | `1.222514124855179008e-36` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 12

- chunk interval: `[5.042220052254024585E-34, 5.042220066155815468E-34]`
- degree: `16`
- sampled max residual: `7.323193503966108728e-36`
- remainder candidate: `8.055512855362719817e-36`
- lower model integral: `4.248076793016266729e-34`
- upper model integral: `5.859179364088810425e-34`
- current chunk width: `1.390179088300000046e-42`
- model interval width: `1.611102571072543696e-34`
- extra chunk width needed: `1.611102557170752907e-34`
- lower margin: `-7.941432592377576502e-35`
- upper margin: `-8.169592979329952569e-35`
- required remainder cap: `-1.140801239672340839e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.832099384363366927e-43` | `0.000000000000000000e+00` | `6.906697701984546990e-44` | `sampled_feasible` |
| 16 | 10 | `2.000998442492927414e-44` | `0.000000000000000000e+00` | `4.447480477593413555e-48` | `sampled_feasible` |

### primary_finite row 0 chunk 13

- chunk interval: `[1.227090661819323409E-25, 1.227090661819323409E-25]`
- degree: `16`
- sampled max residual: `1.363154224789238451e-34`
- remainder candidate: `1.499469647278162478e-34`
- lower model integral: `1.227090646974040873e-25`
- upper model integral: `1.227090676963433667e-25`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.998939279410563015e-33`
- extra chunk width needed: `2.998939279410563015e-33`
- lower margin: `-1.484528257027990772e-33`
- upper margin: `-1.514411022382572243e-33`
- required remainder cap: `-1.494138267729073598e-36`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.183549615799121156e-40` | `9.183549615799121156e-40` | `2.984653625134714376e-40` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.079067079856396736e-39` | `1.079067079856396736e-39` | `3.903008586714626491e-40` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 14

- chunk interval: `[5.828365072281494328E-21, 5.828365072281494328E-21]`
- degree: `16`
- sampled max residual: `1.323933665227714341e-33`
- remainder candidate: `1.456327031751485910e-33`
- lower model integral: `5.828365072267054338e-21`
- upper model integral: `5.828365072296181019e-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.912668114331883722e-32`
- extra chunk width needed: `2.912668114331883722e-32`
- lower margin: `-1.443996068459711131e-32`
- upper margin: `-1.468672045872172591e-32`
- required remainder cap: `-1.233798870623072861e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.009265538105056020e-35` | `3.009265538105056020e-35` | `7.523163845262640051e-36` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.438666668704957630e-35` | `4.438666668704957630e-35` | `1.053242938336769607e-35` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 15

- chunk interval: `[1.894899271905283610E-18, 1.894899271905283610E-18]`
- degree: `16`
- sampled max residual: `6.995790059709728983e-33`
- remainder candidate: `7.695369065681703318e-33`
- lower model integral: `1.894899271905206525e-18`
- upper model integral: `1.894899271905360600e-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.540743955509788682e-31`
- extra chunk width needed: `1.540743955509788682e-31`
- lower margin: `-7.703719777548943412e-32`
- upper margin: `-7.703719777548943412e-32`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.474091755303837753e-33` | `8.474091755303837753e-33` | `1.348150961071065097e-33` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.463706757734299248e-32` | `1.463706757734299248e-32` | `2.214819436045321231e-33` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 16

- chunk interval: `[4.536093331545388464E-17, 4.536093331545388464E-17]`
- degree: `16`
- sampled max residual: `2.234078735489193590e-32`
- remainder candidate: `2.457486609038213010e-32`
- lower model integral: `4.536093331545359489e-17`
- upper model integral: `4.536093331545408793e-17`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.930380657631323784e-31`
- extra chunk width needed: `4.930380657631323784e-31`
- lower margin: `-2.896598636358402723e-31`
- upper margin: `-2.033782021272921061e-31`
- required remainder cap: `-4.314083075427408037e-33`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.033782021272921061e-31` | `2.033782021272921061e-31` | `2.002967142162725287e-32` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.958228394578794270e-31` | `2.958228394578794270e-31` | `2.619264724366640760e-32` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 17

- chunk interval: `[1.859074418258514376E-16, 1.859074418258514376E-16]`
- degree: `16`
- sampled max residual: `6.162975822039154730e-32`
- remainder candidate: `6.779273404243169826e-32`
- lower model integral: `1.859074418258507506e-16`
- upper model integral: `1.859074418258521312e-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.380506584136770659e-30`
- extra chunk width needed: `1.380506584136770659e-30`
- lower margin: `-6.902532920683853297e-31`
- upper margin: `-6.902532920683853297e-31`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.888609052210118054e-31` | `7.888609052210118054e-31` | `5.238529448733281520e-32` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.429810390713083897e-30` | `1.429810390713083897e-30` | `9.552612524160689831e-32` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 18

- chunk interval: `[1.841193083173907953E-16, 1.841193083173907953E-16]`
- degree: `16`
- sampled max residual: `3.081487911019577365e-32`
- remainder candidate: `3.389636702121635272e-32`
- lower model integral: `1.841193083173905021e-16`
- upper model integral: `1.841193083173911924e-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.902532920683853297e-31`
- extra chunk width needed: `6.902532920683853297e-31`
- lower margin: `-2.958228394578794270e-31`
- upper margin: `-3.944304526105059027e-31`
- required remainder cap: `-4.930380657631324058e-33`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `8.135128085091684243e-31` | `8.135128085091684243e-31` | `5.238529448733281520e-32` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.503766100577553754e-30` | `1.503766100577553754e-30` | `1.078520768856852078e-31` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 19

- chunk interval: `[4.953039026911410582E-17, 4.953039026911410582E-17]`
- degree: `16`
- sampled max residual: `3.235562306570556233e-32`
- remainder candidate: `3.559118537227712246e-32`
- lower model integral: `4.953039026911377624e-17`
- upper model integral: `4.953039026911449115e-17`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.149051953565419487e-31`
- extra chunk width needed: `7.149051953565419487e-31`
- lower margin: `-3.266377185680752007e-31`
- upper margin: `-3.882674767884667480e-31`
- required remainder cap: `-3.081487911019577365e-33`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.403560570595270345e-31` | `2.403560570595270345e-31` | `2.002967142162725287e-32` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.759415251443884385e-31` | `3.759415251443884385e-31` | `4.314083075427408311e-32` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 20

- chunk interval: `[3.493317674510505509E-18, 3.493317674510505509E-18]`
- degree: `16`
- sampled max residual: `3.081487911019577365e-33`
- remainder candidate: `3.389636702122535716e-33`
- lower model integral: `3.493317674510473298e-18`
- upper model integral: `3.493317674510541091e-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.779273404243070203e-32`
- extra chunk width needed: `6.779273404243070203e-32`
- lower margin: `-3.235562306570556233e-32`
- upper margin: `-3.543711097672513970e-32`
- required remainder cap: `-1.540743955509788768e-34`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.848892746611746419e-32` | `1.848892746611746419e-32` | `2.888894916580853780e-33` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.158525108795066799e-32` | `3.158525108795066799e-32` | `3.851859888774471706e-33` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 21

- chunk interval: `[5.282361183823985786E-20, 5.282361183823985786E-20]`
- degree: `16`
- sampled max residual: `9.016041670806945186e-35`
- remainder candidate: `9.917645837987639593e-35`
- lower model integral: `5.282361183823886933e-20`
- upper model integral: `5.282361183824085544e-20`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.986115255149336973e-33`
- extra chunk width needed: `1.986115255149336973e-33`
- lower margin: `-9.870390964984583747e-34`
- upper margin: `-9.990761586508785988e-34`
- required remainder cap: `-6.018531076210112375e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.949080227342954900e-34` | `2.949080227342954900e-34` | `5.115751414778595235e-35` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.370377402677662743e-34` | `3.370377402677662743e-34` | `4.513898307157584031e-35` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 22

- chunk interval: `[1.060304455315527169E-22, 1.060304455315527169E-22]`
- degree: `16`
- sampled max residual: `1.770294492338364987e-35`
- remainder candidate: `1.947323941672201534e-35`
- lower model integral: `1.060304455313584025e-22`
- upper model integral: `1.060304455317478673e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.894647883144402971e-34`
- extra chunk width needed: `3.894647883144402971e-34`
- lower margin: `-1.943092161909241251e-34`
- upper margin: `-1.951555721235161721e-34`
- required remainder cap: `-4.231779662960235133e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.466878533124692530e-37` | `4.466878533124692530e-37` | `8.228460455756012556e-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.993361585591555054e-37` | `7.993361585591555054e-37` | `1.528142656068973760e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 23

- chunk interval: `[9.047626348891176453E-27, 9.047626348891191467E-27]`
- degree: `16`
- sampled max residual: `7.131112372445665694e-37`
- remainder candidate: `7.844223619690234090e-37`
- lower model integral: `9.047626341006442994e-27`
- upper model integral: `9.047626356694890213e-27`
- current chunk width: `1.501400000000000112e-41`
- model interval width: `1.568844721938046453e-35`
- extra chunk width needed: `1.568843220538046511e-35`
- lower margin: `-7.884733108003298668e-36`
- upper margin: `-7.803698327151263705e-36`
- required remainder cap: `-4.050949831306640328e-39`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.874309994165254238e-41` | `2.372909994165254381e-41` | `1.147943701974890145e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `9.183549615799121156e-41` | `7.682149615799121299e-41` | `2.869859254937225361e-41` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 24

- chunk interval: `[9.952621041934797796E-34, 9.952621539777714228E-34]`
- degree: `16`
- sampled max residual: `4.770574721512544500e-39`
- remainder candidate: `5.247633193663799429e-39`
- lower model integral: `9.952100090972409932e-34`
- upper model integral: `9.953149617611142468e-34`
- current chunk width: `4.978429164320000177e-41`
- model interval width: `1.049526638732535729e-37`
- extra chunk width needed: `1.049028795816103643e-37`
- lower margin: `-5.209509623885667986e-38`
- upper margin: `-5.280778334275362183e-38`
- required remainder cap: `-3.314514061268353869e-41`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.003401792520242316e-44` | `0.000000000000000000e+00` | `1.128975813542943441e-47` | `sampled_feasible` |
| 16 | 10 | `2.000887255480987578e-44` | `0.000000000000000000e+00` | `3.763252711809811470e-48` | `sampled_feasible` |

### primary_finite row 0 chunk 25

- chunk interval: `[2.287473435937924131E-37, 2.287487121726707353E-37]`
- degree: `16`
- sampled max residual: `8.251484583034500338e-42`
- remainder candidate: `9.077633041337950200e-42`
- lower model integral: `2.286578649622405598e-37`
- upper model integral: `2.288394176230672971e-37`
- current chunk width: `1.368578878322200058e-42`
- model interval width: `1.815526608267372666e-40`
- extra chunk width needed: `1.801840819484150740e-40`
- lower margin: `-8.947863155185525034e-41`
- upper margin: `-9.070545039655982366e-41`
- required remainder cap: `7.088001680880962758e-45`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.000003643644025958e-44` | `0.000000000000000000e+00` | `1.127572612070145038e-50` | `sampled_feasible` |
| 16 | 10 | `2.000000269278579467e-44` | `0.000000000000000000e+00` | `1.179775047814133234e-51` | `sampled_feasible` |

