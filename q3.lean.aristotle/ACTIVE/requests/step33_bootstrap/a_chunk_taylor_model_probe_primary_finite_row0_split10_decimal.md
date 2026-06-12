# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 26
- cells with sampled feasible degree: 0
- degrees: `12,16`
- fit samples: 17
- check samples: 81

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 12 | `6.105941042605931763E-1` | `6.581692593728582000E-6` | 0 |
| 16 | `2.892866741302988136E-1` | `6.479522228772200000E-7` | 0 |

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
- sampled max residual: `1.314939427859952252E-2`
- remainder candidate: `1.446433370645947477E-2`
- lower model integral: `-4.940251351143627267E-1`
- upper model integral: `-2.047384609851732313E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.892866741291894954E-1`
- extra chunk width needed: `2.892866741291895138e-01`
- lower margin: `-1.404904449144764311e-01`
- upper margin: `-1.487962292147130827e-01`
- required remainder cap: `-4.152892150118325581e-04`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.581692593728582000E-6` | `6.581692593728582000E-6` | `2.991524859093119148E-6` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `6.479522228772200000E-7` | `6.479522228772200000E-7` | `2.945236637953316716E-7` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 1

- chunk interval: `[2.615058139399545823E-1, 2.615058139399545823E-1]`
- degree: `16`
- sampled max residual: `5.041798265699124143E-14`
- remainder candidate: `5.545978092269036558E-14`
- lower model integral: `2.615058139393924298E-1`
- upper model integral: `2.615058139405016255E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.109195618453807312E-12`
- extra chunk width needed: `1.109195618453807398e-12`
- lower margin: `-5.621614285189480142e-13`
- upper margin: `-5.470623953840458853e-13`
- required remainder cap: `-7.549516567451064278e-16`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-2` | `0.000000000000000000E+18` | `1.267415974817193317E-22` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-2` | `0.000000000000000000E+18` | `1.252580481454165961E-28` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 2

- chunk interval: `[1.623500002662727337E-1, 1.623500002662727337E-1]`
- degree: `16`
- sampled max residual: `5.551529977222983068E-18`
- remainder candidate: `6.106682974945281375E-18`
- lower model integral: `1.623500002662726721E-1`
- upper model integral: `1.623500002662727942E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.221336594989056275E-16`
- extra chunk width needed: `1.221336594989056245e-16`
- lower margin: `-5.551115123125782702e-17`
- upper margin: `-8.326672684688674053e-17`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-3` | `0.000000000000000000E+18` | `1.955101217379029674E-26` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-3` | `0.000000000000000000E+18` | `1.221696263303657232E-33` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 3

- chunk interval: `[4.574132198443945260E-2, 4.574132198443945260E-2]`
- degree: `16`
- sampled max residual: `1.121164709886051520E-20`
- remainder candidate: `1.233281180874656672E-20`
- lower model integral: `4.574132198443945248E-2`
- upper model integral: `4.574132198443945272E-2`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.466562361749313344E-19`
- extra chunk width needed: `2.466562361749313391e-19`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-3` | `0.000000000000000000E+18` | `8.135488650800902898E-29` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-3` | `0.000000000000000000E+18` | `1.207765930551021426E-36` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 4

- chunk interval: `[6.765808406913482313E-3, 6.765808406913482313E-3]`
- degree: `16`
- sampled max residual: `4.188174773632566218E-21`
- remainder candidate: `4.606992250995822840E-21`
- lower model integral: `6.765808406913482267E-3`
- upper model integral: `6.765808406913482359E-3`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.213984501991645680E-20`
- extra chunk width needed: `9.213984501991646145e-20`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-4` | `0.000000000000000000E+18` | `3.827026968019373409E-29` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-4` | `0.000000000000000000E+18` | `9.006585486096974250E-38` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 5

- chunk interval: `[5.169774839176038619E-4, 5.169774839176038619E-4]`
- degree: `16`
- sampled max residual: `1.963594550730536200E-21`
- remainder candidate: `2.159954005803589820E-21`
- lower model integral: `5.169774839176038404E-4`
- upper model integral: `5.169774839176038835E-4`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.319908011607179640E-20`
- extra chunk width needed: `4.319908011607179875e-20`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-6` | `0.000000000000000000E+18` | `1.695932866613968588E-29` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-6` | `0.000000000000000000E+18` | `2.760055522520362101E-38` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 6

- chunk interval: `[1.892225314469768391E-5, 1.892225314469768391E-5]`
- degree: `16`
- sampled max residual: `6.246817458404026228E-22`
- remainder candidate: `6.871499204244428851E-22`
- lower model integral: `1.892225314469767702E-5`
- upper model integral: `1.892225314469769076E-5`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.374299840848885770E-20`
- extra chunk width needed: `1.374299840848885703e-20`
- lower margin: `-6.776263578034402713e-21`
- upper margin: `-6.776263578034402713e-21`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-7` | `0.000000000000000000E+18` | `7.148683233673288429E-30` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-7` | `0.000000000000000000E+18` | `7.091239823095172572E-39` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 7

- chunk interval: `[2.897508287881122299E-7, 2.897508287881122299E-7]`
- degree: `16`
- sampled max residual: `1.206163657131235924E-22`
- remainder candidate: `1.326780022844359516E-22`
- lower model integral: `2.897508287881109041E-7`
- upper model integral: `2.897508287881135577E-7`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.653560045688719032E-21`
- extra chunk width needed: `2.653560045688719188e-21`
- lower margin: `-1.323488980084844280e-21`
- upper margin: `-1.323488980084844280e-21`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-9` | `0.000000000000000000E+18` | `1.074508805532799164E-30` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-9` | `0.000000000000000000E+18` | `1.242208830009343960E-39` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 8

- chunk interval: `[1.476670460523115116E-9, 1.476670460523115116E-9]`
- degree: `16`
- sampled max residual: `1.180155734351862570E-23`
- remainder candidate: `1.298171307787048828E-23`
- lower model integral: `1.476670460522985631E-9`
- upper model integral: `1.476670460523245266E-9`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.596342615574097655E-22`
- extra chunk width needed: `2.596342615574097839e-22`
- lower margin: `-1.294537658645488311e-22`
- upper margin: `-1.302809464771018588e-22`
- required remainder cap: `-4.135903062765138604e-26`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-12` | `0.000000000000000000E+18` | `7.434377101358343828E-32` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-12` | `0.000000000000000000E+18` | `2.570659372004308877E-40` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 9

- chunk interval: `[1.665838345718554951E-12, 1.665838345718554951E-12]`
- degree: `16`
- sampled max residual: `3.841279126627695062E-25`
- remainder candidate: `4.225407039290464568E-25`
- lower model integral: `1.665838345714238045E-12`
- upper model integral: `1.665838345722688859E-12`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.450814078580929136E-24`
- extra chunk width needed: `8.450814078580928485e-24`
- lower margin: `-4.316848821761113178e-24`
- upper margin: `-4.133883578847772584e-24`
- required remainder cap: `-9.148262145667029131e-27`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.772000000000000000E-31` | `1.772000000000000000E-31` | `2.550517663341842125E-32` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-16` | `0.000000000000000000E+18` | `5.669839713797812843E-41` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 10

- chunk interval: `[1.829338978707496745E-16, 1.829338978707496745E-16]`
- degree: `16`
- sampled max residual: `1.191701824086073852E-25`
- remainder candidate: `1.310872006494681237E-25`
- lower model integral: `1.829338965671913017E-16`
- upper model integral: `1.829338991889353147E-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.621744012989362475E-24`
- extra chunk width needed: `2.621744012989362405e-24`
- lower margin: `-1.303558379732151471e-24`
- upper margin: `-1.318185635851985777e-24`
- required remainder cap: `-7.313628059917152716e-28`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.813860000000000000E-33` | `2.813860000000000000E-33` | `5.602035913537309170E-34` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-21` | `0.000000000000000000E+18` | `4.166146846268436723E-42` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 11

- chunk interval: `[2.451698236335648757E-22, 2.451698236335648757E-22]`
- degree: `16`
- sampled max residual: `2.881579858766867845E-28`
- remainder candidate: `3.169737844643554629E-28`
- lower model integral: `2.451666886734165096E-22`
- upper model integral: `2.451730281491057967E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.339475689287109258E-27`
- extra chunk width needed: `6.339475689287109512e-27`
- lower margin: `-3.134960148363652256e-27`
- upper margin: `-3.204515540934138155e-27`
- required remainder cap: `-3.477769626173306272e-30`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.034826326656990000E-36` | `2.034826326656990000E-36` | `5.762772380070516555E-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.343472000000000000E-44` | `1.343472000000000000E-44` | `6.074989101764863237E-44` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 12

- chunk interval: `[5.042220052254024585E-34, 5.042220066155815468E-34]`
- degree: `16`
- sampled max residual: `2.792855333891390851E-35`
- remainder candidate: `3.072140867280529936E-35`
- lower model integral: `2.043008033040402608E-34`
- upper model integral: `8.187289767601462480E-34`
- current chunk width: `1.390179088300000046e-42`
- model interval width: `6.144281734561059871E-34`
- extra chunk width needed: `6.144281720659268751e-34`
- lower margin: `-2.999212019213621904e-34`
- upper margin: `-3.145069701445647274e-34`
- required remainder cap: `-7.292883416511707841e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.319038352122093278E-43` | `0.000000000000000000E+18` | `3.942810032809339967E-43` | `sampled_feasible` |
| 16 | 10 | `5.305049728470434411E-48` | `0.000000000000000000E+18` | `2.068597539094626582E-48` | `sampled_feasible` |

### primary_finite row 0 chunk 13

- chunk interval: `[1.227090661819323409E-25, 1.227090661819323409E-25]`
- degree: `16`
- sampled max residual: `7.695302448267930769E-34`
- remainder candidate: `8.464832693094723846E-34`
- lower model integral: `1.227090578595628925E-25`
- upper model integral: `1.227090747892282787E-25`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.692966538618944769E-32`
- extra chunk width needed: `1.692966538618944860e-32`
- lower margin: `-8.322369459664006972e-33`
- upper margin: `-8.607295928238638476e-33`
- required remainder cap: `-1.424632342873157575e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.605858307160000000E-42` | `6.605858307160000000E-42` | `1.399466922699990151E-42` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.397000000000000000E-50` | `1.397000000000000000E-50` | `4.533853390198289995E-50` | `split_model_interval_wider_than_parent_chunk_interval` |

### primary_finite row 0 chunk 14

- chunk interval: `[5.828365072281494328E-21, 5.828365072281494328E-21]`
- degree: `16`
- sampled max residual: `7.211639111184068066E-33`
- remainder candidate: `7.932803022302474873E-33`
- lower model integral: `5.828365072203336781E-21`
- upper model integral: `5.828365072361992841E-21`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.586560604460494975E-31`
- extra chunk width needed: `1.586560604460494892e-31`
- lower margin: `-7.815739687204904123e-32`
- upper margin: `-8.049860546069477481e-32`
- required remainder cap: `-1.170604294322866749e-34`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.224000000000000000E-40` | `1.224000000000000000E-40` | `8.467722096909278079E-42` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-25` | `0.000000000000000000E+18` | `2.402092708650595824E-49` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 15

- chunk interval: `[1.894899271905283610E-18, 1.894899271905283610E-18]`
- degree: `16`
- sampled max residual: `3.705639563706197411E-32`
- remainder candidate: `4.076203520076817152E-32`
- lower model integral: `1.894899271904876586E-18`
- upper model integral: `1.894899271905691827E-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.152407040153634304E-31`
- extra chunk width needed: `8.152407040153633820e-31`
- lower margin: `-4.071415902434616593e-31`
- upper margin: `-4.082971482100940008e-31`
- required remainder cap: `-7.703719777548943840e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-21` | `0.000000000000000000E+18` | `4.134734332983200213E-41` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-21` | `0.000000000000000000E+18` | `4.279099727408680196E-49` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 16

- chunk interval: `[4.536093331545388464E-17, 4.536093331545388464E-17]`
- degree: `16`
- sampled max residual: `3.304762897253575249E-32`
- remainder candidate: `3.635239186978932774E-32`
- lower model integral: `4.536093331545351720E-17`
- upper model integral: `4.536093331545424425E-17`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.270478373957865547E-31`
- extra chunk width needed: `7.270478373957865508e-31`
- lower margin: `-3.697785493223492838e-31`
- upper margin: `-3.574525976782709743e-31`
- required remainder cap: `-6.162975822039155072e-34`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-19` | `0.000000000000000000E+18` | `5.747712097270531787E-41` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-19` | `0.000000000000000000E+18` | `5.821757161831823930E-49` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 17

- chunk interval: `[1.859074418258514376E-16, 1.859074418258514376E-16]`
- degree: `16`
- sampled max residual: `4.732496132019929084E-32`
- remainder candidate: `5.205745745221921993E-32`
- lower model integral: `1.859074418258509151E-16`
- upper model integral: `1.859074418258519562E-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.041149149044384399E-30`
- extra chunk width needed: `1.041149149044384456e-30`
- lower margin: `-5.176899690512889973e-31`
- upper margin: `-5.176899690512889973e-31`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-17` | `0.000000000000000000E+18` | `6.126065279050361897E-41` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-17` | `0.000000000000000000E+18` | `5.342215242919102833E-49` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 18

- chunk interval: `[1.841193083173907953E-16, 1.841193083173907953E-16]`
- degree: `16`
- sampled max residual: `9.632010442842470234E-33`
- remainder candidate: `1.059521148712671726E-32`
- lower model integral: `1.841193083173906915E-16`
- upper model integral: `1.841193083173909034E-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.119042297425343451E-31`
- extra chunk width needed: `2.119042297425343657e-31`
- lower margin: `-9.860761315262647568e-32`
- upper margin: `-9.860761315262647568e-32`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-17` | `0.000000000000000000E+18` | `4.943608981990565287E-41` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-17` | `0.000000000000000000E+18` | `4.149622166055846170E-49` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 19

- chunk interval: `[4.953039026911410582E-17, 4.953039026911410582E-17]`
- degree: `16`
- sampled max residual: `1.330078297570221173E-32`
- remainder candidate: `1.463086127327243290E-32`
- lower model integral: `4.953039026911395957E-17`
- upper model integral: `4.953039026911425218E-17`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.926172254654486580E-31`
- extra chunk width needed: `2.926172254654486618e-31`
- lower margin: `-1.417484439069005588e-31`
- upper margin: `-1.479114197289397135e-31`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-18` | `0.000000000000000000E+18` | `2.794761372356555006E-41` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-18` | `0.000000000000000000E+18` | `1.391534528795991147E-49` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 20

- chunk interval: `[3.493317674510505509E-18, 3.493317674510505509E-18]`
- degree: `16`
- sampled max residual: `2.906609765899088257E-33`
- remainder candidate: `3.197270742488997083E-33`
- lower model integral: `3.493317674510473245E-18`
- upper model integral: `3.493317674510537191E-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.394541484977994166E-32`
- extra chunk width needed: `6.394541484977994015e-32`
- lower margin: `-3.235562306570556233e-32`
- upper margin: `-3.158525108795066799e-32`
- required remainder cap: `-7.703719777548943840e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-20` | `0.000000000000000000E+18` | `5.864202510085346794E-42` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-20` | `0.000000000000000000E+18` | `5.907142882172553977E-50` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 21

- chunk interval: `[5.282361183823985786E-20, 5.282361183823985786E-20]`
- degree: `16`
- sampled max residual: `3.593502810613211520E-34`
- remainder candidate: `3.952853091674532672E-34`
- lower model integral: `5.282361183823594694E-20`
- upper model integral: `5.282361183824385264E-20`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.905706183349065345E-33`
- extra chunk width needed: `7.905706183349065078e-33`
- lower margin: `-3.912045199536572827e-33`
- upper margin: `-3.996304634603514395e-33`
- required remainder cap: `-4.212971753347078161e-36`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-22` | `0.000000000000000000E+18` | `1.106765785840547403E-42` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-22` | `0.000000000000000000E+18` | `1.803715690100047342E-50` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 22

- chunk interval: `[1.060304455315527169E-22, 1.060304455315527169E-22]`
- degree: `16`
- sampled max residual: `8.924321464778033532E-35`
- remainder candidate: `9.816753611255836886E-35`
- lower model integral: `1.060304455305737120E-22`
- upper model integral: `1.060304455325370627E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.963350722251167377E-33`
- extra chunk width needed: `1.963350722251167425e-33`
- lower margin: `-9.789987151388339281e-34`
- upper margin: `-9.843589693785835592e-34`
- required remainder cap: `-2.680127119874815602e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.110000000000000000E-42` | `1.110000000000000000E-42` | `1.507244343365018153E-43` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `1.087484655968893876E-51` | `split_integral_center_mismatch` |

### primary_finite row 0 chunk 23

- chunk interval: `[9.047626348891176453E-27, 9.047626348891191467E-27]`
- degree: `16`
- sampled max residual: `3.685009219184958098E-36`
- remainder candidate: `4.053510141103453907E-36`
- lower model integral: `9.047626307968275637E-27`
- upper model integral: `9.047626389038478459E-27`
- current chunk width: `1.501400000000000112e-41`
- model interval width: `8.107020282206907815E-35`
- extra chunk width needed: `8.107018780806908114e-35`
- lower margin: `-4.092290010381048443e-35`
- upper margin: `-4.014728620185264003e-35`
- required remainder cap: `-3.877983414011573677e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.685643400000000000E-44` | `0.000000000000000000E+18` | `8.669307672846701953E-45` | `sampled_feasible` |
| 16 | 10 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `1.173881858068918930E-52` | `sampled_feasible` |

### primary_finite row 0 chunk 24

- chunk interval: `[9.952621041934797796E-34, 9.952621539777714228E-34]`
- degree: `16`
- sampled max residual: `2.422404243145062038E-38`
- remainder candidate: `2.664644667459568242E-38`
- lower model integral: `9.949989624863829648E-34`
- upper model integral: `9.955318914198748784E-34`
- current chunk width: `4.978429164320000177e-41`
- model interval width: `5.329289334919136484E-37`
- extra chunk width needed: `5.328791492002704203e-37`
- lower margin: `-2.631417070969559518e-37`
- upper margin: `-2.697374421033529730e-37`
- required remainder cap: `-3.272975357376875044e-40`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.389521074615749381E-46` | `0.000000000000000000E+18` | `4.247777186246625555E-47` | `sampled_feasible` |
| 16 | 10 | `1.518101547315451900E-53` | `0.000000000000000000E+18` | `4.277049377182868155E-54` | `sampled_feasible` |

### primary_finite row 0 chunk 25

- chunk interval: `[2.287473435937924131E-37, 2.287487121726707353E-37]`
- degree: `16`
- sampled max residual: `4.255898273458220007E-41`
- remainder candidate: `4.681488100804042008E-41`
- lower model integral: `2.282857708330957043E-37`
- upper model integral: `2.292220684532565127E-37`
- current chunk width: `1.368578878322200058e-42`
- model interval width: `9.362976201608084016E-40`
- extra chunk width needed: `9.349290412824862836e-40`
- lower margin: `-4.615727606967295247e-40`
- upper margin: `-4.733562805857941163e-40`
- required remainder cap: `-5.207470505392080654e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.968803883669887967E-49` | `0.000000000000000000E+18` | `5.989309626917644453E-50` | `sampled_feasible` |
| 16 | 10 | `1.166951957700370511E-55` | `0.000000000000000000E+18` | `2.841222730517599798E-57` | `sampled_feasible` |

