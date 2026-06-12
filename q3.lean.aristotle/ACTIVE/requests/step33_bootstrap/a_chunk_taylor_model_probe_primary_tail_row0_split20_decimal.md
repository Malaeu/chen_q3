# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 26
- cells with sampled feasible degree: 15
- degrees: `16,20`
- fit samples: 17
- check samples: 61

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 16 | `1.069959434584423830E-35` | `1.006254809592333229E-63` | 11 |
| 20 | `6.396100277982145387E-40` | `5.827792179832646054E-75` | 11 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_tail` | 0 | `0.00` | 0 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 1 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 2 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 3 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 4 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 5 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 6 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 7 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 8 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 9 | `20` | 20 |
| `primary_tail` | 0 | `0.00` | 10 | `20` | 20 |
| `primary_tail` | 0 | `0.00` | 11 | `16,20` | 16 |
| `primary_tail` | 0 | `0.00` | 12 | `16,20` | 16 |
| `primary_tail` | 0 | `0.00` | 13 | `16,20` | 16 |
| `primary_tail` | 0 | `0.00` | 14 | `20` | 20 |
| `primary_tail` | 0 | `0.00` | 15 | `20` | 16 |
| `primary_tail` | 0 | `0.00` | 16 | `20` | 20 |
| `primary_tail` | 0 | `0.00` | 17 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 18 | `-` | 20 |
| `primary_tail` | 0 | `0.00` | 19 | `20` | 20 |
| `primary_tail` | 0 | `0.00` | 20 | `20` | 20 |
| `primary_tail` | 0 | `0.00` | 21 | `20` | 16 |
| `primary_tail` | 0 | `0.00` | 22 | `16,20` | 16 |
| `primary_tail` | 0 | `0.00` | 23 | `16,20` | 16 |
| `primary_tail` | 0 | `0.00` | 24 | `16,20` | 16 |
| `primary_tail` | 0 | `0.00` | 25 | `16,20` | 16 |

## Best Degree Details

### primary_tail row 0 chunk 0

- chunk interval: `[1.088613911944200701E-29, 1.088613911944221150E-29]`
- degree: `20`
- sampled max residual: `5.368079448005079965E-43`
- remainder candidate: `5.904887392805587961E-43`
- lower model integral: `1.088613911943623623E-29`
- upper model integral: `1.088613911944804601E-29`
- current chunk width: `2.044899999999999842e-43`
- model interval width: `1.180977478561117592E-41`
- extra chunk width needed: `1.160528478561117659e-41`
- lower margin: `-5.770547076089596698e-42`
- upper margin: `-5.835006805448538283e-42`
- required remainder cap: `7.006492321624085355e-45`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-37` | `0.000000000000000000E+18` | `4.887859129892461288E-61` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-37` | `0.000000000000000000E+18` | `7.180098054068599441E-70` | `sampled_feasible` |

### primary_tail row 0 chunk 1

- chunk interval: `[7.162922067052422385E-26, 7.162922067052422487E-26]`
- degree: `20`
- sampled max residual: `2.574566653881967778E-42`
- remainder candidate: `2.832023319270164556E-42`
- lower model integral: `7.162922067052419613E-26`
- upper model integral: `7.162922067052425277E-26`
- current chunk width: `1.019999999999999940e-42`
- model interval width: `5.664046638540329112E-41`
- extra chunk width needed: `5.562046638540329275e-41`
- lower margin: `-3.443831105924670434e-41`
- upper margin: `-2.295887403949780289e-41`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-30` | `0.000000000000000000E+18` | `3.841390279308805279E-60` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-30` | `0.000000000000000000E+18` | `2.351730683925947688E-69` | `sampled_feasible` |

### primary_tail row 0 chunk 2

- chunk interval: `[1.174784504455502726E-23, 1.174784504455502726E-23]`
- degree: `20`
- sampled max residual: `6.659089258830299594E-42`
- remainder candidate: `7.324998184713329553E-42`
- lower model integral: `1.174784504455502719E-23`
- upper model integral: `1.174784504455502733E-23`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.464999636942665911E-40`
- extra chunk width needed: `1.464999636942665882e-40`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `9.606384773352084647E-60` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `3.392786023715215357E-69` | `split_integral_center_mismatch` |

### primary_tail row 0 chunk 3

- chunk interval: `[2.109279318875671532E-22, 2.109279318875671532E-22]`
- degree: `20`
- sampled max residual: `3.255805784230956100E-42`
- remainder candidate: `3.581386362654051710E-42`
- lower model integral: `2.109279318875671532E-22`
- upper model integral: `2.109279318875671533E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.162772725308103419E-41`
- extra chunk width needed: `7.162772725308103035e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-24` | `0.000000000000000000E+18` | `1.423757689491986214E-59` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-24` | `0.000000000000000000E+18` | `4.755028473255566123E-69` | `split_integral_center_mismatch` |

### primary_tail row 0 chunk 4

- chunk interval: `[7.464841416472772846E-22, 7.464841416472772846E-22]`
- degree: `20`
- sampled max residual: `8.394348606742547970E-42`
- remainder candidate: `9.233783467416802767E-42`
- lower model integral: `7.464841416472772845E-22`
- upper model integral: `7.464841416472772846E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.846756693483360553E-40`
- extra chunk width needed: `1.846756693483360532e-40`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `1.490113640955050889E-59` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `4.560258297885883213E-69` | `split_integral_center_mismatch` |

### primary_tail row 0 chunk 5

- chunk interval: `[6.632731636340872877E-22, 6.632731636340872877E-22]`
- degree: `20`
- sampled max residual: `3.906713095660193623E-42`
- remainder candidate: `4.297384405226212986E-42`
- lower model integral: `6.632731636340872877E-22`
- upper model integral: `6.632731636340872878E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.594768810452425971E-41`
- extra chunk width needed: `8.594768810452425817e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `1.276799734572034295E-59` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `3.840176436922629547E-69` | `split_integral_center_mismatch` |

### primary_tail row 0 chunk 6

- chunk interval: `[1.562922755943454187E-22, 1.562922755943454187E-22]`
- degree: `20`
- sampled max residual: `2.756912122008753306E-42`
- remainder candidate: `3.032603334209628636E-42`
- lower model integral: `1.562922755943454187E-22`
- upper model integral: `1.562922755943454187E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.065206668419257273E-41`
- extra chunk width needed: `6.065206668419257355e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-24` | `0.000000000000000000E+18` | `5.313877190640583046E-60` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-24` | `0.000000000000000000E+18` | `1.771200464124651795E-69` | `sampled_feasible` |

### primary_tail row 0 chunk 7

- chunk interval: `[8.856206616415421738E-24, 8.856206616415421738E-24]`
- degree: `20`
- sampled max residual: `7.347721606232841677E-43`
- remainder candidate: `8.082493766856125844E-43`
- lower model integral: `8.856206616415421729E-24`
- upper model integral: `8.856206616415421746E-24`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.616498753371225169E-41`
- extra chunk width needed: `1.616498753371225108e-41`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `2.506481373236672825E-60` | `split_integral_center_mismatch` |
| 20 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `9.432364019793949146E-70` | `split_integral_center_mismatch` |

### primary_tail row 0 chunk 8

- chunk interval: `[8.959177851417245136E-26, 8.959177851417245137E-26]`
- degree: `20`
- sampled max residual: `2.169581883555369299E-43`
- remainder candidate: `2.386540071910906229E-43`
- lower model integral: `8.959177851417244896E-26`
- upper model integral: `8.959177851417245374E-26`
- current chunk width: `9.999999999999999530e-45`
- model interval width: `4.773080143821812459E-42`
- extra chunk width needed: `4.763080143821812461e-42`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-29` | `0.000000000000000000E+18` | `7.609557846641112683E-61` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-29` | `0.000000000000000000E+18` | `1.752845910722612250E-70` | `sampled_feasible` |

### primary_tail row 0 chunk 9

- chunk interval: `[8.140234144392528233E-29, 8.140234144400148171E-29]`
- degree: `20`
- sampled max residual: `2.915402427941551321E-44`
- remainder candidate: `3.206942670735706453E-44`
- lower model integral: `8.140234144396306182E-29`
- upper model integral: `8.140234144396370321E-29`
- current chunk width: `7.619937999999999770e-41`
- model interval width: `6.413885341471412905E-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `3.777900659819706823e-41`
- upper margin: `3.777900659819706823e-41`
- required remainder cap: `3.810410784192042324e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `5.554085694688640169E-62` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-33` | `0.000000000000000000E+18` | `4.850053348138436853E-71` | `sampled_feasible` |

### primary_tail row 0 chunk 10

- chunk interval: `[1.140827387352955264E-33, 1.140827387524570999E-33]`
- degree: `20`
- sampled max residual: `7.473989497535192667E-46`
- remainder candidate: `8.221388447288711933E-46`
- lower model integral: `1.140827387430693837E-33`
- upper model integral: `1.140827387447136614E-33`
- current chunk width: `1.716157350000000034e-43`
- model interval width: `1.644277689457742387E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `7.773870866644539683e-44`
- upper margin: `7.743439836761313981e-44`
- required remainder cap: `8.565573708738601315e-45`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-42` | `0.000000000000000000E+18` | `6.772690866606023693E-63` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-42` | `0.000000000000000000E+18` | `3.044079667107487455E-72` | `sampled_feasible` |

### primary_tail row 0 chunk 11

- chunk interval: `[-8.837748021078401890E-42, 8.837748021079727269E-42]`
- degree: `16`
- sampled max residual: `1.669483516466391636E-45`
- remainder candidate: `1.836431868113030800E-45`
- lower model integral: `2.255435910494654791E-43`
- upper model integral: `2.622722284117260950E-43`
- current chunk width: `1.767549604215812916e-41`
- model interval width: `3.672863736226061600E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `9.063291612127867397e-42`
- upper margin: `8.575475792668001496e-42`
- required remainder cap: `8.593840111349131629e-43`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `1.004835721372541693E-63` | `0.000000000000000000E+18` | `5.758343223717263303E-65` | `sampled_feasible` |
| 20 | 20 | `5.814645108962224000E-75` | `0.000000000000000000E+18` | `4.419065153120971550E-74` | `sampled_feasible` |

### primary_tail row 0 chunk 12

- chunk interval: `[3.059912354327532428E-37, 3.060735573364219415E-37]`
- degree: `16`
- sampled max residual: `2.059507480794628355E-44`
- remainder candidate: `2.265458228874091191E-44`
- lower model integral: `3.060321628509029705E-37`
- upper model integral: `3.060326159425487454E-37`
- current chunk width: `8.232190366869870071e-41`
- model interval width: `4.530916457748182381E-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.092741814974117616e-41`
- upper margin: `4.094139387316279119e-41`
- required remainder cap: `4.115396397261765804e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `4.130000000000000000E-67` | `0.000000000000000000E+18` | `1.995276711462449830E-65` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-51` | `0.000000000000000000E+18` | `3.774940576585937499E-74` | `sampled_feasible` |

### primary_tail row 0 chunk 13

- chunk interval: `[1.154864319132177578E-31, 1.154864321102527489E-31]`
- degree: `16`
- sampled max residual: `1.045803432546298027E-42`
- remainder candidate: `1.150383775800927830E-42`
- lower model integral: `1.154864320001284079E-31`
- upper model integral: `1.154864320231360835E-31`
- current chunk width: `1.970349911000000179e-40`
- model interval width: `2.300767551601855659E-41`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `8.691065460041014704e-41`
- upper margin: `8.711666736995440022e-41`
- required remainder cap: `9.841448297155370743e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-37` | `0.000000000000000000E+18` | `3.619956646800403699E-64` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-37` | `0.000000000000000000E+18` | `1.714922052294283525E-73` | `sampled_feasible` |

### primary_tail row 0 chunk 14

- chunk interval: `[1.466836656785285560E-28, 1.466836656785516390E-28]`
- degree: `20`
- sampled max residual: `5.661372768646634081E-46`
- remainder candidate: `6.227510045511297489E-46`
- lower model integral: `1.466836656785400913E-28`
- upper model integral: `1.466836656785401038E-28`
- current chunk width: `2.308299999999999999e-41`
- model interval width: `1.245502009102259498E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `1.152427857060729559e-41`
- upper margin: `1.152427857060729559e-41`
- required remainder cap: `1.152427857060729527e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-32` | `0.000000000000000000E+18` | `9.713074354230529931E-64` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-32` | `0.000000000000000000E+18` | `5.439528665968640091E-73` | `sampled_feasible` |

### primary_tail row 0 chunk 15

- chunk interval: `[1.039353807274181180E-26, 1.039353807274190931E-26]`
- degree: `16`
- sampled max residual: `6.443440598215832123E-42`
- remainder candidate: `7.087784658037415335E-42`
- lower model integral: `1.039353807274179212E-26`
- upper model integral: `1.039353807274193387E-26`
- current chunk width: `9.750999999999999342e-41`
- model interval width: `1.417556931607483067E-40`
- extra chunk width needed: `4.424569316074832003e-41`
- lower margin: `-1.865408515709196485e-41`
- upper margin: `-2.439380366696641557e-41`
- required remainder cap: `4.591774807899560833e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-29` | `0.000000000000000000E+18` | `3.065009735282300707E-63` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-29` | `0.000000000000000000E+18` | `1.138328112111420283E-72` | `sampled_feasible` |

### primary_tail row 0 chunk 16

- chunk interval: `[1.088964554058981853E-25, 1.088964554058983101E-25]`
- degree: `20`
- sampled max residual: `2.644757143927121380E-45`
- remainder candidate: `2.909232858319833518E-45`
- lower model integral: `1.088964554058982477E-25`
- upper model integral: `1.088964554058982477E-25`
- current chunk width: `1.248000000000000052e-40`
- model interval width: `5.818465716639667036E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.591774807899560578e-41`
- upper margin: `6.887662211849340867e-41`
- required remainder cap: `4.591774807899560833e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `4.057596873281736853E-63` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `1.330715271750769887E-72` | `sampled_feasible` |

### primary_tail row 0 chunk 17

- chunk interval: `[2.540430612489620270E-25, 2.540430612489620418E-25]`
- degree: `20`
- sampled max residual: `3.685971597838741363E-46`
- remainder candidate: `4.054568757622615499E-46`
- lower model integral: `2.540430612489620344E-25`
- upper model integral: `2.540430612489620344E-25`
- current chunk width: `1.480000000000000075e-41`
- model interval width: `8.109137515245230999E-45`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.591774807899560578e-41`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `candidate_not_sampled_feasible`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `4.444101113116978327E-63` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-26` | `0.000000000000000000E+18` | `1.353151586247470839E-72` | `sampled_feasible` |

### primary_tail row 0 chunk 18

- chunk interval: `[1.540147041358927228E-25, 1.540147041358927315E-25]`
- degree: `20`
- sampled max residual: `1.810685359218516943E-45`
- remainder candidate: `1.991753895140368637E-45`
- lower model integral: `1.540147041358927271E-25`
- upper model integral: `1.540147041358927272E-25`
- current chunk width: `8.699999999999999579e-42`
- model interval width: `3.983507790280737274E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `0.000000000000000000e+00`
- upper margin: `2.295887403949780289e-41`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `candidate_not_sampled_feasible`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `2.958962224555526001E-63` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `9.139457354529086827E-73` | `sampled_feasible` |

### primary_tail row 0 chunk 19

- chunk interval: `[2.405481629996556414E-26, 2.405481629996558583E-26]`
- degree: `20`
- sampled max residual: `2.848255112693400528E-46`
- remainder candidate: `3.133080623962740581E-46`
- lower model integral: `2.405481629996557498E-26`
- upper model integral: `2.405481629996557499E-26`
- current chunk width: `2.168999999999999972e-41`
- model interval width: `6.266161247925481162E-45`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `1.147943701974890145e-41`
- upper margin: `1.147943701974890145e-41`
- required remainder cap: `1.147943701974890208e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `1.801279522420515746E-63` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-28` | `0.000000000000000000E+18` | `6.075352904594603819E-73` | `sampled_feasible` |

### primary_tail row 0 chunk 20

- chunk interval: `[8.147318881491188501E-28, 8.147318881491492156E-28]`
- degree: `20`
- sampled max residual: `2.976221540387299660E-46`
- remainder candidate: `3.273843694426029626E-46`
- lower model integral: `8.147318881491340295E-28`
- upper model integral: `8.147318881491340361E-28`
- current chunk width: `3.036550000000000020e-41`
- model interval width: `6.547687388852059252E-45`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `1.506676108842043315e-41`
- upper margin: `1.524612729185400973e-41`
- required remainder cap: `1.506676108842043378e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-30` | `0.000000000000000000E+18` | `7.919803764043238153E-64` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-30` | `0.000000000000000000E+18` | `1.693511610247807745E-73` | `sampled_feasible` |

### primary_tail row 0 chunk 21

- chunk interval: `[3.897019935837682468E-30, 3.897019935848419416E-30]`
- degree: `16`
- sampled max residual: `8.952444935733996307E-43`
- remainder candidate: `9.847689429307395938E-43`
- lower model integral: `3.897019935833141812E-30`
- upper model integral: `3.897019935852837191E-30`
- current chunk width: `1.073694800000000012e-41`
- model interval width: `1.969537885861479188E-41`
- extra chunk width needed: `8.958430858614792088e-42`
- lower margin: `-4.540907673644569718e-42`
- upper margin: `-4.418294058016148225e-42`
- required remainder cap: `5.307417933630244656e-43`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-34` | `0.000000000000000000E+18` | `1.031692829650500032E-64` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-34` | `0.000000000000000000E+18` | `6.938972895774958172E-74` | `sampled_feasible` |

### primary_tail row 0 chunk 22

- chunk interval: `[9.619205939759073932E-34, 9.619207532651919918E-34]`
- degree: `16`
- sampled max residual: `2.963937370565279974E-44`
- remainder candidate: `3.260331107621807971E-44`
- lower model integral: `9.619206732982978849E-34`
- upper model integral: `9.619206739503641064E-34`
- current chunk width: `1.592892845985999954e-40`
- model interval width: `6.520662215243615942E-43`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `7.932239060759395473e-41`
- upper margin: `7.931482783809874858e-41`
- required remainder cap: `7.964086100003910340e-42`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-39` | `0.000000000000000000E+18` | `2.113389005311758965E-65` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-39` | `0.000000000000000000E+18` | `6.637290786570527961E-75` | `sampled_feasible` |

### primary_tail row 0 chunk 23

- chunk interval: `[6.535489503380224650E-40, 6.536662018235220400E-40]`
- degree: `16`
- sampled max residual: `1.349339308926366643E-45`
- remainder candidate: `1.484273239819003307E-45`
- lower model integral: `6.535928468896332843E-40`
- upper model integral: `6.536225323544296644E-40`
- current chunk width: `1.172514854995750051e-43`
- model interval width: `2.968546479638006615E-44`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `4.389655161083892292e-44`
- upper margin: `4.366946909234534755e-44`
- required remainder cap: `5.851220149054067004e-45`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `1.005116800000000000E-66` | `0.000000000000000000E+18` | `2.509752655042616951E-67` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-55` | `0.000000000000000000E+18` | `6.312605540379211325E-76` | `sampled_feasible` |

### primary_tail row 0 chunk 24

- chunk interval: `[-2.225337606182590454E-44, 2.225337606187822005E-44]`
- degree: `16`
- sampled max residual: `1.041458745037029146E-48`
- remainder candidate: `1.145604619540732061E-48`
- lower model integral: `4.048770467735195376E-46`
- upper model integral: `4.277891391643341789E-46`
- current chunk width: `4.450675212370412459e-44`
- model interval width: `2.291209239081464122E-47`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `2.265825310859942325e-44`
- upper margin: `2.182558692271388481e-44`
- required remainder cap: `2.183704296890929058e-45`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `9.714197915355825315E-70` | `0.000000000000000000E+18` | `3.555230321671877627E-69` | `sampled_feasible` |
| 20 | 20 | `1.314707087042205425E-77` | `0.000000000000000000E+18` | `7.639050345123094529E-78` | `sampled_feasible` |

### primary_tail row 0 chunk 25

- chunk interval: `[3.214914812559243507E-37, 3.214930332717216431E-37]`
- degree: `16`
- sampled max residual: `4.487396387575612510E-46`
- remainder candidate: `4.936136026333173761E-46`
- lower model integral: `3.214922523409382241E-37`
- upper model integral: `3.214922622132102767E-37`
- current chunk width: `1.552015797292399841e-42`
- model interval width: `9.872272052666347523E-45`
- extra chunk width needed: `0.000000000000000000e+00`
- lower margin: `7.710850138854734139e-43`
- upper margin: `7.710585113352754200e-43`
- required remainder cap: `7.759946473710943721e-44`
- failure mode: `sampled_feasible`
- fits sampled residual and integral: `True`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 20 | `0.000000000000000000E-45` | `0.000000000000000000E+18` | `1.989224631721946973E-67` | `sampled_feasible` |
| 20 | 20 | `0.000000000000000000E-45` | `0.000000000000000000E+18` | `1.042198831681089754E-76` | `sampled_feasible` |

