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
| 12 | `6.698052927670270969E-1` | `7.219926990587104000E-6` | 0 |
| 16 | `3.173397702708245806E-1` | `7.107849046027000000E-7` | 0 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_finite` | 0 | `0.00` | 0 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 1 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 2 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 3 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 4 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 5 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 6 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 7 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 8 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 9 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 10 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 11 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 12 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 13 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 14 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 15 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 16 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 17 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 18 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 19 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 20 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 21 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 22 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 23 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 24 | `-` | 16 |
| `control_finite` | 0 | `0.00` | 25 | `-` | 16 |

## Best Degree Details

### control_finite row 0 chunk 0

- chunk interval: `[-3.887204663947871600E-1, -3.887204663947871600E-1]`
- degree: `16`
- sampled max residual: `1.442453501225494422E-2`
- remainder candidate: `1.586698851348043864E-2`
- lower model integral: `-5.428347431903619699E-1`
- upper model integral: `-2.254949729207531970E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.173397702696087729E-1`
- extra chunk width needed: `3.173397702696087452e-01`
- lower margin: `-1.541142767955748227e-01`
- upper margin: `-1.632254934740339503e-01`
- required remainder cap: `-4.555608339229577424e-04`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.219926990587104000E-6` | `7.219926990587104000E-6` | `3.281616509122616080E-6` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.107849046027000000E-7` | `7.107849046027000000E-7` | `3.230839665067250583E-7` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 1

- chunk interval: `[2.546688145455398839E-1, 2.546688145455398839E-1]`
- degree: `16`
- sampled max residual: `5.525791051748316144E-14`
- remainder candidate: `6.078370156923147758E-14`
- lower model integral: `2.546688145449237665E-1`
- upper model integral: `2.546688145461394406E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.215674031384629552E-12`
- extra chunk width needed: `1.215674031384629616e-12`
- lower margin: `-6.160627563644993643e-13`
- upper margin: `-5.995759444488157897e-13`
- required remainder cap: `-8.271161533457416423e-16`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-2` | `0.000000000000000000E+18` | `1.389052157517324594E-22` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-2` | `0.000000000000000000E+18` | `1.372682360569708477E-28` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 2

- chunk interval: `[1.307425628490114938E-1, 1.307425628490114938E-1]`
- degree: `16`
- sampled max residual: `6.027661686232017326E-18`
- remainder candidate: `6.630427854855219059E-18`
- lower model integral: `1.307425628490114269E-1`
- upper model integral: `1.307425628490115595E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.326085570971043812E-16`
- extra chunk width needed: `1.326085570971043921e-16`
- lower margin: `-8.326672684688674053e-17`
- upper margin: `-5.551115123125782702e-17`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-3` | `0.000000000000000000E+18` | `2.183448907938644084E-26` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-3` | `0.000000000000000000E+18` | `1.338363771574160853E-33` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 3

- chunk interval: `[2.695636479632815730E-2, 2.695636479632815730E-2]`
- degree: `16`
- sampled max residual: `3.826727849210696524E-20`
- remainder candidate: `4.209400634131766176E-20`
- lower model integral: `2.695636479632815688E-2`
- upper model integral: `2.695636479632815772E-2`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `8.418801268263532352E-19`
- extra chunk width needed: `8.418801268263532031e-19`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-4` | `0.000000000000000000E+18` | `2.798171048113632178E-28` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-4` | `0.000000000000000000E+18` | `9.919201645795821306E-37` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 4

- chunk interval: `[2.503180893782816734E-3, 2.503180893782816734E-3]`
- degree: `16`
- sampled max residual: `7.698051765129198517E-21`
- remainder candidate: `8.467856941642118368E-21`
- lower model integral: `2.503180893782816648E-3`
- upper model integral: `2.503180893782816818E-3`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.693571388328423674E-19`
- extra chunk width needed: `1.693571388328423744e-19`
- lower margin: `0.000000000000000000e+00`
- upper margin: `0.000000000000000000e+00`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-5` | `0.000000000000000000E+18` | `1.316831940954384828E-28` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-5` | `0.000000000000000000E+18` | `2.701950456838170533E-37` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 5

- chunk interval: `[9.713320536247765406E-5, 9.713320536247765406E-5]`
- degree: `16`
- sampled max residual: `1.656846680149793641E-21`
- remainder candidate: `1.822531348164773006E-21`
- lower model integral: `9.713320536247763612E-5`
- upper model integral: `9.713320536247767257E-5`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.645062696329546011E-20`
- extra chunk width needed: `3.645062696329546108e-20`
- lower margin: `-1.355252715606880543e-20`
- upper margin: `-1.355252715606880543e-20`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-7` | `0.000000000000000000E+18` | `3.053957009213229298E-29` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-7` | `0.000000000000000000E+18` | `9.889962001697917242E-38` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 6

- chunk interval: `[1.309463143374291504E-6, 1.309463143374291504E-6]`
- degree: `16`
- sampled max residual: `1.659481944556366414E-22`
- remainder candidate: `1.825430139012003056E-22`
- lower model integral: `1.309463143374289608E-6`
- upper model integral: `1.309463143374293259E-6`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.650860278024006112E-21`
- extra chunk width needed: `3.650860278024005820e-21`
- lower margin: `-1.905824131322175763e-21`
- upper margin: `-1.694065894508600678e-21`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-9` | `0.000000000000000000E+18` | `4.146041850067608373E-30` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-9` | `0.000000000000000000E+18` | `2.797458654060721865E-38` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 7

- chunk interval: `[4.298555905056391531E-9, 4.298555905056391531E-9]`
- degree: `16`
- sampled max residual: `5.249065474092823587E-23`
- remainder candidate: `5.773972021502105946E-23`
- lower model integral: `4.298555905055826320E-9`
- upper model integral: `4.298555905056981115E-9`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.154794404300421189E-21`
- extra chunk width needed: `1.154794404300421232e-21`
- lower margin: `-5.649643583737179019e-22`
- upper margin: `-5.897797767503087322e-22`
- required remainder cap: `-1.240770918829541512e-24`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.000000000000000000E-30` | `1.000000000000000000E-30` | `1.496893313499434546E-30` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-12` | `0.000000000000000000E+18` | `5.454456200786284249E-39` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 8

- chunk interval: `[1.638304517494040998E-12, 1.638304517494040998E-12]`
- degree: `16`
- sampled max residual: `1.045175876041677204E-23`
- remainder candidate: `1.149693463645844925E-23`
- lower model integral: `1.638304517377782703E-12`
- upper model integral: `1.638304517607721395E-12`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.299386927291689850E-22`
- extra chunk width needed: `2.299386927291689679e-22`
- lower margin: `-1.162582560000890212e-22`
- upper margin: `-1.136803847795715900e-22`
- required remainder cap: `-1.288834636062847411e-25`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.018170000000000000E-30` | `1.018170000000000000E-30` | `1.614858104264455197E-31` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-17` | `0.000000000000000000E+18` | `6.549663349145081872E-40` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 9

- chunk interval: `[1.041377626709139973E-17, 1.041377626709139973E-17]`
- degree: `16`
- sampled max residual: `7.885557477572802640E-25`
- remainder candidate: `8.674113225330082904E-25`
- lower model integral: `1.041376765470711985E-17`
- upper model integral: `1.041378500293357051E-17`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.734822645066016581E-23`
- extra chunk width needed: `1.734822645066016436e-23`
- lower margin: `-8.612384279703650746e-24`
- upper margin: `-8.735842171550937592e-24`
- required remainder cap: `-6.172894669401540383e-27`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.540324542433000000E-33` | `9.540324542433000000E-33` | `2.237552218962100628E-33` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.481000000000000000E-41` | `1.481000000000000000E-41` | `3.581300123023375899E-41` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 10

- chunk interval: `[2.882814182503397357E-28, 2.882814182503409833E-28]`
- degree: `16`
- sampled max residual: `4.891978776514200322E-30`
- remainder candidate: `5.381176654165620355E-30`
- lower model integral: `2.359787812179248396E-28`
- upper model integral: `3.436023143012372467E-28`
- current chunk width: `1.247600000000000013e-42`
- model interval width: `1.076235330833124071E-28`
- extra chunk width needed: `1.076235330833111590e-28`
- lower margin: `-5.230263703241487574e-29`
- upper margin: `-5.532089605089628325e-29`
- required remainder cap: `-1.509129509240053599e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.892077565041735206E-38` | `9.891952805041735206E-38` | `3.948552189048297151E-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.240961073934802651E-43` | `0.000000000000000000E+18` | `7.718730103331006364E-44` | `sampled_feasible` |

### control_finite row 0 chunk 11

- chunk interval: `[1.003957457774199916E-19, 1.003957457774199916E-19]`
- degree: `16`
- sampled max residual: `3.287803522920123944E-29`
- remainder candidate: `3.616583875212136339E-29`
- lower model integral: `1.003957454124724524E-19`
- upper model integral: `1.003957461357892275E-19`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `7.233167750424272677E-28`
- extra chunk width needed: `7.233167750424272338e-28`
- lower margin: `-3.649475346127861890e-28`
- upper margin: `-3.583692319982399268e-28`
- required remainder cap: `-3.289151307273131158e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.212663620000000000E-37` | `1.212663620000000000E-37` | `1.784838551414980816E-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `4.756917573408463626E-46` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 12

- chunk interval: `[2.904838114089298239E-16, 2.904838114089298239E-16]`
- degree: `16`
- sampled max residual: `8.020702658753062114E-29`
- remainder candidate: `8.822772924628368325E-29`
- lower model integral: `2.904838114080421884E-16`
- upper model integral: `2.904838114098067430E-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.764554584925673665E-27`
- extra chunk width needed: `1.764554584925673770e-27`
- lower margin: `-8.876164297933672208e-28`
- upper margin: `-8.769175037663072482e-28`
- required remainder cap: `-5.374114916818143100e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.000000000000000000E-37` | `1.000000000000000000E-37` | `4.310340166096634303E-38` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-19` | `0.000000000000000000E+18` | `9.824780694900968859E-46` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 13

- chunk interval: `[1.524260430846941593E-14, 1.524260430846941593E-14]`
- degree: `16`
- sampled max residual: `2.976334430012531606E-29`
- remainder candidate: `3.273967873013784766E-29`
- lower model integral: `1.524260430846907882E-14`
- upper model integral: `1.524260430846973361E-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.547935746027569533E-28`
- extra chunk width needed: `6.547935746027569754e-28`
- lower margin: `-3.376324674345930527e-28`
- upper margin: `-3.155443620884047222e-28`
- required remainder cap: `-9.466330862652141315e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-16` | `0.000000000000000000E+18` | `8.589020673987915759E-38` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-16` | `0.000000000000000000E+18` | `1.159888639881692687E-45` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 14

- chunk interval: `[8.279132473214025765E-14, 8.279132473214025765E-14]`
- degree: `16`
- sampled max residual: `8.903784282763833199E-29`
- remainder candidate: `9.794162711040216519E-29`
- lower model integral: `8.279132473213927468E-14`
- upper model integral: `8.279132473214123351E-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.958832542208043304E-27`
- extra chunk width needed: `1.958832542208043129e-27`
- lower margin: `-9.844984097158227332e-28`
- upper margin: `-9.718766352322865443e-28`
- required remainder cap: `-1.262177448353618959e-30`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-15` | `0.000000000000000000E+18` | `8.612407759841529026E-38` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-15` | `0.000000000000000000E+18` | `9.815516794374170106E-46` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 15

- chunk interval: `[8.267657395615381315E-14, 8.267657395615381315E-14]`
- degree: `16`
- sampled max residual: `2.726634156355392781E-29`
- remainder candidate: `2.999297571990932059E-29`
- lower model integral: `8.267657395615351676E-14`
- upper model integral: `8.267657395615411662E-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.998595143981864118E-28`
- extra chunk width needed: `5.998595143981863749e-28`
- lower margin: `-3.029225876048685333e-28`
- upper margin: `-3.029225876048685333e-28`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-15` | `0.000000000000000000E+18` | `6.740095174368888085E-38` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-15` | `0.000000000000000000E+18` | `7.450532792626880696E-46` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 16

- chunk interval: `[1.781532338152280662E-14, 1.781532338152280662E-14]`
- degree: `16`
- sampled max residual: `2.127686530910648770E-29`
- remainder candidate: `2.340455184001713647E-29`
- lower model integral: `1.781532338152257346E-14`
- upper model integral: `1.781532338152304155E-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.680910368003427294E-28`
- extra chunk width needed: `4.680910368003427140e-28`
- lower margin: `-2.335028279454194944e-28`
- upper margin: `-2.335028279454194944e-28`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-16` | `0.000000000000000000E+18` | `3.011311570568514614E-38` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-16` | `0.000000000000000000E+18` | `2.457864317492153750E-46` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 17

- chunk interval: `[7.546586899752640299E-16, 7.546586899752640299E-16]`
- degree: `16`
- sampled max residual: `1.370572961991821328E-30`
- remainder candidate: `1.507630258191003460E-30`
- lower model integral: `7.546586899752485364E-16`
- upper model integral: `7.546586899752786890E-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.015260516382006921E-29`
- extra chunk width needed: `3.015260516382007114e-29`
- lower margin: `-1.548139526496235668e-29`
- upper margin: `-1.469253435974134488e-29`
- required remainder cap: `-3.944304526105059246e-32`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-18` | `0.000000000000000000E+18` | `6.731804271099374746E-39` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-18` | `0.000000000000000000E+18` | `1.084340758738907207E-46` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 18

- chunk interval: `[4.179784978062698203E-18, 4.179784978062698203E-18]`
- degree: `16`
- sampled max residual: `9.854913755371201830E-31`
- remainder candidate: `1.084040513090832201E-30`
- lower model integral: `4.179784978051827509E-18`
- upper model integral: `4.179784978073508319E-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.168081026181664403E-29`
- extra chunk width needed: `2.168081026181664462e-29`
- lower margin: `-1.087071897809931405e-29`
- upper margin: `-1.080985959185667740e-29`
- required remainder cap: `-3.004450713244087862e-33`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.100000000000000000E-38` | `1.100000000000000000E-38` | `1.619219487958870666E-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-21` | `0.000000000000000000E+18` | `1.126279119073253027E-47` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 19

- chunk interval: `[9.956362955204717537E-22, 9.956362955204717537E-22]`
- degree: `16`
- sampled max residual: `2.201607067473051968E-32`
- remainder candidate: `2.421767774220357165E-32`
- lower model integral: `9.956362952851030197E-22`
- upper model integral: `9.956362957694565745E-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.843535548440714331E-31`
- extra chunk width needed: `4.843535548440713975e-31`
- lower margin: `-2.353687636674062988e-31`
- upper margin: `-2.489847498318510195e-31`
- required remainder cap: `-6.807899042674294206e-34`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.011312000000000000E-39` | `1.011312000000000000E-39` | `1.703170194316035210E-40` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `2.308689565543259335E-48` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 20

- chunk interval: `[2.187950514254602220E-28, 2.187950514254607777E-28]`
- degree: `16`
- sampled max residual: `1.697166290332483896E-33`
- remainder candidate: `1.866882919365732286E-33`
- lower model integral: `2.187765174175784397E-28`
- upper model integral: `2.188138550759657544E-28`
- current chunk width: `5.556999999999999999e-43`
- model interval width: `3.733765838731464571E-32`
- extra chunk width needed: `3.733765838675894133e-32`
- lower margin: `-1.853400788177398853e-32`
- upper margin: `-1.880365050498983545e-32`
- required remainder cap: `-1.348213113164533871e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.209584175645615133E-41` | `1.154014175645615133E-41` | `3.170952966058376375E-42` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.378953585323680995E-49` | `0.000000000000000000E+18` | `6.655512503040100102E-50` | `sampled_feasible` |

### control_finite row 0 chunk 21

- chunk interval: `[3.619200973670753045E-28, 3.619200973670757772E-28]`
- degree: `16`
- sampled max residual: `5.075177693151252604E-35`
- remainder candidate: `5.582695462466377864E-35`
- lower model integral: `3.619195408360835616E-28`
- upper model integral: `3.619206573751760549E-28`
- current chunk width: `4.727000000000000005e-43`
- model interval width: `1.116539092493275573E-33`
- extra chunk width needed: `1.116539092020575654e-33`
- lower margin: `-5.565309917454127838e-34`
- upper margin: `-5.600081002594865280e-34`
- required remainder cap: `-1.738554010408342365e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.610357898988731518E-43` | `0.000000000000000000E+18` | `3.549703956052911420E-44` | `sampled_feasible` |
| 16 | 10 | `2.388602903850000000E-51` | `0.000000000000000000E+18` | `1.933383323049104633E-51` | `sampled_feasible` |

### control_finite row 0 chunk 22

- chunk interval: `[7.969609101483642699E-23, 7.969609101483642705E-23]`
- degree: `16`
- sampled max residual: `3.535498237730851253E-34`
- remainder candidate: `3.889048061503936379E-34`
- lower model integral: `7.969609101099191890E-23`
- upper model integral: `7.969609101877001502E-23`
- current chunk width: `5.999999999999999780e-41`
- model interval width: `7.778096123007872757E-33`
- extra chunk width needed: `7.778096063007872850e-33`
- lower margin: `-3.844513049081832409e-33`
- upper margin: `-3.933592010987145357e-33`
- required remainder cap: `-4.453948095265647100e-36`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.629000000000000000E-42` | `0.000000000000000000E+18` | `3.007737020512803641E-43` | `sampled_feasible` |
| 16 | 10 | `0.000000000000000000E-27` | `0.000000000000000000E+18` | `1.001162086467203657E-50` | `sampled_feasible` |

### control_finite row 0 chunk 23

- chunk interval: `[3.605217865087363231E-20, 3.605217865087363231E-20]`
- degree: `16`
- sampled max residual: `1.593897860967398240E-33`
- remainder candidate: `1.753287647064138065E-33`
- lower model integral: `3.605217865085613802E-20`
- upper model integral: `3.605217865089120377E-20`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.506575294128276129E-32`
- extra chunk width needed: `3.506575294128276096e-32`
- lower margin: `-1.748985130746658559e-32`
- upper margin: `-1.757411074253352716e-32`
- required remainder cap: `-4.212971753347078161e-36`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `1.556356163130993237E-42` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-23` | `0.000000000000000000E+18` | `2.162902112379373299E-50` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 24

- chunk interval: `[8.725308178754835832E-19, 8.725308178754835832E-19]`
- degree: `16`
- sampled max residual: `2.160281230040927048E-33`
- remainder candidate: `2.376309353045019753E-33`
- lower model integral: `8.725308178754596610E-19`
- upper model integral: `8.725308178755071871E-19`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.752618706090039507E-32`
- extra chunk width needed: `4.752618706090039775e-32`
- lower margin: `-2.388153131040172458e-32`
- upper margin: `-2.368893831596300099e-32`
- required remainder cap: `-1.925929944387235960e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-20` | `0.000000000000000000E+18` | `2.236969464618382628E-42` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-20` | `0.000000000000000000E+18` | `2.870943578819393339E-50` | `split_integral_center_mismatch` |

### control_finite row 0 chunk 25

- chunk interval: `[3.013084795960276602E-18, 3.013084795960276602E-18]`
- degree: `16`
- sampled max residual: `1.638298652247086733E-33`
- remainder candidate: `1.802128517471795406E-33`
- lower model integral: `3.013084795960258392E-18`
- upper model integral: `3.013084795960294435E-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.604257034943590812E-32`
- extra chunk width needed: `3.604257034943590713e-32`
- lower margin: `-1.810374147724001702e-32`
- upper margin: `-1.771855548836256985e-32`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `0.000000000000000000E-19` | `0.000000000000000000E+18` | `2.468654479948863277E-42` | `split_integral_center_mismatch` |
| 16 | 10 | `0.000000000000000000E-19` | `0.000000000000000000E+18` | `2.834214176983481676E-50` | `split_integral_center_mismatch` |

