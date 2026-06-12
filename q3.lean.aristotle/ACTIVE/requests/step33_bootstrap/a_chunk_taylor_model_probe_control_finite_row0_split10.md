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
| 12 | `2.643524497637732007e-01` | `1.548629071678604664e-06` | 0 |
| 16 | `6.050891560079742215e-02` | `1.508145627686224888e-07` | 0 |

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
- sampled max residual: `2.750405254570431612e-03`
- remainder candidate: `3.025445780027475207e-03`
- lower model integral: `-4.185613236356364175e-01`
- upper model integral: `-3.580524080350869220e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.050891560054949547e-02`
- extra chunk width needed: `6.050891560054949547e-02`
- lower margin: `-2.984085724084928337e-02`
- upper margin: `-3.066805835970021210e-02`
- required remainder cap: `-4.136005594254643647e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.548629069814122516e-06` | `1.548629069814122516e-06` | `7.038929933367299441e-07` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.508145600070953662e-07` | `1.508145600070953662e-07` | `6.855205747502424174e-08` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 1

- chunk interval: `[2.546688145455398839E-1, 2.546688145455398839E-1]`
- degree: `16`
- sampled max residual: `1.120978310176212744e-14`
- remainder candidate: `1.233076141193834145e-14`
- lower model integral: `2.546688145454155117e-01`
- upper model integral: `2.546688145456620922e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.465805337692472676e-13`
- extra chunk width needed: `2.465805337692472676e-13`
- lower margin: `-1.243449787580175325e-13`
- upper margin: `-1.222355550112297351e-13`
- required remainder cap: `-1.054711873393898664e-16`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.110223024625156540e-15` | `1.110223024625156540e-15` | `6.591949208711866959e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.665334536937734811e-15` | `1.665334536937734811e-15` | `1.249000902703301108e-16` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 2

- chunk interval: `[1.307425628490114938E-1, 1.307425628490114938E-1]`
- degree: `16`
- sampled max residual: `4.510281037539698445e-17`
- remainder candidate: `4.961309141293668537e-17`
- lower model integral: `1.307425628490110070e-01`
- upper model integral: `1.307425628490120062e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.992007221626408864e-16`
- extra chunk width needed: `9.992007221626408864e-16`
- lower margin: `-4.996003610813204432e-16`
- upper margin: `-4.996003610813204432e-16`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.106226635438360972e-16` | `6.106226635438360972e-16` | `4.510281037539698445e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `8.881784197001252323e-16` | `8.881784197001252323e-16` | `6.591949208711866959e-17` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 3

- chunk interval: `[2.695636479632815730E-2, 2.695636479632815730E-2]`
- degree: `16`
- sampled max residual: `1.301042606982605321e-17`
- remainder candidate: `1.431146867680865853e-17`
- lower model integral: `2.695636479632801397e-02`
- upper model integral: `2.695636479632829846e-02`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.844946500601963635e-16`
- extra chunk width needed: `2.844946500601963635e-16`
- lower margin: `-1.422473250300981817e-16`
- upper margin: `-1.422473250300981817e-16`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.318389841742373392e-16` | `1.318389841742373392e-16` | `1.301042606982605321e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.873501354054951662e-16` | `1.873501354054951662e-16` | `1.387778780781445676e-17` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 4

- chunk interval: `[2.503180893782816734E-3, 2.503180893782816734E-3]`
- degree: `16`
- sampled max residual: `2.710505431213761085e-18`
- remainder candidate: `2.981555974335137579e-18`
- lower model integral: `2.503180893782788480e-03`
- upper model integral: `2.503180893782848328e-03`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.984795992119984476e-17`
- extra chunk width needed: `5.984795992119984476e-17`
- lower margin: `-2.818925648462311528e-17`
- upper margin: `-3.165870343657672947e-17`
- required remainder cap: `-1.734723475976807191e-19`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.127570259384924611e-17` | `1.127570259384924611e-17` | `1.301042606982605321e-18` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.994931997373328159e-17` | `1.994931997373328159e-17` | `2.168404344971008868e-18` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 5

- chunk interval: `[9.713320536247765406E-5, 9.713320536247765406E-5]`
- degree: `16`
- sampled max residual: `1.287490079826536515e-19`
- remainder candidate: `1.416239087809190311e-19`
- lower model integral: `9.713320536247623080e-05`
- upper model integral: `9.713320536247907683e-05`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.846030702774449139e-18`
- extra chunk width needed: `2.846030702774449139e-18`
- lower margin: `-1.423015351387224570e-18`
- upper margin: `-1.423015351387224570e-18`
- required remainder cap: `0.000000000000000000e+00`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `5.149960319306146062e-19` | `5.149960319306146062e-19` | `7.453889935837842984e-20` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.047314121155778821e-19` | `7.047314121155778821e-19` | `1.016439536705160407e-19` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 6

- chunk interval: `[1.309463143374291504E-6, 1.309463143374291504E-6]`
- degree: `16`
- sampled max residual: `1.905824131322175763e-21`
- remainder candidate: `2.096406544454393414e-21`
- lower model integral: `1.309463143374271401e-06`
- upper model integral: `1.309463143374313329e-06`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.192813088908786678e-20`
- extra chunk width needed: `4.192813088908786678e-20`
- lower margin: `-2.011703249728963305e-20`
- upper margin: `-2.181109839179823373e-20`
- required remainder cap: `-8.470329472543003861e-23`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.776263578034402713e-21` | `6.776263578034402713e-21` | `1.376428539288238051e-21` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `9.952637130238028984e-21` | `9.952637130238028984e-21` | `1.482307657695025593e-21` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 7

- chunk interval: `[4.298555905056391531E-9, 4.298555905056391531E-9]`
- degree: `16`
- sampled max residual: `1.943874439499615036e-23`
- remainder candidate: `2.138261883449576657e-23`
- lower model integral: `4.298555905056181228e-09`
- upper model integral: `4.298555905056608053e-09`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.268251960773622802e-22`
- extra chunk width needed: `4.268251960773622802e-22`
- lower margin: `-2.101038755884690294e-22`
- upper margin: `-2.167213204888932508e-22`
- required remainder cap: `-3.308722450212110883e-25`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.481541837659083025e-23` | `2.481541837659083025e-23` | `4.135903062765138374e-24` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.805030817743927304e-23` | `3.805030817743927304e-23` | `8.271806125530276749e-24` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 8

- chunk interval: `[1.638304517494040998E-12, 1.638304517494040998E-12]`
- degree: `16`
- sampled max residual: `2.015646897922795220e-24`
- remainder candidate: `2.217211587715074816e-24`
- lower model integral: `1.638304517471735726e-12`
- upper model integral: `1.638304517516079958e-12`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.434423175430149485e-23`
- extra chunk width needed: `4.434423175430149485e-23`
- lower margin: `-2.230519986730515300e-23`
- upper margin: `-2.203903188699634185e-23`
- required remainder cap: `-1.330839901544055871e-26`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `9.693522803355793065e-27` | `9.693522803355793065e-27` | `2.423380700838948266e-27` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.615587133892632177e-26` | `1.615587133892632177e-26` | `4.846761401677896532e-27` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 9

- chunk interval: `[1.041377626709139973E-17, 1.041377626709139973E-17]`
- degree: `16`
- sampled max residual: `1.539588320505958565e-25`
- remainder candidate: `1.693547152556554652e-25`
- lower model integral: `1.041377458004782546e-17`
- upper model integral: `1.041377796714213058e-17`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.387094305113108844e-24`
- extra chunk width needed: `3.387094305113108844e-24`
- lower margin: `-1.687043573712734451e-24`
- upper margin: `-1.700050731400374393e-24`
- required remainder cap: `-6.503578843819971014e-28`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.241496590896006807e-32` | `7.241496590896006807e-32` | `2.465190328815661892e-32` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `6.625199008692091335e-32` | `6.625199008692091335e-32` | `2.157041537713704155e-32` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 10

- chunk interval: `[2.882814182503397357E-28, 2.882814182503409833E-28]`
- degree: `16`
- sampled max residual: `1.210502712824891819e-30`
- remainder candidate: `1.331552984107382087e-30`
- lower model integral: `2.751758182007442056e-28`
- upper model integral: `3.018068778828918256e-28`
- current chunk width: `1.247600000000000013e-42`
- model interval width: `2.663105968214762002e-29`
- extra chunk width needed: `2.663105968214637006e-29`
- lower margin: `-1.310560004959552049e-29`
- upper margin: `-1.352545963255084397e-29`
- required remainder cap: `-2.099297914770339593e-32`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.737350014767794482e-38` | `1.737225254767794500e-38` | `6.934835523352371509e-39` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.259947331547443896e-42` | `3.012347331547443724e-42` | `1.076197220601459510e-42` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 11

- chunk interval: `[1.003957457774199916E-19, 1.003957457774199916E-19]`
- degree: `16`
- sampled max residual: `6.208752769404808842e-30`
- remainder candidate: `6.829628046345291688e-30`
- lower model integral: `1.003957457087900301e-19`
- upper model integral: `1.003957458453825911e-19`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.365925609269057945e-28`
- extra chunk width needed: `1.365925609269057945e-28`
- lower margin: `-6.862995986338013829e-29`
- upper margin: `-6.796260106352565623e-29`
- required remainder cap: `-3.336793999272410208e-32`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `5.537048590113303078e-34` | `5.537048590113303078e-34` | `1.444447458290426890e-34` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `8.546314128218359098e-34` | `8.546314128218359098e-34` | `2.648153673532449298e-34` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 12

- chunk interval: `[2.904838114089298239E-16, 2.904838114089298239E-16]`
- degree: `16`
- sampled max residual: `1.521022432879263387e-29`
- remainder candidate: `1.673124676167189838e-29`
- lower model integral: `2.904838114087621452e-16`
- upper model integral: `2.904838114090968194e-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.346742390400142584e-28`
- extra chunk width needed: `3.346742390400142584e-28`
- lower margin: `-1.676822461660413219e-28`
- upper margin: `-1.669919928739729366e-28`
- required remainder cap: `-3.451266460341926430e-32`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.380506584136770659e-30` | `1.380506584136770659e-30` | `1.972152263052529514e-31` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.218671295934095703e-30` | `2.218671295934095703e-30` | `4.190823558986625216e-31` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 13

- chunk interval: `[1.524260430846941593E-14, 1.524260430846941593E-14]`
- degree: `16`
- sampled max residual: `7.099748146989106249e-30`
- remainder candidate: `7.809722961688018555e-30`
- lower model integral: `1.524260430846932865e-14`
- upper model integral: `1.524260430846948642e-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.577721810442023611e-28`
- extra chunk width needed: `1.577721810442023611e-28`
- lower margin: `-8.835242138475332221e-29`
- upper margin: `-6.941975965944903888e-29`
- required remainder cap: `-9.466330862652141315e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.310887241768094443e-29` | `6.310887241768094443e-29` | `7.099748146989106249e-30` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.041296394891735583e-28` | `1.041296394891735583e-28` | `1.380506584136770659e-29` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 14

- chunk interval: `[8.279132473214025765E-14, 8.279132473214025765E-14]`
- degree: `16`
- sampled max residual: `4.259848888193463749e-29`
- remainder candidate: `4.685833777012810573e-29`
- lower model integral: `8.279132473213976904e-14`
- upper model integral: `8.279132473214070305e-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.340113117816779776e-28`
- extra chunk width needed: `9.340113117816779776e-28`
- lower margin: `-4.922492048579113666e-28`
- upper margin: `-4.417621069237666110e-28`
- required remainder cap: `-2.524354896707237917e-30`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.165185579566942333e-28` | `4.165185579566942333e-28` | `2.524354896707237777e-29` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `6.563322731438818221e-28` | `6.563322731438818221e-28` | `5.206481974458677916e-29` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 15

- chunk interval: `[8.267657395615381315E-14, 8.267657395615381315E-14]`
- degree: `16`
- sampled max residual: `2.129924444096731875e-29`
- remainder candidate: `2.342916888506405286e-29`
- lower model integral: `8.267657395615353869e-14`
- upper model integral: `8.267657395615401831e-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.796274303743751777e-28`
- extra chunk width needed: `4.796274303743751777e-28`
- lower margin: `-2.776790386377961555e-28`
- upper margin: `-2.019483917365790222e-28`
- required remainder cap: `-3.786532345060856526e-30`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.407879110554770999e-28` | `3.407879110554770999e-28` | `2.366582715663035416e-29` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.679798517591284999e-28` | `5.679798517591284999e-28` | `4.259848888193463749e-29` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 16

- chunk interval: `[1.781532338152280662E-14, 1.781532338152280662E-14]`
- degree: `16`
- sampled max residual: `1.814380082008327152e-29`
- remainder candidate: `1.995818090209159924e-29`
- lower model integral: `1.781532338152260521e-14`
- upper model integral: `1.781532338152300280e-14`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.975858962313899499e-28`
- extra chunk width needed: `3.975858962313899499e-28`
- lower margin: `-2.019483917365790222e-28`
- upper margin: `-1.956375044948109277e-28`
- required remainder cap: `-3.155443620884047397e-31`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `7.888609052210118054e-29` | `7.888609052210118054e-29` | `8.677469957431129860e-30` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `1.546167374233183139e-28` | `1.546167374233183139e-28` | `1.498835719919922430e-29` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 17

- chunk interval: `[7.546586899752640299E-16, 7.546586899752640299E-16]`
- degree: `16`
- sampled max residual: `1.183291357831517708e-30`
- remainder candidate: `1.301620493614670635e-30`
- lower model integral: `7.546586899752514209e-16`
- upper model integral: `7.546586899752774533e-16`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.603240987229338958e-29`
- extra chunk width needed: `2.603240987229338958e-29`
- lower margin: `-1.262177448353618889e-29`
- upper margin: `-1.341063538875720069e-29`
- required remainder cap: `-3.944304526105059246e-32`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.338734978715564930e-30` | `4.338734978715564930e-30` | `6.409494854920720919e-31` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `7.987216665362744530e-30` | `7.987216665362744530e-30` | `1.380506584136770659e-30` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 18

- chunk interval: `[4.179784978062698203E-18, 4.179784978062698203E-18]`
- degree: `16`
- sampled max residual: `1.825781587279099589e-31`
- remainder candidate: `2.008359746007019970e-31`
- lower model integral: `4.179784978060692290e-18`
- upper model integral: `4.179784978064709010e-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.016719492014019095e-30`
- extra chunk width needed: `4.016719492014019095e-30`
- lower margin: `-2.006048630073744865e-30`
- upper margin: `-2.010670861940274231e-30`
- required remainder cap: `-2.311115933264682938e-34`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.311115933264683024e-32` | `2.311115933264683024e-32` | `5.392603844284260389e-33` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.543711097672513970e-32` | `3.543711097672513970e-32` | `6.933347799794049071e-33` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 19

- chunk interval: `[9.956362955204717537E-22, 9.956362955204717537E-22]`
- degree: `16`
- sampled max residual: `4.118367967992900730e-33`
- remainder candidate: `4.530204764793191281e-33`
- lower model integral: `9.956362954758843068e-22`
- upper model integral: `9.956362955664884021e-22`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `9.060409529584381606e-32`
- extra chunk width needed: `9.060409529584381606e-32`
- lower margin: `-4.458753516171808879e-32`
- upper margin: `-4.601656013412572727e-32`
- required remainder cap: `-7.145124862038191961e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `6.394689268473244043e-36` | `6.394689268473244043e-36` | `1.880790961315660013e-36` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `9.968192094972998068e-36` | `9.968192094972998068e-36` | `2.821186441973490019e-36` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 20

- chunk interval: `[2.187950514254602220E-28, 2.187950514254607777E-28]`
- degree: `16`
- sampled max residual: `3.275308896619861075e-34`
- remainder candidate: `3.602839786291847599e-34`
- lower model integral: `2.187914623163625542e-28`
- upper model integral: `2.187986679959351179e-28`
- current chunk width: `5.556999999999999999e-43`
- model interval width: `7.205679572563694365e-33`
- extra chunk width needed: `7.205679572007994680e-33`
- lower margin: `-3.589109097675971557e-33`
- upper margin: `-3.616570474349624198e-33`
- required remainder cap: `-1.373068806777701627e-36`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `3.946056475538684872e-42` | `3.390356475538684633e-42` | `1.345246525751824388e-42` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.735334602362042922e-42` | `2.179634602362043002e-42` | `1.165880322318247803e-42` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 21

- chunk interval: `[3.619200973670753045E-28, 3.619200973670757772E-28]`
- degree: `16`
- sampled max residual: `9.622694000356988047e-36`
- remainder candidate: `1.058496340139268854e-35`
- lower model integral: `3.619199917152685938e-28`
- upper model integral: `3.619202034145366663e-28`
- current chunk width: `4.727000000000000005e-43`
- model interval width: `2.116992680724887169e-34`
- extra chunk width needed: `2.116992675997887247e-34`
- lower margin: `-1.056518067008470336e-34`
- upper margin: `-1.060474608783846239e-34`
- required remainder cap: `-1.978268421402654271e-38`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `2.645651500645254630e-42` | `2.172951500645254629e-42` | `9.865141188846712179e-43` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `4.484155085839414627e-42` | `4.011455085839414626e-42` | `1.793662034335765851e-42` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 22

- chunk interval: `[7.969609101483642699E-23, 7.969609101483642705E-23]`
- degree: `16`
- sampled max residual: `6.574075363618781412e-35`
- remainder candidate: `7.231482900080660083e-35`
- lower model integral: `7.969609101411794109e-23`
- upper model integral: `7.969609101556424583e-23`
- current chunk width: `5.999999999999999780e-41`
- model interval width: `1.446304739364726104e-33`
- extra chunk width needed: `1.446304679364726097e-33`
- lower margin: `-7.184856571095985706e-34`
- upper margin: `-7.278190822551275334e-34`
- required remainder cap: `-4.666712572764481741e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.819526838371378783e-37` | `4.818926838371378687e-37` | `1.175494350822287508e-37` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `5.407274013782522537e-37` | `5.406674013782522441e-37` | `1.410593220986745010e-37` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 23

- chunk interval: `[3.605217865087363231E-20, 3.605217865087363231E-20]`
- degree: `16`
- sampled max residual: `3.099190855942961015e-34`
- remainder candidate: `3.409109941547257533e-34`
- lower model integral: `3.605217865087022992e-20`
- upper model integral: `3.605217865087704290e-20`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.812977178269846830e-33`
- extra chunk width needed: `6.812977178269846830e-33`
- lower margin: `-3.400470058058713303e-33`
- upper margin: `-3.412507120211133527e-33`
- required remainder cap: `-6.018531076210112375e-37`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.925929944387235853e-34` | `1.925929944387235853e-34` | `3.611118645726067224e-35` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `3.009265538105056020e-34` | `3.009265538105056020e-34` | `6.168994353115364842e-35` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 24

- chunk interval: `[8.725308178754835832E-19, 8.725308178754835832E-19]`
- degree: `16`
- sampled max residual: `6.500013562306921004e-34`
- remainder candidate: `7.150014918547613777e-34`
- lower model integral: `8.725308178754760273e-19`
- upper model integral: `8.725308178754902792e-19`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.425188158846554531e-32`
- extra chunk width needed: `1.425188158846554531e-32`
- lower margin: `-7.511126783110219827e-33`
- upper margin: `-6.740754805355325486e-33`
- required remainder cap: `-3.851859888774471920e-35`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `4.044452883213195291e-33` | `4.044452883213195291e-33` | `3.611118645726067224e-34` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `6.355568816477878315e-33` | `6.355568816477878315e-33` | `5.537048590113303078e-34` | `split_model_interval_wider_than_parent_chunk_interval` |

### control_finite row 0 chunk 25

- chunk interval: `[3.013084795960276602E-18, 3.013084795960276602E-18]`
- degree: `16`
- sampled max residual: `1.203706215242022408e-33`
- remainder candidate: `1.324076836767224819e-33`
- lower model integral: `3.013084795960262294e-18`
- upper model integral: `3.013084795960288487e-18`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.619264724366640760e-32`
- extra chunk width needed: `2.619264724366640760e-32`
- lower margin: `-1.425188158846554531e-32`
- upper margin: `-1.194076565520086229e-32`
- required remainder cap: `-1.155557966632341469e-34`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 10 | `1.271113763295575663e-32` | `1.271113763295575663e-32` | `7.222237291452134449e-34` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `2.503708927703406609e-32` | `2.503708927703406609e-32` | `1.492595706900107786e-33` | `split_model_interval_wider_than_parent_chunk_interval` |

