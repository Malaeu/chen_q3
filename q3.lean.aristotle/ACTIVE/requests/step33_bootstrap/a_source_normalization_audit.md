# Step33A A-source normalization audit

This is a non-mutating diagnostic. It compares the imported Step22 A table
against Step22-Omega and Q3.a_star finite-window candidates, including
sign and scalar-fit probes.

It does not edit CSV files, radius payloads, radius-floor data, LDL data,
or Lean proof files.

## Summary

### primary

- receiver source: `centeredBSplineArchKernelProfile / Q3.a_star`
- imported table source: `Step22 Omega positive-axis payload`
- PSD cert source: `current imported A payload with derived C/R/D and finite penalty floors`
- symbolic relation: `Q3.a_star(xi) = -2*pi*Omega(2*pi*xi)`
- best exact formula: `step22_positive`
- best exact max error: `0.0000000000000000e+00`
- best Q3 scalar fit: `lambda * q3_astar_positive`
- best Q3 scalar lambda: `-6.3445348160449380e-03`
- best Q3 scalar max error: `3.8759651649191423e-01`

| formula | max abs error | mean abs error |
| --- | ---: | ---: |
| step22_positive | 0.0000000000000000e+00 | 0.0000000000000000e+00 |
| step22_full_even | 4.3748178349373795e-01 | 7.8883603887025977e-02 |
| q3_astar_positive | 3.9572235160479778e+01 | 3.0833851566704817e+00 |
| q3_astar_full_even | 7.9021105875595637e+01 | 6.0878867094539375e+00 |
| neg_q3_astar_positive | 3.9325506269751941e+01 | 2.9256179488964302e+00 |
| neg_q3_astar_full_even | 7.8774376984867800e+01 | 5.9301195016798856e+00 |

| fitted formula | lambda | max abs error | mean abs error |
| --- | ---: | ---: | ---: |
| lambda * q3_astar_positive | -6.3445348160449380e-03 | 3.8759651649191423e-01 | 7.0857985992859474e-02 |
| lambda * q3_astar_full_even | -3.1722674080224690e-03 | 3.8759651649191423e-01 | 7.0857985992859474e-02 |
| lambda * neg_q3_astar_positive | 6.3445348160449380e-03 | 3.8759651649191423e-01 | 7.0857985992859474e-02 |
| lambda * neg_q3_astar_full_even | 3.1722674080224690e-03 | 3.8759651649191423e-01 | 7.0857985992859474e-02 |

PSD sanity for `lambda * neg_q3_astar_full_even`:

- D min eigenvalue: `-3.8722781523319921e-01`
- D floor: `1.2228594783222341e-04`
- D passes: `False`
- R min eigenvalue: `3.3644908902995263e-01`
- R floor: `1.3569220778186006e-01`
- R passes: `True`

Sampled signed delta rows:

| signed delta | imported A | q3 full | -q3 full | imported / -q3 full | fitted error |
| ---: | ---: | ---: | ---: | ---: | ---: |
| -2 | -2.235303949220050490000000000000e-1 | 7.469675830471349000000000000000e+0 | -7.469675830471349000000000000000e+0 | 2.992504627980621594940882728000e-2 | 1.998345857365076191432717473000e-1 |
| -1 | -4.374817834937379524000000000000e-1 | 1.572542934926196200000000000000e+1 | -1.572542934926196200000000000000e+1 | 2.782002155726642754400100368000e-2 | 3.875965164919142468212169370000e-1 |
| 0 | 1.233644453639219513000000000000e-1 | -7.889774143023172000000000000000e+1 | 7.889774143023172000000000000000e+1 | 1.563599199769382220874930802000e-3 | 1.269202883417861932959776365000e-1 |
| 1 | -4.374817834937379524000000000000e-1 | 1.572542934926196200000000000000e+1 | -1.572542934926196200000000000000e+1 | 2.782002155726642754400100368000e-2 | 3.875965164919142468212169370000e-1 |
| 2 | -2.235303949220050490000000000000e-1 | 7.469675830471349000000000000000e+0 | -7.469675830471349000000000000000e+0 | 2.992504627980621594940882728000e-2 | 1.998345857365076191432717473000e-1 |

### control

- receiver source: `centeredBSplineArchKernelProfile / Q3.a_star`
- imported table source: `Step22 Omega positive-axis payload`
- PSD cert source: `current imported A payload with derived C/R/D and finite penalty floors`
- symbolic relation: `Q3.a_star(xi) = -2*pi*Omega(2*pi*xi)`
- best exact formula: `step22_positive`
- best exact max error: `0.0000000000000000e+00`
- best Q3 scalar fit: `lambda * q3_astar_positive`
- best Q3 scalar lambda: `-5.1223513295320352e-03`
- best Q3 scalar max error: `4.4294613163128610e-01`

| formula | max abs error | mean abs error |
| --- | ---: | ---: |
| step22_positive | 0.0000000000000000e+00 | 0.0000000000000000e+00 |
| step22_full_even | 4.8730924398478542e-01 | 8.2166259416780837e-02 |
| q3_astar_positive | 3.7628813989154693e+01 | 3.1340362190046194e+00 |
| q3_astar_full_even | 7.5231379074650604e+01 | 6.1859061785924556e+00 |
| neg_q3_astar_positive | 3.7576316181837143e+01 | 2.9697037001710576e+00 |
| neg_q3_astar_full_even | 7.5178881267333068e+01 | 6.0215736597588965e+00 |

| fitted formula | lambda | max abs error | mean abs error |
| --- | ---: | ---: | ---: |
| lambda * q3_astar_positive | -5.1223513295320352e-03 | 4.4294613163128610e-01 | 8.1000000193529806e-02 |
| lambda * q3_astar_full_even | -2.5611756647660176e-03 | 4.4294613163128610e-01 | 8.1000000193529806e-02 |
| lambda * neg_q3_astar_positive | 5.1223513295320352e-03 | 4.4294613163128610e-01 | 8.1000000193529806e-02 |
| lambda * neg_q3_astar_full_even | 2.5611756647660176e-03 | 4.4294613163128610e-01 | 8.1000000193529806e-02 |

PSD sanity for `lambda * neg_q3_astar_full_even`:

- D min eigenvalue: `-4.2820294431048789e-01`
- D floor: `1.2636922821866160e-05`
- D passes: `False`
- R min eigenvalue: `2.7269198879802420e-01`
- R floor: `1.9590640625249765e-03`
- R passes: `True`

Sampled signed delta rows:

| signed delta | imported A | q3 full | -q3 full | imported / -q3 full | fitted error |
| ---: | ---: | ---: | ---: | ---: | ---: |
| -2 | -2.460736057093875218000000000000e-1 | 8.228638331900756000000000000000e+0 | -8.228638331900756000000000000000e+0 | 2.990453532942506866082949160000e-2 | 2.249986174595624688833273954000e-1 |
| -1 | -4.873092439847854229000000000000e-1 | 1.732138601963182000000000000000e+1 | -1.732138601963182000000000000000e+1 | 2.813338629093975777953352257000e-2 | 4.429461316312860927285396004000e-1 |
| 0 | 2.624890365877484422000000000000e-2 | -7.520513017099184000000000000000e+1 | 7.520513017099184000000000000000e+1 | 3.490307589268635335714356051000e-4 | 1.663646456007300684518525189000e-1 |
| 1 | -4.873092439847854229000000000000e-1 | 1.732138601963182000000000000000e+1 | -1.732138601963182000000000000000e+1 | 2.813338629093975777953352257000e-2 | 4.429461316312860927285396004000e-1 |
| 2 | -2.460736057093875218000000000000e-1 | 8.228638331900756000000000000000e+0 | -8.228638331900756000000000000000e+0 | 2.990453532942506866082949160000e-2 | 2.249986174595624688833273954000e-1 |

## Interpretation

The current imported A table matches the Step22 positive-axis Omega payload,
not the literal current Q3.a_star receiver and not a constant scalar multiple
of that receiver at useful accuracy. The sign probe is still valuable: it
shows the finite PSD contour prefers the opposite Arch sign from the naive
Q3.a_star migration, but the table itself is not simply `-Q3.a_star`.

The next proof target should therefore be a source-normalization bridge,
not a data mutation.  The bridge must account for sign, eta=2*pi*xi,
Jacobian, packet-frequency, cosine-argument, and positive/full-window
conventions before any A payload generation resumes.
