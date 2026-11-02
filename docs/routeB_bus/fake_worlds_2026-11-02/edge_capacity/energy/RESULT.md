# Finite constant/head/cross/volume energy decomposition

DIAGNOSTIC_NEVER_A_PROOF. Exact finite source algebra for the saved selected physical vectors; no new source eigensystem, no zero search, no independently summed infinite zero tail. Source equations are (5.4)–(5.7) in `3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1`.

The constant indicator has physical modal vector chi=(sqrt(L),0,...). For e=f(L/2), set h=f−e chi. The scalar coefficient C_T is K[chi] minus its finite strict low-zero head. X_T and V_T are computed from the same full source bilinear form minus the corresponding finite head pairings. All source terms remain in K; no additional zeta pole is inserted, and the DH source has none.

Every head uses the true signed zero metric. For DH the realified reflected rows carry opposite signs, so its head is not replaced by the positive capacity Gram. Each selected cutoff and q is retained, including separate m120 zeta q63/q64/q65 branches.

| world | m | q | mode | C_T | R_head | R_C | R_cross | R_volume | R_total |
|---|---:|---:|---|---:|---:|---:|---:|---:|---:|
| dh | 55 | 27 | matched_midpoint | 0.054182032724 | 84.297925474 | 2.4655207205 | -0.42260132068 | 0.33315361991 | 86.673998493 |
| dh | 55 | 50 | native_kappa1p1 | 0.035945190871 | -45.548186819 | 2.3530468352 | 2.9067624118 | 2.9630369101 | -37.325340661 |
| dh | 80 | 41 | matched_midpoint | 0.041126739015 | 632.28740974 | 2.3843992238 | 3.1814248989 | 10.910800881 | 648.76403474 |
| dh | 80 | 73 | native_kappa1p1 | 0.028666685829 | -284.62586175 | 2.3489605562 | -0.40487757293 | 0.080778267454 | -282.6010005 |
| dh | 120 | 63 | DH_adjacent_cardinality_bracket_exact_q64_impossible | 0.029731255654 | -242.04162963 | 2.2368517685 | 2.2544770267 | 3.0371636627 | -234.51313717 |
| dh | 120 | 65 | DH_adjacent_cardinality_bracket_exact_q64_impossible | 0.029895898389 | -250.62188769 | 2.2832087522 | 2.2723679897 | 1.9056989576 | -244.16061199 |
| dh | 120 | 108 | native_kappa1p1 | 0.022022020617 | -1450.5164861 | 2.3251540581 | 0.8279030261 | 0.15219162329 | -1447.2112374 |
| dh | 160 | 89 | matched | 0.025031838911 | -768.07931918 | 2.3347759029 | 2.2903188476 | 2.4398667834 | -761.01435765 |
| dh | 160 | 144 | native | 0.017341995149 | -3252.8153852 | 2.2048826204 | 0.86813292746 | 0.18620468494 | -3249.556165 |
| dh | 200 | 115 | matched | 0.020655999165 | -625.96094804 | 2.2654771222 | 1.1810981034 | 0.77603841315 | -621.7383344 |
| dh | 200 | 180 | native | 0.015544797853 | -1942.1664354 | 2.2898308882 | 0.46432233049 | 0.047377453722 | -1939.3649047 |
| dh | 240 | 139 | matched | 0.01838793493 | -453.52112406 | 2.2836806224 | -0.18308679026 | 0.021241569315 | -451.39928866 |
| dh | 240 | 216 | native | 0.013280352095 | -778.90194131 | 2.2104358227 | 0.89838430844 | 0.22464152313 | -775.56847966 |
| zeta | 55 | 27 | zeta_kappa_1p1_baseline | 0.024603838603 | 1.7420812618 | 1.6106183652 | -3.5153055579 | 3.7431354592 | 3.5805295283 |
| zeta | 80 | 41 | zeta_kappa_1p1_baseline | 0.019576928919 | 1.6898266413 | 1.6041419687 | -2.9159076694 | 3.9219904588 | 4.3000513993 |
| zeta | 120 | 63 | additional_adjacent_cardinality_bracket | 0.015989694 | 2.1921636893 | 1.6588518589 | -3.2776506244 | 3.8634857949 | 4.4368507188 |
| zeta | 120 | 64 | zeta_kappa_1p1_baseline | 0.015715939423 | 1.6189177575 | 1.6593382125 | -3.5535809238 | 4.5269892176 | 4.2516642639 |
| zeta | 120 | 65 | additional_adjacent_cardinality_bracket | 0.01567310037 | 1.7421413909 | 1.6613095035 | -3.376041522 | 3.897923516 | 3.9253328884 |
| zeta | 160 | 89 | native_kappa1p1 | 0.013505250069 | 1.4189477127 | 1.7170741259 | -3.5398635298 | 4.3232034028 | 3.9193617116 |
| zeta | 200 | 115 | native_kappa1p1 | 0.011292191731 | 1.9832589347 | 1.6633995286 | -3.4172439401 | 4.2960649702 | 4.5254794935 |
| zeta | 240 | 139 | native_kappa1p1 | 0.0098035490309 | 1.4469430244 | 1.6317425782 | -3.2288211096 | 4.293303396 | 4.1431678891 |

Here R_j divides each corresponding physical energy term by e^2 log(T)/(pi T). In particular R_C=pi T C_T/log(T). The total is the **sum of all four columns**, not the constant contribution alone. The CSV retains all unscaled H,e,C,X,V, constant source/head values, and absolute/relative closure residuals.

## Verification limits and reproduction

Maximum absolute energy identity residual: 3.2660504415756509300361470984535229692322145732105324019083449369529109467797499e-201.
Maximum edge-scale identity residual: 1.0745885020456999129299562073339733800472315349519201498067757826647102584286516e-196.
Maximum scaled arithmetic precision change: 6.6823940152401952792710907475738120085082529901745585263018e-151.

These two-precision changes evaluate the same source-coordinate files twice; they do not improve or certify the saved eigenvector, matrix quadrature, zero census, or nonzero endpoint. Reported ratios are floating diagnostics. If e were zero, the unscaled identity would remain but no R ratio would be formed.

`energy_split.py` evaluates a saved A/E/f case. `prepare_large.py` uses the pinned source moment helper to materialize the full finite A and actual finite signed head for the saved larger vectors, without an eigensolver. Its provenance records the selected-vector, source-helper, and zero-table byte hashes, quadrature order, and source arithmetic precision. The full source arch tail is analytic, not a finite zero-tail truncation.

Run `python summarize_energy.py --expect 21` after reproducing the listed energy JSON cases. `ENERGY_VALIDATION.json` identifies every input and output hash. No cofinal edge law, selected-volume sign, route-state, RH claim, or interval certificate is asserted.

Maximum relative difference from the original saved selected eigenvalue: 5.4427449139041806765945613511191379646201971126620437089356097483693533534768081e-97.
Maximum edge-scale difference from that saved value: 2.4631030496108210231474328298441773688389435632293828152013303159734224035829135e-96.
