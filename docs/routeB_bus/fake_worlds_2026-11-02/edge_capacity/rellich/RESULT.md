# Fixed-N Rellich verification

DIAGNOSTIC_NEVER_A_PROOF; Route B CHALLENGER / NOT_RH.

Coverage: 8 zeta saved cells and 13 DH saved controls. No large full-carrier eigensystem was solved by these scripts. Shared source A and evaluation QR were rebuilt for the nine high cells; the capacity worker independently computed reduced spectra.

The local path is L_tau=L exp(tau), with integer N fixed and actual active zero coordinates fixed. Analytic dotE uses the entire-sinc removable values (a rational rearrangement away from modal points). Projector velocity is evaluated using F=E U and F^T y=U^T c, then dotPi c=(I-UU^T)dotE^T y; this avoids forming the ill-conditioned squared raw Gram inverse. Every correction 2<r,dotPi c> is retained.

For large saved cells, finite differences concern the Rayleigh quotient of the saved vector transported by the actual projector Pi(L_tau), normalized physically. For a simple stationary compressed eigenvector this has the same first derivative as the eigenvalue branch. They are not new large-cell eigenvalue calculations. Only the source m=8 control rebuilds actual compressed eigenbranches on both sides.

| world | m | q | source virial | moving-projector correction | FD maximum absolute error | FD error / (e^2 log T/T) |
|---|---:|---:|---:|---:|---:|---:|
| dh | 55 | 27 | -0.7053551 | -1.8266126 | 1.3453176e-14 | 6.7637096e-13 |
| dh | 55 | 50 | 10.339681 | -1.4899813e-9 | 1.4157078e-13 | 2.5334443e-12 |
| dh | 80 | 41 | -1.2210034 | 6.3320589 | not run | not run |
| dh | 80 | 73 | -3.1893216 | 1.4459684e-13 | not run | not run |
| dh | 120 | 63 | -7.0770771 | 7.8926257 | not run | not run |
| dh | 120 | 65 | -9.6183829 | 7.732561 | not run | not run |
| dh | 120 | 108 | -5.0989012 | 8.6744557e-16 | not run | not run |
| dh | 160 | 89 | -7.6000499 | 7.3588776 | not run | not run |
| dh | 160 | 144 | -4.5595778 | -1.2861743e-18 | not run | not run |
| dh | 200 | 115 | -11.149858 | 6.650912 | not run | not run |
| dh | 200 | 180 | -8.486155 | 1.1435659e-20 | not run | not run |
| dh | 240 | 139 | -15.32582 | 0.063944632 | not run | not run |
| dh | 240 | 216 | -1.2994798 | -7.092844e-27 | not run | not run |
| zeta | 55 | 27 | -0.027477494 | -0.0032202866 | 1.6349111e-16 | 1.7406033e-12 |
| zeta | 80 | 41 | 6.8723003e-5 | -1.8059587e-5 | 3.2350176e-14 | 1.1598617e-7 |
| zeta | 120 | 63 | 3.3005194e-5 | -1.2333241e-6 | 2.1132436e-13 | 1.3671867e-5 |
| zeta | 120 | 64 | 2.186663e-7 | -9.2301118e-9 | 2.6551044e-13 | 0.00058574889 |
| zeta | 120 | 65 | -4.0327675e-11 | -3.1568739e-10 | 1.6540682e-25 | 3.0294612e-14 |
| zeta | 160 | 89 | -7.2976631e-13 | -4.2965147e-14 | 3.3378366e-35 | 8.7015436e-20 |
| zeta | 200 | 115 | 2.7425232e-19 | -6.3356365e-21 | 3.2316238e-35 | 8.0012519e-13 |
| zeta | 240 | 139 | -2.9377574e-23 | -2.8028345e-23 | 9.4721192e-35 | 5.3290359e-10 |

## Threshold and precision controls

The m=8 exact seven-group control and both numerical settings reproduce the source signs. At 55dps/GL48 the left/right actual eigenvalue FD errors are 1.3245e-10 and 1.5089e-10 for h=1e-12; the corresponding h=1e-8 errors at 40dps/GL32 are 1.3245e-6 and 1.5089e-6. The moving correction is -0.819394427141790169..., and the prime-power-8 right-minus-left kick is -0.524710330246889024....

All requested large m are mixed-factor composites. Their zeta birth Mangoldt coefficient vanishes; their DH birth coefficient also vanishes because these m are multiples of5. Consequently the large-cell right/left derivative kick is zero. This is verified separately from the nonzero m8 control. No discrete N=m sequence derivative is inferred.

Coarse high-cell FD steps can be inaccurate on the tiny endpoint scale despite small absolute errors: the coarse JSONs are retained. A single necessary h=1e-40 refinement is reported for the high zeta cells, with identical active coordinates. Ratios are floating diagnostics; there is no interval-certified denominator or cofinal sign conclusion.

Source replay errors compare the saved source coordinates/matrices with independently evaluated full scalar arithmetic/archimedean/pole forms. The direct Leibniz check evaluates the interior integral from independent analytic trigonometric moments at three shifts. The boundary/volume column is the dilation flux -2e B_L, not the Abel energy-ledger boundary column. DH uses its odd-gamma kernel, all b(n), and no pole.

Primary source: inbox3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1, PROSHKA_VERDICT_EDGE_LAW_RELLICH_v1_2026-11-02.md, equations2.2–4.7. This bounded verification finds no source-identity error; it does not establish a selected-volume sign or edge law.

See summary.csv for every raw absolute/relative metric, individual JSONs for fixed-active-set/gap/constraint guards, and source_m8_checks.py plus m8_dps40.json/m8_dps55.json for the true one-sided threshold experiment.
