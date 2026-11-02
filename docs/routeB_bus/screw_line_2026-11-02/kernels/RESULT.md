# SCREW_LINE: formal inverse kernels on every integer cell

**DIAGNOSTIC_NEVER_A_PROOF.** Literal N=m,L=log(m),native kappa1.1; both zeta and Davenport–Heilbronn. All221integers m20..240 are present in each world. No full-carrier spectrum was recomputed.

## What was actually evaluated

Let E be the unweighted physical Fourier sampling matrix at the complete numerical positive-height census below T. DH reflected off-line pairs use isometric sqrt(2) real/imaginary rows. For B=E A E^T and evaluation vector e_z, the saved scalar is K_z=(E e_z)^T B^(-1)(E e_z). This is congruent to U(U^T A U)^(-1)U^T on the finite complement when E has full row rank. It is an inverse-form proxy, not an identified Weyl or de Branges kernel.

Two distinct evaluation conventions are retained: formal analytic continuation of the physical cosine factor phi_n(i eta), and entire Fourier evaluation phi_hat_n(i eta), eta=1/2,1,2. The window indicator itself has no analytic continuation; the physical-cosine alternative does not assert that the zero-extended carrier functions are entire. Neither is silently chosen as the Suzuki source map. The real endpoint is f(log(m)/2), with d_b=(1,sqrt(2),...)/sqrt(log m). Mixed endpoint kernels d_b^T E^T B^(-1)E e_z are saved for the atom-jump checks.

At these purely imaginary points the evaluation columns are real. We report r_proxy=1/(eta*K_z) literally, without an absolute-value repair. Its square cannot become negative: a negative square is not a possible diagnostic of DH indefiniteness. Negative K and signed inverse proxies are instead distinguished from the independently computed form inertia.

## Complement inertia and scalar signs

First negative complement inertia: zeta=None; DH=52. Registered S1 (DH first indefinite in50..56): PASS.

The known original full-carrier DH onset m51 is a separate saved-source fact. The native complement is still positive at51; it becomes indefinite at52, returns positive at53, and becomes indefinite again at54. Moving integer carriers and moving zero constraints are not a nested fixed-kernel family.

|world|evaluation|eta|negative K cells|first negative K|negative r_proxy² cells|
|---|---|---:|---:|---:|---:|
|zeta|endpoint|0|0|None|0|
|zeta|physical|0.5|0|None|0|
|zeta|physical|1|0|None|0|
|zeta|physical|2|0|None|0|
|zeta|fourier|0.5|0|None|0|
|zeta|fourier|1|0|None|0|
|zeta|fourier|2|0|None|0|
|dh|endpoint|0|0|None|0|
|dh|physical|0.5|5|52|0|
|dh|physical|1|5|52|0|
|dh|physical|2|4|52|0|
|dh|fourier|0.5|1|52|0|
|dh|fourier|1|1|52|0|
|dh|fourier|2|1|52|0|

|m|DH q|negative form levels|endpoint K sign|
|---:|---:|---:|---:|
|48|43|0|1|
|49|45|0|1|
|50|46|0|1|
|51|47|0|1|
|52|48|1|1|
|53|49|0|1|
|54|49|1|1|
|55|50|1|1|
|56|51|1|1|

## Numerical controls and reproduction

The original source arithmetic coefficients, conductor/gamma shift, poles, endpoints and all integer DH atoms are retained. Arch integrals are evaluated by equivalent digamma/trigamma moments plus a finite geometric tail. An explicit entrywise bound for that omitted arch series is saved per cell. This bound does not cover rounding, zero-census errors, or certify the mathematical source operator.

Compiled Arb midpoint matrices use1024bits. Solves use the approximate compiled LU routine, not a certified interval inverse. Symmetric LDL pivots give a separate numerical inertia without an eigenvalue or singular-value tolerance cutoff. Whole-cell inverse failure or unresolved pivots would block a row rather than be converted to a positive kernel. All requested cells completed.

Maximum per-right-hand-side normalized solve backward residual: 5.169487e-309. Maximum relative mixed-kernel symmetry defect: 1.5588507e-139. Source A and saved-vector energy comparisons at55,120,240; QR-vs-congruence endpoint inverse checks;1536bit repetitions at55,120,240 and DH51..54 are recorded in validation.json.

`kernels.csv` contains all3094endpoint/point rows, keeping arbitrary-range decimal strings (no float underflow). `inertia.csv` contains all442form counts and source/cutoff information. Per-cell JSON records retain all metadata and tail bounds; the parent package archives and restores these losslessly. `RESULT.json` preserves the complete negative-K integer lists and S1 score. The transition audit separately distinguishes discrete integer changes from fixed-N atom-derivative jumps.

Replay with python-flint and mpmath installed: `python3 screw_kernels.py --input-root INPUT_ROOT --bits 1024`. INPUT_ROOT contains the pinned zeta_zeros_capacity.csv and edge_law/dh/dh_zeros_extended.json. Then run `validate.py` with explicit input/EDGE paths and `report.py`. No actual Weyl-radius conclusion or RH/route-state export is made.
