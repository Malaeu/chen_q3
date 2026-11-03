# Three-window MP ε sensitivity and endpoint carriers

DIAGNOSTIC_NEVER_A_PROOF. ζ only, m16,24,40. Literal400bit source with GL256×8panels; mpmath120 decimal digits. Endpoint offsets are preserved as MP strings; adding them to1 in binary64 would erase the intrinsic widths.

|m|width at ε=10^-20|width at ε=10^-40|width at ε=10^-60|width at ε=10^-80|width at ε=10^-100|
|---|---:|---:|---:|---:|---:|
|16|2.581309e-20|4.659258e-32|4.659257e-32|4.659257e-32|4.659257e-32|
|24|1.564015e-20|3.528471e-40|4.189811e-48|4.189811e-48|4.189811e-48|
|40|1.106206e-20|1.414735e-40|2.182743e-60|2.258441e-78|2.023881e-78|

These selected windows show ε-controlled widths at larger ε and intrinsic scales as ε decreases. The m40 ε10^-80 width is still changing by about12% before ε10^-100. Thus ε-sized binary64 full-grid widths should not be interpreted as intrinsic widths without sensitivity evidence. No extrapolation to the untested larger windows is established here.

At ε10^-100 the lower/upper offsets are approximately:

|m|u_minus−1|u_plus−1|smallest quiet eigenvalue|
|---|---:|---:|---:|
|16|−4.6592043683e-32|5.3069671377e-37|5.4561380117e-38|
|24|−4.1897849543e-48|2.5766688128e-53|2.6905128126e-54|
|40|−2.0238782524e-78|2.9339482863e-84|2.9811770275e-85|

The κ1 quiet dimensions(q,r) are(5,12),(8,17),(16,25). A direct MP physical-evaluation residual and Q-orthogonality check accompanies every quiet compression. These minima are well above the observed source/span numerical floors; they are positive numerical diagnostics, not certified signs.

At the upper endpoint, squared overlap with quiet eigenmode1 is0.9999999999815,0.9999999999946,0.9999999999997. The ratios (u_plus−1)/λquiet,min are9.726599889,9.576868769,9.841576865, with arithmetic B slopes approximately−0.1028,−0.1044,−0.1016. The upper exit follows the lowest quiet mode in these pilots.

The lower endpoint is **not** simply quiet mode2. Its squared overlaps are about93.29%,93.21%,93.39% with mode1 and6.71%,6.79%,6.61% with mode2. Its B slopes are positive, approximately0.06820,0.06927,0.06749. All six endpoint carriers have quiet mass numerically indistinguishable from1 at ordinary precision. Full MP coefficients, overlap lists, projected D Rayleigh values, baseline A Rayleigh values, slopes, and endpoint residuals are saved in ENDPOINTS_m*.json.

The whitening is G=A1+εI=LLᵀ, H=L^-1 B L^-T; offsets are−1/hmax and−1/hmin. Carriers are normalized L^-T times the corresponding H eigenvectors. No controls, inertia counts, full-grid MP extension, or rigorous interval certification were performed.
