# Physical-kernel normalization gate

DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER_NOT_RH. PX_RH_CLAIM: NOT_MADE.

PASS: all 12 positive-a grid cells at m=80 agree entrywise within the fixed absolute tolerance 1e-12. All four a=0 Q-only PSD controls pass. No A source construction or full planted scan was run. The predictions commit supplied by the parent is bc9204929faccc66f952ff9df9273e0b94afed4e; this partial local checkout has no Git metadata, so this worker does not independently certify commit/push history. The actual predictions bytes are SHA-256 pinned in gate.json.

## Normalization and independent calculation

Set L=log(80), I=[-L/2,L/2], j=0,...,80, omega_j=2*pi*j/L, d_0=1 and d_j=sqrt(2) otherwise. Use the real physically L2-orthonormal basis phi_j(x)=d_j*(-1)^j*cos(omega_j*x)/sqrt(L); dimension is 81. Multiplicity is one. There is no division by sigma, dimension, L, or another matrix scale.

For z=gamma+i*a, the source coefficient is c_j=2*d_j*z*sin(z*L/2)/(sqrt(L)*(z^2-omega_j^2)). The analytic reference is Q_jk=4*Re(c_j*c_k), with a transpose, without complex conjugation. The reference coefficients and all 81-by-81 entries are evaluated at 80 decimal digits using mpmath. The a=1/3 reference is the exact high-precision rational 1/3; 0.05 and 0.1 are parsed from decimal strings. A stable algebraically equivalent expression is

    c_j = d_j*(-1)^j*sqrt(L)/2
          * [sinc((z-omega_j)*L/2)+sinc((z+omega_j)*L/2)],
    sinc(t)=sin(t)/t, sinc(0)=1.

The script also evaluates the original source quotient independently at all grid coefficients: maximum discrepancy from the sinc expression is 1.663e-79. Exact removable resonances at a=0, gamma=omega_j, j in {0,1,40,80}, are separately checked against c_0=sqrt(L) or c_j=(-1)^j*sqrt(L/2). This avoids an artificial pole at either signed resonance.

Independently, integrate the physical kernel K(x,y)=4*Re[cos(z*x)*cos(z*y)] against phi_j(x)*phi_k(y) on the full square I-by-I. Fubini gives Qquad_jk=4*(r_j*r_k-s_j*s_k), where

    r_j = integral_I phi_j(x)*cos(gamma*x)*cosh(a*x) dx,
    s_j = -integral_I phi_j(x)*sin(gamma*x)*sinh(a*x) dx.

These two physical integrals use composite Gauss-Legendre quadrature only: the quadrature routine never calls the quotient, sinc, or analytic coefficient routine. For each gamma the interval is partitioned into ceil(L*(gamma+omega_80)/12) equal panels, then repeated at orders 12, 20 and 32 per panel. Nodes and weights come from scipy.special.roots_legendre (double precision); panel geometry, real integrands and summation use NumPy long double (18 decimal digits on this host). In the physical integrator a=1/3 is computed as long-double 1 divided by 3. No half-interval or symmetry factor is hidden.

## Actual convergence and errors

Each number below is the maximum absolute entrywise difference from the 80-digit analytic matrix. gate.json also records coefficient errors, worst entry indices, node counts, and changes between consecutive orders for every cell. Both orders 20 and 32 must pass 1e-12; order 12 is a convergence diagnostic. The last two orders are limited by the double-precision quadrature rule and are not claimed to converge monotonically.

| a | gamma | order 12 | order 20 | order 32 |
|---|---:|---:|---:|---:|
| 0.05 | 14 | 8.544e-14 | 8.629e-15 | 1.467e-14 |
| 0.05 | 50 | 5.529e-14 | 1.009e-14 | 1.710e-14 |
| 0.05 | 200 | 1.795e-15 | 6.538e-17 | 1.113e-16 |
| 0.05 | 800 | 2.626e-18 | 8.748e-21 | 1.213e-20 |
| 0.1 | 14 | 8.865e-14 | 8.701e-15 | 1.479e-14 |
| 0.1 | 50 | 5.772e-14 | 1.020e-14 | 1.729e-14 |
| 0.1 | 200 | 1.859e-15 | 6.686e-17 | 1.138e-16 |
| 0.1 | 800 | 5.630e-19 | 5.868e-21 | 5.379e-21 |
| 1/3 | 14 | 1.369e-13 | 9.714e-15 | 1.651e-14 |
| 1/3 | 50 | 9.461e-14 | 1.183e-14 | 2.003e-14 |
| 1/3 | 200 | 2.887e-15 | 8.858e-17 | 1.508e-16 |
| 1/3 | 800 | 5.141e-17 | 1.336e-19 | 2.091e-19 |

For a=0 all coefficients are real and Q=4*r*r^T is exactly PSD with rank at most one. Float64 eigvalsh of Q has minimum eigenvalues -3.086e-15, -3.581e-15, -4.938e-18, -1.040e-20 for gamma 14,50,200,800 respectively. These are roundoff diagnostics within 1e-12, never planted detections. This control does not establish positivity of A+Q or replace the parent experiment's source controls.

Initial budget was 120 CPU seconds. Actual main gate run used 10.7805 process CPU seconds and 10.7982 wall seconds, maximum RSS 81876 KiB. No tolerance was changed and no budget extension was needed. The numerical quadrature comparison is not a certified enclosure.

## Exact source pins

- `/tmp/corner_PROSHKA_VERDICT_CCM_HIGHER_MOMENTS_2026-11-04.md`: SHA-256 `079ed09b355c6350047d0cd218c084256ad06c5c8ab159b37e4c25bcf52afaa2`. Line 122 fixes the physical basis; section 8, Theorem 5, lines 603-612 fixes the coefficient and multiplicity-one block.
- `/tmp/corner_PROSHKA_VERDICT_EXACT_MECHANISM_E1_E3_2026-11-04.md`: SHA-256 `0a9393b1f01a4904503b1fa50bf55f32a31c75467ec4cdc25666527dac1b5d9e`. Lines 151-154 fix the physical basis; section 9(i), lines 439-443 fixes the physical kernel. Its illustrative gamma=7 is replaced by the precommitted diagnostic grid, retaining the same kernel formula.

Run from the checkout root:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 docs/routeB_bus/corner_vs_matrix_detection_2026-11-04/gate/run_gate.py

The code hash and package versions are recorded in gate.json. This worker writes only gate/ and performs no commit or push.
