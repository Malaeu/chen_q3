# Probe 9 -- lattice error against Xi and the alternating curvature form

Precommit: `docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md` (ADDENDUM 10). DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## Xi convention

centeredXi(z) = riemannXi(1/2 + i z), riemannXi(s) = 1/2 + (1/2) s(s-1) completedRiemannZeta0(s); implemented here via the algebraically identical classical formula xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s) in acb (valid since s = 1/2 + i*real never hits the poles 0,1).
Source checked: `q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean` lines 10-25.

## Xi implementation checks

- Xi(0) = 0.497120778188314 (imag rel error 1.079e-113)
- Xi'(0) = 0.000e+00 (should vanish -- Xi is even)
- Xi''(0) = -0.0229719443151454
- kappa_Xi = -Xi''(0)/(2 Xi(0)) = 0.02310499312  (reference ~0.02310)

## Per-cell table

| m=N | dps (rec/work) | W_k*L^2 | sup|Delta|*L^2 | n* | S_Xi | S_Delta | tail | kappa_check | kappa_Probe4 | 8-sig agree |
|---|---|---|---|---|---|---|---|---|---|---|
| 13 | 240/240 | 0.194969 | 0.2542 | 3 | 0.02401565983 | 0.002791274283 | -0.0009106667075 | 0.02589626741 | 0.02589626741 | True |
| 23 | 240/240 | 0.28049 | 0.450754 | 3 | 0.0235553207 | 0.00315802339 | -0.0004503275842 | 0.02626301651 | 0.02626301651 | True |
| 43 | 240/240 | 0.303233 | 0.557941 | 4 | 0.02329428964 | 0.002738063687 | -0.0001892965295 | 0.0258430568 | 0.0258430568 | True |
| 83 | 240/240 | 0.277189 | 0.584887 | 4 | 0.02317592431 | 0.002063078359 | -7.093119552e-05 | 0.02516807147 | 0.02516807147 | True |
| 163 | 900/240 | 0.224798 | 0.547908 | 5 | 0.02312957798 | 0.001414507185 | -2.458486636e-05 | 0.0245195003 | 0.0245195003 | True |

## Low-mode profile (Delta_n, n = 1..8)

- m=13: [-1.449160e-02, -3.721169e-02, -3.863828e-02, -2.103235e-02, -5.085532e-03, 5.473379e-04, 6.248490e-04, 9.575380e-05]
- m=23: [-1.148977e-02, -3.405498e-02, -4.584872e-02, -3.832761e-02, -2.084664e-02, -6.506317e-03, -1.512471e-04, 8.819309e-04]
- m=43: [-7.136923e-03, -2.322090e-02, -3.679662e-02, -3.943989e-02, -3.114641e-02, -1.822857e-02, -7.317195e-03, -1.283115e-03]
- m=83: [-3.972410e-03, -1.371187e-02, -2.405305e-02, -2.995405e-02, -2.918562e-02, -2.296560e-02, -1.454352e-02, -7.070713e-03]
- m=163: [-2.075589e-03, -7.442666e-03, -1.393163e-02, -1.906525e-02, -2.111700e-02, -1.970387e-02, -1.569805e-02, -1.062345e-02]

## Verdicts

- `P_WEIGHTED_LATTICE_ERROR_POLYLOG` (p=0.65): W_k * L^2 <= 10 at every cell -> **CONFIRMED**
- `P_SUP_LATTICE_ERROR_POLYLOG` (p=0.45): sup_{n<=N} |Delta_n| * L^2 <= 10 at every cell -> **CONFIRMED**
