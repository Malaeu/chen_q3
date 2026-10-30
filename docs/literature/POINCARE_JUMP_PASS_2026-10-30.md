# Literature pass: sharp Poincare / spectral-gap bounds for the MARKOV jump form (6.9) — 2026-10-30

Target (MARKOV verdict (6.8)-(6.9), identity checked to 1e-9): E_h[F] >= 8 Var_mu(F) + 8 |int tanh(x/2) F dmu|^2, constant 8 sharp.
Method: one researcher agent (WebSearch + arXiv full texts via pdftotext); observer re-checked the quotes marked [checked].

## Findings
| Source | What it gives | Sharp? | Fits our kernel? |
|---|---|---|---|
| Chen-Wang, arXiv:math/9804150, Thm 1.2, 1.4 | Cheeger and Dirichlet-Neumann localisation bounds for general symmetric forms | no (quadratic in Cheeger constant) | yes, but loses the constant 8 |
| Chen, arXiv:math/0101227, Thm 2.1, 3.2 | dual variational formulas lambda_1 = sup_w inf I(w)^-1 | yes | only birth-death and 1D diffusions (single-birth extension: not opened) |
| Frank-Lieb-Seiringer, arXiv:math/0610593, Prop 4.1 | ground-state transform for non-local forms, sharp Hardy | yes (identity) | our (6.8) is already this move |
| Haeseler-Keller, arXiv:1002.1040, Thm 3.1 [checked, txt:212-216] | Allegretto-Piepenbrink: bottom >= E iff a positive w with (L - E) w >= 0 exists | yes, bottom of a positivity-preserving form only | graphs; not for a gap |
| Spener-Weber-Zacher, arXiv:1903.00521 | fractional Laplacian on R^d fails every Bakry-Emery CD(kappa, N) | obstruction | Gamma_2 route closed |
| Chen-Weth, arXiv:1710.03416; Laptev-Weth, arXiv:2009.03395 | logarithmic Laplacian (our j ~ 1/(2s)): existence, simple first eigenvalue | no | no gap bounds; d >= 2 for the second |
| Suzuki, arXiv:2606.09096, intro [checked, txt:75-77] | relay of Yoshida: Q_W(v) >= 0 for all odd v in C_c^inf implies RH | — | odd sector alone suffices (agrees with MARKOV (4.19)) |
| Connes-Consani-Moscovici, arXiv:2310.18423 | prolate functions give extremely small Weil eigenvalues on windows | — | any constant loss is fatal |

No paper links Weil positivity to a Poincare or spectral-gap inequality of a Markov process. No theorem forbids a sharp method either.

## Agent's candidate 1 killed by the observer probe
Candidate: in the folded odd sector replace positive off-diagonals by -|a_ij| (A_abs, Markov-type), then use a Barta /
Allegretto-Piepenbrink certificate, which is exact for A_abs. Folded odd sector: archimedean and pole couplings are Markov-type;
positive couplings come only from prime jumps log n crossing the window centre (the reflected-prime obstruction).
`docs/routeB_bus/thetagrade_2026-10-28/crossing_prime_probe.py` (dps 40): on the odd bottom f of K_O (no sign change on the
right half), crossing weight T = 0.19 (m = 3) .. 0.42 (m = 12), lam0(K_O) = 1.2e-4 .. 4.1e-26, so 2T / lam0 = 3.3e3 .. 2.0e25
and A_abs(|f|) = -0.39 .. -0.84 < 0. The comparison loses everything once a prime jump fits in the window (m >= 3).
For windows without crossing primes (Suzuki's small windows) A_abs = A and PF is exact: that is Suzuki Thm 1.4, nothing new.

## Verdict
No foreign tool found that reaches the sharp constant 8 for this kernel. Williams-method search for (6.9): dead end at this depth.
Reopen trigger: an exact (sup-inf) gap formula for symmetric jump processes beyond birth-death, or a comparison that keeps the
crossing-prime couplings. DIAGNOSTIC_NEVER_A_PROOF.
