# PROGRESS — source-exact evaluator of d_S(xi)

## 2026-09-06 (start)
- Stage: S0 setup. Workspace created. numpy 1.26.4 / scipy 1.11.4 / mpmath 1.2.1.
- Read verdict sections 0-3 (eq (1)-(23)).
- Dictionary check done ON PAPER (to be re-checked numerically):
  V: L^2(log line) -> L^2(0,inf), (Vg)(u) = u^{-1/2} g(log u), unitary.
  U_c g(x) = g(x-c)  ==>  physical  U_c f(u) = e^{-c/2} f(u e^{-c}).
  c = a = log p : U_a f(u) = p^{-1/2} f(u/p)                 [matches task]
  c = -j a      : U_{-ja} f(u) = p^{j/2} f(p^j u)            [matches task]
  Compressed kernel: U_{-ja} F_inf has kernel p^{j/2} * 2cos(2 pi p^j u v),
  coefficient (1-r^2) r^j * r^{-j} = 1 - 1/p  ==> c_j = 1-1/p, beta_j = 2 pi p^j (j>=0).
  U_a F_inf has kernel r * 2 cos(2 pi u v / p), coefficient -r * r = -1/p
  ==> c_{-1} = -1/p, beta_{-1} = 2 pi / p.   MATCHES verdict 2.2. Jacobian cancels r^j. OK.
- Next: implement I(beta,xi), J(beta,xi) closed forms + quadrature cross-check.
- Doubts: rigorous tail bound (13) has an unspecified constant C and is numerically
  useless at attainable truncation J (at J=8 it is O(0.1)). Plan: report BOTH the
  shape-only rigorous bound and an EMPIRICAL convergence study in J.

## S1/S2 done (I,J,gamma,q,A_inf)  — 2026-09-06
- I(beta,xi) closed form (incomplete gamma) vs exact power series: agree to 1e-42 at
  (beta,xi) = (0,1000),(3,2),(25,10),(200,30),(1000,50),(100,100),(2pi*2^8,60).
  |I| sqrt(beta) -> 1.25331 = sqrt(pi/2) exactly (Lemma 3 regime beta >> T). CONFIRMED.
  J = -dI/ds by mpmath.diff and by series with squared denominator: agree to 1e-42.
  Cost 8 ms per call even at beta = 2.2e14. J_u = 55 is affordable.
- |gamma_S| = 1 to 1e-12; (gamma'/gamma)/i = q_S to 5e-11 (finite difference), S = {inf} and {inf,2}.
- A_inf Nystrom (GL, symmetrized): eigenvalues +0.99997137627, -0.97948473467,
  +0.52408589623, -0.05897658918, +0.00273232874, -0.00007629136 (N-converged 200..3200).
  These SQUARE to the quoted Slepian values 0.99994275335 / 0.95939034545 / 0.27466602663 /
  0.0034782381 to 4e-12.  ==> the quoted list is spec(A_inf^2) = the prolate concentration
  eigenvalues; spec(A_inf) = +-sqrt of them with alternating signs. VALIDATION PASSES.
  alpha_inf = 0.9999713762674, so ||Z_inf|| = 1/(1-alpha^2) = 17466.
- d_inf(xi) computed (single-term kernel, NO truncation): d(0)=+0.8550, d(1)=+0.3223,
  d(5)=+0.03663, d(16)=-0.05070, d(40)=-3.3369e-3, d(80)=-9.1692e-4, d(120)=-5.8213e-4.
  Terms cancel to 5 digits at small xi (Z is near-singular); double precision still leaves ~11 digits.

## OBSTRUCTION found (recorded before it is resolved)
- The truncated Euler multiplier m^(J)(xi) = (1-r^2) sum_{j<=J} r^j e^{i j a xi} - r e^{-i a xi}
  has sup|m^(J)| > 1 for EVERY J (1.0824 at J=6, 1.0487 at J=8), and
  sup|m^(J) - m| = (1+r) r^(J+1) EXACTLY (checked on 2e5 points). Hence
  alpha_2^(J) = ||A_2^(J)|| numerically 1.0039 (J=5), 1.0064 (J=6), 1.0047 (J=7) > 1,
  so Z = (I-A^2)^{-1} is indefinite for the truncated operator and (6) cannot be applied raw.
- The rate r^J = 2^{-J/2} is intrinsic (m is analytic only in the strip |Im| < a/2), while the
  Nystrom cost grows like beta_J = 2 pi 2^J. J=8 (beta=1608, N~4000) is the practical ceiling;
  operator-norm truncation error there is 0.0754.
- Plan: (i) normalize A^(J) by sup|m^(J)| (a 1+O(r^{J+1}) rescaling, same order as the
  truncation already committed) so alpha<1; (ii) run J=4..8 and report the empirical
  J-sequence as the honest error estimate; (iii) t_S and ||u||^2 carry the full j<=55 sum.

## Galerkin route (coordinator's fix) — 2026-09-06
- Implemented Legendre-Galerkin: phi_m(u)=sqrt(2m+1)P_m(2u-1);
  S_mn(beta)=int int phi_m 2cos(beta u t) phi_n = 2 sqrt((2m+1)(2n+1)) Re[i^n int P_m(2u-1)e^{i beta u/2} j_n(beta u /2) du],
  composite GL, 6 pts/wavelength.  <phi_m,f_xi> has the CLOSED FORM
  (2pi)^{-1/2} sqrt(2m+1) prod_{k=1..m}(s-k)/prod_{k=0..m}(s+k), s=1/2+i xi  (checked at m=1 by hand).
- VALIDATION (independent channel): Galerkin d_inf agrees with the Nystrom+fine-grid d_inf
  to 8 significant digits at xi=0,1,5,16,40,80,120, and the Galerkin t_gal reproduces the
  closed-form t_inf to 1e-15. d_inf is therefore VERIFIED by two disjoint discretizations.
- FAILED for S={inf,2}: no M-convergence (d_2(16) = -0.074 / -0.053 / -0.063 at M=32/64/96).
  Two causes, both understood:
  (a) my analytic large-beta tail S_mn ~ phi_m(0)phi_n(0) pi/beta is valid only while
      beta >> 2 pi M^4 (its rank-1 norm M^2 pi/beta must not exceed the true ||S(beta)||=sqrt(2pi/beta));
      at M=96, J1=10 it produced alpha=2.26. DROPPING the tail is better (error <= (1+r) r^{J1+1}).
  (b) STRUCTURAL, and this is the real blocker: f_xi = v^{-1/2+i xi} is NOT in L^2(0,1)
      (|<phi_m,f_xi>| ~ m^{-1/2}), so the eigen-expansion of t and of ||u||^2 converges only
      logarithmically in M.  The verdict's (6) is written exactly to avoid this (u=A f_xi is L^2),
      but recovering u in a basis re-introduces the same slowly convergent j-series.
- HARD OBSTRUCTION for d_2 (recorded): (6) contains 1/(1-lambda_n^2). A_inf already has
  lambda_0 = 0.99997138, i.e. 1-lambda^2 = 5.7e-5, and the finiteness of d_S rests on an EXACT
  cancellation Re{gamma conj(c_n)^2} - lambda_n |c_n|^2 = O(1-lambda_n^2) which holds only for
  the true operator. Any operator error eta enters d as eta/(1-lambda^2). For S={inf,2} the
  attainable eta is the multiplier tail (1+r) r^{J1+1}: 4.7e-3 at J1=16, 1.2e-3 at J1=20,
  while the numerics put ||A_2|| within 0.0754 of 1 and its second eigenvalue rising
  0.830/0.893/0.934/0.960/0.976 at J=4..8 (geometric extrapolation ratio 0.63 -> ~1.00).
  So 1-alpha_2 is not resolvable here and d_2 via (6) is NOT computable at this precision.

## 23:50 — production runs
- BUG FOUND AND FIXED (mine): the first prod_op pass clipped |lambda| at 0.999, which destroys the
  exact near-unit cancellation and gave d_inf(16) = -9.5e-3 instead of -5.07e-2. No clipping,
  no rescaling now; modes with |lambda|>=1 (truncation artifacts) are dropped and reported.
- t_S tables done for xi = 0(0.25)600, J_u = 55, scalar tail bound 3.5e-8 (well under 1e-6).
- d_inf: log-log slope of |d_inf| on [60,600] = -2.0008 (running-max envelope -2.087). Theorem 4
  archimedean exponent CONFIRMED.
- W_h mass (from the diagnostic |hhat|^2 row): 10/25/50/75/90/99% quantiles at
  xi = 58.5 / 122 / 203 / 297 / 429 / 568. So the sign integral lives at LARGE xi, exactly where
  the near-unit modes are dormant (term_0 = -3e-5 at xi=120 vs total -4.5e-4).
  2*int_0^600 W dxi / H = 5.827 vs Lemma 5's exact 2pi = 6.283 -> the array holds 93% of the mass.

## 00:15 — validations that are already closed
- k_inf(xi) = q_inf/2pi + d_inf is EXACTLY 0 (to 1e-16) for xi <= 2 and rises to +0.7256 at 600.
- int_0^X d_inf dxi = 7.32/X to 3 digits for X = 100,200,300,400,500,600
  (0.073322/0.036608/0.024415/0.018308/0.014646/0.012205) ==> int_0^inf d_inf = 0.
  Tr D_inf = 0 CONFIRMED, and the 7.32/X law matches d_inf * xi^2 ~ -7.3.
- |d_inf| log-log slope on [60,600] = -2.0043, running-max envelope -2.0920. O(xi^-2) CONFIRMED.
- k_inf vs the finite-carrier diagnostic k_arch: max|res| = 1.28e-4 on [16,120] (rms 4.7e-5),
  i.e. BETTER than the carrier's claimed 1e-3. Beyond the carrier's validity the residual grows
  exactly as the verdict's order-of-limits warning predicts: 1.0e-2 on [120,300], 1.33e-1 on [300,600].
- carrier row 1 (q_inf/2pi) reproduces our q_inf/2pi to 2.2e-16: the carrier's digamma column is exact.
- d_S(-xi) = d_S(xi) to 0 (machine) — d is even, so full-line integrals are 2x the half-line.
- |hhat|^2 (npy row 4) is oscillatory with a broad maximum near xi=200 (1.9e6) and decays by a
  factor ~2 per 100 in xi after 400. 2*int_0^600 W_h = 5.8267 vs Lemma 5's exact 2pi = 6.28319,
  so 7.26% of the phase-marginal mass sits beyond xi=600. That deficit is used as an EXACT
  tail-mass constraint: |tail of int W_h d_2| <= 0.4565 * sup_{xi>600}|d_2|.
- Eigenvalue table of the Nystrom A_2^{(J)} (no rescaling), J=4..8: lambda_0 -> -1 from above
  (-0.9911, -1.0039, -1.0064, -1.0047, -1.0018) and lambda_1 rises 0.8300/0.8928/0.9337/0.9597/0.9758
  with increment ratio 0.622, geometric limit 1.0024. lambda_2 -> 0.6212, lambda_3 -> 0.5619.
  So the semilocal pair carries TWO near-unit angles where the archimedean place carries one.

## 00:40 — d_2 results (J=6,7 in; J=8 running)
- Thm 4 exponent for d_2: running-max envelope slope -0.482 / -0.483 / -0.494 on
  [60,600] / [100,600] / [200,600]. -1/2 CONFIRMED (raw slope -0.54..-0.60).
- (v) first cosine coefficient of k_2-k_inf over complete periods 2pi/a = 9.06472:
  -0.1479 ([50,294.8], 27 periods), -0.1505 ([50,593.9], 60), -0.1490 ([100,299.4], 22),
  -0.1513 ([100,598.6], 55), -0.1521 ([200,598.9], 44).  Target -a r/pi = -0.156013.
  Sine coefficient -> 0 (|s1| <= 3e-4). CONFIRMED, converging at the O(X^{-1/2}) rate.
- d_2 is NOT one-signed: negative on 56% of [16,600].
- k_2 = q_2/2pi + d_2 dips NEGATIVE: min -0.01512 at xi=8.25 (needs the J=8 check).
- S5 first pass: m(h) = -int W_h d_2 = +0.01201 (J=6) / +0.01325 (J=7). POSITIVE but ~25x
  smaller than the diagnostic +0.34/+0.36. Leading term alone gives only +0.00194: the positive
  sign is carried by the reservoir term -2<u,Zu> <= 0, which integrates coherently.
  int W_h d_inf = -0.004736, so A(h) = +0.004736.

## 01:00 — S5 breakdown, quadrature check
- m(h) = -int W_h d_2:  J=6 +0.012007, J=7 +0.013246.  Decomposition (J=7):
  from 2Re(gamma t_2)      +0.001943
  from 2Re(gamma <u,AZu*>) +0.000062
  from -2<u,Zu>            +0.011241   <- carries the sign; -2<u,Zu> <= 0 pointwise, so this
                                          contribution to m(h) is >= 0 for ANY admissible h.
  A(h) = -int W_h d_inf = +0.004736;  w = a/sqrt2 = 0.490129;  B(h) = w + int W_h(d_2-d_inf) = +0.4816.
- Quadrature check of the S5 integral: trapz at step 0.25 / 0.5 / 1.0 gives
  +0.013246 / +0.013308 / +0.013211; Simpson +0.013225 / +0.013341 / +0.013004. Error <= 1e-4.
- STRUCTURE FOUND: |t_2(xi)| peaks exactly at xi = 0 mod 2pi/log2 = 9.0647 (checked at
  408, 417, 426, 435, 444.25, 453.25 -> residues 0.088, 0.024, 9.024, 8.959, 0.080, 0.015).
  The peak height is the Poisson-kernel maximum 1/(1-r) = 3.41 times the mean and the peaks are
  ~0.4 wide, because t_2 = (1/pi) sum_j c_j J(beta_j,-xi) has phases -xi log beta_j = -xi(log 2pi + j log 2),
  an arithmetic progression, i.e. a Poisson kernel in the variable xi log 2. This makes d_2 spiky;
  the 0.25 grid resolves it (checked by decimation).
- Missing weight beyond 600: exactly 2pi - 5.8267 = 0.45648 by Lemma 5. With sup|d_2| ~ 0.10 there
  the tail bound on m(h) is +-0.046 -- LARGER than m(h) itself. This is the dominant error term.

## 01:40 — DONE
- J=8 landed. m(h) J-sequence +0.012007 / +0.013246 / +0.013424, increments ratio 0.144,
  geometric limit +0.013453. Resolved error +-3e-4 on |xi|<=600.
- STRUCTURAL RESULT: every eigen-mode's contribution to d_2 beyond 2Re{gamma t_2} is <= 0
  (because |Re{gamma conj(c_n)^2}| <= |c_n|^2 and |lambda_n| <= sup|m_2| = 1). Hence
  d_2(xi) <= 2Re{gamma_2 t_2} pointwise, m(h) >= -int W_h 2Re{gamma_2 t_2} = +0.001943,
  and any unresolved near-unit angle can only INCREASE m(h). The sign is robust upward.
- CARRIER REPRODUCED: feeding the diagnostic's own k rows to the same integrator gives
  m = +0.358740, matching the reported +0.34/+0.36. Source-exact is 27x smaller (+0.0134).
  Even A(h) alone: ours +0.004736 (verified by two channels) vs carrier +0.093609.
- Report written: D2_REPORT.md (208 lines).
- OPEN / what would close it: |hhat|^2 beyond xi=600 (7.27% of the Lemma-5 mass, currently
  bounded only by +-0.046). Nothing else limits the sign statement.

## 02:10 — follow-ups
- ANALYTIC hhat VALIDATED: eta(x)=exp(-1/(1-(x/d0)^2)) normalized to int eta = 1, d0=0.05068313851,
  hhat = -(xi^2+1/4) etahat. My |hhat|^2 reproduces the diagnostic array row 4 on ALL of [0,600]
  to 1e-11 relative (median ratio 1.0000000000). The array is exactly this h.
- Extending to xi=3000 captures H/H_exact = 0.99999293 and 2*int_0^3000 W = 6.283141 of 2pi=6.283185
  (deficit 4.4e-5 = 0.0007%, target was <0.1%). H_exact = 1.6434228127646e8 recovered to 7e-6 rel.
- Polynomial pole-null tests eta_k = N_k (1-(x/d0)^2)^k, int eta_k = 1, h_k=(d^2-1/4)eta_k:
  H_2 = ||h_2||^2 = 6.7284982340e7, H_4 = 1.7785336975e8 (exact Gauss-Legendre in x).
  Lemma 5 check int W_k -> 2pi: k=4 reaches 99.998% by xi=600 and 100.000% by 1500;
  k=2 reaches 94.83% by 600, 98.95% by 3000, 99.92% by 40000 (heavy tail: |hhat_2|^2 ~ xi^-2).
  Fraction below xi=150: k=4 98.618%, k=2 79.008%.

## 02:40 — section 7 numbers (operator extension still running past xi=600)
- With the operator part set to its |xi|<=600 values only (lead-only beyond 600):
  frozen h  : m = +0.013454 (J=8) / +0.013276 (J=7); floor +0.001973; vs delta_M=0.020866 -> m < delta_M
  h_2       : m = +0.025790 (J=8) / +0.026090 (J=7); floor +0.003687; m > delta_M, margin +0.004924
  h_4       : m = +0.024253 (J=8) / +0.024606 (J=7); floor +0.003509; m > delta_M, margin +0.003387
- W-mass below xi=16 (where d_2 is ill-conditioned): 0.05% (bump), 0.13% (k=2), 0.05% (k=4).
  The near-unit-angle obstruction is irrelevant to all three sign integrals.
- W-mass coverage: k=4 reaches 100.000% by xi=600 (deficit 4e-7) -> essentially no tail term;
  bump 99.9993% by 3000; k=2 only 98.95% by 3000 (|hhat_2|^2 ~ xi^-2), so k=2 keeps a
  tail uncertainty ~0.0659 * sup_{>3000}|d_2| ~ 3e-3, comparable to its own margin.

## 03:20 — sections 7 and 8 written
- Analytic hhat matches the array to 1e-11; extension to xi=3000 leaves a 0.0007% mass deficit
  (bump) / 4e-7 (h_4) / 1.05% (h_2). Cheap v-grid validated against the production run to 7e-17.
- m(h): bump +0.013628, h_2 +0.026895, h_4 +0.024253 (J=8); spreads +1.8e-4 / -3.0e-4 / -3.5e-4.
  vs delta_M = 0.020866: bump BELOW (-0.00724), h_2 ABOVE (+0.00603), h_4 ABOVE (+0.00339).
- Judge's inverse-free representation VERIFIED independently: d = ell - sum_n(<x,Tx^n x>+<y,Ty^n y>)
  matches the (6) assembly to 7.8e-15 on all 2401 points; all terms >= 0; Sx[0]+Sy[0]=||u||^2 to 6e-17.
- M_N crosses delta_M at N=2 (h_2) and N=5 (h_4) for BOTH J=7 and J=8; never for the frozen h
  (it saturates at its own limit +0.013627). J-spread of M_N is flat in N (2e-4..4e-4), as predicted.
- D2_REPORT.md now 331 lines (sections 0-8).

## 2026-09-07 — tail constant fixed (SCALARFLOOR verdict + independent check)
`prod_t.py::tail_bound` used the parent's (13) with the shape constant set to 1. The constant is false: at xi = 0 the
ratio |J| sqrt(beta)/(1 + log beta) tends to Gamma(1/2)cos(pi/4) = 1.2533 (1.33 at beta_56), and the stored bound
3.499e-8 was 0.75x the true truncation error 4.64e-8 (summation j = 56..89 and asymptotics agree). Replaced by the
verdict's proved uniform (32) with C = 256: eps_55 = 8.96e-6, floor error 4*pi*eps_55 = 1.13e-4. The t tables are
unchanged (exact closed forms); only the `tail` column of the npz was recomputed. All floors reported in
D2_SOURCE_EXACT_EVALUATOR_REPORT carry an extra -1.13e-4 budget; none changes sign (0.0035 -> 0.0034, 0.0019 -> 0.0018).
Still NOT a certificate: dropped modes in prod_op.py (|lam| >= 1 - 1e-12) remain; the certificate route is inverse-free (verdict (38)).
