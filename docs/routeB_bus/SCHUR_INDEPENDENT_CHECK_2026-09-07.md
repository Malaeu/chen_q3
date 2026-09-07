# SCHURCHECK — independent check of PROSHKA_VERDICT_GOAL058_SIGNED_SCHUR_COMPLEMENT_2026-09-07

Checker: fresh agent, no access to the request file or to any other verdict than [R] (2),(6),(8),(10)-(16)
and [CF2] §3.2. All numbers below were produced here (scripts in this directory). Convention throughout:
a=log2=0.6931472, r=2^-1/2, delta=(log3-log2)/8=0.0506861, d0=a/4=0.1732868, hhat(xi)=int h e^{-i xi x}dx.

## HEADLINE

1. **c = cosh(a/2)-1 = 0.0606601718 is CORRECT, and positive.** Re-derived independently and confirmed
   numerically to 10 digits. The coefficient the verdict never displays is
   `1 - r/2 - sqrt2/2 = -c`, i.e. the three families give `2 - sqrt2 - r = -2(cosh(a/2)-1) = -0.12132034`,
   and `-2pi * (1/4pi) * (-2c) = +c`. Numerical slope test:
   `(K_T(t1)-K_T(t2))/(S(t1)-S(t2)) -> 0.060660172` at t=1e-6..2e-6 (err 1e-10 vs cosh(a/2)-1).
2. **p(T) vs the probe: CONFIRMED and extended.** With the observer's evaluator, extended to T=960,1920:

   | T | p(T) from (11) | probe F(h_T) | probe/p |
   |---:|---:|---:|---:|
   | 30 | 9.169304e-03 | 2.950632e-03 | 0.32179 |
   | 60 | 4.584652e-03 | 2.417698e-03 | 0.52735 |
   | 120 | 2.292326e-03 | 1.738925e-03 | 0.75859 |
   | 240 | 1.146163e-03 | 1.054631e-03 | 0.92014 |
   | 480 | 5.730815e-04 | 5.601127e-04 | 0.97737 |
   | **960** | **2.865407e-04** | **2.848541e-04** | **0.99411** |
   | **1920** | **1.432704e-04** | **1.430580e-04** | **0.99852** |

   The relative defect 1-ratio falls by a factor 2.5-4 per octave, i.e. F(h_T)-p(T) decays faster than
   1/T^2 — strictly better than the o(1/T) claimed in (15). p from (10) equals (11) to machine precision.
   Probe stability (band +-250 vs +-800 around T): T=480 agrees to 2e-6, T=960 to 4e-7, T=1920 to 0.24%
   (1.427143e-4, ratio 0.99612). F is a ~1e3-fold cancellation inside the band, so treat the last digit
   of any single T as band-dependent; the trend across six octaves is not.
3. **NEW NEGATIVE RESULT (diagnostic, not a proof): the positive-extension certificate (20) FAILS for the
   verdict's own fixed quintic cutoff.** Computing R = K_T - cS on (-d0,d0) numerically gives
   R in [-1.0481, -1.0011] (strictly negative, essentially constant), so ||chi R||_1 = 0.28476 and
   `p(xi) + FT(chi R)(xi) < 0` on roughly xi in [0.13, 110], minimum **-2.08e-01 at xi = 5.98**
   (p=4.51e-02, FT(chi R)=-2.53e-01). The verdict's own §4.2 escape clause applies
   (`SCHUR_FIXED_EXTENSION_NEGATIVE_NOT_CLASS_REFUTATION`), but the §10 CODEX DIRECTIVE's success
   branch `SCHUR_SOURCE_POSITIVE_EXTENSION_CERTIFIED` is predicted dead for this chi and should be
   rescoped before spending on interval enclosures.
4. **End-to-end cross-channel check PASSES.** For h4=(d^2-1/4)(1-(x/delta)^2)^4:
   spatial `int K_T(t) C_h(t) dt = 1058.7908` (my kernel from (5), J=70, incl. the -2pi and the two
   half-translates) vs frequency `-int (1-cos a xi) ell2 |hhat|^2 dxi = 1058.7612` (observer's dens.py
   evaluator). Ratio 1.0000279. This validates (5)-(6) and dens.py against each other.

## PER-ITEM VERDICT

**1. §2.1 (3), L, S positive definite — CORRECT.**
L(z)=int_0^1(-log u)cos(zu)du = Si(z)/z confirmed to 1e-32 at z=0.3,1,5,30; L',L'' formulas confirmed
against numerical differentiation. On a 1e5-point grid up to z=4000: max|L|/min(1,4/|z|)=1.0000,
max|L''|/min(1/9,12/z^2)=1.0000, max|L'|/min(|z|/9,5/z^2)=1.00056 — the excess is float cancellation in
sin z - Si z at z~1e-5; the exact expansion L'(z) = -z/9 + z^3/150 - ... gives |L'| < z/9 strictly.
max|Si| on the grid = 1.85194 (< the 4 used). Positive definiteness: FT of L(beta t) is
(pi/beta)log(beta/|xi|)1_{|xi|<beta} >= 0 — confirmed, and it reproduces p in (10) exactly.

**2. §2.2 (5) — CORRECT, and the "Thus" step is the first asserted step (see item 13).**
Re-derived from scratch: t_J = (2pi)^-1 FT[(-s)_+ H_J], gamma_J(xi)=int H_J e^{i xi s}ds, and with
k(t)=(1/2pi)int m e^{i xi t}dxi the kernel of gamma_J t_J is (1/2pi)int_{-inf}^0 (-y)H(y)H(y-t)dy, i.e.
I_J(-t)/(2pi); symmetrising for 2Re() gives exactly (I_J(t)+I_J(-t))/(2pi). Note the verdict's I_J(t)
uses H(s+t) where the direct convolution gives H(s-t); the symmetrisation makes this harmless, but the
orientation as written is the mirror one.
Numerics (J=2): (I(t)+I(-t))/2pi vs formula (5): rel. diff 4.7e-16 (t=0.1), 6.8e-16 (t=0.3).
Independent normalisation test: FT of the kernel (5) vs 2Re(gamma_J t_J) computed from closed forms —
agreement to 1e-5..1e-6 relative at xi=0,1,3,7,13. Also derived and confirmed
gamma_J(xi)=2 Gamma(s)cos(pi s/2) sum_j c_j beta_j^{-s} (s=1/2+i xi); for the full sum this equals
[CF2] (24) to 1e-31 and |gamma|=1. **The 2pi normalisation is right.**

**3. §2.3, the resonant-index calculation and c — CORRECT.**
i=j gives D(t)/(4pi); i=j+1 near +a gives (1/4pi){sqrt2 e^{t/2}S(2(1-e^t)) + r e^{-t/2}S(1-e^{-t})};
j=i+1 near -a is the mirror. S(2z)=S(z)-L(2pi z) is exact (beta_j*2=beta_{j+1}). Index -1 resonates only
finitely often; L is entire so those terms are smooth. Collecting with A1=e^{t/2}S(1-e^t) etc.:
brace = -c(A1+A2) + (sqrt2/2)[e^{t/2}L(2pi(1-e^t))+e^{-t/2}L(2pi(1-e^{-t}))], hence
K_T = (c/2)D - (sqrt2/4)[...] - 2pi[N0 - N+/2 - N-/2], i.e. **(7) is reproduced coefficient by
coefficient, sqrt2/4 included**, and (6) follows. Numerically R=K_T-cS is even to 2.4e-14, bounded in
[-1.0481,-1.0011], ||R||_1 ~ 0.351, ||R'||_1 ~ 0.088 on (-d0,d0): W^{1,1} confirmed.
Sign: **c > 0**; omitting either translated family destroys it (2-sqrt2 = 0.586 > 0, wrong sign) — the
verdict's warning in the last paragraph of §2.3 is exactly right.

**4. §2.3 (8) and the nonresonant separation — CORRECT (constants very loose).**
||q_beta||_{W^{1,1}(-d0,d0)} measured: 0.1876 (b=1), 0.1742 (4), 0.1106 (16), 0.1110 (64), 0.0982 (256),
0.0578 (1024), 0.0312 (4096) — against the claimed 2048 beta^{-1/2} = 2048,1024,512,256,128,64,32.
Bound holds with 1000-10000x slack; the **exponent** is right (||q_beta|| -> 2.0 beta^{-1/2}).
kappa = e^{-a-d0}(1-e^{d0}/2) = 0.17044821 > 0, and it equals exactly (1/2)(e^{-d0}-1/2); I re-derived
the case split (n>=1 gives (1-e^{d0}/2)max, n<=-1 gives 2^k(e^{-d0}-1/2)max with k>=-1) and the constant
is sharp for k=-1. Pair count 2n+3 at max index n and sum_{n>J}(2n+3)2^{-n}=(2J+7)2^{-J}: exact
(verified J=2,5,10).

**5. §3 (9)-(14) — CORRECT.**
(9)<->(10) identical after xi=beta_j u. (10)->(11): geometric sums sum 2^-k = 2, sum k2^-k = 2 give
p(T)=2 pi c e^{-theta}(theta+a)/T; numerically p from (10) = p from (11) to machine precision at
T=30..1920. min of e^{-th}(th+a) on [0,a] is a=0.6931472 (attained at BOTH endpoints), max 2/e=0.7357589
at th=1-a; hence c_*=2 pi c a=0.26418549, C_*=4 pi c/e=0.28042648. sup|xi|p(xi)=C_* including |xi|<2pi
(max of T(log(2pi/T)+a) at T=4pi/e gives exactly 4pi/e) — CORRECT. p(xi)>=c_*/(2pi+|xi|) CORRECT.
(14): chi R in W^{1,1} with compact support => FT = FT(R_c')/(i xi) -> Riemann-Lebesgue => o(1/|xi|).

**6. Theorem 1 (15) — CORRECT; the kink worry is unfounded.**
p is continuous at xi=beta_J (the dropping term has log(beta_J/xi)=0) and
p'(xi) = -2 pi c/(xi beta_J) on (beta_{J-1},beta_J), so |p'| <= 2 pi c/xi^2 a.e.; p' jumps by a factor 2
at each knot but p stays Lipschitz, and the proof only uses the Lipschitz bound. On |s|<=T/2 the error
is O(T^-2)·(Schwartz moment) — o(1/T). Pole moments vanish exactly since (d^2-1/4)e^{±x/2}=0.
||h_T||^2/T^4 -> ||eta||^2 confirmed. Numerics: table in HEADLINE 2; F(h_T) >= c_*/(2T) holds with room
(1.43e-4 vs 6.88e-5 at T=1920).
**Log-periodicity: SUPPORTED, NOT RESOLVED by this probe.** New runs across one full dyadic octave
(T=1610,1900,2380,3200; beta_J=3216.99): measured F*T/(2 pi c) = 0.6970, 0.7193, 0.7241/0.6837,
0.7028/0.6945 (the two numbers are band +-250 / band +-800) against the predicted e^{-theta}(theta+a) =
0.6933, 0.7204, 0.7358, 0.6948. All measurements lie in 0.68-0.72, next to the predicted band
[a, 2/e] = [0.69315, 0.73576], but the band-to-band scatter at T=2380 is 5.6%, larger than the 4.3%
width of the predicted oscillation. So the probe neither confirms nor refutes the 6% log-periodic swing.
The verdict's own argument for it, however, is exact algebra (geometric summation of (10)) and is
CORRECT; the claim that Tp(T) has no single limit stands on (11), not on the probe.

**7. Theorem 2 (19) — CORRECT, no gap found.**
Principal norm dominates weight c_*/(2pi+|xi|) [(12), checked]; moments continuous via
|int h psi| <= (int p|hhat|^2)^{1/2}(int |psihat|^2/p)^{1/2} with 1/p <= (2pi+|xi|)/c_* and psihat Schwartz;
sup|r_c/p| < inf and -> 0 at infinity (r_c=o(1/|xi|), p ~ 1/|xi|; near 0, p -> +inf); low band compact by
uniform bound + equicontinuity of xi -> hhat(xi) on a band (both hhat and d/dxi hhat bounded by the same
Cauchy-Schwarz), Arzela-Ascoli; high band -> 0 in norm; K_rel = norm limit of compacts. Essential
spectrum {1}, finitely many eigenvalues <= -1. The completion E00 does consist of distributions supported
in closure(I) (the P-norm dominates a weighted H^{-1/2} norm, so P-Cauchy => distributional convergence,
and support is closed under it) — the one point the verdict leaves implicit. **Sound.**

**8. §4.2 (20)-(23) — logic CORRECT; (20) itself numerically FALSE for the fixed chi (headline 3).**
(20)=>square: trivially, and the compression is unchanged because chi=1 on I-I=(-2delta,2delta) and
2delta=0.101372 < d0=0.173287. Failure of (20) refutes only the extension — stated correctly.
(21): the two structural pieces are right ((2J+7)2^{-J} exact; 2*2048 r^{J+1}/(sqrt(2pi)(1-r)) is the
right shape); the numerical constants C_N, C_chi, the factor (1+c) and 256 were NOT independently
recomputed — UNVERIFIED, but they are conservative by construction and the object is a majorant.
(22): two IBP for R_{c,J} + one for the omitted part gives |FT(chi R)| <= D_J/xi^2 + e_J/|xi|; with
p >= c_*/|xi| for |xi|>=2pi the threshold |xi| >= D_J/(c_*-e_J) is CORRECT.
(23): with A22 >= (1-eta)I, ||A12|| <= eta, A11 >= alpha, the Schur complement is >= alpha - eta^2/(1-eta)
— CORRECT (requires eta<1, which is assumed).

**9. §6 (25)-(28) — CORRECT.**
H=1+x^2-d^2/dx^2 has eigenvalues 2n+2; sum (2n+2)^{-2} = pi^2/24 = 0.41123352, sqrt = pi/(2 sqrt6) =
0.64127492 < 1 — CORRECT. ||T_K||_1 <= ||H^{-1}||_HS ||H_x K||_{L^2} is the HS*HS product bound.
Differentiated kernel bound (x^2+7)|k|+4|k'|+|k''| follows from |chi0'|<=2,|chi0''|<=6. I re-derived the
192: Cauchy-Schwarz on 3 terms x (x^2+7)^2 <= 64(u+3)^4 x length (u+3) = 192(u+3)^5. And
u+3 <= 3(1+|u+s|)(1+|s|) is true, giving 192*3^5 = 46656 = 216^2 — **the constant 216 is exactly right**,
and 5/2 -> 3 is legitimate. (26) = 2x216 for the two quadrants at s=0, plus the shifted Hankel.
(27): sympy — expanding (1+ja)^3 and summing termwise reproduces the displayed closed form identically
(`simplify(lhs-claim)==0`); numeric at r=2^-1/2, a=log2: series 228.30096220154775 vs closed
228.30096220154758. **CORRECT.**
(28): E_nKE_n-K = (E_n-I)KE_n + K(E_n-I), ||E_n||<=1, finite-rank density — correct. The counterexample
E_n=I+|e0><e_n|, K=|e0><e0| gives E_nKE_n-K = |e0><e_n|, trace norm 1, with E_n -> I strongly —
**verified by hand, correct.**

**10. §7 (29) and the Legendre density — CORRECT.**
||(cS*h)'||_2 <= sup(|xi|p)||h|| = C_*||h|| by Plancherel; ||(R_c*h)'||_2 <= ||R_c'||_1||h|| by Young;
mean-zero Poincare on an interval of length 2delta/n has constant (2delta)/(pi n); the rank-n mean map
plus a_{n+1}=s_{n+1} gives (29). Applying P00 is a contraction. Density: eta(x)=int 2sinh((x-y)/2)h(y)dy
is exactly the variation-of-parameters solution of eta''-eta/4=h with zero Cauchy data at -delta
(Wronskian -1), and the two moment conditions int h e^{±x/2}=0 make eta vanish to the right — verified.

**11. §8 (30)-(31) — CORRECT.**
Exhaustion by C_c^inf((-R,R)) is trivial. Unions of pole-null classes cannot exhaust: the constraints are
continuous linear functionals on a fixed support, so their common kernel is closed — correct.
|x|^2+|y|^2-3Re(conj(x)y): matrix [[1,-3/2],[-3/2,1]], eigenvalues 2.5 and -0.5; positive on each axis,
-1 at (1,1) — correct. (31): reflection sends P_lambda to I-P_{1/lambda}; the difference of the two
cutoffs is multiplication by 1_{[0,log lambda)} and (conjugated) 1_{[-log lambda,0)}; each tests to
log lambda ||v||^2 since Tr(T_v M_{1_E} T_v^*) = |E| ||v||^2 and gamma is unimodular. Total
-2 log lambda ||v||^2 — **re-derived, correct, sign included.**

**12. §1 corrections — (i),(iii) CORRECT; (ii) not checkable from the permitted sources.**
(i) From (1), the kernel of T is -int b e^{i xi t}dxi (T = -2pi T_b), so a kernel carrying -1/(2pi)
    is T/(2pi). Internally CORRECT. (The request file was not readable here.)
(iii) P=|u><u|, Q=|w><w|, <u,w>=c: in the o.n. basis (u,w'), PQ+QP = [[2c^2, c s],[c s, 0]], s=sqrt(1-c^2),
    eigenvalues c^2 ± c. **CORRECT.** For P=Q: -{P,P} = -2P, not PSD. CORRECT.
(ii) The sign of F = -Tr(T_v(PQ+QP)T_v^*) and the identity (2) come from [R] (1),(4),(9); the algebraic
    point that n2 >= 0 does not give L2-n2 >= 0 is valid regardless. UNVERIFIABLE here at the level of
    the source normalisation; flagged, not disputed.

## 13. RESULT codes, registrations, first asserted step

- **No RESULT code needs to change.** Nothing checked contradicts Q1..Q4 as coded, and
  `HIGH_MODULATION_LEADING_COEFFICIENT: LOG_PERIODIC_NOT_A_SINGLE_CONSTANT`,
  `SINGULAR_VALUE_UPPER_RATE: O_N_INVERSE`, `SHIFTED_EULER_TRACE_NORM_EXPONENT: 3` are all supported.
- **Registrations I would accept:** all four.
  `P_SCHUR_DYADIC_KERNEL_AND_COEFFICIENT_SURVIVES` — ACCEPT (5)-(14) including the 2pi factor and all
  three resonance families; (6),(7) re-derived exactly.
  `P_SCHUR_HIGH_MODULATION_POSITIVE_LEADING_TERM_SURVIVES` — ACCEPT; (18) also re-derived: with
  eps=delta/sqrt k, ||g||^2 ~ eps^{-3}||f''||^2 and the numerator ~ eps^{-2}int sigma(|s|/eps)|s|^3|fhat|^2
  reproduces (18) exactly, hence Theta(k^{-1/2}).
  `P_SCHUR_RELATIVE_COMPACTNESS_SURVIVES` — ACCEPT.
  `P_SCHUR_SHIFT_TRACE_EXPONENT_THREE_SURVIVES` — ACCEPT (216, pi/(2sqrt6), (27), (28) all check).
  Side check of an older registration: 18+72 sqrt2 = 119.8234 < 120 — holds, but by 0.15%.
- **First step in §2-§3 that is asserted rather than derived:** §2.2, the word *"Thus"* in
  "Thus the inverse Fourier kernel of ell_J = 2Re(gamma_J t_J) is K_{ell,J}=(I_J(t)+I_J(-t))/(2pi)".
  The convolution-theorem computation, the 2pi and the orientation are all hidden there (and the
  orientation as printed is the mirror image of the direct computation; harmless only because of the
  symmetrisation). **The load-bearing asserted step is the next one:** §2.3 never displays the
  coefficient collection `2 - sqrt2 - r = -2(cosh(a/2)-1)`. That single line is the whole positivity of
  the paper and it is left to the reader. Both are correct as checked here; both should be written out.

## Residual cautions

- Everything above is float/mpmath numerics plus paper re-derivation. No interval arithmetic, no kernel.
  The (20) failure is DIAGNOSTIC_NEVER_A_PROOF, but it is robust: it needs only R<0 and
  ||chi R||_1 = 0.285 > sup_{xi>0.13} p(xi), both of which follow from the verified (6)-(7).
- My first attempt at an "independent" ell2 (dyadic quadrature of J(beta,-xi)) disagreed with dens.py at
  xi=7,120. That was MY error: mp.quad cannot resolve cos(beta v) for beta up to 2 pi 2^55. For
  beta <= 2 pi 2^8 the two agree to 2e-10, and the end-to-end test (headline 4) vindicates dens.py.
  Recorded as a confabulation-risk datum against my own first number, not against the verdict.
