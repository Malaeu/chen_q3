# CLASSFLOORCHECK — independent check of PROSHKA_VERDICT_GOAL058_CLASS_FLOOR_REPRESENTATION_2026-09-07
Own re-derivation + own computation (mpmath/sympy/numpy; python-flint only to reproduce `budget.py`).
No recorded packet or scalar run re-executed. Scripts read-only.
## 1. §3 Theorem 1, |J| <= 120 b^{-1/2}(1+log b) — **CORRECT** (every constant)
After y = beta v: J = b^{-1/2-i xi} int_0^b b(y)y^{i xi}cos y dy, b(y)=y^{-1/2}log(b/y) >= 0 and
decreasing (b' = -y^{-3/2}[(1/2)log(b/y)+1] < 0).
- (0,1): int_0^1 y^{-1/2}(log b - log y)dy = **2 log b + 4** exactly.
- non-stationary (|xi|<B/2 or >4B): phi' monotone, |phi'| >= 1/2; van der Corput I gives primitive
  <= 2/lambda + TV(1/phi') = 4/lambda = **8**; second mean value with b decreasing >= 0 gives
  <= 8 b(B) <= 8 B^{-1/2}log b; sum_B 2^{-k/2} = 1/(1-2^{-1/2}) -> total **(16+8 sqrt2) log b**.
- stationary: |xi|/4 <= B <= 2|xi| leaves **at most 4** dyadic B (ratio 8 -> <=4 powers of 2);
  |phi''| = |xi|/y^2 >= (B/2)/(2B)^2 = 1/(8B). Splitting at |phi'| <= sqrt(lambda): middle
  <= 2/sqrt(lambda); each complement 2/sqrt(lambda) (two boundary terms) + 1/sqrt(lambda) (monotone
  variation of 1/phi') = 3/sqrt(lambda), two of them **6/sqrt(lambda)** -> **8/sqrt(lambda)** =
  16 sqrt(2B); Abel gives 16 sqrt2 log b each, 4 of them 64 sqrt2 log b.
- Total 4 + (2+16+8 sqrt2+64 sqrt2) log b = 4 + **(18+72 sqrt2)** log b, = **119.823376 < 120**.
  Every printed constant checks exactly; averaging the two exponentials is free.
Numerics (series, dps ~ beta/2.3+70), beta in {1,10,100,1000} x xi in {0,5,50,500}: all 16 cells obey
both bounds. C=1 counterexample: from (8) at xi=0, |J|sqrt(b) = sqrt(pi/2)log b + 4.4288 + O(1/b),
tail <= TV((log v)v^{-1/2})/beta = 1.4715/beta; |J|sqrt(b)/(1+log b) = 1.6491 (1e3), 1.4676 (1e6),
1.3643 (1e12), 1.2670 (1e100) -> **Gamma(1/2)cos(pi/4) = 1.25331413732 > 1**. A limit, not a sample.
## 2. §4, analytic domain of RESONANCE (6) — **CORRECT algebraically; one step only sketched**
(14)-(15) **CORRECT**. U_c has multiplier e^{-i c xi}, so b_S is the multiplier of B_S and b_S(-xi) of
B_S*. F_inf = C_{m_inf}R with m_inf(xi)m_inf(-xi)=1 gives F_inf B_S* F_inf = B_S; all factors are
multipliers, hence commute, hence B_S(B_S*)^{-1}F_inf = (B_S*)^{-1}F_inf B_S* identically. F_S = C_m R
with m(xi) = m_inf(xi)b_S(xi)/b_S(-xi) = gamma_S(-xi); involution <=> m(xi)m(-xi)=1 (holds),
self-adjointness <=> conj m(-xi)=m(xi) (same, given |m|=1), reality <=> the same.
(16) **CORRECT**: (I-rU_a)sum_j r^j U_{-ja} = (1-r^2)sum_j r^j U_{-ja} - r U_a, as printed.
4.1 **CORRECT**. Compact self-adjointness attains the norm, forcing F_S f = +-f with f in (0,1); B_S*
and its inverse preserve (-inf,0] in log (|1-r e^{i a xi}| >= 1-r > 0); g = B_S* f in L^1(0,1) has an
entire cosine transform vanishing on (1,inf).
4.2 nuclearity **CORRECT**. On supp(chi(x)k(x+y)chi(y)) x,y >= -1, so |x|+|y| <= (x+y)+4: rapid decay
in x+y IS Schwartz decay in (x,y). T = H^{-2}(H^2 T), H^{-2} trace class (sum(2n+1)^{-2} < inf), H^2 T
bounded. [T_v,P] has kernel v(x-y)(1_{y<=0}-1_{x<=0}), supported on the two off-diagonal quadrants
where it is +-v(-(x'+y')): Hankel with Schwartz symbol. P T_v F_S P: T_v F_S = C_{vhat m}R and
R P = (I-P)R, so it is Hankel with Schwartz symbol (vhat m is Schwartz — m's derivatives are
polynomially bounded) times a unitary. T_v P F_S P = [T_v,P]F_S P + P T_v F_S P is an algebraic
identity; both terms trace class. **The chain is sound.**
(17) **CORRECT, twice.** G = W*W = [[I,A],[A,I]], G^{-1} = [[Z,-AZ],[-AZ,Z]], I - G^{-1} =
[[-A^2Z,AZ],[AZ,-A^2Z]] since I - Z = -A^2 Z; S_S = I - proj(ran W) as ker P cap ker Q = (ran W)^perp.
Random finite model (n=12,k=5, F = O diag(+-1)O^T): ||D - W N W*|| = 6.4e-15 / 1.8e-15 in the two
trials with ||A||<1; the two trials that drew ||A||=1 fail, exactly as the hypothesis predicts.
||D+D^2-(PQ+QP)|| = 1.3e-15 in all four; by hand D^2 = K^2-2K+I-S_0, D+D^2 = K^2-K = PQ+QP.
(18)-(19) **CORRECT.** Phat = (1/2)delta + (i/2pi)pv 1/(xi-eta) re-derived from
int_{-inf}^0 e^{i(eta-xi)x}dx = pi delta - i pv(1/(eta-xi)); the delta cancels in C_m P C_m* - P
because |m|=1; the divided difference is smooth with diagonal m' conj(m); the kernel is Schwartz,
hence trace class, hence Tr = int diagonal. i m' mbar = q_S verified from gamma_S'/gamma_S = i q_S,
m(xi)=gamma_S(-xi), q_S even; q_S itself re-derived by log-differentiating (15):
i[Re psi(1/4+i xi/2) - log pi - 2 sum_p log p sum_j p^{-j/2}cos(j xi log p)]. Exact match.
Independent numeric: circle model, exact Blaschke m(z)=(z-c)/(1-cbar z) (|m|=1, i m' mbar = -Poisson
kernel), P_+ the Riesz projection, w a real trig polynomial: Tr((C_m P_+ C_m* - P_+)M_w) =
**-1.760000000000** at Nf = 64/128/256/512, versus -(Poisson extension of w at c) = **-1.76**. Exact
to 12 digits. (A first attempt with a non-band-limited m gave -0.466 vs -0.200: Toeplitz truncation
artefact, not a failure of (19).)
(20) **CORRECT**: S_S = R_S + D_S is immediate; Tr(T_v S_S T_v*) = ||T_v S_S||_HS^2 as S_S is a
projection; both summands trace class (Schwartz kernel; §4.2). (21) **CORRECT**. U_c F_inf has kernel 2 e^{-c/2}cos(2 pi e^{-c}uv), giving exactly beta_{-1}=2pi/p,
c_{-1}=-1/p, beta_j=2pi p^j, c_j=1-1/p. Then A_S f_xi yields sqrt(2/pi)sum c_j I(beta_j u,xi) and the
double integral yields (1/pi)sum c_j J(beta_j,-xi); int_0^1 int_0^1 F(uv)du dv = int_0^1(-log v)F(v)dv
re-derived by w=uv + Fubini. L^2 bound **CORRECT**: split at u = 1/beta, |I| <= 2 below and
|I| <= 120(beta u)^{-1/2} above -> ||I(beta.,xi)||^2 <= (4+120^2 log beta)/beta; the needed
|I| <= 120 beta^{-1/2} follows from the same dyadic argument with amplitude y^{-1/2} (again 119.823).
(22)-(24) **CORRECT.** I recomputed the whole block trace: with Omega = W*T_v*T_v W and
C_{|vhat|^2} = int|vhat|^2 |f_xi><f_xi|, the [[0,A],[A,0]] blocks give int|vhat|^2 2Re(gamma_S t_S) =
int|vhat|^2 ell_S (using <f_{-xi},A f_xi> = conj t_S), and AZ = A + A^3 Z with diag(A,A) on both sides
gives exactly -2<u,Zu> + 2Re(gamma <u,AZ ubar>) — i.e. (23) with gamma, not gammabar. Cross-document
check: substituting (23) into ell_S - d_S with w = e^{-i phi/2}u, X=Re w, Y=Im w reproduces
SCALARFLOOR (7), 2<X,(I+A)^{-1}X> + 2<Y,(I-A)^{-1}Y> >= 0, via (I-A)Z=(I+A)^{-1}, (I+A)Z=(I-A)^{-1}.
It passes. (24) **CORRECT**: |vhat_h|^2 = 4 sin^2(a xi/2)|hhat|^2/(2H) = (1-cos a xi)|hhat|^2/H = W_h.
§4.3 Weil identification checks: the two-lobe autocorrelation lives in |t| <= a+2delta = 0.7946 <
log 3, so only p=2, j=1 survives, and the pole terms die on the moment-null class. §4.6 checks: eta_4
is in H^4_0(I) (traces through order 3 vanish) and for phi in C_c^inf(I) the two moments of
(d^2-1/4)phi vanish *identically* (integrate by parts against e^{+-x/2}) — no moment correction needed.
**First asserted-but-unwritten step (the only one found).** §4.4 stage 1 ("their diagonal traces
follow by an absolutely convergent smooth-kernel expansion"). At fixed finite Euler truncation and
frequency cutoff, Tr(A^{[J]} E* C_{|vhat|^2} F_S E) = int |vhat|^2 gamma_S t_S^{[J]} dxi is a
Fubini/Mercer interchange in which f_xi|_(0,1) is not in L^2(0,1), only L^1. It is provable (A^{[J]}
has a bounded kernel, so the pairing converges absolutely and |t^{[J]}| is bounded, giving the
majorant |vhat|^2 sup|t^{[J]}|) but the verdict does not write it. Referee-grade presentation gap,
not a refutation.
## 3. §2.3 series stopping rule — **CORRECT**
`h4arb.py:99` `if 2 * n > bub + 4 and term.abs_upper() < thresh:`, with `:93`
`thresh = arb(2) ** (-prec + 10)` (prec=400 -> 2^-390 << 1) and `:98`
`term = -term * b2 / ((2 * n) * (2 * n - 1))`, i.e. term = beta^{2n}/(2n)! exactly. term < 1 gives
(2n)! > beta^{2n}; with (2n)! <= (2n)^n n^n = (2n^2)^n (top n factors <= 2n, n! <= n^n) this forces
2n^2 > beta^2, i.e. **2n > sqrt2 beta**. Then term_{n+1}/term_n = beta^2/((2n+2)(2n+1)) < 2n^2/(4n^2)
= 1/2 and |s+2n| increases, so the full ratio is < 1/2 and `:105`
`rem = 2 * (acb(term) / (d * d)).abs_upper()` is a valid geometric remainder. The comment
`2n > beta + 4` alone gives ratio ~ 1 - 11/beta, i.e. NOT < 1/2 — the verdict's diagnosis and repair
are both right. `C_pow_cos` (`:51`, `:55`, thresh = 2^{-prec-10}) runs the identical argument.
## 4. §2.5 serialization — **CORRECT on all four points**
(a) `cert.py:43-45` `float(b.mid().str(25, radius=False))` / `r*1.000001 + abs(m)*2.0**-50 + 1e-300`;
`assemble.py:18-19` `float(mid); float(rad)` / `rad*1.0001 + abs(mid)*2.0**-48 + 1e-300`; also
`packassemble.py:65`. So `h4arb.py:15` ("NOTHING here is converted to a Python float on the
certificate path") is false for the transport layer. Padding adequate: 25-digit decimal (~1e-24 rel.)
+ double rounding (2^-53 = 1.1e-16) < 2^-50 = 8.9e-16; 1.000001/1.0001 dominate the radius conversion.
(b) `packassemble.py:51-52` `EBASE_DEF = "5.02304551867e-9"`, `EBASEM_DEF = "1.24819457775e-17"`,
emitted by `packequad.py:111` `out[best][0].str(12)` on a thin `abs_upper()` — `arb_get_str` is
last-place accurate, NOT outward. The in-code pad `packassemble.py:168-169`
`arb(ebase) * (1 + arb(2) ** -40)` is **0.457 ulp** (Ebase) and **0.114 ulp** (Ebasem): it does NOT
cover a downward last-digit rounding. The verdict's 1e-18 / 1e-26 are **100 ulp** each. Real defect.
(c) reallocation arithmetic **CORRECT** (delta = 0.0506831385135205, T0 = 13.9371046604,
4 pi eps_90 = 9.4726921e-10, all reproduced by running `budget.py`): released (17/32)*9.4726921e-10 =
**5.0323677e-10** > 4e-10 (eps_J linear in C; 120/256 = 15/32); quadrature guard 2 delta 1e-18 =
**1.0136628e-19**; frequency guard 2 T0[2 sqrt(2pi*2delta*1e-26)+2 delta 1e-26] = **4.44907e-12** <
5e-12; total 4.4491e-12, released/cost = **113**. The bracket follows term for term from
sqrt(D_i+d_i) <= sqrt(D_i)+sqrt(d_i), D_i <= 2 pi H_ii, d_i = 2 delta H_ii 1e-26; units consistent via
||h_i||_1 <= sqrt(2 delta H_ii).
(d) `abs_lower` IS used: `packassemble.py:178,179` (mass, positive here), `:238`
`lo = (q.mid() - q.rad()).abs_lower()`, `:302` `lam.abs_lower()`. Line 238 is the dangerous one — a
negative lower endpoint would print as its absolute value AND make the adjacent
`bool(lo > arb(1)/500)` report **True** for a negative floor. All values are positive in this run, so
no sign is misreported. Verdict CORRECT, if anything understated.
## 5. §2.4 rank, pencil, Weyl — **CORRECT**
sympy with symbolic delta: `h4z - (h4 - h5)` simplifies to **0**; all five profiles satisfy
int h e^{+-x/2} = 0 exactly; rank{h4,h5,h6,h4z} = **3**, rank{h4,h5,h6,h7} = **4**; the coefficient
kernel is **(-1,1,0,1)** = the verdict's (1,-1,0,-1) up to sign, and equals ker L for
L = [[1,0,0,1],[0,1,0,-1],[0,0,1,0]]. The synthesis identity sum c_k h_k^req = sum (Lc)_i h_i^(3)
verifies symbolically — that is exactly F_requested = L*F_3 L and H_requested = L*H_3 L. Weyl chain:
lambda_min(F0+D) >= lambda_min(F0) - ||D||_2; ||D||_2 = rho(D) <= rho(|D|) <= rho(R) = ||R||_2 for
symmetric D with |D| <= R (Perron-Frobenius); ||R||_2 <= ||R||_F always and <= sqrt(||R||_1||R||_inf)
= ||R||_inf for symmetric R. `rnorm_bound` = min(fro,inf), `spd_certify` Choleskys F0 - sI. Sound.
## 6. §5.2 (26)-(27) — **CORRECT**
2 pi, not 4 pi: the Rayleigh quotient IS F(h) = -int W_h ell_2 (numerator H F(h), denominator H) and
int W_h = 2 pi for every h of the class, since the autocorrelation of h vanishes at a (2 delta =
0.10137 < a = 0.69315). So the factor 2 from |1-cos| <= 2 is genuinely absorbed;
2 pi ||ell_2||_inf <= 4 pi T0 = **175.1388 < 176**. (26) re-derived: numerator >= 1/500 -
||T||(2 eps + eps^2), denominator <= (1+eps)^2; at eps = 1e-6 the right side is **0.001647996528 >
1/1000**. It already fails at eps = 5e-6 (0.000240) — 1e-6 is the right choice, not slack.
## 7. §5.1 — **CORRECT**
1/2+cos(a xi): Plancherel gives int|hhat|^2(1/2+cos a xi) = pi H + 2 pi(autocorr at a) = pi||h||^2
whenever supp h is shorter than a. Numeric, C^inf bump on (-delta,delta): 0.0211907408 vs
pi||h||^2 = 0.0211907408, relative difference **1.4e-14**; and 1/2+cos changes sign.
q_2(0) = psi(1/4) - log pi - 2 log2 sum_{j>=1}2^{-j/2} = -4.22745353338 - 1.14472988585 -
2(0.69314718056)(2.41421356237) = **-8.71899406728 < 0**. So k_2 >= 0 forces d_2(0) >= -q_2(0)/2pi > 0,
and the pointwise form of (24) (= SCALARFLOOR (7)) gives ell_2(0) >= d_2(0) > 0; since 1-cos(a xi) > 0
off 0, -b < 0 on a punctured neighbourhood of 0. CORRECT.
## 8. §5.4 (29)-(32) — **CORRECT**
A_N: g perp ran Pi_N means int g x^k = 0 for k=0..N (as <P_00 p,g> = <p,g> on H_00), so |ghat| <=
||g||_1(delta X)^{N+1}/(N+1)! <= sqrt(2 delta)(delta X)^{N+1}/(N+1)!||g||; e^{delta X} is pure slack,
so the stated bound holds conservatively. ||F E_I g||_{L^2(-X,X)} <= sqrt(2X)(2pi)^{-1/2}A_N||g|| =
sqrt(X/pi)A_N||g|| **exactly**. (29): ||T(I-Pi_N)|| <= 2 pi[M_X sqrt(X/pi)A_N + B_X], doubled by
self-adjointness for the other block -> **4 sqrt(pi X)M_X A_N + 4 pi B_X**; factor two right. (30): after v = e^{-x} the integrand is x e^{-x/2}e^{i(+-beta e^{-x} - xi x)}; with beta <= T/2,
|psi'| >= T/2 and |psi''|,|psi'''| <= T/2, giving |1/psi'| <= 2/T, |(1/psi')'| <= 2/T, |(1/psi')''| <=
6/T — the verdict's three numbers. Two integrations by parts: f(0)=0 kills the first boundary term,
the second is |f'(0)g(0)^2| = 4/T^2, and (u'g)' = f''g^2 + 3f'g g' + f g''g + f(g')^2 gives
**[4||f''||_1 + 12||f'||_1 + 16||f||_1]/T^2** — the verdict's formula term for term. With ||f||_1 = 4,
||f'||_1 = 4/e = 1.4715 <= 4, ||f''||_1 = 1+2e^{-2} = 1.2707 <= 3: 4+12+48+64 = **128**. Grid test
(xi in {2,5,20,100,400,1200} x beta/(xi/2) in {0..1}): worst |J| xi^2/128 = **0.0174**.
(31): re-derived exactly — j <= J_X uses (30) (128(J_X+2)/X^2, J_X+2 terms from j=-1), j > J_X uses
(12) with beta_j^{-1/2} = (2pi)^{-1/2}r^j and 1+log beta_j = 1+log beta_{J_X+1}+a(j-J_X-1); the 1/pi
prefactor is |ell_2| <= (1/pi)sum_j|J(beta_j,.)|. L_X = 191.98 (4pi), 43.06 (1e3), 2.342 (1e6),
0.1043 (1e9) -> 0. B_X <= 2 L_X, M_X <= 4 T0 CORRECT. (32): spec(Pi_N T Pi_N) = spec(block) union {0},
so the mandatory min{0,.} is right; Weyl does the rest.
## 9. §5.5 — **CORRECT** (both standard)
Obstruction: -eps<e,.>e on e perp ran Pi_N leaves the compression unchanged and only enlarges the
complement bound, so "positive head + unsigned tail <= eps" is a theorem only when eps <
lambda_min(head) — which a compact operator with infimum 0 can never supply. Schur: expanding
||A^{1/2}x + A^{-1/2}By||^2 + <y,(C_0-B*A^{-1}B)y> returns <x,Ax>+2Re<x,By>+<y,C_0y> identically; the
range/pseudoinverse caveat for semidefinite A is exactly Albert's condition.
## 10. RESULT codes — no change required
- **Q1 CERTIFICATE_RATIFIED**: defensible. Both implementation defects are real; the repair arithmetic
  holds with a factor 113 of slack; the exported statements (11) use rational thresholds, not printed
  decimals. Correctly flagged as ratification of recorded output (`INTERVAL_RUNS_RERUN_BY_JUDGE: false`).
- **Q2 PROVED_ON_CLASS**: correct; sharp constant 18+72 sqrt2 = 119.823376.
- **Q3 PROVED_ON_CLASS**: justified as a paper theorem, with one unwritten step. All algebra in
  (14)-(24) re-derived independently, and two independent numerical channels (random involution model
  for (17); Blaschke circle model for (19)) confirm the two formulas carrying the section. The single
  gap is analysis-level: **§4.4 stage 1, the Fubini/Mercer interchange identifying the operator trace
  with the xi-integral of a Mellin-kernel diagonal built from the non-L^2 wave f_xi.** I would not
  downgrade the code — the verdict marks `VERIFIER: PAPER`, `INDEPENDENT_REVIEW: pending` and scopes
  Q3 to "the requested source and domain" — but PROVED_ON_CLASS currently rests on that one sentence.
- **Q4 PARTIAL_WITH_PRECISE_REMAINDER**: correct; §5.1-§5.5 all check out.
- Not said by the verdict, worth adding: `packassemble.py:238` `(q.mid()-q.rad()).abs_lower()` can
  print a negative normalized floor as positive and make the adjacent `>= 1/500` test report True.
  A live latent bug, beyond the general §2.5 warning.

**UNVERIFIABLE here** (out of scope, not re-run): the recorded `I_compact`, `MASS[...]` and pivot
values in `out/main.txt` / `packet/out/verify.txt`; the enclosure [0.00343936, 0.00357821]; the claim
that the packet pencil floor exceeds 1/1000.
