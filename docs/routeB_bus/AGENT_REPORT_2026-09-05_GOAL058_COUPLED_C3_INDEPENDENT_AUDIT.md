# Agent report — independent paper audit of COUPLED verdict 6b103bd1, Section C3 (Opus, 2026-09-05)

Observer second-channel check of the auditor's constants (mpmath): Xi(0)/A = 0.8791346724 (match), Fhat(0) = 2*sqrt(pi) = 3.5449077 (match), Fhat(1) = 1.4916541219 (match), min a(t)*2t*e^(1/2) = 1.6495456 (match); pre-derivation file written 10:49:21, report 11:04:57 (order verified). Auditor's residual trust boundary: the domain lemma B(f,v)=0 for all v in X, C_X = |c_A|+14 and f > 0 on R are inherited from XIDEV, not re-proved here.

---

# Independent paper audit — Section C3 of PROSHKA_VERDICT_GOAL058_COUPLED_SIGNED_SQUARE_CERTIFICATE_..._2026-09-05.md

**Pre-registration.** 4 of 4 requested statements (TRANS-RAD, compact-cutoff budget, INDEP, NO-MINORANT)
were derived independently from the "Objects and inherited analytic facts" paragraph BEFORE any C3 proof
was read. Frozen text: `/home/chirurgie/.claude/jobs/4b35770d/tmp/audit_c3/MY_DERIVATIONS_PRE.md`.
**All four agree with the verdict**, including the mechanism (radical → cutoff → Fatou → Vandermonde) and,
where I computed them, the explicit constants. No statement of C3 was found false.

## Verdicts

| Lemma | Verdict | Note |
|---|---|---|
| C3.1 TRANS-RAD | **SURVIVES** | matches my derivation line for line; also confirmed numerically |
| C3.2 NULL-BUDGET | **SURVIVES** | every constant in `C_q^2` re-derived exactly (below) |
| C3.3 INDEP | **SURVIVES** | Fourier convention and Vandermonde step correct |
| C3.4 NO-MINORANT | **SURVIVES** | scope guard (a) holds; Fatou (b) and countability (c) correct |
| C3.5 exact CSS impossible | **SURVIVES** | every inequality in the numeric chain checked; threshold exact, not rounded |
| C3.6 product measure + finite matrices | **SURVIVES** | one wording caveat (below) |
| Positive control | **SURVIVES** | F-hat(pi/2)=0 verified to 1e-26; the control is decisive |

## Item-by-item checks requested

**(a) s_{q,R} in C_c^inf; no substitution of the noncompact r_q into CSS.** Clean. The hypothesis
`A_S(s) <= D(s)` is instantiated only at s_{q,R} = chi_R·r_q, which is compactly supported and smooth
because f is smooth and strictly positive. r_q enters only (i) as the pointwise Fatou limit and (ii) on
the bounded set E where S s_{q,R} = S r_q *exactly*. This is the crucial guard and it is not violated
anywhere in C3.2–C3.6 or in C4.1.
*Minor documentation gap:* C_c^inf needs f in C^inf, but the inherited-facts list gives only the j=0,1
envelope (RAD-ENV) and f>0. Phi is real-analytic, so this is bookkeeping, not a hole.

**(b) Fatou step.** Correct. Integrand W|S s_{q,R}|^2 >= 0 (W >= 0). For every fixed x, once
R > max_l |x+tau_l| all k sample points lie in [-R,R] where chi_R = 1, so S s_{q,R}(x) = S r_q(x) —
pointwise convergence *everywhere*, stronger than Fatou needs. Combined with
0 <= A_S(s_{q,R}) <= D(s_{q,R}) <= |D(s_{q,R})| -> 0 this gives int W|S r_q|^2 = 0. No domination is
claimed and none is needed.

**(c) Countability / null-set bookkeeping.** Correct and load-bearing. Each q gives its own null set N_q;
Q is countable so N = union N_q is null; only outside N do all rational q hold *simultaneously at the same
x*, which is what C3.3 requires. C3.3 then upgrades Q to R by continuity of q -> sum d_l f(p_l - q).

**(d) Vandermonde step.** Correct, and the Fourier convention is consistent. With ghat(z)=int g e^{-izx}dx
and F(q)=sum d_l f(p_l-q), substituting u = p_l - q gives F-hat(xi) = f-hat(-xi)·sum d_l e^{-i xi p_l} —
exactly the displayed formula (I re-derived it; the reflection sign is right). f in L^1 => f-hat continuous;
f-hat(0)=int f > 0 => f-hat nonzero on some (-delta,delta) => the exponential polynomial P vanishes on an
interval. P is entire, so P^{(j)}(0)=0 for j=0..k-1 gives sum d_l p_l^j = 0, and the Vandermonde
prod_{i<j}(p_j-p_i) != 0 (distinct p_l) forces d = 0.
*Numeric:* int f = Xi(0)/A = **0.8791346724 > 0**, so the hypothesis is not vacuous.

**(e) Hidden positivity of Q or reality of zeta zeros — NONE FOUND.** Swept every step.
C3.1 uses only B(f,·)=0, which holds because f-hat = Xi/A vanishes at *every* zero regardless of location;
C3.2 uses only the envelope and the control bound (X); C3.3 uses only int f > 0; C3.4 uses W >= 0, which is
a hypothesis on the *proposed certificate*, not on Q — and D(s_{q,R}) >= 0 is *derived* from that
hypothesis, not assumed. C3.5's witness bound uses a(t)>0, the value of c_A, and A_pm(g)>0 for g >= 0 — no
zero locations. The verdict's own disclaimers ("Neither head assumes global Q>=0", "Neither claims
D(s_{q,R})<0") are accurate.

**(f) C3.5 nonzeroness chain — every inequality checked.**
- `a(t) >= e^{-1/2}/(2t)` on (0,1]: true, since 1-e^{-2t} <= 2t and e^{-t/2} >= e^{-1/2}. Numeric minimum
  of a(t)·2t·e^{1/2} over (0,1] = **1.6495 >= 1** (attained as t->0).
- Disjoint supports for t >= l: ||Delta_t g||^2 = ||g(.+t)||^2 + ||g||^2 = **2** with ||g||_2 = 1. Correct.
- Prime correlations: C_g(log n)=0 for all n >= 2 as soon as l <= log 2 = 0.693; the verdict imposes the
  stricter l <= (1/2)log2 = 0.3466 — conservative, not an error.
- Pole term: g >= 0 => A_pm(g) > 0 => 2Re(A_+ conj(A_-)) = 2 A_+ A_- >= 0, and it enters (Q) with a **+**
  sign, so dropping it is a valid weakening. Sign is right.
- Constants: c_A = gamma + log(8 pi) + pi/2 = **5.37218341923**. Threshold l = exp[-e^{1/2}(c_A+1)] =
  **2.7372975e-5**; at that l, e^{-1/2} log(1/l) = **6.372183419 = c_A + 1 exactly**, so Q(g) >= 1 is tight
  by construction, not rounded. The *true* lower bound int_l^inf 2a(t)dt - c_A = **8.09**, a factor-8 margin
  over the claimed 1.
- Independent numeric of the mechanism (normalized Gaussian bumps, grid 2e-6):
  Q(g) = 0.7422 (w=0.05), 1.5267 (w=0.02), 2.1760 (w=0.01) — positive and growing at rate
  0.89·log(1/l) against the verdict's lower rate e^{-1/2}=0.6065 and the true asymptotic rate 1.
  Mechanism confirmed.

**(g) C3.6 product-measure extension and the (1,-2,1) remark.**
The extension is sound: Fatou on (J,mu) x R needs only pointwise convergence at each fixed (j,x), which
holds because each S_j has finitely many finite shifts; partitioning J by stencil cardinality handles
unbounded k; the countable-Q argument then applies a.e. on the product. Restriction to bounded x and
bounded shifts is genuinely needed for CERTIFICATE-KILL (R must dominate all sampled points on E) and is
correctly flagged.
*Wording caveat:* here the coefficients depend on j, so the sharp conclusion is "for a.e. (j,x): W(j,x)=0
**or** S_j is trivial", not "W = 0 a.e."; the verdict's phrase "every active stencil trivial" is correct,
but the C3.4 slogan must not be transported verbatim.
Finite-matrix remark verified numerically: M = v v^T with v=(1,-2,1) has M·1 = (0,0,0), eigenvalues
{0,0,6} (PSD), and M_13 = **+1 > 0**; every nonnegative combination of two-point edge squares
(e_i-e_j)(e_i-e_j)^T has all off-diagonal entries <= 0, so M lies outside that cone. Both directions of
"PSD with zero row sums <=> sum lambda_i u_i u_i^T, u_i perp 1" are correctly proved (spectral theorem
forward, expansion backward). The verdict's warning that this finite fact must not be transported to the
continuum is exactly the point the request got wrong.

## Positive control
F(x)=e^{-(x-1)^2}+e^{-(x+1)^2}, omega=pi/2, Q_*(g)=|g-hat(omega)|^2. With g-hat(z)=int g e^{-izx}dx:
F-hat(z) = (e^{-iz}+e^{+iz})·gauss-hat(z) = 2 cos(z) · sqrt(pi) e^{-z^2/4}. Verified by quadrature:
F-hat(pi/2) = **-1.80e-26** (numerical zero) vs formula -1.799e-26; F-hat(1) = 1.491654122 vs 1.491654122;
F-hat(0) = 3.544907702 = 2 sqrt(pi). So F-hat(omega)=0 and every translate of F sits in the radical of Q_*.
Q_* is manifestly >= 0 and nonzero (g = e^{i omega x} phi gives Q_*(g) = (int phi)^2 > 0), F is positive,
continuous and integrable, and Gaussian tails give the same cutoff budget — so C3.4 applies verbatim to
Q_*(F·s).
**Conclusion: the control is valid and decisive.** It shows the C3 mechanism kills a *certificate class*
and is fully compatible with the form being nonnegative; C3 therefore contains no disguised disproof of
Weil positivity / RH. This is the correct falsifier for the theorem, and it passes.

## Constants I re-derived exactly (C3.2)
- ||e^{|x|} e_R||^2 <= A_0^2/(2 a_q) · e^{-2 a_q e^{2R}} — exact (substitute u = e^{2x}).
- ||e_R'||^2 <= (A_1^2 + c_chi^2 A_0^2)/a_q · e^{-2 a_q e^{2R}} — exact, via (a+b)^2 <= 2a^2+2b^2 and
  e^{2x} >= 1.
- D(u) <= (2/3)||u'||^2 + (32/3)||u||^2: needs a(t) <= 4/(3t) on (0,1] (numeric max of t·a(t) =
  **0.70146** <= 4/3) and a(t) <= (4/3)e^{-t/2} for t >= 1 (numeric max of a(t)e^{t/2} on [1,inf) =
  **1.15652** <= 4/3). Resulting coefficients: (4/3)·(1/2) = 2/3 OK, and (16/3)·2 e^{-1/2} =
  **6.4697 <= 32/3 = 10.667** OK (the verdict is conservative here, dropping e^{-1/2}).
- Hence C_q^2 = [(35/3)A_0^2 + (4/3)(A_1^2 + c_chi^2 A_0^2)]/(2 a_q): the 35/3 = 1 + 32/3 combines the
  X-weight term with the D-bound term — **matches exactly**.
- a_q = a_* e^{-2|q|} is valid for *all* x (|x-q| >= |x|-|q| always), so no R > |q| restriction is needed.
- CERTIFICATE-KILL's sufficient condition e^{2R} > (2 a_q)^{-1} log(1 + 2 C_X C_q^2/eta) is correct (the
  "1+" makes it stronger than the exact requirement log(2 C_X C_q^2/eta)).

## Independent numerical verification of the *inherited* inputs (different channel)
All of C3 rests on two facts the verdict imports rather than proves: B(f,·)=0 on X, and the control bound
(X). I tested the first directly from the source definitions (FFT autocorrelation, trapezoid, Lambda(n) up
to 3000, tail of a(t) to t=80):
- f-hat = Xi: int Phi e^{-izx} dx vs Xi(z)=xi(1/2+iz) agree to 10 digits at z = 0, 1, 3, 10
  (0.4971207782, 0.4857574297, 0.4031652073, 0.03796785031). Phi is even.
  A = ||Phi||_2 = 0.565466013092, ||f||_2 = 1.000000000000.
- Q(f) = D(f) - c_A + 2 A_+ A_- - 2 sum w_n C_f(log n), with D(f)=3.8837, c_A=5.3722, 2A_+A_-=1.5637,
  2 sum=0.0752: **Q(f) = 1.8e-10** at dx=2e-5 (3.6e-6 at dx=1e-4 — pure discretization, scaling with grid).
  The radical fact is thus confirmed to ~1e-10.
- **TRANS-RAD confirmed numerically**: Q(U_q f) = Q(f) to all printed digits for q in {0.5, -1, 2}, and
  with a test vector v of scale Q(v)=2.17598, B(U_q f, v) = 9.9e-11, 2.9e-11, -4.1e-11 respectively
  (relative ~1e-10). This is an independent channel for C3.1, not a re-reading of the verdict.
- (RAD-ENV) envelope spot-checked: A_0 = 23.91 from the stated p_0 recursion; f(0)=1.580 <= 4.970,
  f(1)=4.87e-7 <= 2.18e-4, f(1.5)=2.29e-23 <= 4.75e-13. Envelope holds with room.

## Residual trust boundary (the only real caveat)
Not audited here, because not derivable from the quoted paragraph: (i) the *proof* of B(f,v)=0 for **all**
v in X (I verified it numerically at specific v, and structurally via f-hat = Xi, but the domain lemma of
[X] is inherited); (ii) the constant C_X = |c_A|+14 in (X); (iii) strict positivity of f on all of R. If
(i) held only on a subspace not containing e_R, C3.2 would collapse; nothing in my checks suggests that.

## Bottom line
C3.1–C3.6 **SURVIVE** as paper mathematics. The kill is genuine and its scope is correctly stated: it
removes exact *and* minorant finite-stencil (also mu-integrated finite-stencil) certificates for D, and it
does so without any positivity or zero-location input. It does not touch Weil positivity itself — the
Gaussian-pair control proves that separation constructively. Two cosmetic items only: f in C^inf should be
listed among the inherited facts, and the C3.6 conclusion should be phrased as "W = 0 or the stencil is
trivial, a.e. in (j,x)".

---

# Frozen pre-reading derivations (written before the C3 proofs were read)

# Independent derivations from the "Objects" section ONLY (written before reading C3)

## (1) TRANS-RAD
Term-by-term translation invariance of (Q):
H(U_q g)=||g||^2; D(U_q g)=D(g) since ||U_q g(.+t)-U_q g||=||g(.+t)-g||;
C_{U_q g}(t)=C_g(t); A_pm(U_q g)=e^{\pm q/2}A_pm(g) hence
A_+(U_qg) conj(A_-(U_qg)) = e^{q/2}e^{-q/2} A_+ conj(A_-) = invariant.
So Q(U_q g)=Q(g) for all g; by (complex) polarization B(U_q g,U_q v)=B(g,v).
X is U_q-invariant: ||e^{|x|}g(x-q)||_2 <= e^{|q|}||e^{|x|}g||_2 and D invariant,
so ||U_q g||_X <= e^{|q|}||g||_X (bounded translation action).
Therefore B(U_q f, v) = B(U_q f, U_q U_{-q} v) = B(f, U_{-q}v) = 0 by (RAD-ENV) B(f,.)=0.
=> every translate U_q f is a radical vector. QED

## (2) compact-cutoff budget
chi_R smooth, =1 on [-R,R], supp in [-R-1,R+1], |chi_R'|<=c. f>0 smooth => r_q=U_q f/f smooth,
s_{q,R}=chi_R r_q is C_c^infty, and f*s_{q,R}=chi_R * U_q f.
Write g=U_q f - e_R with e_R=(1-chi_R)U_q f.
B bilinear + TRANS-RAD kills B(U_qf,.) and B(.,U_qf):
  Q(f s_{q,R}) = B(e_R,e_R), so |Q(f s_{q,R})| <= C_X ||e_R||_X^2.   (*)
Envelope: for |x|>=R>|q|, |x-q|>=|x|-|q| so |f(x-q)| <= A_0 exp(-a_q e^{2|x|}), a_q=(pi/2)e^{-2|q|}.
||e^{|x|}e_R||_2^2 <= A_0^2 * 2 * int_R^inf e^{2x} e^{-2 a_q e^{2x}} dx = (A_0^2/(2a_q)) e^{-2 a_q e^{2R}}.
D(e_R) <= C(||e_R||_2^2 + ||e_R'||_2^2) using ||v(.+t)-v||<=min(t||v'||,2||v||) and
int_0^1 a(t) t^2 dt < inf, int_1^inf 4a(t) dt < inf; e_R' = -chi_R' U_qf + (1-chi_R)U_qf',
so same double-exponential factor with A_0,A_1,c.
=> |Q(f s_{q,R})| <= K(q,A_0,A_1,c,C_X) * exp(-2 a_q e^{2R}) -> 0 as R->infty.  (NULL-BUDGET)
The noncompact r_q is NEVER fed to the inequality; only s_{q,R} in C_c^infty is.

## (3) INDEP
Claim: f continuous, integrable, int f>0, y_1<...<y_k distinct, d_j not all 0.
If sum_j d_j f(y_j - q)=0 for all q in Q, then by continuity in q it holds for all real q.
Set tf(u)=f(-u); the function is sum_j d_j tf(q-y_j), whose Fourier transform is
hat{tf}(z) * P(z), P(z)=sum_j d_j e^{-i z y_j}.  hat{tf}(0)=int f>0 and hat{tf} continuous
(f in L^1) => hat{tf} != 0 on some (-delta,delta) => P == 0 on (-delta,delta).
P entire; d^m/dz^m at 0: sum_j d_j (-i y_j)^m = 0 for all m=0..k-1.
Vandermonde in the distinct y_j is invertible => all d_j=0. Contradiction. QED

## (4) NO-MINORANT
Hypothesis: W>=0 measurable, S s(x)=sum_j c_j s(x+tau_j), tau_j distinct, c_j real nonzero,
and int W|Ss|^2 <= D(s) for every compact smooth s.
Fix q in Q. Put s=s_{q,R}. Integrand W|S s_{q,R}|^2 >= 0. For every fixed x, once R>max|x+tau_j|
all k sample points lie in [-R,R], so S s_{q,R}(x) = S r_q(x): pointwise convergence everywhere.
Fatou: int W |S r_q|^2 <= liminf_R int W|S s_{q,R}|^2 <= liminf_R D(s_{q,R}) = 0 by (2).
So W |S r_q|^2 = 0 a.e.: there is a null set N_q with S r_q(x)=0 for a.e. x in {W>0}.
N = union over q in Q of N_q is null (countability is exactly why q ranges over Q).
Take x in {W>0} \ N. Then for all rational q:
   0 = S r_q(x) = sum_j c_j f(x+tau_j-q)/f(x+tau_j) = sum_j d_j f(y_j - q),
with y_j=x+tau_j distinct and d_j=c_j/f(y_j) != 0 (f>0).  By (3) this is impossible.
Hence {W>0} \ N is empty up to null sets => |{W>0}|=0 => W=0 a.e. QED

## Consequences I expect C3.5 to need
If D(s)=sum_m int W_m|S_m s|^2 with W_m>=0 and finite stencils, then each summand is itself
a minorant of D (all others nonneg) => every W_m=0 a.e. => D==0.  So a single witness with
D(s)!=0 kills the class. Witness: g=f s nonnegative smooth bump, ||g||_2=1, support length l.
 - a(t)=e^{-t/2}/(1-e^{-2t}) >= e^{-1/2}/(2t) on (0,1]: since 1-e^{-2t}<=2t and e^{-t/2}>=e^{-1/2}.
 - t>=l => supports of g and g(.+t) disjoint => ||g(.+t)-g||^2 = 2.
   D(g) >= int_l^1 a(t)*2 dt >= e^{-1/2} log(1/l).
 - -c_A H(g) = -c_A, c_A = gamma+log(8pi)+pi/2.
 - 2Re(A_+ conj(A_-)) >= 0 for g>=0 real (both integrals positive) -- helps, sign is favorable.
 - C_g(log n)=0 for all n>=2 as soon as l <= log 2.
 => Q(g) >= e^{-1/2} log(1/l) - c_A, which exceeds 1 once l <= exp(-(c_A+1)e^{1/2}).
