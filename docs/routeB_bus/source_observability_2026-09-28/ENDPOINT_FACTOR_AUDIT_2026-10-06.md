# Endpoint factor: accepted obstruction and scalar-test preflight

Source: PROSHKA_ENDPOINT_FACTOR_INLINE_2026-10-06.md, question2 in
CAUSAL_DRESSING_AUDIT_2026-10-06.md. Same six-field growth phase;
full complex original carrier, m=N, L=log m. RH/SP remain OPEN.

## One independent check of answer2

causal_algebra_audit checked equations (1)-(21), including endpoint Gram
identity, constant-mode comparison, signed polar subtraction, sine integral,
archimedean bound, all-prime-power correlation and quantifiers. Accepted:

- For B=I-R, B*B=I-u_L tensor u_L, ||u_L||²=1-m^-1.
  F*F=Z*Z-v_L tensor v_L, v_L=Z*u_L. On e0, ||Fe0||²<=4,
  ||Ze0||²>=(m-1)/(2L). This is not an inverse-norm lower bound.
- D_F-D_Z=H-H_plus-2(Y_F-Y_Z), with 0<=Y_F,Y_Z<=LI.
- For unit p_L=sqrt(2/L)sin(2pi x/L), k=2pi/L, d=1/4+k²,
  b_L=<p,(H-H_plus)p>=2/d+8k² sinh(L/2)/(L d²).
  For L>=4pi this is >=32pi² sqrt(m)/L³; D_arch(p)<=72pi²/L².
- Thus D_F<=D_Z+a0 D_arch+C m^eta fails on every late original
  cell for every fixed a0,C>=0 and 0<eta<1/2. Only this transfer is killed.
- J_m=2 sum_(n<=m) Lambda(n)/sqrt(n) [(1-log(n)/L)cos(k log n)
  +sin(k log n)/(kL)]+b_L retains every prime power and its endpoint.
  |<p,D_F p>-J_m|<=L and W(p)=D_arch(p)-cA+2<p,Hp>-J_m.

Clarification: answer2's necessary scalar bound (19) follows from the FULL
carrier target (21), not from the already killed transfer (T).
AUTOPSY: dropped=UNVERIFIED; note=removing I-R from the signed polar comparison loses a cofinal sqrt(m)/log(m)^3 term on an original two-mode vector.

## Root attempt: scalar good cells via the Landau argument

The following root derivation passed one bounded independent check by
growth_symbol_attempt, including the H1 extension, Laplace continuation
and integer rounding. Status: PAPER_OWN rev for this scalar statement only.
It uses the established full Weil zero formula, not RH or zero simplicity.
Let w=rho-1/2 range over all nontrivial zeta zeros with multiplicities r_w.
There are constants gamma0,w0>0 with |Im w|>=gamma0 and |w|>=w0,
and sum r_w |w|^-3<infinity. Real zeros in (0,1) are excluded, and
analyticity on compact sets plus the usual zero count gives these facts.

Center p_L on [-L/2,L/2]. It is real and odd (an overall minus sign
from translation has no effect). Direct integration gives

 M_p(w)=+/-2k sqrt(2/L) sinh(wL/2)/(w²+k²),
 W(p_L)=-16pi²/L³ sum_w r_w (cosh(wL)-1)/(w²+(2pi/L)²)².

At removable denominators interpret by continuity. For the argument below
choose L0>2pi/w0 so no such issue arises. The zero formula extends to
this endpoint-vanishing H1 test: compact mollifications g_epsilon=p_L*rho_epsilon converge in H1, hence
in D_arch (translation bound), and the prime/pole forms converge on a
fixed compact support. M_g=M_p M_rho, with |M_rho(w)|<=exp(epsilon/2)
on the zero strip for a nonnegative unit-mass mollifier. Thus the zero
series is uniformly dominated by sum r_w|w|^-4. The signed source formula
and zero count are recorded in PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md
section 3.1, (K16); no positive Gram interpretation is used.

Put Q(L)=-L³W(p_L). For L>=L0 expand normally

 (w²+(2pi/L)²)^-2
 =sum_(ell>=0) (-1)^ell(ell+1)(2pi)^(2ell)L^(-2ell)w^(-4-2ell).

Initially for Re z>1/2, the Laplace transform of Q is obtained termwise.
For a=2ell>0 the exponential term e^(wL) contributes

 I_a(z-w)=e^(-(z-w)L0)/Gamma(a)
          integral_0^infinity t^(a-1)e^(-t L0)/(z+t-w) dt;
 I_0(z-w)=e^(-(z-w)L0)/(z-w).

The cosh gives half the terms with w and -w; the -1 term uses w=0
inside I_a only (the outer coefficient retains the actual zero w).
On compact subsets of Re z>0, |Im z|<gamma0/2, denominators for
+/-w are bounded below by gamma0/2, and those for the constant term
by Re z. Integral bounds give L0^-a times a compact-dependent constant.
The outer sum is dominated by sum r_w|w|^-4 times the convergent
series (ell+1)(2pi/(L0 w0))^(2ell). Thus this supplies an analytic
continuation of the Laplace transform across EVERY positive real z.

Elementary Landau step: if Q is not eventually nonnegative, arbitrarily
large negative values already suffice. Otherwise discard an initial
interval, so Q>=0. Its Laplace convergence abscissa sigma_c is finite
above (Q=O(e^(L/2))). If sigma_c>0, analyticity in a disk about sigma_c
allows a Taylor expansion about sigma_c+epsilon reaching sigma_c-epsilon.
The Taylor coefficients in the leftward variable are the nonnegative
moments integral L^n e^(-(sigma_c+epsilon)L)Q(L)/n!. Monotone convergence
would then make the Laplace integral finite at sigma_c-epsilon, a
contradiction. Therefore sigma_c<=0 (including the possibility -infinity).
In particular Q(L)>=e^(eta L) eventually is impossible for any eta>0.
So for every eta>0 there are arbitrarily large L with Q(L)<=e^(eta L).

From answer2, J(L)=Q(L)/L³+D_arch(p_L)-cA+2<p_L,Hp_L>.
The last three terms are bounded for L>=L0. Differentiating the absolutely
convergent zero formula gives W'(p_L as a function of L)=O(e^(L/2))
using sum r_w|w|^-3<infinity; its rational L factors are uniformly bounded.
Rounding e^L to the nearest integer changes L by O(e^-L), hence W by
o(1). The other terms remain uniformly bounded. It follows that for
every eta>0, J_m<=C_eta m^eta on arbitrarily large integer m. The original
schedule m_j=preAnchorTailStart(P)+j+2 contains every late integer.

This proves only a ONE-VECTOR upper estimate, unconditionally in RH.
It cannot give a simultaneous cell for all vectors in the increasing
carrier. Taking a supremum destroys the signed Laplace representation;
individual good subsequences cannot be intersected without a new theorem.

Source schedule: G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:366
defines preAnchorTailShift D P k=preAnchorTailStart D P+k; m=index+2.
Decision: the scalar good-cell test is closed but nondiscriminating for RH.
The full-carrier polar estimate, SP, G1/G3 and RH remain OPEN.

## Exact next question (3/10)

Continuation 3/10, SAME six-field negative-bottom-growth phase. Answer2 is processed, with one independent check of (1)-(21): accepted. SP/RH remain OPEN. The attempted D_F <= D_Z+a0 D_arch+C_eta m^eta transfer is KILLED for eta<1/2 on every late original cell. In (19), the necessary scalar estimate follows from full target (21), not the killed transfer T.

We completed your proposed scalar good-cell test unconditionally, so do not spend this turn re-proving it. Here is our checked own attempt:
Center the real odd p_L. With w=rho-1/2, all zeros/multiplicities included,
M_p(w)=+/-2k sqrt(2/L)sinh(wL/2)/(w²+k²), k=2pi/L,
Q(L)=-L³W(p_L)=16pi² sum_w r_w(cosh(wL)-1)/(w²+(2pi/L)²)².
The source signed explicit formula extends to p_L by compact mollification in H1: M_(p*rho)=M_p M_rho, |M_rho|<=e^(epsilon/2) on the zero strip, and sum r_w|w|^-4 converges. No RH.
No real zeta zeros implies min|Im w|=gamma0>0, min|w|=w0>0; zero count gives sum r_w|w|^-3 finite. Choose L0>2pi/w0 and expand the denominator as sum_ell (-1)^ell(ell+1)(2pi)^(2ell)L^(-2ell)w^(-4-2ell).
Laplace of L^-a e^(wL) on [L0,infinity), for a=2ell>0, continues as
e^(-(z-w)L0)/Gamma(a) integral_0^infinity t^(a-1)e^(-tL0)/(z+t-w)dt;
a=0 gives e^(-(z-w)L0)/(z-w).
In Re z>0, |Im z|<gamma0/2, denominators for +/-w are uniformly separated and the constant -1 part only has a possible singularity at zero. The outer series converges normally by (2pi/(L0w0))^(2ell). Thus Laplace Q continues across every positive real z.
If Q is not eventually nonnegative, negative values already supply good cells. Otherwise the elementary Landau positive-real singularity argument forces its Laplace convergence abscissa <=0. Hence for every epsilon>0, arbitrarily large L have Q(L)<=e^(epsilon L).
Q'=O(e^(L/2)), so rounding e^L to nearest integer changes Q by o(1). Original m_j=preAnchorTailStart(P)+j+2 contains every late integer. Since J_m=Q(log m)/(log m)^3+D_arch(p_m)-cA+2h_L, the scalar J_m<=C_eta m^eta on arbitrarily large original cells is PROVED_PAPER without RH.
This closes only the scalar necessary test. Individual good subsequences cannot be intersected for every vector of the growing carrier. Taking the supremum destroys the signed Laplace representation.

Also checked while you worked: with B_m=compression(D_F-D_arch), b_m=lambda_max(B_m), exact K_m=-B_m+E_m and -(cA+2L)I<=E<=(-cA+8+2L)I give |b_m+lambda_min K_m|<=cA+8+2L. The polar target is equivalent at subpolynomial scale to the original SP, not a reduction by itself. Actual ambient ||F_L||>=sqrt((m-4)/log m) from simultaneous finite phase recurrence; this says nothing about carrier restriction or the signed form. Abstract norm/positivity inequalities and stripping I-R are exhausted.

NEXT MATHEMATICAL TASK: advance the FULL source-specific joint inequality
for every eta>0, there are arbitrarily large original m such that
<f,D_F f> <= D_arch(f)+C_eta m^eta||f||² for EVERY f in the same full complex V_m.
Keep F=(I-R)Z, all prime powers, the finite boundary, and all cross terms. We need a quantitative estimate exploiting arithmetic cancellation, not another exact identity equivalent to SP, a scalar necessary condition, an ambient norm bound, or an assumed RH/Mobius square-root estimate.

Attempt a concrete source-preserving mechanism that couples all carrier directions on a common cell (e.g. a genuinely controlled block/Schur decomposition of the joint prime-minus-pole form). Pay any tail and off-diagonal budget in the original norm, including increasing dimension 2m+1 and high modes. Use known unconditional literature only with exact theorem/hypothesis mapping. A partial result is useful only if it controls an explicit nontrivial part with a precise remaining bound and improves the earlier O(sqrt(m)log m) floor. If this unsmoothed polar mechanism is stalled, say exactly where and identify the single weakest new estimate with its own cheapest discriminator; do not turn the already closed scalar test into apparent RH progress. Try to produce mathematics toward the common-cell full-carrier bound. Same phase, no RH claim.

Question3 sent through the authorized same-thread connector at about
2026-10-06 19:51 UTC. Readback initially lagged on completed question2,
but the live browser shows the complete new question3, model Pro,
ChatGPT antwortet, empty composer and Stoppen. No resend; answer3 pending.
Next useful observation: around 20:12 UTC or a completion notification.
