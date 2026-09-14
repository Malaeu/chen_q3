# Brownian intake: the conditional primitive profiles do not preserve V

STATUS: ACCEPTED_LIMITED_PAPER_INTAKE.
Verdict: ACCEPT_NAMED_CONDITIONAL_BROWNIAN_PROFILE_MISMATCH_ONLY.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. ALL_ORDER_SOURCE_SIGN: OPEN.
RH: OPEN. PX_RH_CLAIM: NOT_MADE.
Isolated PAPER evidence; no Lean or canonical admission.

## Immutable delivery and review

The full response was fetched from GitHub commit
1953179544258aa3adb3cc6dcb483419ffe49bc3. It changes only
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_BROWNIANHODGE_2026-09-13.md`:
50817 UTF-8 bytes / 664 LF / final LF / CR 0, SHA256
7649d7600e9ddac8407aa24a93ebf624466d1a3410e44270de70c3476595dfa9,
Git blob cdd03e7da883835122818529b0ebe993ec27b199.
Root read all 664 lines and independently checked the operative proofs.
The sole checker, sibling5_check, returned the verdict above; review SHA256
9da9be863dd83068f37c94e3b7ca646dfbe445994c9d0df073d543319efec6c6.

REQ-2026-09-13-BROWNIANHODGE was sent at 2026-09-13T08:51:20.511Z
in the existing owner-authorized chat. Request commit
3f057975d59adcd9b61a3585c8f293624ba742ae, 9895 bytes / 123 LF, SHA256
f40965ea88f8ae000af0e31b3e26d7310c2abf8a09bea89a07d8ae4990a1b93d.
The completed UI reply was observed on 2026-09-13 near 09:23 UTC:
natural reasoning 24m20s, with exactly the response commit and path.
Assignments and full answers travelled through GitHub; no new request or
duplicate send is part of this receipt.

Root and checker verified all five committed inputs, including the ORIGINAL
206-line Brownian report at 3f057975, SHA256
accbbc050d41c54cf09927571b24106f2a6a6e84a960cf076b8f4dbf900cd809.
The independently accepted parent profile preflight was later appended at
6556d34e863955e68bde80b03323bd95adb2a531 (294-line report, SHA256
00b5e80a573bd3a31c28f21ffa4fcf11695746c7df56274d12c0a94370e225fa).
It was not silently substituted for Proshka's pinned 206-line input.

## Exact object and positive carrier retained

Keep p=Phi/Z, f=Phi/A, Z=integral Phi=xi(1/2), A=||Phi||_2.
Let U=sum_(n>=1) E_n/(pi n^2), with independent unit exponentials,
nu=law(U), and let an independent copy have total T=U+U'. Set alpha=1/4.
The density r of T obeys Phi(x)=exp(5x/2) r(exp(2x)). Tilting the joint
law by T^alpha/C, C=E T^alpha=2Z, gives X=(1/2)log T the density p.

The accepted Brownian carrier on D_alpha=L2((1+u^alpha)nu) is

    Q(F,G)=integral (u+v)^alpha conjugate(F(u)) G(v) nu(du)nu(dv),
    PF=F-[Q(1,F)/C] 1,
    H(F,G)=Q(F,1)Q(1,G)/C-Q(F,G)=-Q(PF,PG).

It has H>=0 with radical the constants. This independently proved positive
carrier remains valid. It has not thereby been identified with original V.

For t=exp(2x), the tested conditional profile is

    k_x(u)=h_nu(t-u)/r(t) for 0<u<t, and zero otherwise,
    J_x=P k_x.

The law eta_t=k_x nu is the conditional law of U given U+U'=t.
The T-dependent tilt leaves it unchanged. Each k_x is in D_alpha;
compact x-families are continuous there and admit the stated Bochner integrals.

Writing beta(t)=integral E(u+U')^alpha eta_t(du) and
D(t,s)=integral (u+v)^alpha eta_t(du)eta_s(dv), with independent marginals,
the complete mixed kernel is exactly

    B(x,y)=H(J_x,J_y)=beta(t)beta(s)/C-D(t,s).                 (1)

The D term is retained throughout; B(x,x)>0.

## Quantitative mismatch, using the complete source

Split W=sum_(n>=2) E_n/(pi n^2). Exact finite telescopes and monotone
convergence give E exp(pi W)=2 and E[W exp(pi W)]/2=3/(4pi)=ell.
With chi(u)=(1/2)E[exp(pi W) 1_(W<u)], the full density is

    h_nu(u)=2pi exp(-pi u) chi(u),
    r(t)=4pi^2 exp(-pi t) Bcal(t),
    Bcal(t)=integral_0^t chi(u)chi(t-u)du,
    0<Bcal(t)<=t,  0<=t-Bcal(t)<=2ell.

The independent first-exponential convolution also gives h_nu<=pi.
No modes were discarded. These identities supply the conditional-law and
tail bounds used in the response's equations (13)--(27).

For either pair (x,y)=(r,r+log 2) or (-r-log 2,-r), for EVERY r>=15,
the normalized correlations obey

    rho_B=B(x,y)/sqrt(B(x,x)B(y,y)) > 19/20,
    0<rho_V=V_f(x,y)/sqrt(V_f(x,x)V_f(y,y)) < 17/20.

At small total energy, beta(t)->E U^alpha>0 and D(t,s)->0.
At large total energy, U/T conditional on T=t tends to Uniform(0,1);
beta(t) grows as (4/5)t^alpha and its product dominates D.
Both ends therefore drive rho_B to 1 at fixed node separation.
For the actual full V integral, the corresponding limit is sech(x-y),
equal to 4/5 at separation log 2. The response proves explicit bounds,
not just these limits, using the full Bcal factor and V(-x,-y)=V(x,y).

In particular rho_V-rho_B < -1/10 already at the explicit r=15 pairs.
This excludes V(x,y)=w(x)w(y)B(x,y) for every positive scalar weight w.
Complex node phases cannot repair the discrepancy in correlation magnitude.
Adding constants before the primitive projection cannot repair it either.

## What the negative residual actually witnesses

The unrestricted exact identity is V=B+R, with

    R(x,y)=V_f(x,y)-beta(t)beta(s)/C+D(t,s).

No positive sign for this unrestricted R is established. If one instead
forces the Brownian term to exhaust each diagonal, its weight is uniquely
w(x)=sqrt(V_f(x,x)/B(x,x)). The resulting residual R_w has zero diagonal.
For either explicit two-node family and c_i=1/sqrt(V_f(x_i,x_i)),

    sum_ij conjugate(c_i) R_w(x_i,x_j) c_j
      =2(rho_V-rho_B)<-1/5,
    sum_ij conjugate(c_i) V_f(x_i,x_j) c_j=2+2rho_V>0.

Thus the negative witness is for the DIAGONAL-MATCHED RESIDUAL. It is not
a negative witness for V or for the original Weil form. It excludes a repair
by an additional positive kernel after that diagonal has been exhausted.
A smaller Brownian term leaving diagonal reserve is not excluded.
Derivatives, other explicit observables, and other Brownian maps remain open.

## Replay, accounting and next research boundary

Root inspected then extracted Appendix A verbatim and replayed it with exact
fractions. Script SHA256
fa429e6316e20c64b4c129ed1cbf9d72ba5fd5f49f8ae2889fa0c1a90a1273d8.
Root and checker stdout both exactly match the producer's printed stdout,
SHA256 dcf2859e6efc8952e2cfef8fa6db8f86e74fd21b515f1c116616a5fae05dec83.
The 14 rational budgets pass; the target rational upper bound is
2484962480000/2988017988003. The N=2,...,30 telescopes are a finite
calibration, with the universal identities proved analytically above.
Source evaluations, quadratures, Hankel scans and Lean runs: zero.
Appendix B's environment-specific script was replaced by independent
git-show byte/blob comparisons; its producer environment was not reproduced.

Historical full-source-sign no-delta count: 4->5 after this accepted intake.
This is the SECOND completed source construction since the owner's resumed
brainstorming authorization (Villain, then Brownian). Carrier and preflight
work are not extra attempts and do not reset that source-sign count.
No owner-wait block follows solely from the historical count.

The next proposed map must retain a nonconstant correlation at separated
nodes on both source ends. The unchanged conditional profiles are excluded;
a differently named copy of the same map is not a new candidate. A successful
end test would still be only necessary: every mixed term, domain and full
V identity would need proof. No next Pro request is delivered by this intake.

## Exact intake review receipt

Corrected 151-line draft SHA256
cbd8cb946cfe41e7a39c981aa5dfa5115a721a8f45206f0eb80b08ff781ba73f
was independently CLEAN after spelling out the constant function in P.
Final review receipt SHA256
a52c64353d5e613f9bf83cd72d569e9f792f8ecebe1fdc6a8b405e9c92c3c07e.
Only the acceptance status and this receipt were then added.
