# Signed cofactor/dual Mellin identity

Own attempt after f092b424, using the nonprincipal squarefree H>1 fibre of FREE_COFACTOR_COMPLETION_ATTEMPT.md. No full estimate. Independent mobius_source_audit bounded PASS for (1)–(2), convergence, all fixed phases and exponent 1-s; not an analytic gain.

Let Q=q_H, psi=conjugate(chi_H), ell a fixed S-supported period resolving eta, primary normalization and reciprocity/unit factors. Let phi be that fixed periodic factor so chi_H^*(k)=phi(k)psi(k) on primary good k. In lattice sums phi includes the primary indicator. For f|rad(m), define
A_f(j)=sum_x mod ell phi(f H x)e(jx/ell),
W(t)=F(t)/t,
I(L)=sum_(k,m)=1 chi_H^*(k)/q_k F(q_k/L).
The Q3 CRT normalization yields exactly

I(L)=psi(ell)tau_H(psi)/(q_ell Q)
  *sum_f|rad(m) mu(f)psi(f)/q_f
  *sum_j in O conjugate(psi(j)) A_f(j)
           Wtilde(L q_j/(q_f q_ell Q)).                        (1)

Zero frequency vanishes because H>1 and psi is primitive. All nonzero elements including units are retained. The fixed-period sum A_f is independent of the short divisor e. Neither (k,e)=1 nor (f,e)=1 is imposed.

Define D_f(s)=sum_j!=0 conjugate(psi(j))A_f(j)q_j^(-s) and
M_T(w;chi_H^*,m)=sum_qe<=T,(e,m)=1 mu(e)chi_H^*(e)q_e^(-w).
Let What(s)=integral_0^infty Wtilde(t)t^(s-1)dt. On any fixed line Re s=c>1, absolute convergence and Mellin inversion give

B_H,m(N)= -psi(ell)tau_H(psi)/(q_ell Q)
 *sum_f|rad(m) mu(f)psi(f)/q_f
 *(1/(2pi i)) integral_(c) What(s)(N/(q_f q_ell Q))^(-s)
                      D_f(s) M_T(1-s;chi_H^*,m) ds.            (2)

The exponent 1-s is forced by q_e^-1 times q_e^s from the dual scale. Wtilde is smooth at zero and rapidly decreasing at infinity; its Mellin transform is defined for Re s>0 and rapidly decreasing vertically on fixed positive lines. D_f converges absolutely for Re s>1; M_T is a finite Dirichlet polynomial. This proves (2) on its stated line, with no contour movement.

The tempting replacement M_T(1-s) by a reciprocal Hecke L-function is NOT justified: even the infinite Mobius Dirichlet series is absolutely convergent only for Re(1-s)>1, i.e. Re s<0, disjoint from the above absolute-convergence line. Moreover T is finite and tied to Z. Analytic continuation of the infinite series would not bound or eliminate its truncated tail. If used later, it must carry an independently proved tail estimate, contour justification and all residues.

Negative control: T=1 gives M_T(w)=1 for every w, whereas a nontrivial reciprocal Euler product is not identically1. Thus no exact replacement exists even before considering asymptotics. Equation (2) preserves the signed structure but by itself produces no cancellation estimate. Principal moving conductors and repeated-prime H remain in the full Q3 formula; the nonprincipal restriction here does not erase those sectors.

Decision target: prove a joint bound for the actual D_f(s)M_T(1-s) with the outside H,d,v sums retained, or supply an exact transformation whose residue and remainder satisfy the full consumer. A name such as Voronoi/Rankin–Selberg is insufficient. The cubic-bias source is only a partial coefficient-pair analogue; its lower operator norm is not a substitute for this upper bound.
