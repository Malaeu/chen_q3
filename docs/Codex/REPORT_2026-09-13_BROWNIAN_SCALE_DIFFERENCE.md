# Brownian scale differences: the natural normalized repair has the wrong correlation decay

STATUS: ACCEPTED_LIMITED_PAPER_FIXED_STEP_DIFFERENCE_OBSTRUCTION.
Scope: two explicit fixed-step difference maps; no general Brownian exclusion.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN. PX_RH_CLAIM: NOT_MADE.
No Lean or canonical admission. No new Proshka task is dispatched.

The owner requested mathematics before further execution or checks. The
following proof was derived first, from the existing complete-source identities.
It tests the scale-difference suggestion already present in the Brownian
response; that suggestion is not a newly discovered idea.

## 1. Exact inputs and the two maps

All dependencies are pinned to source base
5871760c6114dff9ecbea5d4d1a59a9da3bff751:

- `docs/Codex/REPORT_2026-09-13_BROWNIANHODGE_INTAKE.md`, exact object,
  full conditional density, and the target same-end correlation limit.
- `docs/Codex/REPORT_2026-09-13_BROWNIAN_PRIMITIVE_FORM.md`, B3--B4:
  the positive form H and its projection P.
- `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_BROWNIANHODGE_2026-09-13.md`,
  section 12: the unexecuted logarithmic scale-difference suggestion.

Keep alpha=1/4, p=alpha+2=9/4. Let nu be the law of
U=sum_(n>=1) E_n/(pi n^2), with independent unit exponentials. Let U' be an
independent copy and C=E(U+U')^alpha. Let eta_t be the conditional law of
U given U+U'=t. For t=exp(2x), its density relative to nu is k_x.

On the existing domain D_alpha=L2((1+u^alpha)nu), put

    Q(F,G)=int (u+v)^alpha conjugate(F(u))G(v) nu(du)nu(dv),
    P F=F-[Q(1,F)/C]1,
    H(F,G)=Q(F,1)Q(1,G)/C-Q(F,G)=-Q(PF,PG) >= 0.

Every fixed k_x is in D_alpha. Write

    beta(t)=int E(u+U')^alpha eta_t(du)>0,
    D(t,s)=int (u+v)^alpha eta_t(du)eta_s(dv),
    J_x=P k_x.

The accepted exact identity is

    H(J_x,J_y)=beta(t)beta(s)/C-D(t,s).                    (1)

For one fixed h>0, consider separately

    L_x=J_(x+h)-J_x,                                      (2)
    q_x=J_x/beta(exp(2x)),
    M_x=q_(x+h)-q_x.                                      (3)

Both maps are defined before calculation, lie in D_alpha, and are
Q-orthogonal to 1. Formula (2) is an ordinary scale difference. Formula (3)
first normalizes the coefficient of the common rank-one contribution,
then takes its difference. No derivative or exchange of derivative and
limit is used. Adding constants to any representative changes neither H
nor these conclusions.

The actual kernel is

    V(x,y)=int_0^infinity (x+y+2t) f(x+t)f(y+t) dt,
    f=Phi/||Phi||_2.

Its previously proved full-source correlation limit, for each fixed d, is

    V(r,r+d)/sqrt(V(r,r)V(r+d,r+d)) -> sech(d), r->infinity. (4)

We prove that neither (2) nor (3) realizes V, even with arbitrary positive
scalar weights depending on x. It suffices to fail this one source end.

## 2. Scaling the complete conditional law

The accepted full density, not a truncation, has the form

    h_nu(u)=2pi exp(-pi u) chi(u),
    B(t)=int_0^t chi(u)chi(t-u) du,
    0<=chi<=1, chi(u)->1, B(t)/t->1.

Consequently the law of U/t under eta_t has density

    chi(tv)chi(t(1-v))/(B(t)/t),  0<v<1.                   (5)

Dominated convergence proves convergence in L1 to the uniform density on
(0,1). The domination holds for all sufficiently large t since B(t)/t->1.
Also E(U')^alpha<infinity: E U'=pi/6 and 0<alpha<1 suffice.

The inequality, for a,b>=0,

    0 <= (a+b)^alpha-a^alpha <= b^alpha

and (5) imply

    beta(t)/t^alpha -> int_0^1 v^alpha dv=1/(alpha+1).      (6)

For fixed a,b>0, independent copies of (5), and bounded continuous
(v,w)->(av+bw)^alpha on [0,1]^2 give

    D(Ta,Tb)/T^alpha -> I(a,b)
      =int_0^1 int_0^1 (av+bw)^alpha dv dw
      =[(a+b)^p-a^p-b^p]/[(alpha+1)p ab].                 (7)

There is no missing infinite-source tail: (5) is the exact conditional
law, while the sole unbounded U' term in (6) is controlled by its alpha
moment. Only fixed a,b are needed in (7).

## 3. Ordinary differences leave the original defect

For x=r+u and y=r+v, with h,u,v fixed, (6) gives

    beta(exp(2(x+h)))-beta(exp(2x))
      ~ exp(2alpha(r+u)) (exp(2alpha h)-1)/(alpha+1).

Applying (1) to (2), its rank-one contribution is of order exp(4alpha r)
with positive nonzero coefficient. The four D terms are O(exp(2alpha r))
by (7). Thus

    H(L_r,L_(r+d))/sqrt(H(L_r,L_r)H(L_(r+d),L_(r+d))) -> 1 (8)

for every fixed d. The denominator is positive for all sufficiently large r.
This differs from (4) for every d!=0. Ordinary differences therefore do
not remove the common rank-one dominance; changing a scalar normalization
after forming L_x cannot alter its normalized correlations.

## 4. Normalized differences remove the rank-one term exactly

Set R(x,y)=D(exp(2x),exp(2y))/(beta(exp(2x))beta(exp(2y))). From (1),

    H(q_x,q_y)=1/C-R(x,y).                                (9)

In H(M_x,M_y), the constant 1/C cancels exactly. Put

    F(d)=(2cosh d)^p-2cosh(pd),
    K=(alpha+1)/p=5/9.

Equations (6)--(7), with a=exp(2u), b=exp(2v), give

    exp(2alpha r) R(r+u,r+v)
      -> K exp(-alpha(u+v)) F(u-v).                      (10)

Taking the four fixed shifts in (9), define

    A_h(d)=F(d+h)+F(d-h)-2cosh(alpha h)F(d).

Then

    exp(2alpha r) H(M_(r+u),M_(r+v))
      -> K exp(-alpha(u+v+h)) A_h(u-v).                  (11)

All finite matrices on the left are positive semidefinite because H is.
Their finite entrywise limits are positive semidefinite. Removing the
positive diagonal factors in (11) shows that A_h(u-v) is a positive
semidefinite kernel. This uses positivity of the independently proved H,
not the unknown positivity of V.

## 5. Exact asymptotic mismatch

For d->+infinity, the convergent expansion in exp(-2d) gives

    F(d)=p exp(alpha d)
      +p(p-1)/2 exp(-(2-alpha)d)
      +O(exp(-(2+alpha)d)),                              (12)

at alpha=1/4. Indeed expand exp(pd)(1+exp(-2d))^p and subtract
exp(pd)+exp(-pd); the omitted binomial remainder is
O(exp(-(4-alpha)d)), smaller than the displayed remainder.

The difference defining A_h annihilates exp(alpha d) exactly. For fixed h>0,

    A_h(d)=c_h exp(-7d/4)+O(exp(-9d/4)),
    c_h=p(p-1)[cosh(7h/4)-cosh(h/4)]>0.                  (13)

In particular A_h(d)>0 for some sufficiently large d. Its two-node PSD
matrix then gives A_h(0)>=|A_h(d)|>0. This establishes strict positivity of
the limiting diagonal without numerical evaluation or an unstated
nondegeneracy hypothesis.

It now follows from (11) that the normalized correlation of M has the limit

    rho_M(r,r+d) -> A_h(d)/A_h(0).                       (14)

This limiting function has decay

    A_h(d)/A_h(0) ~ [c_h/A_h(0)] exp(-7d/4),

whereas the required function sech(d) is asymptotic to 2 exp(-d). Hence
the two limiting functions are different; their ratio tends to zero as
d->+infinity. Equations (4) and (14) cannot hold for identical kernels.

The order of limits matters and is fixed: first r->infinity for each
fixed h,d, producing two functions of d; only then compare those
functions as d->infinity. No uniform-in-d claim or interchange is used.
In particular some fixed sufficiently large d already distinguishes them.

## 6. Consequence and exact scope

For each fixed h>0, neither L_x nor M_x gives

    V(x,y)=w(x)w(y)H(N_x,N_y), N=L or M,

on all real nodes, for any positive scalar function w. Normalized
correlations are invariant under such weights. Allowing nonzero complex
node factors cannot repair the magnitude discrepancy either.

The normalized difference really does remove the former rank-one
contribution. That repair is mathematically meaningful, but its resulting
correlation decay is still wrong. Thus eliminating the old defect is not
enough to obtain the required map.

This theorem does not exclude variable-step differences, arbitrary
operators or observables, sums with a separately controlled positive
remainder, or the Brownian approach in general. It makes no claim about
infinitesimal derivatives: h is fixed before every limit. It supplies no
negative V witness, no full source sign, and no IC/ODD2/RH closure.

No numerical evaluation, finite-rank scan, new literature theorem,
automated proof search, or Proshka request is used in this derivation.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The ordinary scale difference retains limiting correlation one; the beta-normalized fixed-step difference has correlation decay exp(-7d/4), whereas the actual kernel requires sech(d).

## 7. Independent read after completion of the mathematical derivation

The sole read-only reviewer `/root/sibling5_check` returned CLEAN on the
complete proof draft SHA256
256e1d97ddae0e351ff221040418abb694d05ccc39c7316f595bae13fea674b9.
The reviewer checked the conditional-law scaling, I(a,b) constant,
four-shift signs, positive leading coefficient, the strict-diagonal
argument from the PSD limit, the ordered limits, and the exact fixed-step
scope. No mathematical corrections were requested. Only the status,
autopsy summary, and this receipt were added afterward; the proof is
unchanged. This read supplies no Lean or canonical admission.
