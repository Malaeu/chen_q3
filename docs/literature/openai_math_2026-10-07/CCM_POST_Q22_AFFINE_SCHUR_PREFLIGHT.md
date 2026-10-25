# After Q22: affine Schur preflight, not a new arithmetic bound

2026-10-25. Base af62cef8. Status: conditional interface calculation;
no source-specific positivity supplied, no CCM/RH status change, no Q23 sent.
Q22 original §4 and §9.1 already proposed this representation. This note
checks its missing hypotheses rather than claiming a new representation.

## Exact full-form decomposition

Work on H=ran(P), with the original sparse P, N=m, L=log(m), and
K=(P K_m P)|H. Let E be the two Mellin evaluations of Q22. On sufficiently
late cells EE* is invertible. Define J=E*(EE*)^-1 and Pi=I_H-JE.
Pi is the orthogonal projection onto ker(E); it is NOT a replacement for P.
For the actual returned vector x use its actual data b=Ex, including its
return error, rather than silently setting b to the limiting data.
Then x=Jb+y, y=Pi x, and exactly

    x*Kx = b*J*KJb + 2 Re(y*d) + y*B y,
    d=Pi K Jb,   B=(Pi K Pi)|ker(E).

Here y*d means conjugate transpose y times d. K is unchanged: all prime
powers, both times, self/cross terms, archimedean and boundary terms remain.
This finite decomposition introduces no return error. An application to the
pre-return pair must still include the Q22 growing-profile return cost.

## What minimization would actually require

For fixed b, the infimum over the WHOLE affine fiber Ex=b is finite exactly
when B is positive semidefinite and d lies in range(B). In that case it is

    b*J*KJb - d*B^dagger d.

Indeed diagonalize Hermitian B. A negative eigenvalue gives a quadratic
ray tending to minus infinity. If B>=0 but d has a nonzero component in
ker(B), its linear mixed term gives such a ray. Otherwise completing the
square on range(B) proves the displayed formula. Positive definiteness is
sufficient but not necessary; the pseudoinverse/range condition cannot be
omitted. This is finite-dimensional algebra, not a property proved for CCM.

The actual source-radical residuals form a restricted subset of this fiber.
Failure to bound the enlarged fiber does NOT disprove a bound on that subset,
nor establish that actual B has a negative eigenvalue.

## Full known budget and the first unpaid line

Q22 supplies only K >= -b_m I_H, b_m=12 sqrt(m)+4+c_A. Thus it supplies
B>=-b_m I, not B>=0. For tau>b_m the shifted block B+tau I is positive;
completing its square gives

    x*Kx >= b*J*(K+tau I)Jb
              - d*(B+tau I)^-1 d - tau ||x||^2.

The coupling d is unchanged because Pi J=0. The last term is mandatory.
The known guarantee costs tau of half-power size. There is no established
bound for the effective b-quadratic term either, so no full improved budget
is claimed. Taking tau=m^eta with eta<1/2 requires a new bound on B and its
coupling; it does not follow from the supplied floor. Restricting attention
to this decomposition therefore has not reduced the arithmetic debt.

## Shelf and exact controls

The registered ask.sh query "CCM Mellin Schur complement kernel coercivity
two point interpolation" returned INCOMPLETE (semantic-index freshness),
not absence. A concrete hit, H2aPenaltyCoercivity.lean:102, explicitly takes
a positive-semidefinite penalty certificate hcert as a hypothesis. It is
not a source-specific provider for this E and P.

An exact SymPy control used A=[[2,i],[-i,3]], C=[1+i,2]^T, b=[1,-1]^T.
For B=2 the complex square identity gives minimum 4. With the same A,C,b,
B=-1 gives the real ray 5-2u-u^2; B=0 gives 5-2u. Both are unbounded below.
These are abstract controls of prerequisites, NOT sampled CCM matrices.
Replay code is /tmp/ccm_schur_preflight_check.py; no dependency installed.

Decision: do not promote a PSD/Schur rewrite into an arithmetic supplier or
send Q23 solely requesting its missing sign. Return to the centered actual
pair before enlargement to all of ker(E); a next attempt needs a concrete
source-dependent relation and must retain d and the full return budget.
This is one interface preflight, not three failed mechanisms or a killed route.

## Follow-up: actual pair relation checked against Q19 (duplicate, not a new attempt)

Q17 §1.6 and Q19 §2 give, for Fourier convention M_f(it)=integral exp(itx)f(x),
with s=t-gamma, eta=c_w/conjugate(c_w), and v=-conjugate(w),

    M_k(it)=U(s) M_g(it),
    U(s)=eta [(delta-is)/(delta+is)]^r,  |U(s)|=1.

The separately normalized c_v=(-1)^r conjugate(c_w) is essential. Thus for
the full real-line finite-prime operator with multiplier
D_m(it)=sum_(n<=m) Lambda(n)/sqrt(n) [n^(it)+n^(-it)], both self prime
forms are equal, not merely bounded independently. For the actual pair,

    |M_fa(it)|^2 = 2[1-Re(exp(-2isa)U(s))] |M_g(it)|^2.

This retains the mixed phase. It is exactly Q19's
M_C(i gamma+is)=kappa A(i(gamma+s))^2/(delta+is)^(2r), expressed as a
unit-modulus multiplier times |M_g|^2. It is NOT a new source relation.
The multiplier commutes with the real-line convolution operator; it is NOT
asserted to commute with the finite cutoff or original P. Return of the
whole actual pair uses inherited Q17 rho_K=o(1) and its full mixed/tail costs.

Unit modulus alone gives |J(a;m)|<=2 W_m ||g||^2<=12 sqrt(m)||g||^2.
This bound preserves both signs of time and all prime powers, but its full
returned budget is O_w(sqrt(m))+O_w(log m)+o(1), worse than the retained
O_w(sqrt(m)/log^2(m)+log m) estimate. It supplies no new exponent. Equality
of self terms is not a bound on the real mixed term because D_m is signed.
Ten exact rational checks (r=1..5) confirmed the normalization and modulus;
the displayed algebra proves the relation for every positive integer r.
No hypothetical zero was assigned a numerical value, and no actual CCM
matrix was numerically evaluated. Do not count this duplicate as a second
substantive failed mechanism or as a reason for an automatic Q23.
