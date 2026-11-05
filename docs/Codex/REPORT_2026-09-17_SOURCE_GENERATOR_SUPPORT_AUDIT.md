# The exact full-source generator returns to the existing SUPPORT condition

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed A1--A6.
SOURCE_BASE: 7dcc9c210791f12dc419a0db3d3957185a6cb191.
Date: 2026-09-17. Original all-row V and RH remain open.

## A1. Reconciled question and exact source

The full conditional transport C10--C13 preserves the original scalar
flux but supplies no sign. The radial-carrier exclusions do not apply
to the full translated source, which retains shift orientation. Here we
construct its natural full-line generator, pay its domain/core issue,
and determine whether its positive-commutator formulation is a new
mechanism or the existing source-phase SUPPORT target.

Use the complete f=Phi/||Phi||_2 and Fourier convention

    F(omega)=int_R f(t) exp(-i omega t)dt,
    I=(-log(2)/2,0), H=L2(R,dt), P+=1_(t>=0), P-=1-P+.

Fourier Plancherel uses measure d omega/(2pi). The source f is real, even,
positive and holomorphic in |Im t|<pi/4, with the already proved full
complex-strip double-exponential tails. Thus F is a nonzero real-even
entire function, F(0)>0, and its real zeros are isolated. Their location
and multiplicity need NOT be known. The accepted normalization is

    F(z)=xi(1/2-i z)/||Phi||_2.

Keep u_x(t)=f(t+x), w_x(t)=(t+x)f(t+x), for all real t. The physical
cutoff remains in P+, and the exact target is

    V[c]=2 Re <P+ u_c,w_c>,
    u_c=sum_i c_i u_(x_i), w_c=sum_i c_i w_(x_i), x_i in I. (A1)

No source term, boundary interval or mixed coefficient is removed.

## A2. A source-defined skew-adjoint generator without RH

On real omega away from the isolated zeros of F set m(omega)=F'/F.
Set m arbitrarily, say zero, at those zeros; this changes no L2 operator.
Since F and F' are real on R, m is real and finite almost everywhere.
Define the maximal Fourier multiplication operator B by

    hat(Bu)(omega)=i m(omega) hat u(omega),
    Dom(B)={u in H: m hat u belongs to L2(d omega/(2pi))}. (A2)

Multiplication by a real measurable finite-a.e. function is self-adjoint
on its maximal domain; this also follows directly by testing its adjoint
on sets where |m| is bounded. Hence B is densely defined, closed and
skew-adjoint. The poles of m at real F zeros are included by the domain,
not removed by a bounded-multiplier assertion.

For each real x, Fourier differentiation gives exactly

    hat u_x=exp(i omega x)F,
    hat w_x=i exp(i omega x)F',
    u_x in Dom(B), Bu_x=w_x.                            (A3)

Thus B is independently specified by the source and realizes the exact
full-line input/output relation. It does not act on the half-line
zero-extended profiles by the same multiplier; P+ is kept OUTSIDE B.
This does not contradict the old half-line common-multiplier exclusion.

Put, for u,v in Dom(B),

    b(u,v)=<P+u,Bv>+<Bu,P+v>,
    b[u]=2 Re <P+u,Bu>.                                (A4)

It is a Hermitian graph-norm-continuous form and A1 becomes b[u_c]=V[c].
If the products were defined on an invariant domain, its formal operator
would be [P+,B]. No assertion P+Dom(B) subset Dom(B), nor a literal
operator commutator on all Dom(B), is used here. The form A4 is the
precise object. Even the Gaussian has a nontrivial cutoff boundary.

## A3. The admissible translates are a graph core, not just L2-dense

This stronger density is needed before asserting positivity on all of
Dom(B). It follows from the full source tails, without RH.

Fix 0<eta<delta<pi/4. Shifting the Fourier contour to
Im t=-delta sign(omega), and likewise the integral for F', gives

    |F(omega)|+|F'(omega)| <= C_delta exp(-delta|omega|). (A5)

For Re t>=0, each full theta mode has exponential modulus bounded by
exp[-pi n^2 exp(2 Re t) cos(2delta)] times its polynomial prefactor;
cos(2delta)>0. Summing all modes gives a uniform double-exponential
bound, and evenness supplies the other end. These bounds make the
horizontal integrals of (1+|t|)|f(t+-i delta)| finite and make both
vertical sides tend to zero. The contour shift is
therefore justified for each real omega with one finite C_delta. No
zero-free region or asymptotic derivative formula is assumed.

Define the finite measure

    dmu(omega)=(|F(omega)|^2+|F'(omega)|^2)d omega/(2pi).

A5 gives int exp(2eta|omega|)dmu<infinity. The map
hat u=F q is an isometry from L2(mu) onto Dom(B) with graph norm
(||u||^2+||Bu||^2)^(1/2). Indeed the squared graph weight is
|F|^2(1+|m|^2)=|F|^2+|F'|^2 almost everywhere; isolated zeros cause no
missing L2 subspace. This also verifies surjectivity by q=hat u/F a.e.

The u_x correspond to q_x(omega)=exp(i omega x). These are complete in
L2(mu) already for x in I. If q is orthogonal to every q_x, the finite
complex measure dnu=conj(q)dmu has an exponential moment by Cauchy--Schwarz.
Its Fourier transform int exp(i omega z)dnu is holomorphic on
|Im z|<eta and zero on I. The scalar identity theorem makes it zero
on all real z; Fourier uniqueness for finite measures gives nu=0, hence
q=0 mu-a.e. Therefore

    span{u_x:x in I} is dense in Dom(B) in graph norm.   (A6)

Since |b(u,v)|<=||u||||Bv||+||Bu||||v||, A6 proves exactly

    V[c]>=0 for all finite complex rows in I
        iff b[u]>=0 for every u in Dom(B).              (A7)

This is a conditional equivalence. Neither side has been established.

## A4. The sign is precisely a one-sided support law for the unitary flow

Define a strongly continuous unitary group directly by its multiplier

    T_tau=Fourier_inverse M_(exp(-i tau m)) Fourier,
    tau in R.                                         (A8)

It preserves Dom(B), commutes with B there, and for u in Dom(B)
(d/dtau)T_tau u=-B T_tau u in H. The derivative follows by dominated
convergence using |(exp(-i tau m)-1)/tau|<=|m|. Therefore

    d/dtau ||P+ T_tau u||^2=-b[T_tau u].                (A9)

If b>=0 on Dom(B), the left norm is nonincreasing for tau>=0. Density
of Dom(B) in H extends the inequality to every u in H. For u in H-=P-H,
its initial P+ norm is zero, so

    T_tau(H-) subset H- for every tau>=0.              (A10)

Conversely suppose A10. For u=p+n with p=P+u,n=P-u,
P+T_tau n=0. Unitarity gives ||P+T_tau u||<=||p||. Apply this to each
u in Dom(B) and take the right derivative at zero in A9. It yields
b[u]>=0. Hence A7 is equivalent to A10. Unitarity alone is insufficient;
the direction of the half-line support is the additional, unpaid property.

## A5. Exact Cayley comparison with the already accepted FULLVPOS operator

The accepted operator from FULLVPOS is

    U=Fourier_inverse M_S Fourier,
    S=(F-iF')/(F+iF').                                 (A11)

On R the denominator has no zero unless F=F'=0. At such common real
zeros the ratio is removable with the convention of that report. Changes
at isolated frequencies do not affect its L2 operator. Equations A2/A11
give the bounded Cayley identity

    U=(1-B)(1+B)^(-1)=2(1+B)^(-1)-1.                   (A12)

The inverse exists on all H since |1+i m|>=1. In particular the original
phase U has not been replaced by a new transfer function.

If A10 holds, then the norm-convergent Bochner integral on each vector

    (1+B)^(-1)u=int_0^infinity exp(-tau)T_tau u d tau

preserves H-. Hence U does too.
For the converse, suppose U(H-) subset H-. For tau>=0 define

    h_tau(w)=exp[-tau(1-w)/(1+w)], |w|<1.

Its modulus is at most one. For 0<r<1, the power series for h_tau(rU)
converges in operator norm, and every nonnegative power of U preserves
H-. Thus h_tau(rU) preserves H-. The boundary multiplier S equals -1
only on an irrelevant null set: away from zeros, (1-i m)/(1+i m)=-1
would give 1=-1. As r increases to one,

    h_tau(rS(omega)) -> exp(-i tau m(omega)) a.e.

The common bound one gives strong L2 convergence to T_tau. Closedness
of H- proves A10. Thus

    A10 iff U(H-) subset H- iff P+ U P-=0.              (A13)

This is EXACTLY the old SUPPORT condition, with the same orientation,
normalization, full source and all-finite quantifier. Through the accepted
SUPPORTSTABILITY intake and SOURCE_SUPPORT_HUNT/W2 analysis it is the same unresolved unweighted
source stability requirement, not a weaker new entrance. No simple-zero
assumption appears in A2--A13.

## A6. Exact controls and the decision

For f_a(t)=exp(-a t^2), a>0, F'/F=-omega/(2a), so B=-(1/(2a))partial_t
and T_tau u(t)=u(t+tau/(2a)), which preserves negative support.
For a finite source row, direct integration yields

    b[u_c]=|u_c(0)|^2/(2a)=V_a[c]>=0.

The positive contribution is the physical boundary; P+ need not preserve
the derivative operator domain. This confirms the orientation and factors.

For the established control f0=exp(-t^2)-exp(-2t^2)/4, the same generator
construction and graph-core proof apply (the Gaussian entire tails supply
A5). Its already accepted negative full-V finite row implies failure of
A10/A13. Thus skew-adjointness, a unitary full-line flow, graph-core
density, scalar source evenness and an exact input/output match cannot
by themselves prove the one-sided support law. No negative row for the
actual theta source is produced here.

Result of the planned return: the conditional identities do not supply
an extra positive energy operator. The natural exact full-source generator
can be constructed, but its positive-commutator sign is precisely the
previously known SUPPORT target after a Cayley transform. Do not dispatch
SUPPORT again under the names unitary propagation, positive commutator,
causal flow, or conserved full-line energy without a new SOURCE-SPECIFIC
hypothesis proving A10. This audit identifies the duplicate mechanism;
it supplies no new lower bound for V and no RH proof or refutation.

The new graph-core/flow comparison is a domain audit, not a new positive
mechanism. The existing source-pinned integrated-sign and source-support
hunt briefs, their primary-source cards and incomplete shelf receipts
were reconciled. No new external search, source download or theorem
premise is used in this audit; no search absence/novelty claim is made.
No canonical admission, numerical source scan or Lean run is claimed.

## Exact source pins

- REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, full strip tails and
  Fourier normalization: 1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
- REPORT_2026-09-15_FULLVPOS_INTAKE.md, exact phase and SUPPORT:
  8f9abe3e60ce3188709ad5b6e91022980a78bc33f70635fcb4f3fe6abb77aad6.
- REPORT_2026-09-15_SOURCE_SUPPORT_HUNT.md, same xi multiplier and W1/W2:
  9b059659b10948bed90d9df482cfe97e9cc229116e1db46b029bba81a22c4966.
- REPORT_2026-09-17_CONDITIONAL_CONNECTION.md, C10--C18:
  2aa3c9dcd948045ee21dbc0f530fa73037968dce40d8c4592bedd48aed1757c9.
- REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md, non-theta negative control:
  51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f.
- REPORT_2026-09-15_SUPPORTSTABILITY_INTAKE.md, accepted W2/SUPPORT
  equivalence: 14f8e48fd325f41df7b46f1da84140e1ff56b16df95ee3c6b9c0000f9ae9e895.

## Independent acceptance

Candidate SHA256: `8fa7f3b681732de1c784127178b0e438cc5bbc1950660a6df3f0514abd622f95`.
Review SHA256: `58870bcfb16b11071d46c1a020a5e8900f6ba92e8ae9a7e0ec153e3cf2f2d345`.
Verdict: `ACCEPT_EXACT_SOURCE_GENERATOR_SUPPORT_EQUIVALENCE_ONLY`.
The parent independently checked the full-line Fourier signs, maximal
operator domain, graph-core proof, projection-energy derivative, both
Cayley support implications and Gaussian boundary factors. Full reviewer
and parent checks are embedded in the paired certificate. This is an
exact equivalence audit of the existing SUPPORT target, not a new
positive mechanism. No numerical test, Lean certification, canonical
admission, source-sign counter reset or proof of original V positivity
is claimed. RH remains open.
