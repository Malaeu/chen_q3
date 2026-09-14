# Source curvature, moment inequalities, and the first unpaid Hankel minor

Status: ACCEPTED_PAPER_SOURCE_MOMENT_INTERFACE_ONLY.
Parent mathematical task, 2026-09-12. No Lean or canonical admission.
This is an analytic consequence of the already accepted full theta-source
curvature. It supplies no new numerical certificate and does not assert
all-order Hankel positivity, global ODD2, global IC, or RH.

## 1. Source lock and exact consumer

Use the unchanged positive, even spatial theta source Phi. Set

    Z=integral_R Phi(x)dx,  p(x)=Phi(x)/Z,
    U=X^2 for X with density p,  mu_k=E[U^k],  mu_0=1.

All mu_k are finite and positive. The law of U has positive density
Phi(sqrt(u))/(Z sqrt(u)) for u>0, hence is not supported at one point.
Here Z is the L1 normalization; it is not the earlier A=||Phi||_2.
Constant normalization disappears from every logarithmic derivative below.

Accepted source dependencies, verified against their full file bytes:

- docs/Codex/REPORT_2026-09-12_ODD2_SMALL_NODE_TAIL5.md, SHA256
  088cfa2fcaa28a3d7d17e7e4da7f59722561907f5e177d2dc47b08bff4557766:
  h(u)=log Phi(sqrt(u)) extends analytically at0, h'(0)<0,
  and h''(u)<=-1/4 for every u>=0.
- docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, SHA256
  1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282:
  full-source positivity, evenness, smoothness, superexponential decay,
  weighted derivative integrability and the exact xi/Fourier identity.
- docs/Codex/REPORT_2026-09-12_ALL_ODD_TO_RH.md, SHA256
  760fd70fd1e6c3f5b07f8c6eced03bf3f2dfb69698cfb67f597ead219ff8940a:
  RH is equivalent to positivity of every finite coefficient Hankel matrix
  H_n=[a_(i+j+1)]_(0<=i,j<=n), where g=-E'/E=sum a_n w^n and
  E(w)/E(0)=sum (-1)^k mu_k w^k/(2k)! near0 and indeed entire.

The exact consumer of this note is the source-to-coefficient interface in
the third dependency. The all-order sign required there remains unpaid.
We prove an all-index source moment inequality, pay the scalar H_0 entry,
and isolate the exact next 2-by-2 determinant without promoting its sign.

## 2. An exact integration-by-parts identity

Define the real source score b(u)=-2h'(u). Then

    b(u)>0,  b'(u)>=1/2,  p'(x)=-x b(x^2)p(x).             (2.1)

For every integer k>=1, integrate the derivative of x^(2k-1)p(x)
on the whole real line. Polynomially weighted p and p' are integrable,
and x^(2k-1)p(x) tends to0 at both infinities. Thus

    E[b(U)U^k]=(2k-1)mu_(k-1).                             (2.2)

This is a full-source identity: no theta-mode truncation or finite x-cutoff
is taken. Using the whole real line also avoids any unaccounted boundary
term from the square-root density at u=0. The analytic extension of h
ensures (2.1) is valid at x=0 by continuity.

## 3. Quantitative covariance under every size-biased law

For k>=1 introduce the probability measure

    nu_k(du)=u^k law(U)(du)/mu_k.

Write Cov_k and Var_k for covariance and variance under nu_k.
Identity(2.2), used at k and k+1, gives

    E_k[b(U)]=(2k-1)mu_(k-1)/mu_k,
    E_k[U]=mu_(k+1)/mu_k,
    E_k[b(U)U]=2k+1.

Consequently

    Cov_k(b(U),U)
      =2k+1-(2k-1)mu_(k-1)mu_(k+1)/mu_k^2.               (3.1)

Let U,V be independent with law nu_k. The mean-value integral and(2.1)
show for all u,v>=0 that

    (b(u)-b(v))(u-v)>=(u-v)^2/2.

All terms below are integrable by(2.2) and the finite source moments.
In particular positivity of b makes the mixed independent products
integrable; no second moment of b is needed. Expanding the two products,

    Cov_k(b(U),U)
      =(1/2)E_k[(b(U)-b(V))(U-V)]
      >=(1/4)E_k[(U-V)^2]
      =(1/2)Var_k(U).                                     (3.2)

Multiply(3.1)-(3.2) by mu_k^2. For every integer k>=1 this proves

    (2k+1)mu_k^2-(2k-1)mu_(k-1)mu_(k+1)
      >=(mu_k mu_(k+2)-mu_(k+1)^2)/2 >0.                 (M)

Strictness follows because nu_k has positive density on all of(0,infinity),
so Var_k(U)>0. This is one proof for every k, not finitely many evaluated
moment inequalities. The nonnegative margin in(M) is an ordinary moment
Gram determinant, whose sign follows directly from variance.

Equivalently, if q_k=mu_k/(2k-1)!! with q_0=1, then q_k^2>q_(k-1)q_(k+1)
for every k>=1. The stronger quantitative statement is(M).
This normalized moment log concavity does not establish the coefficient
Hankel sign demanded by the RH criterion.

## 4. Exact logarithmic-derivative coefficients

Let E be the entire function from the accepted odd-to-RH reduction and put

    e(w)=E(w)/E(0)=sum_(n>=0)e_n w^n,
    e_n=(-1)^n mu_n/(2n)!, e_0=1,
    g(w)=-e'(w)/e(w)=sum_(n>=0)a_n w^n.

The power series for e follows by differentiating the full Fourier integral
or by its entire even expansion. As e(0)=1, g is analytic on a disk about0.
The identity e g=-e' gives the exact recurrence

    a_n=-(n+1)e_(n+1)-sum_(j=0)^(n-1)a_j e_(n-j).        (4.1)

The sum is empty for n=0. Define

    P4=3mu_1^2-mu_2,
    P6=30mu_1^3-15mu_1 mu_2+mu_3,
    P8=630mu_1^4-420mu_1^2 mu_2+35mu_2^2
                                      +28mu_1 mu_3-mu_4.

Successive exact substitution into(4.1) yields

    a_0=mu_1/2,  a_1=P4/12,  a_2=P6/240,  a_3=P8/10080. (4.2)

At k=1, (M) therefore proves the strict scalar coefficient budget

    a_1>=(mu_1 mu_3-mu_2^2)/24 >0.                       (4.3)

Thus H_0=[a_1] is positive definite for the actual full source, with no
new source evaluation. This statement concerns the scalar first Hankel
matrix; its index must not be confused with a physical odd kernel size.

## 5. The first unpaid determinant

The next matrix in the all-order criterion is

    H_1=[[a_1,a_2],[a_2,a_3]].

The already proved a_1>0 makes its PSD condition exactly equivalent to

    a_1 a_3-a_2^2
      =[10 P4 P8-21 P6^2]/1209600 >=0.                  (H1)

Indeed the Schur remainder is a_3-a_2^2/a_1. If(H1) holds, that remainder
is nonnegative and hence a_3>=0 automatically; conversely PSD implies it.
For every complex pair c the exact decomposition is

    c*H_1 c=a_1|c_1+(a_2/a_1)c_2|^2
                              +(a_3-a_2^2/a_1)|c_2|^2.   (5.1)

No sign of 10 P4 P8-21 P6^2 has been proved in this note. In particular,
(M) has not been shown to imply(H1). Calling(5.1) a new norm would merely
assume the missing Schur sign. If(H1) were negative, the explicit vector
(-a_2/a_1,1) would witness this coefficient matrix's negativity. It is
not by itself a supplied physical two-node K witness; converting it back
requires the corresponding analytic limits and test construction.

The ordinary moment matrices [mu_(i+j)] are automatically PSD because
they integrate |sum c_i U^i|^2 against a positive law. The required
matrices [a_(i+j+1)] instead contain nonlinear, signed expressions in
the mu_k. Positivity of the first kind must not be substituted for
positivity of the second. An inequality at one index, or any finite
collection of successful H_n, does not prove the all-order criterion.

## 6. Decision effect and validation boundary

The next source-sign target in this interface is now the explicit scalar
polynomial(H1) in mu_1,...,mu_4, while RH requires the entire H_n family.
The all-index quantitative statement(M) is available as an analytic
supplier, with(4.3) its first exact coefficient consumer. A next proof
must preserve the correlations between moments when addressing(H1),
or supply a stronger structure that proves every H_n at once.

No new numerical campaign, polynomial control example, theta evaluation,
interval subdivision, root search, external theorem import or Lean run
is performed. The derivation uses full-source integration by parts,
covariance, finite moments and exact power-series algebra.
It does not reset the current source-sign no-delta counter and does not
change global ODD2/IC or RH status. The live Proshka LOW1-LOW3 request
continues independently and has not received this pending candidate.

## 7. Independent acceptance receipt

The sole independent checker /root/sibling5_check read the full candidate,
7877 bytes/186 LF/final LF/0 CR, SHA256
67f68d824cfa031f26e099a5e6064d81318e861807226039acfeecdaaf3d5171,
and returned ACCEPT for the analytic supplier/interface only.
The review verified the full-line integration by parts, every k>=1,
covariance integrability without E[b^2], quantitative variance margin,
normalized moment ratios, all four coefficients and the exact H1
numerator. It also checked the distinction between L1/L2 normalizations
and between ordinary moment Grams and logarithmic-derivative Hankels.
The parent independently derived these identities and verified all three
accepted source hashes against the isolated checkout before review.

Only the status line and this receipt changed after independent review.
H_0>0 is accepted at PAPER scope; H_1 and all H_n remain unpaid.
There is no new source run, no source-sign counter reset, no global
ODD2/IC or RH claim, and no Lean or canonical admission.
