# All-order odd positivity already implies classical RH

Status: ACCEPTED_PAPER_CONDITIONAL_ALL_ODD_TO_RH_REDUCTION.
No source sign is proved; no RH claim or canonical admission.
This is a proposed reduction of the still-open all-rank consumer, not an
extension of the accepted ODD2 sign theorem to arbitrary sizes.

## 1. Exact source and proposed theorem

Use the unchanged source f=Phi/A, A=||Phi||_2>0, f real, even, positive,
with every exponential-weighted derivative moment finite. Set

    F(z)=integral_R f(x)exp(-izx)dx=xi(1/2-iz)/A,
    V(s,t)=integral_0^infinity(s+t+2v)f(s+v)f(t+v)dv,
    K(s,t)=V(s,t)-V(s,-t).

The normalization, entire Fourier transform, weighted decay and full
V/Q/Weil transfer are independently accepted in
docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, SHA256
1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
The Fourier identity extends from its original open Mellin half-plane
to all z by the identity theorem. K here is the same ODD2 source kernel.

The proposed theorem is

    [for every n>=1, all x_1,...,x_n>0 and all c in C^n,
                 sum conj(c_i)K(x_i,x_j)c_j>=0]  ==> RH.       (O)

Conversely, RH implies full V positivity by the accepted Weil transfer,
hence (O)'s premise by the exact odd four-node/parity assembly. Thus
all-order ODD positivity is equivalent to RH for this exact source.
An independently supplied even-sector sign is unnecessary for this route.
ODD2 is only the n=2 part; (O) does not assume it suffices.

The proof below reconstructs the needed analytic Loewner mechanism from
positive coefficient matrices and a bounded operator. It does not import
the general Loewner theorem or assume a source-positive operator exists.
The operator is constructed only under the explicit unpaid hypothesis(O).

## 2. Reflection, integrability and the zero-height Fourier kernel

With d=s-t, the full-line integral

    integral_R (s+t+2v)f(s+v)f(t+v)dv

is zero: after u=v+(s+t)/2 the integrand is
2u f(u+d/2)f(u-d/2), an odd integrable function. Substituting v->-v
and using f even then proves V(-s,-t)=V(s,t). V is symmetric as well.
Consequently K is symmetric and odd in each variable, and vanishes if
either variable is zero. Source decay also makes V and K continuous.

For any fixed h>0, absolute Fubini gives

    integral_R2 exp(h(s+t))|V(s,t)|dsdt
      <= (1/(2h)) integral_R2 |X+Y|f(X)f(Y)exp(h(X+Y))dXdY
      < infinity.                                             (2.1)

The substitution is X=s+v,Y=t+v. Simultaneous reflection gives the same
statement for -h. Since1<=exp(h(s+t))+exp(-h(s+t)), V is in L1(R2).
Reflection in just t preserves L1, so K is in L1(R2) too.
For |a|<=h the two endpoint weights dominate exp(a(s+t))|V|.

Define

    W_a(u,v)=integral_R2 exp(a(s+t))V(s,t)exp(ius-ivt)dsdt.

For a>0 the same absolutely convergent calculation as(2.1), with the
source integral differentiated once, gives directly

    W_a(u,v)=[-i conjugate(F'(u+ia))F(v+ia)
                      +i conjugate(F(u+ia))F'(v+ia)]
                     /[2a+i(u-v)].                            (2.2)

This identity uses no division by F and no zero-free assertion. Indeed
the numerator is the double Fourier integral of
(X+Y)f(X)f(Y)exp(a(X+Y)); the denominator is the integral of
exp[-(2a+i(u-v))t] on t>=0.

Dominated convergence from(2.1) passes a down to zero. Since F is real
and even on the real axis, for u!=v we obtain the continuous kernel

    W(u,v)=[F(u)F'(v)-F'(u)F(v)]/(u-v).                        (2.3)

On the diagonal its continuous value is F'(u)^2-F(u)F''(u).
Fourier transforming K, with the same signs as W, gives exactly

    W_odd(u,v)=W(u,v)-W(u,-v).                                 (2.4)

There are no Fourier normalization factors in(2.2)-(2.4): these are the
unscaled double transforms. The inverse convention would have(2pi)^-2,
but no inverse transform is used here.

## 3. Transfer of the all-order positive hypothesis

Assume(O)'s premise. Oddness extends it from positive nodes to all real
nodes: replace each nonzero x_i by |x_i| and each coefficient by
sgn(x_i)c_i, combine repeated nodes, and discard zeros.

For any continuous compactly supported complex a, rectangle Riemann sums
and continuity of K then give

    integral_R2 conjugate(a(s))K(s,t)a(t)dsdt>=0.              (3.1)

For real frequencies u_1,...,u_n and complex c_j take
a_R(t)=chi_R(t)sum c_j exp(-iu_j t), with0<=chi_R<=1 and chi_R->1.
The fixed finite trigonometric sum is uniformly bounded. K in L1 gives
dominated convergence in(3.1), hence every finite W_odd matrix is PSD.
This transfer requires the hypothesis at every finite size, not size2.

Because F is even entire, there is a real entire function E with

    E(z^2)=F(z),       E(w)=sum_(n>=0) F^(2n)(0)w^n/(2n)!.

The latter series has infinite radius: the even subsequence of an entire
power series still has zero root limsup in the squared variable.
E(0)=F(0)>0. In a complex disk around0 where E is nonzero put

    g(w)=-E'(w)/E(w)=sum_(n>=0) a_n w^n,   a_n real.

For distinct small positive u,v, algebra in(2.3)-(2.4) yields

    W_odd(u,v)=4uv F(u)F(v)
                 *[g(u^2)-g(v^2)]/(u^2-v^2).                 (3.2)

The diagonal formula follows continuously. Choose epsilon>0 so E has no
zero in a disk containing[0,epsilon] and F(u)>0 for0<=u<=sqrt(epsilon).
For any finite nodes x_i in(0,epsilon), the real diagonal matrix with
entries2sqrt(x_i)F(sqrt(x_i)) is invertible. Equation(3.2) therefore
implies positivity of every divided-difference matrix

    L_g(x_i,x_j),  L_g(x,y)=[g(x)-g(y)]/(x-y),
                  L_g(x,x)=g'(x).                            (3.3)

Only a finite diagonal congruence on this nonzero interval is used.
No bounded inverse Fourier multiplier or division at a zero is asserted.

## 4. Analytic lemma: local Loewner positivity excludes nonreal poles

This section proves the special analytic theorem needed here.
Suppose a real analytic g near0 has every matrix(3.3) positive on some
interval(0,epsilon). Then its germ extends holomorphically to the upper
and lower half-planes, with Im g(z)>=0 whenever Im z>0.

### 4.1. All coefficient Hankel matrices are positive

The convergent two-variable expansion near(0,0) is

    L_g(x,y)=sum_(i,j>=0) a_(i+j+1) x^i y^j.                 (4.1)

For a fixed degree n choose nodes x_k=(k+1)t, k=0,...,n, with t>0 small.
Inverse Vandermonde weights define linear functionals ell_(i,t) satisfying
ell_(i,t)(x^j)=delta_ij for0<=j<=n. For analytic functions they converge
to coefficient extraction at0 as t->0. To see the error, write
ell_(i,t)=t^-i times fixed weights at nodes1,...,n+1: every Taylor term
of degree j>n contributes O(t^(j-i)), uniformly within a smaller disk.
Applying these real linear combinations to both variables of(4.1) and
taking the limit preserves positive semidefiniteness. Consequently

    H_n=[a_(i+j+1)]_(0<=i,j<=n) is PSD for every n.           (4.2)

This also handles arbitrary complex coefficient vectors. The nodes are
strictly positive throughout; no division by the axis factor at0 occurs.

### 4.2. Construct the operator from the unpaid positive moments

Set s_n=a_(n+1). Define L(t^n)=s_n on C[t], and
<p,q>=L(conjugate(p)q), antilinear in the first argument. By(4.2) this
is positive semidefinite. Its Cauchy-Schwarz inequality follows by
applying positivity to p+lambda q for all complex lambda.

Let N={p:<p,p>=0}. If p is in N, Cauchy-Schwarz with q=t^2 p gives

    ||tp||^2=<p,t^2p>=0.

Thus multiplication X[p]=[tp] is well-defined on C[t]/N and symmetric.
Let H be the Hilbert completion. No positivity of X itself is assumed.

Take any r>0 strictly inside the analytic radius of g and let M_r be a
bound for |g| on |z|=r. Cauchy's coefficient estimate gives
|a_j|<=M_r r^-j. For any fixed p(t)=sum p_i t^i put
m_n=||X^n p||^2. These nonnegative numbers satisfy

    m_n<=M_r r^(-2n-1)(sum |p_i|r^-i)^2,
    m_n^2<=m_(n-1)m_(n+1), n>=1,                            (4.3)

the latter by Cauchy-Schwarz for X^(n-1)p and X^(n+1)p.
Log convexity, including zero cases by continuity or direct CS, implies
m_1<=m_0^(1-1/n)m_n^(1/n) for n>=1. For m_0=0 the null-space argument
already gives m_1=0. For m_0>0, use(4.3) and let n->infinity to obtain

    ||Xp||^2<=r^-2||p||^2.                                  (4.4)

Hence X extends to a bounded everywhere-defined symmetric, therefore
selfadjoint, operator T on H. If H={0}, the same formulas below hold
with zero vectors. Let v=[1]; then <v,T^n v>=s_n for every n.

### 4.3. Resolvent extension without a spectral-measure theorem

For any nonreal lambda,
||(T-lambda)w||>=|Im lambda|||w||. This follows by taking the imaginary
part of <w,(T-lambda)w>. Its range is closed; its orthogonal complement
is ker(T-conjugate(lambda))={0}, so the range is all H. Therefore
I-zT is invertible for every nonreal z. Resolvent identities give
holomorphic dependence there. Define

    G(z)=a_0+z<v,(I-zT)^-1 v>.                               (4.5)

For |z|<r, the norm-convergent Neumann series and the moment equalities
give G(z)=a_0+sum_(n>=0)s_n z^(n+1)=g(z).
Thus(4.5) is a genuine extension of the germ, not a separately chosen map.

For w=(I-zT)^-1v, v=w-zTw. Since <Tw,w> is real,

    Im[z<v,w>]=(Im z)||w||^2.

Accordingly Im G(z)>=0 in the upper half-plane; the function is
holomorphic throughout that half-plane and its lower counterpart.
The source norm or an RH-equivalent contraction was not smuggled in:
the entire construction was derived from the explicit hypothesis(4.2).

## 5. Apply the analytic lemma to the entire source E

The meromorphic function -E'/E agrees with G in the upper-half-plane
part of a disk around0. The upper half-plane with E's discrete zeros
removed is connected (a path on a compact set can detour the finitely
many zeros it meets). By the identity theorem -E'/E=G there.
If E had a zero z_0 in the upper half-plane of multiplicity m>=1, then

    -E'(z)/E(z)=-m/(z-z_0)+a holomorphic function.

This contradicts equality with the holomorphic G on a punctured disk.
Thus E has no upper-half-plane zero. Real coefficients exclude lower
zeros by conjugation, so every zero of E is real.

The remaining nonpositive axis is excluded by the actual source:

    E(-u^2)=F(iu)=integral_R f(x)exp(ux)dx>0, u real.        (5.1)

The integral is finite by the accepted weighted decay and strictly
positive because f>0; E(0)>0 as well. Hence every E zero is positive.
Since F(z)=E(z^2), every F zero is real. The exact Mellin/Fourier
identification in section1 therefore puts every nontrivial zeta zero
on Re s=1/2. This proves implication(O), conditionally on its premise.

## 6. A still weaker exact all-order interface

The proof used odd positivity only to obtain(4.2). Consequently the
following all-order Hankel condition alone is sufficient for RH:

    write g(w)=-d/dw log[xi(1/2-i sqrt(w))/A]=sum a_n w^n;
    every finite H_n=[a_(i+j+1)]_(0<=i,j<=n) is PSD.          (H)

The square-root notation means the entire even function E, so it does
not introduce a branch choice. A cancels from the logarithmic derivative.
Together with the accepted RH=>full V=>odd positivity direction, RH,
all-order odd K positivity, and(H) are equivalent for this source.

No H_n source sign has been established in this note, and no finite
set of successful H_n or ODD2 tests would establish(H). The operative
unpaid quantifier is every n. The constructive operator in section4 is
conditional on that quantifier; calling it positive without(H) would be
the same circular norm assumption already excluded in prior reviews.

## 7. Controls, evidence and what this changes

A generic reflection-invariant kernel need not have odd positivity imply
even positivity: V_0(s,t)=st-1 has K_0(s,t)=2st PSD at every odd size,
while V_0(0,0)=-1. It lacks the exact theta-source integral/Fourier
identities and integrability used in sections2-3, so it is not a
counterexample to(O). This control prevents an unsupported parity claim.

No new theta evaluations, truncation, interval run, source convolution
test or numerical root search is used. The current complete min>=1 ODD2
result and pending Proshka whole-LOW request are unchanged. If global
ODD2 closes, all higher odd orders still require proof. The even sector
can be recovered through the RH/full-Weil equivalence after all-order
odd positivity; it is not paid by ODD2 alone.

Classical background used explicitly: Fourier integral algebra, dominated
convergence, Riemann sums, power series/identity theorem, Cauchy coefficient
estimate, finite PSD limits, Hilbert completion and bounded-operator
resolvent identities. The nontrivial local Loewner continuation needed
here is proved in section4, rather than cited from an unverified source.
A search-provider token failure and an unavailable author webpage supplied
no theorem evidence and are not cited as mathematical dependencies.

This would remove a separate even-sign obligation from this selected
all-odd route if independently accepted. It does not prove a new actual
sign family or reset the current source-sign no-delta counter.

## 8. Independent acceptance receipt

The sole independent checker /root/sibling5_check read the entire
13075byte/289LF candidate, SHA256
0ac61a1e3a659d64f5a8fd32bed0b4f2d872ac45ca9ff9528fe055db43422fe3,
and returned ACCEPT for the conditional reduction only. The independent
audit separately checked full-line reflection, weighted L1/Fubini, Fourier
signs, the factor4uvF(u)F(v), all-order PSD transfer, the Vandermonde
coefficient limit, the null ideal, bounded multiplication from coefficient
growth/log convexity, the nonreal resolvent, and pole exclusion.
It found no hidden RH premise beyond the explicit unpaid all-order sign.
The parent rederived these steps before the review and checked the exact
accepted source-transfer hash and its normalization.

Only the status line and this receipt changed after independent review.
The reduction does not add a source-positive matrix family, does not
promote ODD2, and does not reset the source-sign no-delta counter.
No Lean or canonical admission and no RH proof is claimed.
