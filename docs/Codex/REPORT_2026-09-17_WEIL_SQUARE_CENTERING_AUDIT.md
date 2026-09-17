# Exact transport of Weil squares and the unchanged arithmetic functional

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.
Base: 1753cf850f3a9e23dfa5aef91e75cc5c0b81ce3e.
Scope: the bounded scalar normalization/test-class check left in S6 of
REPORT_2026-09-17_MODULAR_SCATTERING_SOURCE_AUDIT.md. No new search, source
family or proof dispatch. Original full V, the RH goal, canonical HOLD,
phase and source-sign counters remain unchanged. This is not a proof of
the sign of V or an exact import of Wong's printed full RHS.

The preceding goal turn completed an independently checked source/domain
audit and terminal Proshka synchronization: PROGRESS for the route audit,
not original-form sign progress. This note advances the identified interface
by fixing the scalar test transport instead of leaving it vaguely unpaid.

**Main result.** A literal identification of the two square classes is
false, with an explicit smooth test below. However the positive scalar
test class can be transported exactly: multiply the profile by sqrt(x).
This works for all complex compact smooth profiles and all finite mixtures.
The same operation shifts the Mellin argument. Keeping that shift in the
zero functional and the scattering response is mandatory. Thus the test
cone is repairable; the original full functional has not acquired a sign.

## C0. Exact sources and the scope of this check

The previous accepted modular audit, SHA256
59376eb8b2c4129d9747e679ca2d94d06be4390837175c99afedea93224103c5,
fixes the complete scalar response

\[
m(v)=\frac{\Lambda(v)}{\Lambda(1+v)}
=C((1+v)/2),\qquad
\Lambda(w)=\pi^{-w/2}\Gamma(w/2)\zeta(w).
\]

The unitary v-axis is Re v=0 and corresponds to Re s=1/2 for Eisenstein E(s).
The project's xi is w(w-1)Lambda(w)/2; its elementary factors are not dropped.
The same accepted audit binds the full Maass-Selberg norm including the cutoff.

The old full-sign transfer report has SHA256
1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
It links the all-test Weil sign to the original full theta V. This note
examines the standard scalar Mellin square interface for that all-test
criterion; it does not newly derive a numerical equality between the
project's additive Q, an Eisenstein norm and any expression below.
In particular no original finite V family is assigned a negative value.

Primary passages already fetched and reconciled, not new discovery:

- [Wong, arXiv:1608.02296v2](https://arxiv.org/pdf/1608.02296v2), section 2.1
  (weighted inverse), section 3.1 (test transform), Theorem 4.1 and its proof
  pp.11-12 (m(v) and evenness), Remark 5.2 pp.19-20 (norm positivity).
  PDF SHA256 bc4c09e40a2e1d9d01797274bba875357f9d689688e288c1ba61ffd5aa01a7ae.
  Its inconsistent printed explicit RHS remains unimported.
- [Goldfeld, Exploring.pdf](https://www.math.columbia.edu/~goldfeld/Exploring.pdf),
  pp.1-3 (completed function and truncation), Theorem 4.1 p.8 and Lemma 4.2
  p.9 (full identity). PDF SHA256
  da2ce5e958da27fb20f17b1cc0cbff4f17c24e28efa76590f47aba7d5d4f0209.

All calculations C1-C6 below are supplied directly, rather than inferred
from a common symbol for the two involutions in a secondary account.

## C1. The two involutions and the exact positive transport

Let D=C_c^infinity((0,infinity);C), with multiplicative convolution

\[
(a*b)(x)=\int_0^\infty a(y)b(x/y)\frac{dy}{y},
\quad \widehat a(v)=\int_0^\infty a(x)x^{v-1}\,dx.
\]

All Mellin transforms are entire. Define, for real alpha,

\[
(J_\alpha a)(x)=x^{-2\alpha}\overline{a(1/x)},
\qquad (T_\alpha a)(x)=x^\alpha a(x).
\]

J_alpha is a conjugate-linear involution and direct change of variable gives

\[
\widehat{J_\alpha a}(v)
=\overline{\widehat a(2\alpha-\bar v)}. \tag{C1.1}
\]

Thus a square a*J_alpha a has transform
\(\widehat a(v)\overline{\widehat a(2\alpha-\bar v)}\), nonnegative
on Re v=alpha. In particular J_(1/2) is the usual weighted conjugate
inverse x^-1 conjugate(a(1/x)); J_0 is the unweighted one.

Multiplication by a character is a bijective algebra map on D:

\[
T_\alpha(a*b)=(T_\alpha a)*(T_\alpha b),\quad
T_\alpha J_\alpha=J_0T_\alpha,\quad
\widehat{T_\alpha a}(v)=\widehat a(v+\alpha). \tag{C1.2}
\]

The first identity follows from x^alpha=y^alpha(x/y)^alpha inside the
unchanged integral. Its inverse is T_(-alpha). Consequently

\[
\boxed{T_{1/2}(a*J_{1/2}a)
=(T_{1/2}a)*J_0(T_{1/2}a).} \tag{C1.3}
\]

There is no positivity hypothesis on a, and no restriction to real or even
profiles. For every finite family a=sum_j c_j a_j the identity retains all
conjugate cross terms. Compact smooth support is preserved both ways, so
this pays the complete scalar square-class transport, not just a finite
diagnostic. On logarithmic coordinates, the centered profile is
psi(e^u)=e^(u/2)a(e^u); every complex compact smooth additive profile is
obtained in this way.

## C2. A concrete smooth counterexample to omitting the transport

Choose any real even nonnegative phi in C_c^infinity((-1,1)) with integral 1.
For delta=1/100 let

\[
b_\delta(x)=\delta^{-1}\phi(\log x/\delta),\qquad
a_\delta(x)=b_\delta(x)+\tfrac12 b_\delta(x/4).
\]

These are legitimate compact smooth functions on (0,infinity), and their
Mellin transform is

\[
H_\delta(v)=(1+\tfrac12 4^v)B_\delta(v),\qquad
B_\delta(v)=\int_{-1}^1\phi(u)e^{\delta vu}\,du.
\]

Set g_delta=a_delta*J_(1/2)a_delta, and t0=pi/log(4). Since 4^(it0)=-1,

\[
\widehat g_\delta(it_0)
=-\tfrac12 B_\delta(it_0)\overline{B_\delta(1+it_0)}. \tag{C2.1}
\]

For |v|<=5, the elementary bound
\(|B_\delta(v)-1|\le e^{\delta|v|}-1\le1/19\) holds: use
e^r<=1/(1-r) for 0<=r<=1/20. Both it0 and 1+it0 have modulus <5,
since pi<4 and log(4)>1. Therefore the product in (C2.1) differs from 1
by at most 2/19+1/19^2=39/361, and

\[
\boxed{\operatorname{Re}\widehat g_\delta(it_0)
\le-161/361<0.} \tag{C2.2}
\]

Yet \(\widehat g_\delta(1/2+it)=|H_\delta(1/2+it)|^2\ge0\)
for every real t. This is an analytic compact-smooth control, with an
explicit width and bound, not a distributional atom or a numerical test.
The function g_delta is real, so merely averaging its transform at v and
-v leaves its real part on iR and remains negative at t0. This rules out
literal identification or literal even symmetrization in the same variable.
It does not rule out (C1.3), which fixes the problem exactly.

A negative spectral weight at one point is not a negative full spectral
integral. Neither (C2.1) nor (C2.2) is a negative witness for original V.

## C3. Correct centering also preserves the entire Weil zero functional

Write g=a*J_(1/2)a, psi=T_(1/2)a, p=T_(1/2)g=psi*J_0 psi, and
P(v)=hat p(v). Then

\[
P(v)=\widehat g(v+1/2),\quad
P(it)=|\widehat\psi(it)|^2\ge0,\quad
\widehat g(\rho)=P(\rho-1/2). \tag{C3.1}
\]

Thus, with multiplicities and no hypothesis on zero locations,

\[
\boxed{\sum_\rho\widehat g(\rho)
=\sum_\rho P(\rho-1/2).} \tag{C3.2}
\]

The sums converge absolutely for these tests: after x=e^u, integration by
parts gives arbitrarily fast vertical decay uniformly in bounded real
strips; the classical zeta zero count is O(T log(T+2)). The functional
equation preserves the zero multiset under rho->1-rho. Hence the centered
multiset rho-1/2 is invariant under v->-v. Define the linear inversion
R p(x)=p(1/x) and p_even=(p+R p)/2. Its transform is
P_even(v)=(P(v)+P(-v))/2, so

\[
\sum_\rho P_{\rm even}(\rho-1/2)=\sum_\rho P(\rho-1/2),\qquad
P_{\rm even}(it)=\tfrac12\bigl(|\widehat\psi(it)|^2+
|\widehat\psi(-it)|^2\bigr)\ge0. \tag{C3.3}
\]

More explicitly R is an algebra involution commuting with J_0, so p_even
is the sum of two J_0 squares with weights 1/2, made from psi and R psi.
This proves the scalar Weyl-symmetric positive-weight transport for every
original complex profile. It does not assert a single spherical group
convolution-square lift for those profiles. Such a group lift is a
different hypothesis, not needed to establish (C3.1)-(C3.3).

No RH premise appears here. Positivity on iR does not give positivity at
rho-1/2 without a theorem controlling those evaluation points or the whole
zero sum. This is the same missing full sign, explicitly retained.

## C4. What fails if the test shift is paid but the functional is left fixed

The algebraic repair does not leave arbitrary linear functionals unchanged.
For any test g and any point w,
\(\widehat{T_{1/2}g}(w)=\widehat g(w+1/2)\), not hat g(w).
In particular using p instead of g in an unshifted zero sum gives

\[
\sum_\rho\widehat p(\rho)=\sum_\rho\widehat g(\rho+1/2), \tag{C4.1}
\]

whereas the desired expression is (C3.2). Equality of these two functionals
has not been supplied. This report does not replace the inconsistent
printed Wong formula by either side or claim either complete functional
is negative. It only fixes exactly what arguments a valid substitution uses.

The same warning applies to every non-spectral term. For example at any
prime power n, p(n)=sqrt(n)g(n); any fixed coefficient times g(n) changes
accordingly. A linear integral int k(x)g(x)dx is transported to
int k(x)x^(-1/2)p(x)dx. Evaluation at 1 is unchanged, but neither an
integral with its old kernel nor a prime sum with its old weights is
automatically unchanged. A correct full explicit formula must transform
these terms together. No boundary, pole or archimedean term is set to zero.

## C5. The source-side shift and its complete divisor bookkeeping

For the actual scalar m, the complete meromorphic Lambda has only the
nontrivial zeta zeros and simple poles at 0 and 1. Its functional equation
gives

\[
m(-v)=m(v)^{-1},\qquad
m(v)=\frac{L(v-1/2)}{L(v+1/2)},\quad L(w)=\Lambda(w+1/2). \tag{C5.1}
\]

In particular, with all multiplicities retained:

| Feature of m(v) | Position | Reason |
|---|---|---|
| zero of order mult(rho) | v=rho | Lambda(v) vanishes; Re(1+rho)>1 gives nonzero denominator |
| pole of order mult(rho) | v=rho-1 | denominator vanishes; Lambda(rho-1)=Lambda(2-rho)!=0 |
| simple pole | v=1 | numerator's pole, finite nonzero Lambda(2) below |
| simple zero | v=-1 | denominator's pole at 0, finite nonzero Lambda(-1)=Lambda(2) above |
| removable point | v=0 | the poles of Lambda(v) and Lambda(1+v) cancel; m(0)=-1 |

The last value follows from residues -1 and +1 of Lambda at 0 and 1.
The two nontrivial strips are disjoint; there are no unmentioned zero/pole
cancellations in this table. This uses the full completed source, not only
the zero part of a logarithmic derivative. In particular the simple pole
v=1 cannot disappear by dropping an entire-xi prefactor.

Centering numerator zeros at rho-1/2 replaces the response by

\[
m_+(v)=m(v+1/2)=\frac{\Lambda(v+1/2)}{\Lambda(v+3/2)}.
\]

Its nontrivial-zero family becomes rho-1/2 but its nontrivial-pole family
becomes rho-3/2. The elementary pole moves to 1/2, the elementary zero to
-3/2, and the removable point to -1/2. Centering the denominator poles
instead uses \(m_-(v)=m(v-1/2)\): the nontrivial poles are rho-1/2 and the
nontrivial zeros rho+1/2; the elementary pole is at 3/2, the elementary zero
at -1/2, and the removable point at 1/2. A uniform translation cannot put
both nontrivial families at rho-1/2, since their separation remains one.

These are exact different responses. For example m is regular at 1/2,
whereas m_+ has a pole there. Their unitary-contour formulas cannot be
identified by merely renaming v: v=it for m_+ evaluates the old m on
Re v=1/2, and for m_- on Re v=-1/2. No contour is shifted through zeros
or poles without residues in this report. No global nonnegativity for a
shifted logarithmic-derivative distribution is claimed.

## C6. Result for the original research decision

The scalar test-class question now has a constructive answer, C1 and C3:
the correct character multiplication, complex involution and even
symmetrization are explicit and retain the full class. We should not keep
asking whether that scalar transport exists. C2 excludes the tempting
unweighted substitution, not the corrected map.

The outstanding source interface is now stated with both sides present:
the positive centered weights must be paired with the **centered** complete
Weil functional (including its full arithmetic and boundary terms). The
existing modular norm theorem uses the fixed m(v), whose paired divisor
families are displaced by +/-1/2 from the centered zeros as in C5. This
note provides no exact norm identity for that original functional, no sign
for its total correction, and no proof that a group-level lift supplies it.

We do not submit a renamed request for RH or an additional unproved growth
bound. A future source-level candidate would have to give that complete
functional equality and sign mechanism, not merely the scalar test map
which is already paid here. The printed Wong RHS remains unimported until
its signs, parameters, test map and all corrections are consistently derived.

No original V witness, global VAR/Pick result, RH proof/refutation, Lean
run, canonical admission, source-sign counter reset or new Pro proof job.

## Independent acceptance

Verdict: ACCEPT_SCALAR_WEIL_SQUARE_CENTERING_AND_FUNCTIONAL_AUDIT_ONLY.
Final candidate SHA256: 2f309295097bebfc02435890d453bf0a4313f2f89250ee4fea55c184799d3d20.
Complete review SHA256: 4864354e1498fc9a48db2540f70f57dfeddbcd82249132527f4aa848140e3f40.
Complete parent check SHA256: e54d5a58b8313072cd8a84950f8bb88a72f93739446483c18f4ca4f74cb67aff.
The parent read the full independent review and checked the final C5 wording
clarification, which explicitly lists all shifted elementary zeros and removable
points. The exact scalar transport is accepted on the full stated class;
no full Wong RHS, original-V sign or RH assertion is accepted. The certificate
embeds both checks and binds the primary sources and previous accepted audit.
