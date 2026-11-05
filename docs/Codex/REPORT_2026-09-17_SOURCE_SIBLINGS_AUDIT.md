# Source siblings: Sheffer theta profiles and positive matrix ensembles

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed source mappings and PF control.
Date: 2026-09-17. Isolated analytical research; canonical production remains HOLD.
FULL_V_SIGN: OPEN. RH: OPEN. PX_RH_CLAIM: NOT_MADE.

## Question and exact return point

The original source has an additive total-positivity property and a weighted
inversion identity. Can an existing positive construction use them together to
supply the missing sign? A construction positive in every matrix dimension is
useful only if its positivity controls the original V, with its actual weights
and cutoff. The present test checks two concrete published siblings, not an
exhaustive search or a new RH criterion.

The fixed probability density, with zero extension to t<=0, is

    r(t)=sum_{k>=1}(4 pi^2 k^4 t-6 pi k^2) exp(-pi k^2 t), t>0.
    T = sum_{k>=1} Gamma(2,rate pi k^2),  density r.
    r(1/t)=t^(5/2)r(t).
    M_r(z)=integral r(t)t^(z-1)dt=2 xi(2z-2), z in C.

Here xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2. The actual log-source is
Phi(x)=exp(5x/2)r(exp(2x)), with f=Phi/||Phi||_2. The consumer remains

    V(x,y)=integral_0^infinity (2X+x+y)f(X+x)f(X+y)dX,
    sum_{i,j} conjugate(c_i)V(x_i,x_j)c_j >= 0

for EVERY finite family x_i in the original open negative interval I and
EVERY complex coefficient family. No dimension cutoff or real-only restriction
is introduced. The accepted full-sign transfer identifies this target with
RH; nothing below supplies that sign.

## Published inputs and version boundary

A. Cheon--Forgacs--Tran, *Sheffer sequences with zeros on a line*, arXiv
2508.18229v1, https://arxiv.org/html/2508.18229v1 . Locators: equations (2.7),
(2.12), (2.18)--(2.23), Theorems 5, 9, 11. Short exact quotation from the
introductory discussion of Theorem 11: "understanding the zeros of the scaled
Mellin transform becomes equivalent of understanding the zeros of the zeta
function." Only the p=-1/2, p*=0, N=0 specialization is used, and its formulas
are proved directly below. The general extra-factor Theorem 1 is not imported.
The journal-version full text was not checked; no assertion about that version
is made. The separate improper integrals below are used only for Re(s)>1,
followed by meromorphic continuation where explicitly stated.

B. Forster--Kieburg--Kosters, *Polynomial Ensembles and Polya Frequency
Functions*, arXiv 1710.08794v4, https://arxiv.org/html/1710.08794v4 . Locators:
Definitions 2.2--2.3, Theorems 2.9(1)--(2), 2.10, equation (2.27). Exact
quotation, Theorem 2.9(1): "if and only if it is a Pólya frequency function of
order" (followed by n). The positive Hermitian construction uses ordinary
additive derivatives. The multiplicative GL construction has a DIFFERENT
hypothesis, total positivity after a logarithmic change of density. We apply
2.10 only at nu=0 to square complex matrices with their ADDITIVE convolution
structure; this is not the multiplicative GL statement.

## S1. Exact Sheffer identity for the full theta source

Define polynomials q_j(u) and theta profiles psi_j by

    (1-w)^(u-1/2)(1+w)^(-u)=sum_{j>=0} q_j(u) w^j/j!,
    phi_j(v)=j! L_j^(-1/2)(v) exp(-v/2),
    psi_j(t)=sum_{k>=1} phi_j(2 pi k^2 t).

These are precisely the above specialization of source A; p*=0 makes its
Appell composition the identity. The Laguerre generating formula gives

    sum_j phi_j(2v) w^j/j!
      =(1-w)^(-1/2) exp[-v(1+w)/(1-w)].

Integrate against v^(u-1) for Re(u)>0 and w near zero. The result is
Gamma(u)(1-w)^(u-1/2)(1+w)^(-u), so coefficient extraction proves

    integral_0^infinity phi_j(2v)v^(u-1)dv=Gamma(u)q_j(u).

For Re(s)>1, summing the rescaled integrals absolutely (a fixed polynomial
in v times exp(-v), times sum k^(-Re(s))) proves

    integral psi_j(t)t^(s/2-1)dt
      =q_j(s/2) pi^(-s/2)Gamma(s/2)zeta(s).                  (S1)

No RH or analytic interchange across a divergent integral is used. Directly,
q_0=1, q_1(u)=1/2-2u, and q_2(u)=4u^2-2u+3/4. Since
2! L_2^(-1/2)(v)=v^2-3v+3/4, the FULL pointwise sum satisfies

    t r(t)=psi_2(t)-(3/4)psi_0(t).                         (S2)

Thus its Mellin integral with t^(s/2-1) is

    [q_2(s/2)-3/4] pi^(-s/2)Gamma(s/2)zeta(s)
      =s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)=2xi(s).             (S3)

The left side after combining S2 converges for all complex s by the source
endpoint decay; equality extends entirely. The individual psi integrals
are not thereby declared entire improper integrals.

## S2. Where the known polynomial zero theorem stops

Differentiating the generating function yields

    q_(j+1)(u)=(1/2-2u)q_j(u)+j(j-1/2)q_(j-1)(u).

Set p_j(v)=i^j q_j(1/4+iv), and P_j(v)=2^(-j)p_j(v). Then

    P_0=1, P_1=v,
    P_(j+1)(v)=v P_j(v)-[j(j-1/2)/4]P_(j-1)(v).

P_j is the characteristic polynomial of the real symmetric tridiagonal
j by j matrix with zero diagonal and adjacent entries
sqrt(k(k-1/2))/2 for k=1,...,j-1. The entries are positive. Therefore all
its zeros are real and simple (an eigenvector is determined by its first
coordinate through the nonzero adjacent entries). Equivalently all zeros
of q_j(s/2) lie on Re(s)=1/2. This elementary argument, for every integer j,
is independent of source A's general Theorem 1.

But S1 still has zeta(s) as a factor. At any hypothetical nontrivial zeta
zero away from the critical line, q_j(s/2) is finite and Gamma(s/2) is finite
and nonzero, so the continued transform has that zero too. The known zeros
of q_j do not constrain the zeros of the OTHER factor. Likewise S3 gives
back xi, not a new polynomial approximation to it. This is an exact source
identification, with no new sign or zero-free conclusion.

Logical control: a polynomial whose zeros all lie on Re(s)=1/2 can be
multiplied by (s-1/4)(s-3/4), retaining those polynomial zeros and acquiring
off-line zeros. This is not the theta source; it tests only the invalid
factor-to-product inference. The true theta identity S3 is retained exactly.

## M1. A positive matrix construction exists for every size

The source r is PF infinity on the additive real line by the pinned source
intake. Its zero extension is C infinity and Schwartz: at infinity the
full series and each derivative have polynomial times exp(-pi t) bounds;
at zero differentiate the exact reciprocity and apply the same bounds at
1/t. Consequently every derivative has every absolute polynomial moment.
These statements check Definition 2.3(1) for each finite n.

Theorem 2.9(1) of source B therefore applies with omega=r to give a positive
Hermitian matrix ensemble in EVERY finite dimension n. Its eigenvalue
probability density is the correctly normalized expression

    C_n Delta_n(a) det[(-d/da_k)^(j-1)r(a_k)]_(j,k=1,...,n),
    Delta_n(a)=product_(i<j)(a_j-a_i),
    C_n=1/[n! product_(j=0,...,n-1)j!].                    (M1)

For the constant, integration by parts gives the triangular moment matrix
with diagonal (j-1)! integral r=(j-1)!. Andreief's identity gives the stated
normalization. The theorem supplies nonnegativity. This is a density on
n eigenvalues, NOT the Gram matrix [V(x_i,x_j)]. No identification of its
observable variance with V, no consistent coupling of all n, and no spectral
realization of xi zeros are asserted.

## M2. Gamma mixing gives a second positive all-size lift, preserving zeros

Theorem 2.10 at nu=0 applies to the same r and gives the weight

    Omega(x)=integral_0^infinity exp(-x/t)r(t)dt/t, x>0.    (M2)

It defines the paper's positive Polya ensemble on M_0 for every n. Scalar
Omega is also the probability density of T E with independent E exponential
of rate 1. Absolute Fubini (first at sigma=Re(s)>0) proves

    M_Omega(s)=Gamma(s) M_r(s)=2Gamma(s)xi(2s-2), Re(s)>0. (M3)

Indeed the inner x integral equals t^(s-1)Gamma(s), and T has all real
moments. Gamma is finite and zero-free on this half-plane. Thus this
positive construction preserves EXACTLY the Mellin zeros of r there.
Positivity of its matrix probability laws does not itself locate them.

Moreover, the transformation does not retain the original reciprocity:

    lim_(x downarrow 0)Omega(x)=integral r(t)dt/t=:C>0,
    Omega(x)<=C_L x^(-L) integral t^(L-1)r(t)dt, any L>0.

The first follows by dominated convergence; the second follows from the
boundedness of z^L exp(-z). If Omega(1/x)=x^kappa Omega(x) held for any fixed
real kappa, sending x to infinity and choosing L>max(kappa,0) would give
C=0. Hence there is NO weighted reciprocal identity of that power form.
This excludes that identity for this specified lift, not other matrix lifts.

For comparison, Theorem 2.9(2)'s multiplicative hypothesis at the critical
weight omega(t)=t^(1/4)r(t) asks for PF infinity of

    omega(exp(-u))exp(-u)=exp(-5u/4)r(exp(-u))=Phi(-u/2).

Reflection and positive dilation preserve PF infinity. The pinned route
audit already excludes PF infinity of this actual Phi. The additive theorem
cannot be substituted for this false multiplicative hypothesis.

## M3. Smooth PF-infinity controls with positive ensembles AND off-edge zeros

Here the received MELLINEDGE theorem supplies an actual negative control
for the proposed generic implication; it is not an actual-theta V witness.
Fix ANY N sufficiently large for accepted MELLINEDGE. With

    T_N=sum_(k=1,...,N) Gamma(2,rate pi k^2),
    M_N(s)=E[T_N^(s-1)],

the accepted theorem gives a zero s_0 with 11/8<Re(s_0)<2. Choose a closed
disk D centered at s_0, contained in that strip, with no zeros on its
boundary. This is possible because M_N is holomorphic there and is not
identically zero (it is positive at real s>1).

Let T' be an independent copy of full T. For epsilon>0 set

    T_(N,epsilon)=T_N+epsilon T',
    r_(N,epsilon)=r_N * [epsilon^(-1)r(./epsilon)].         (M4)

Every r_N is PF infinity as a finite convolution of one-sided exponential
densities. Additive convolution and positive scaling preserve PF infinity
(the ordered continuous Cauchy--Binet argument of the source intake).
The convolution M4 has a C infinity, flat zero extension and every
polynomial derivative moment: differentiate the Schwartz second factor,
use the finite polynomial moments of r_N, and use weighted Young bounds.
For negative powers, T_(N,epsilon)>=epsilon T'>0 gives every negative
moment; positive moments follow from sums. Thus ONE fixed such smoothed
source satisfies the hypotheses of M1 and M2 for EVERY matrix dimension.

For s in any compact K contained in Re(s)>1,

    M_(N,epsilon)(s) -> M_N(s) locally uniformly as epsilon downarrow 0.

For completeness, almost surely T_N>0. Uniform continuity on K implies
sup_(s in K)|(T_N+epsilon T')^(s-1)-T_N^(s-1)| ->0.
For epsilon<=1 its supremum is bounded by 2[1+(T_N+T')^B], where
B=max(1,sup_K Re(s)-1), an integrable random variable. Dominated convergence
therefore proves the asserted uniform limit directly. The transforms are
holomorphic near D, justified by the same bounds on a slightly larger
compact set (logarithmic factors are absorbed by small power margins).

Rouche's theorem on the boundary of D now implies that for all sufficiently
small positive epsilon the full transform M_(N,epsilon) has a zero in D.
For its gamma lift, Gamma(s)M_(N,epsilon)(s) has that same zero. Thus:

    smooth PF infinity + positive matrix ensembles in every dimension
       does NOT imply Mellin zero-freeness to the right of Re(s)=5/4.

No numerical N, root coordinate or epsilon threshold is asserted. This is
an analytic existential control derived from the accepted exact MELLINEDGE
input. For epsilon<(E[T]-E[T_N])/E[T], its mean differs from E[T], so it is
certainly not the original source. No reciprocal identity is asserted for
M4. Therefore M3 refutes the inference from PF/matrix positivity ALONE;
it does not refute a theorem genuinely using PF plus the actual reciprocity.
It also does not refute RH or supply a negative original V.

## Mechanism decision

| Candidate | What transfers exactly | Missing or false implication |
| --- | --- | --- |
| Sheffer/Laguerre theta profiles | Full r is the combination S2; polynomial zeros controlled in every degree | Zeta factor remains; no control of its zeros |
| Additive Hermitian ensembles | Actual r yields M1 for every n | No identity relating this positive density to the original V |
| Additive square-matrix gamma lift | Actual r yields M2; M3 is exact | Mellin zeros persist and weighted reciprocity is lost |
| Multiplicative critical-weight ensemble | Logarithmic input is exactly Phi(-u/2) | Required PF infinity is already false |

The known property working here is the additive PF infinity of r, derived
from the complete gamma convolution. These constructions do not use the
joint theta reciprocity or any new prime constraint to force the missing
sign. S3 preserves the full arithmetic factor but supplies no inequality
for it. Neither source is admitted as a supplier of V>=0.

Next bounded question, only if this matrix route is continued: an exact
observable or quadratic form identity must identify ORIGINAL V inside these
source-derived ensembles and use a source property absent from M4 controls.
If only the density's nonnegativity or the gamma/Sheffer multiplier is used,
stop this route; M3 and S1 already show why that inference is insufficient.
No new proof request or another decomposition is automatically justified.

## Search provenance and limits

Existing source-pinned joint-source and SUPPORT reports were reconciled
before this bounded search. The passive/Schur hypothesis had already been
examined and was not redispatched. Consensus searches for joint PF/Mellin/
reciprocity and self-reciprocal spectral-density mechanisms returned A and B;
both records were fetched, then the primary HTML bodies above were downloaded
and read. Discovery abstracts are not proof inputs. The selected three new
registered shelf dictionaries (Sheffer/Mellin/Meixner, Polya derivative-type
ensembles, reciprocal matrix gamma convolution) were run AFTER discovery,
not before it: this order missed the skill's fresh-dictionary shelf-first
requirement and is recorded without claiming compliance. All three returned
INCOMPLETE due to semantic-index freshness; lexical hits are not absence.
No refresh, authentication repair or source registration was performed.
The previously failed mgrep authentication was not retried unchanged.
Search coverage remains INCOMPLETE; no novelty or no-other-method claim.

## Source pins

Exact project and primary-source SHA256 pins are appended by the parent
before independent review. New analytic derivations are S1--S3 and M1--M4
applications/filter proofs above. They are PAPER mathematics, not Lean
certification or canonical admission. Full original V positivity remains open.

```json
{
  "project": {
    "docs/Codex/REPORT_2026-09-12_THETA_TN_INFINITY_INTAKE.md": "ae39ab4cbbfae7ad8c04b61dfb9828c6e9efa0247a538da72e4bd3e748de3790",
    "docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md": "1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282",
    "docs/Codex/REPORT_2026-09-15_RH_ROUTE_AUDIT.md": "0978708a88fb2c4802ed3405b37b427ab6890b46a8ffa688edfe757c4a4fe4e3",
    "docs/Codex/REPORT_2026-09-16_MELLINEDGE_INTAKE.md": "c966f1d94717efab0c291b146a39870a7a1852e67d8acf44ccdc3bb6628d3efc",
    "docs/Codex/REPORT_2026-09-16_JOINT_TN_RECIP_HUNT.md": "19d36616dfd4d8996e2e9358410adedeb91605a94bdb5432109a0bf344879db2"
  },
  "primary_and_receipts": {
    "2508.18229v1.html": "5a633292a613289ca6b54d2b1f584d75cdf2b463861387f96bc733a62931f9c1",
    "1710.08794v4.html": "8f7e6b2119ee58ec31515c31dc8aa50769abdc0ce5654c437d756e76a642603b",
    "CONSENSUS_RECEIPTS.json": "a97af848e3671f96adb6e4fd27f9e695b76058e2d62cb7943278edab17d34f63",
    "ASK_RECEIPTS.json": "29618b17a77c9143fe67c74882017c78d808448fb3ae7199cb273911eb16c391"
  }
}
```

## Independent acceptance

Candidate SHA256: `d30a25ed1ad904ecb0e45d14af81981cf399853c190ce1d5a8b2ce0a5d505852`.
Review SHA256: `9420dad86b455b6c861e5bcc44ece2268e7964dbaeb1db74ad27590da7edf602`.
Verdict: `ACCEPT_LIMITED_SOURCE_SIBLINGS_AND_PF_CONTROL`.
The independent reviewer audited S1--S3 and M1--M4 against the exact primary
source bodies and project pins. Parent checks independently reproduce the
normalizations, Jacobi recurrence, confluence sign, Mellin mixing formula,
endpoint obstruction and compact Rouche argument. Complete checks are
embedded in the paired certificate. This accepts only the exact mappings
and the scoped PF/matrix-positivity counterexample. It supplies no proof
of original V positivity or RH, and performs no canonical admission.
