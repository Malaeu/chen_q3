# SIBLING — finite Bezout form and its geometric sign supplier

PAPER_CANDIDATE; attempt 1 of 3; no Proshka request used. Independent review
and parent acceptance are separate stages. No number-field sign or RH claim.

Source: owner advice `docs/Codex/ADVICE_2026-09-11_SIBLING.md` at
8477fd769721eacab272356acaf48cf4fcc6c61d,
SHA256 ad2d466924924d4ce82827317220e697c82d9ea32e4b81a4a5d0fb25a575dc9f.
The advice's genus-two random test is not a premise and was not repeated.

## S1. Exact finite theorem, including support and normalization

Let g>=1, phi_j real, phi_{-j}=phi_j, phi_j=0 for |j|>g, and c=phi_g!=0.
Let Xi(theta)=sum_{j=-g}^g phi_j exp(i*j*theta). The variable theta is complex.
For integer x,y define the FINITE sum

    V(x,y)=sum_{t>=0}(x+y+2t)phi_{x+t}phi_{y+t}.

For any fixed q>0 let H2(x,y)=q^{2(x+y)}V(x,y). Then the following are equivalent:

1. H2 is nonnegative on every finitely supported complex coefficient vector.
2. V is nonnegative on that same class.
3. Every complex zero of Xi has real theta.

The zero polynomial is excluded by the degree hypothesis. For g=0 and a
nonzero constant, V=0 and the assertion is vacuous and true.

Only x,y in {1-g,...,g} can contribute. Indeed, x>g or y>g gives an empty
sum. If min(x,y)<=-g, the sum already includes every integer t on which the
product is nonzero. The involution t -> -x-y-t reverses the weight and,
by evenness, preserves that product. The full sum is zero. This also explains
the apparently infinite zero block in the observer's numerical matrix.

On every finite support, the change b_x=q^{2x}a_x is invertible, so it
preserves positivity; no bounded inverse on an infinite weighted Hilbert
space is claimed or needed.

Set N=2g and define the monic real reciprocal polynomial

    A(z)=z^g Xi(theta)/c=sum_{j=0}^N a_j z^j, z=exp(i*theta),
    a_j=phi_{j-g}/c, a_0=a_N=1, a_j=a_{N-j}.

A has no zero at zero. The exponential substitution proves that condition 3
is precisely that every root of A lies on |z|=1, including multiplicities.
Order the finite block by x=g-p, 0<=p<N, and write V0 for V/c^2 in that order.

    (V0)_{pq}=sum_{t=0}^{min(p,q)}(N-p-q+2t)a_{p-t}a_{q-t}.          (S1)

## S2. The exact Bezout kernel and proof of the equivalence

Define K(z,w)=sum_{p,q=0}^{N-1}(V0)_{pq}z^p w^q. Then

    (1-z*w)K(z,w)
      = N A(z)A(w)-z A'(z)A(w)-w A(z)A'(w).                       (S2)

Proof: subtract consecutive t terms of (S1). Boundary coefficients of degree
N cancel by a_j=a_{N-j}; equivalently substitute w=1/z and use
z A'(z)/A(z)+(1/z)A'(1/z)/A(1/z)=N. Thus the numerator is divisible by
1-z*w, and the quotient has degree at most N-1 in each variable. Coefficient
comparison gives exactly (S1), not just its lower-degree truncation.

If all roots alpha of A lie on the unit circle, count them with multiplicity.
Using alpha^{-1}=conjugate(alpha), logarithmic differentiation in (S2) gives

    K(z,w)=sum_alpha [A(z)/(z-alpha)] [A(w)/(w-conjugate(alpha))].  (S3)

Each quotient is a polynomial even at a multiple root. Its coefficient
matrix is a sum of Hermitian rank-one nonnegative matrices. This proves one
direction of S1 without assuming simple roots.

Conversely suppose V0 is nonnegative. For |z|<1 and A(z)!=0, (S2) gives

    K(z,conjugate(z))
      = |A(z)|^2 [N-2 Re(z A'(z)/A(z))]/(1-|z|^2) >= 0.          (S4)

If alpha is a root inside the disk, alpha!=0. Write its multiplicity as m>=1
and A(z)=(z-alpha)^m B(z), B(alpha)!=0. Along z=(1+epsilon)alpha, for small
positive real epsilon with |z|<1 and no other root on the short segment,

    z A'(z)/A(z)=m(1+epsilon)/epsilon+O(1).

The bracket in (S4) is strictly negative, a contradiction. This treats
multiple roots directly. If any root were outside the circle, reciprocity
would supply one inside. All roots therefore lie on the circle. In the
failure case the evaluation vector (1,z,...,z^{N-1}) supplies a finite complex
negative witness after the indicated choice of z; no root-separation limit is
used in the positive direction.

### Classical name, with the exact real change of variables

This is a Bezoutian, not a Schur-Cohn matrix of A against its own reciprocal
(that latter numerator vanishes). The following identifies the precise pair.
Put

    F(t)=(t+i)^N A((t-i)/(t+i)),
    L(t)=(1+t^2)F'(t)-N*t*F(t).

Reciprocity and reality of A imply F has real coefficients. Both F and L
have degree at most N. F may have degree below N when A(1)=0; keep the same
N-dimensional coefficient space, so zeros mapped to infinity cause no loss.
The real symmetric Bezoutian is defined by the coefficients of

    Bez(F,L)(t,s)=[F(t)L(s)-L(t)F(s)]/(t-s).

Direct differentiation and substitution in (S2) give

    (t+i)^{N-1}(s-i)^{N-1}
      K((t-i)/(t+i),(s+i)/(s-i)) = Bez(F,L)(t,s)/4.              (S5)

The polynomials (t-i)^p(t+i)^{N-1-p}, 0<=p<N, form a basis. The transformation
is therefore an invertible complex congruence from V0 to the real symmetric
Bezoutian divided by 4. This displayed definition fixes the naming and sign
convention; no external Bezout positivity theorem is being imported.

## S3. An explicit invertible Newton-trace congruence

The stronger algebraic dictionary needed by geometry is the following.
Let p_0=N and let p_k be the power sums of the roots of A, with multiplicity.
They are computed from the coefficients, WITHOUT locating any root:

    p_k + a_1 p_{k-1}+...+a_{k-1}p_1+k*a_k=0, 1<=k<N.         (S6)

Reciprocity gives p_{-k}=p_k. Define two N by N real matrices

    M_{jk}=p_{|j-k|}, 0<=j,k<N,
    B_{pj}=a_{N-1-p-j} if p+j<=N-1, and 0 otherwise.

Then det B=(-1)^{N(N-1)/2} and

                         V0 = B M B^T.                       (S7)

Here is a proof valid even when A has multiple roots. For each root alpha,
the coefficients of A(z)/(z-alpha) are the values at alpha of

    B_p(T)=sum_{j=0}^{N-1-p}a_{N-1-p-j}T^j.

This follows by polynomial division, with the last remainder A(alpha)=0.
For arbitrary nonzero alpha (no unit-circle assumption),

    (1-z*w)/[(z-alpha)(w-alpha^{-1})]
      = 1-z/(z-alpha)-w/(w-alpha^{-1}).

Sum over roots and use reciprocity to obtain (S2). The coefficient of z^p w^q
is sum_alpha B_p(alpha)B_q(alpha^{-1}), which is precisely the right side
of (S7). This proof uses formal root identities, never their absolute values.
The anti-diagonal entries of B are 1, proving its determinant and invertibility.

Consequently the coefficient condition actually paid by geometry is the
FINITE positive-type Newton condition M>=0. It is stronger than positivity
of individual point counts or two-by-two entries; by S1 and S7 it is equivalent
to the finite unit-circle conclusion. Its value is that geometry supplies it
independently, rather than reading it back from known zeros.

## S4. The geometric supplier from primitive Frobenius graphs

Let X/F_q be a smooth, projective, geometrically connected curve of genus g.
Write its zeta function, as in the advice, as

    Z_X(T)=exp(sum_{n>=1}N_n T^n/n)=P_X(T)/[(1-T)(1-q*T)],
    N_n=#X(F_{q^n}), A(z)=P_X(z/sqrt(q)).

Use only rationality, degree 2g and the functional equation of P_X, not the
Weil zero bound. These make A the monic reciprocal polynomial used above.
Logarithmic differentiation at zero gives

    p_n=q^{-n/2}(1+q^n-N_n), n>=1, p_0=2g.                   (S8)

Work on the smooth projective surface S=X_bar x X_bar. Choose degree-one
fiber classes F1={point} x X_bar and F2=X_bar x {point}. Then
F1^2=F2^2=0 and F1.F2=1. Let Gamma_n be the graph (x,Frob_q^n(x)), n>=0,
and define REAL numerical divisor classes

    D_n=Gamma_n-q^n F1-F2,  E_n=q^{-n/2}D_n.                 (S9)

Each Gamma_n.F1=1 and Gamma_n.F2=q^n, so E_n is orthogonal to both fibers.
The divisor H=F1+F2 is ample: positive-degree line bundles on a projective
curve have very ample high powers, and the exterior product then embeds the
product by the Segre embedding. The Hodge index theorem therefore gives

    -D.conjugate(D)>=0 for every complex linear combination of the E_n. (S10)

For clarity, apply the real Hodge inequality to Re(D) and Im(D); the
Hermitian expression is minus the sum of their two self-intersections.
The classes need not be linearly independent. Numerical null classes cause
semidefiniteness, not a failed strict-positivity requirement.

The graph intersection numbers, with all inseparable factors, are

    Gamma_n^2=q^n(2-2g),
    Gamma_m.Gamma_n=q^{min(m,n)}N_{|m-n|}, m!=n.              (S11)

Derivation of the first formula: the graph is isomorphic to X_bar and its
normal bundle is (Frob_q^n)^*T_X. Its degree is q^n(2-2g), and self-intersection
is the degree of the normal bundle. This includes n=0, where Gamma_0=Delta.

For m=n+d, d>0, the equalizer of Frob^m and Frob^n is the pullback of Delta
by (Frob^n,Frob^m). Factoring through (id,Frob^d) and Frob^n x Frob^n gives
q^n times the equalizer of id and Frob^d: the pullback of the diagonal
Cartier divisor by simultaneous q^n-Frobenius has multiplicity q^n, not
q^{2n}. Locally a diagonal uniformizer difference becomes its q^n-th power.
The fixed points of Frob^d are exactly X(F_{q^d}), and that graph meets the
diagonal transversely because its differential is zero while the diagonal
has identity differential. Each fixed point therefore contributes 1 before
the q^n factor. This proves the second formula without a root-location claim.

Expanding (S9), using the fiber intersections, gives

    D_m.D_n=Gamma_m.Gamma_n-q^m-q^n,
                       -E_m.E_n=p_{|m-n|}.                 (S12)

For m=n the latter value is exactly 2g. For m>n it is
q^{-(m-n)/2}(1+q^{m-n}-N_{m-n}), exactly (S8). Thus the M of S3 is the
negative intersection Gram matrix of E_0,...,E_{N-1}, and S10 proves M>=0.
This is the geometry -> positivity -> zeros direction requested in Q2.

## S5. Exact dictionary for V and its reservoir/cross terms

For 0<=p<N define the primitive class

    C_p=sum_{j=0}^{N-1-p}a_{N-1-p-j}E_j.

Equations S7 and S12 prove the ENTRY-BY-ENTRY identity

       V(g-p,g-q)=c^2 (V0)_{pq}=-c^2 C_p.C_q.              (S13)

For the actual curve normalization c=1; it is retained for the general
finite theorem. Given any finite complex vector b_x, put

    C_b=c sum_{x=1-g}^g b_x C_{g-x}.

Then

    sum_{x,y}conjugate(b_x)b_y V(x,y)
      =-conjugate(C_b).C_b
      =sum_{t>=0}[2t|F_t|^2+2Re(conjugate(F_t)G_t)],         (S14)
    F_t=sum_x b_x phi_{x+t}, G_t=sum_x x*b_x phi_{x+t}.

The last equality expands the original finite sum, retaining every mixed
term. For H2 replace b_x by q^{2x}b_x throughout. This maps each full V-entry
and the full test to explicit intersection quantities; it does NOT pretend
each individual t-summand is nonnegative or has a canonical separate effective
divisor interpretation. The reservoir and signed cross term are a coordinate
decomposition of the single negative primitive self-intersection. Hodge
controls their SUM. Omitting the cross term would break S13/S14.

Genus one checks the constants directly. For A=z^2+a_1*z+1,
p_1=-a_1 and (C_0,C_1)=(a_1 E_0+E_1,E_0). Hence V is
[[2,a_1],[a_1,2]]. With a_1=-a/sqrt(q), its determinant is 4-a^2/q.
Hodge on E_0,E_1 pays this bound; known Hasse zeros were not substituted.

## S6. What precisely transfers to a checkable Phi question

The finite property is now explicit, not 'some positive geometry': the
Newton sums of the SAME reciprocal coefficient polynomial form a nonnegative
Toeplitz matrix, because the SAME counts give primitive graph intersections.
Positive counts alone do not imply this matrix inequality. The off-circle
control A=z^2-3z+1 has M=[[2,3],[3,2]] with value -2 on (1,-1), and cannot
possess such an intersection realization.

There is a completely coefficient-based way to state the number-field
analogue, without naming or locating zeros. It is included ONLY as a precise
test interface, not as a newly selected Jensen research route. The existing
shelf already records Jensen/Hermite criteria and their missing uniformity
(VORTEX_INVARIANT_LITERATURE_GAP_2026-09-08.md row17; CHAT_DIGESTS lines1038-1046).

For the fixed Phi define I=int_R Phi(x)dx>0 and
F_Phi(z)=I^{-1}int_R Phi(x)exp(-i*z*x)dx. The canonical source is
PROSHKA_VERDICT_GOAL058_SLACK_2026-09-11.md section3.1, SL10:
F_f(z)=xi(1/2-i*z)/A, with f=Phi/A and A=||Phi||2. Consequently
F_Phi=(A/I)F_f=xi(1/2-i*z)/I; the zero sets coincide without frequency
rescaling. Define d_k=F_Phi^{(k)}(0), so

    d_{2j}=(-1)^j I^{-1}int_R x^{2j}Phi(x)dx, d_{2j+1}=0,
    J_n(t)=sum_{k=0}^n binom(n,k)d_k t^k, n even and positive.

Its degree is exactly n because Phi>0 and d_n!=0. Make J_n monic and use
Newton identities to calculate s_m(J_n). The real Hermite trace matrix is

    H^{(n)}_{ij}=s_{i+j}(J_n), 0<=i,j<n.                    (S15)

All these numbers are defined from Phi moments; there is no zero-location
input. The explicit source statement is H^{(n)}>=0 for every positive even n.
This is a sign obligation, NOT a claim proved here for Phi.

For completeness its sufficiency is elementary. For any real polynomial P,
the matrix of its root power sums is nonnegative iff all its roots are real,
including multiplicities. One direction is a real Vandermonde Gram sum. If
alpha,conjugate(alpha) form a nonreal pair, interpolate a real polynomial h
of degree below the number of distinct roots with h(alpha)=i,
h(conjugate(alpha))=-i and zero at the other roots. Conjugation-compatible
interpolation gives real coefficients, and its trace quadratic value is
-2 times the multiplicity of alpha. This proves the converse and supplies
a finite negative witness.

Thus S15 would make all J_n real-rooted. Furthermore J_n(z/n) converges
locally uniformly to F_Phi(z): the k-th Taylor coefficient is multiplied by
(n)_k/n^k in [0,1], tending to 1, and Cauchy bounds on any larger disk give
a common summable majorant. Phi's established superexponential envelope
makes F_Phi entire and justifies its moment derivatives. Hurwitz applied on
nonreal disks, with F_Phi(0)=1, then excludes every nonreal zero. No numerical
moment grid can establish the all-n condition.

The missing NUMBER-FIELD supplier is now exact: a source-defined positive
pairing that realizes these coefficient trace matrices (or the original
SL20 pairing itself) with the required identities, uniformly over the full
family. The surface/Frobenius graph construction supplies that structure for
curves; no arithmetic surface or classes for Phi have been constructed here.
This is consistent with the earlier HODGE same-pairing obstruction, not its
solution. The gain is the explicit finite dictionary S7/S12/S13, not a new
proof of the already known Jensen criterion or of RH. The continuous OC1/OC2
controls remain in force and no finite truncation of Phi is declared a curve.

## S7. Directly checked source scope

Two primary teaching documents from the authored MIT OpenCourseWare course
18.727, Spring2008, were fetched from the course's actual resource links.
All extracted text was read; the relevant theorem/definition pages were also
rendered and inspected. These supply the intersection-theory and Hodge
premises; S1-S15 are the local derivation, not an attribution to those notes.

| Source | Exact locator and verbatim quote | Scope and mapping |
|---|---|---|
| MIT lecture1, 166197bytes, SHA256 7d04b0f0bf9880cee12a3ff0332d5d64a063b4ebe694e76d6ede874af90f98d9 | printedp3/PDFp4, section3: 'Let X = S be a nonsingular, projective algebraic surface over an algebraically closed field k.'; Definition1 gives local intersection multiplicity. Printedp4/PDFp5, Lemma1: 'we have O_X(C) . L = deg L|_C' (mathematical glyphs transcribed) | Apply to X_bar x X_bar. Transversality is used only for id versus positive Frobenius power. Bilinearity and normal-bundle self-intersection preserve inseparable degrees. |
| MIT lecture2, 198721bytes, SHA256 e279bfeed05297da7b511164668148101e3455007ebc553b9f8cc5918363d77f | printedp2/PDFp3, section1.2 Corollary1: 'If D is a divisor on X and H is a hyperplane section on X s.t. (D . H) = 0 then D^2 <= 0 and D^2 = 0 iff D equiv 0.'; printedp3/PDFp4 Theorem3 states signature (1,rho-1). | H=F1+F2 is ample; a positive multiple is a hyperplane class. Extend to real coefficients in the finite numerical space and then Hermitian polarization. Only the primitive nonpositive sign is needed. |

Source URLs:

- https://ocw.mit.edu/courses/18-727-topics-in-algebraic-geometry-algebraic-surfaces-spring-2008/cce30335f2f48854721e541f1c4cb536_lect1.pdf
- https://ocw.mit.edu/courses/18-727-topics-in-algebraic-geometry-algebraic-surfaces-spring-2008/198274c0c471d31fc05d600e28e403db_lect2.pdf

Source caution: lecture1's proof equation(4) prints deg L^{-1}, inconsistent
with its lemma statement and curve Riemann-Roch; the correct value is deg L.
Lecture2's final sentence after Theorem3 prints D^2 equiv 0 where the preceding
Corollary1 supplies the needed D^2<=0. Neither typo is used. The displayed
lemma, Corollary1, normal-bundle identity and signature statement fix our signs.
Original historical publications cited in the notes were not fetched or audited.
This is not an independent reconstruction of all algebraic surface foundations.

The bounded Crossref search returned six metadata candidates, none an exact
supplier for this graph/Bezout map. They were not imported as theorems. Three
local shelf receipts and the source-discovery receipt will be preserved in
the sibling log. No absence-of-literature claim is made.

## S8. Checks, attempted falsification, and decision boundary

One frozen exact symbolic check (SymPy, 1.216181s) passed S2 and S7 for the
fully symbolic monic reciprocal families g=1,2,3, with det B=-1,+1,-1 respectively.
It checked the factor1/4 in S5 for A=z^2+1, whose real transformed kernel is
4(1+t*s); the off-circle g1 vector gives -2; A=(z-1)^4 gives a rank-one
matrix 4*b*b^T, b=(-1,3,-3,1). These are exact controls of the derivation,
not a substitute for its all-degree proof or for Hodge theory.

Script SHA256 f12d59a7b30f669430d7b2c8c0735249c5557ee9d41eeec58fd1df26a1342c85;
full recipe/output in docs/routeB_bus/sibling/sibling_20260911.log,
SIBLING_ALGEBRA_PROCESS_EXIT=0. No old200sample experiment was repeated.

Proposed outcome: Q1 proved at finite PAPER scope; Q2 answered by the exact
geometric supplier S8-S14 and explicit unproved Phi interface S15. This does
not prove or promise a number-field Hodge realization. Independent checker
must decide whether both requested finite parts are met, identify the first
incorrect assertion, and distinguish the new exact dictionary from old criteria.
No production CLOSES/OPENS, Lean admission or PX_RH_CLAIM follows.

## S9. SIBLING2: the observer's half-line coefficients, for every genus

Published steering: ADVICE_2026-09-11_SIBLING2.md at
cba6a846, followed by the addressed WATCH instruction at09f11c6a.
This section proves the two identities, not just the g<=3 numerical examples.
The source's phrase 'not Bezout' is rejected: S5 is an explicit invertible
Bezout congruence. The following geometric congruence coexists with it.

Use p_k from S6/S8, never real angles as an input. Let M_infinity(t,s)=p_{|t-s|}
for nonnegative integers t,s, and U_{t,x}=phi_{x+t}. Each column has finite
support. Then, for ALL integer x,y,

    V(x,y)=sum_{t,s>=0} phi_{x+t}phi_{y+s}p_{|t-s|}
          =(U^T M_infinity U)_{xy}.                         (S16)

Proof on the active block: V is invariant under (x,y)->(1-x,1-y).
Indeed this changes its half-line sum into minus the sum over t<=-1;
the full-line odd-weight sum is zero. In p coordinates this is J V0 J=V0,
where J reverses the N coordinates. In S7, (JB)_{pt}=a_{p-t} for t<=p.
Those are exactly phi_{g-p+t}/c. Conjugate S7 by J to obtain S16 on the
block. Its U-block is triangular with diagonal c, so its range contains
EVERY vector supported on t=0,...,N-1. No rank or simple-root assumption
is lost. Thus positivity of V implies positivity of that finite M block,
which is sufficient by S7/S1 for all roots to lie on the circle.

For x>g the column is zero. For x<=-g its generating polynomial is

    sum_{t>=0}phi_{x+t}z^t=c*z^{-x-g}A(z).

It vanishes at every formal root alpha of A. Since p_{t-s}=sum_alpha
alpha^t alpha^{-s}, its pairing with every column is zero, including at
multiple roots. This proves S16 outside the active block as well.
For g=0, p_k=0 and both sides vanish.

Define the Castelnuovo-Severi form on arbitrary real divisor classes by

    C(D,E)=(D.F1)(E.F2)+(D.F2)(E.F1)-D.E.

It is minus the intersection of the primitive projections. S11 gives

    q^{-(i+j)/2} C(Gamma_i,Gamma_j)=p_{|i-j|}.              (S17)

Its diagonal uses Gamma_i^2=q^i(2-2g), NOT an actual point count N_0.
The observer script's convention N_0:=2-2g is a bookkeeping convention
for this self-intersection only. For

    D_x=sum_{t>=0}q^{-t/2}phi_{x+t}Gamma_t

S16/S17 give V(x,y)=C(D_x,D_y). Hodge supplies C>=0 after primitive
projection. The range argument above completes geometry -> V>=0 -> zeros.
Before that conclusion, 'zero measure on the circle' must instead mean the
algebraic reciprocal power-sum sequence p_k. Real angles would assume the
conclusion. After Hodge and S1 it really is the positive circle measure,
with multiplicities. The observer's two exact identities are confirmed with
these conventions; no floating test was rerun.

## S10. Continuous restatement: exact full Weil pairing of half-line tails

Keep the canonical SLACK f=Phi/A, A=||Phi||2, F(z)=int f(t)e^{-izt}dt,
X, B, alpha, c_A, w_n and h=2 from SL1/SL4. Define the real X-valued family

    k_x(t)=1_{t>=0} f(x+t), x real.

Then the exact continuous counterpart of S16 is

    V_f(x,y)=B(k_x,k_y)
      = int_{t,s>=0} f(x+t)f(y+s) W(t-s) dt ds.              (S18)

The last display is distributional notation, defined below; it is not an
ordinary Lebesgue integral of a positive function or measure. All theta
terms, all prime powers and both pole terms are included. Its normalization
is A^{-2}; there is NO extra 2pi factor in S18.

### The boundary at zero and all tails

For 0<r<=1 the translation energy of k_x obeys

    ||k_x(.+r)-k_x||2^2
      <= r sup_{u>=x}|f(u)|^2 + r^2 int_x^infinity |f'(u)|^2du.

The first term is the boundary jump; it must not be discarded. For r>1
use 4 int_x^infinity |f(u)|^2du. Since alpha(r)=O(1/r) near zero and
decays exponentially at infinity, both bounds are integrable. Also

    ||e^{|t|}k_x||2^2=e^{-2x} int_x^infinity e^{2u}|f(u)|^2du.

Consequently k_x is in X. On x<=0 its X norm is O(e^{-x}+1). On x>=0
it decays faster than every exponential by the full theta envelope ENV;
the same estimates with f' and f'' show x->k_x is continuous in X.
In particular

    J_h=int_R e^{hx}||k_x||_X dx < infinity, h>1.            (S19)

These estimates include the entire t>=0 tail. For explicit approximation,
first cut off t>=R with smooth cutoffs having uniformly bounded derivatives,
then mollify across t=0. The SL1 compact-cutoff/density estimates give
convergence in X, hence in B, without replacing the boundary jump by zero.

### Proof of the identity, with no use of zeros

In the Banach-space integral justified by S19, direct scalar substitution gives

    int_R e^{hx-iux}k_x dx = F(u+ih) q_{h,u},
    q_{h,u}(t)=1_{t>=0}e^{-ht}e^{iut}.                     (S20)

The scalar identity also holds in X: the integral exists in X, and its
continuous embedding in the weighted L2 space identifies the same function.
The kernel T_h(x,y)=e^{h(x+y)}B(k_x,k_y) is continuous and in L1(R^2), since
its L1 norm is at most C_X J_h^2. Continuity of B and S19 justify interchanging
both integrals, giving the EXACT same Fourier convention as SL12:

    int int T_h(x,y)e^{iux-ivy}dxdy
      = conjugate(F(u+ih)) B(q_{h,u},q_{h,v}) F(v+ih)
      = conjugate(F(u+ih)) K_h(u,v) F(v+ih)=W_h(u,v).       (S21)

Here B(q,q)=K_h is the previously proved SL6, not a positivity assumption.
SL12 independently gives the Fourier transform of H_h=e^{h(x+y)}V_f(x,y)
as W_h. Uniqueness of the L1 Fourier transform, followed by continuity,
proves T_h=H_h at EVERY x,y. Cancelling e^{h(x+y)} proves S18's first equality.
This proof uses neither a Hadamard product nor division by F on a function
space. It applies to the SAME canonical source coupling SL10; an arbitrary
positive even control f_c need not have that coupling to this arithmetic B.

### The precise distribution W and its admissible pairing

For a smooth compact function eta, define the even real Weil distribution by

    <W,eta> = int_0^infinity alpha(r)[2eta(0)-eta(r)-eta(-r)]dr
             -c_A eta(0) + int_R 2cosh(r/2)eta(r)dr
             -sum_{n>=2}w_n[eta(log n)+eta(-log n)].         (S22)

This is exactly the polarization of SL1. It extends to

    eta_xy(r)=int_R k_x(s+r)k_y(s)ds

by the SAME formula, not by multiplying arbitrary distributions. This eta
is locally Lipschitz, so its second difference at zero is O(|r|); alpha
therefore has an integrable product at zero. All other terms converge
absolutely: weighted Cauchy-Schwarz gives
|eta_xy(r)|<=e^{-|r|}||e^{|t|}k_x||2 ||e^{|t|}k_y||2.
It pays both pole integrals and sum w_n e^{-log n}<infinity. Polarizing the
translation-energy term gives <W,eta_xy>=B(k_x,k_y), proving the second
part of S18 and every cutoff/tail in its distributional interpretation.
For complex combinations, conjugate the first factor as in B; all bounds
persist by linearity and the continuity estimate.

On compact smooth tests the inherited explicit formula identifies S22 with
sum_lambda eta_hat(lambda), lambda a zero of F, counted with multiplicity,
in the convention eta_hat(z)=int eta(r)e^{-izr}dr. The set is stable under
lambda->-lambda and conjugation, so this convention matches the same B.
The symbol sum exp(-i lambda r) denotes this distributional action, not a
pointwise series. Without RH the lambda may be nonreal. There is no asserted
positive measure on R and no asserted tempered extension to all Schwartz
tests. S18 is proved directly from S22 and SL6/SL10/SL12, so it needs no
unjustified exchange of a zero series with a half-line tail.

Finally for a in C_c^infinity, the X-valued integral K_a=int a(x)k_x dx exists
and the full source quadratic form satisfies

    int int conjugate(a(x))V_f(x,y)a(y)dxdy=B(K_a,K_a).     (S23)

Replacing a(x) by e^{hx}a(x) gives the precise SL14 form H_h. Thus S18
restates the SAME all-test sign problem; it supplies the continuous object,
not its sign. In particular the geometric supplier for these K_a remains
unconstructed, while the finite-field D_x supplier has been proved.

## S11. Bounded Sonin comparison: the exact distinction and stop

Source checked directly: CC-WEILPOS-2020, arXiv:2006.13771v1,
local pdfs/2006.13771.pdf, SHA256
b8e0b54ade8535cf3ca633d1ef325bfc5c793b407da577a83d111726935b58e0.
Read scope: complete printed pages1-3 and AppendixA/B pp49-50;
Theorem1/Corollary2 on p3 visually checked. No claim of full-paper audit.

The relevant primary statements, with their scope, are:

- p2: 'In this paper we consider the simplest instance of this strategy,
  namely when the support of the test function is contained in the interval
  (1/2,2) ... so that rational primes are not involved.'
- p2: the space consists of even L2 functions whose function AND ordinary
  Fourier transform vanish on [-1,1]. 'Even though the scaling action ...
  does not restrict to this subspace', its compressed trace is positive.
- p3, Theorem1/(4): for g supported in [2^{-1/2},2^{1/2}], with multiplicative
  Fourier transform zero at i/2 AND 0, W_infinity(g*g*) >= Tr(theta(g)S theta(g)*).
- p3, (5)/Corollary2: with only the i/2 condition the bound has an additional
  -c|g_hat(0)|^2, 13<c<17. The text states: 'Sonin's trace requires, besides
  the zeros of the Riemann zeta function, an additional contribution'.

Under u=e^t, d*u=dt, the multiplicative Fourier convention in AppendixA
becomes exactly int G(t)e^{-izt}dt, with G(t)=g(e^t). The support interval
becomes |t|<=(log2)/2; G's autocorrelation has support in [-log2,log2].
The pole-annihilating condition is at i/2 (and its involution partner),
not the real frequency0; the EXTRA zero at0 is a separate condition.
This is why the two fiber/pole conditions cannot simply be said to pay the
whole displayed correction. The paper's W_infinity is minus the single
archimedean local distribution. Our W in S22 is the full zero-side Weil
functional with pole and all-prime terms. Outside the paper's support class,
those terms return and cannot be omitted.

The finite construction differs at a precise object: C is minus intersection
on the finite-dimensional primitive numerical divisor space of Xbar x Xbar,
and S17 gives an EQUALITY with all algebraic reciprocal zero moments. The
cited Sonin construction is an infinite-dimensional compressed scaling
representation with a restricted-support inequality and an explicit correction;
it is not identified there as that primitive divisor pairing for a curve.
The p3 analogy between annihilating poles and selecting H^1 does not give
an isometry or an equality of these forms. An equality for an independently
defined function-field Sonin construction is NOT VERIFIED by this source;
no theorem excluding every such construction is claimed.

Thus SIBLING2 IF_A ('their compression IS number-field D_x, only fibers
remain') does not follow. The exact remaining object is a source-defined
pairing realizing FULL W on all K_a, with the archimedean correction and
prime terms accounted for. One may instead define a function-field Sonin
space and test an exact intertwining map, but this cited paper alone supplies
neither that map nor its equality to S17. Stop this shortcut here. No new
Proshka request is justified merely by the shared word 'Frobenius'.

## S12. Review and result scope

Attempt1 supplies the two all-genus finite identities S16/S17 and the fully
normalized continuous restatement S18-S23. The original Q1/Q2 finite theorem
is S1-S14. These are PAPER candidates pending independent review on the
extended exact bytes; the existing PASS1 covered only S1-S8 and found one
WORDING locator defect, corrected with F_Phi=(A/I)F_f, not A*F_f.
No additional numerical run or Proshka request was needed. The Sonin-to-Hodge
identification remains unverified as specified in S11; it is not promoted
by the continuous identity. RH, SL20/DN20 and production admission remain open.
