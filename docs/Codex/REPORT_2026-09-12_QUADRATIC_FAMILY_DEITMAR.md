# A quadratic-character family: actual cutoffs, Hodge input, and Deitmar traces

STATUS: PAPER_CANDIDATE_PENDING_INDEPENDENT_REVIEW.
PX_RH_CLAIM: NOT_MADE. No Lean or production admission.
SOURCE_BASE: 7653a3503d20be4dba91a333ff96e5eea30c738c.

This extends the explicit F9(t) example to a stated family. It does not cover
all Hecke characters, arbitrary base curves, or number fields. No novelty claim
is made. It uses the Hodge index theorem as a genuine geometric input and
derives the needed root bound; it does not cite the finite-field RH as a
premise. It identifies the localized image cutoff, not the whole Q with a
Neron-Severi space. The comparison for the other Q is a trace comparison.

## 1. The exact family and conclusion

Let q be an odd prime power with q congruent1 modulo4. Let D in Fq[t] be monic,
squarefree of odd degree 2g+1, with g>=1. Let X be the smooth projective curve
with affine equation y^2=D(t). It is geometrically integral and has genus g;
the map to P1 has the 2g+1 finite geometric branch points and infinity,
all tame, so the genus follows from Riemann-Hurwitz. Its unique point at
infinity is Fq-rational. The base global field is k=Fq(t), genus0.

Let chi be the quadratic idele-class character constructed in section2.
Its conductor has degree 2g+2; hence 2g_k-2+f=2g. Fix R>=0, and let S
contain infinity, all irreducible factors of D, and every place of degree
at most R. The assertions below concern this chi-component and finite
linear combinations of tests h_m, |m|<=R.

Use pi with component t at infinity and1 elsewhere, so |pi|=q and chi(pi)=1.
Write x=a pi^n on C_S, a in its compact norm-one subgroup K_S. In Deitmar's
multiplicative measure, vol K_S=kappa=log q. Define

    (J xi)(a pi^n)=kappa^(-1/2)chi(a)xi_n,
    h_m(a pi^(-m))=q^(-m/2)kappa^(-1)conjugate(chi(a)),

with h_m zero outside that shell. Thus J* U(h_m)J=V^m, where
(V xi)_n=xi_(n-1); U(h_m) vanishes on the other compact characters.

For N>=g, let S_N project onto the indices -N,...,N. We prove

    J* barQ_(S,q^N,0) J = S_N-R_N,       rank R_N=2g,        (A)

where R_N is the orthogonal projector onto the confluent Mellin root
conditions of L(chi,q^(-1/2)z^(-1)). The normalized roots lambda_j have
modulus1 by the geometric proof in section5. Consequently

    lim_N Tr(R_N V^m)=sum_j lambda_j^m   (m>=1),            (B)

with multiplicities. For every fixed h=sum_(|m|<=R)c_m h_m,

    Tr((Q_(S,q^N,0)-barQ_(S,q^N,0))U(h)) -> 0.             (C)

All normalizations and the zero-shift term are retained below.

## 2. Elementary construction of the genuine character

For a monic irreducible P let eta_P be the quadratic character of its residue
field F_(q^degP), extended by0. Let eta be the one on Fq. Since q is1 modulo4,
eta_P(-1)=1 for every P. Set

* P dividing D: chi_P(P^e u)=eta_P((D/P) modP)^e eta_P(u modP).
* Finite P not dividing D: chi_P is unramified with chi_P(P)=eta_P(D modP).
* Infinity, s=1/t: chi_infty(s^e u)=eta(u(0)).

The products are trivial on k*. To check this it suffices to check constants
and monic irreducible polynomials. For constants c the finite ramified product
is eta(c)^(degD)=eta(c), and infinity gives a second eta(c).
For an irreducible A not dividing D, the A factor eta_A(D modA) equals the
product of the ramified factors eta_P(A modP). Indeed both equal the quadratic
character of the corresponding resultant/norm; swapping the resultant order
adds only a sign, which is a square. Their product is1, and the monic infinity
factor is1. For A=P dividing D, the own factor eta_P(D/P) equals the product
eta_Q(P) over Q dividing D/P by the same resultant identity. Their product
is1. Other factors and infinity are1. This proves the global character claim.

Every ramified finite factor and infinity has conductor exponent1: its unit
character is nontrivial, but trivial on principal units. The conductor degree
is degD+1=2g+2. The compact character is nontrivial.

For monic A put

    chi_D(A)=product_(P|D) eta_P(A modP).

Then the Hecke Euler product is exactly the polynomial Dirichlet series
L(u)=sum_(A monic) chi_D(A)u^degA. For degree n>=degD, monic polynomials
are uniformly distributed modulo D. The sum of chi_D over that residue ring
is0 by CRT and the nontrivial residue characters. Thus

    L(u)=1+a_1u+...+a_(2g)u^(2g),                           (D)

initially with a possibly zero top coefficient. Section3 proves
|a_(2g)|=q^g, so the degree is exactly2g. All coefficients are real integers.

## 3. Actual source vector, its Fourier transform, and the leading coefficient

Take the global additive character from the differential dt, with self-dual
local additive Haar measures. In Deitmar's notation n(P)=0 at finite places
and n(infty)=-2; vol(O_v)=q_v^(-n(v)/2).
Set e_v=chi_v^(-1)1_(O_v*) at the ramified places (including infinity),
and e_v=1_(O_v) at every other place. Put e=product e_v.
It is Schwartz-Bruhat and has e(0)=e-hat(0)=0; the integral at any ramified
factor vanishes by its nontrivial unit character.

For a tame unit character, the elementary Gauss-sum Fourier calculation gives
exact support v(y)=-n(v)-1 and constant absolute value

    |e-hat_v(y)|=q_v^(-(n(v)+1)/2).

For clarity: the finite place support is valuation-1 with amplitude q_v^-1/2;
infinity support is valuation1 with amplitude q^1/2. The latter uses
vol O_infty=q, not1. An unramified finite 1_O is self-dual. Hence

    supp e: |x|<=1,
    supp e-hat: |x|<=q^(2g),                              (E)

and on the outer Fourier shell the product amplitude is q^-g. These bounds
are exact. The local calculation follows by averaging over1+P to force the
valuation, then applying |sum_(a in F_v*) eta_v(a) psi_v(a)|=sqrt(q_v).
That Gauss-sum modulus follows by squaring and character orthogonality; no
statement about zeta zeros is involved.

Define E(f)(x)=|x|^(1/2)sum_(gamma in k*) f(gamma x).
At x=1, only gamma in Fq* contribute and all values equal1, so E(e)(1)=q-1.
At y=pi^(2g), the Fourier outer-shell conditions force gamma=c/D, c in Fq*.
To see uniqueness, at each P|D its valuation must be-1, at infinity gamma y
must have valuation1, and all other finite valuations must be>=0. The degree
condition leaves all other valuations zero. On P1 these conditions specify
c/D. The product of unit characters under scaling by c is chi(c)=1, so all
q-1 terms agree; none is zero. Consequently

    |E(e-hat)(pi^(2g))|=q^g (q-1)q^-g=q-1.

Poisson summation, with the two zero conditions, gives
E(e)(pi^(-2g))=E(e-hat)(pi^(2g)). Directly summing the degree2g polynomials
on the left gives

    E(e)(pi^(-2g))=(q-1)q^-g a_(2g).

Therefore |a_(2g)|=q^g as asserted. This derives the normalization from the
actual source rather than assuming a functional-equation or RH conclusion.

At a general norm q^-n the same polynomial calculation gives
E(e)(pi^-n)=(q-1)q^(-n/2)a_n. Norm-positive shells are zero. In Mellin
coordinates this reads, up to one fixed nonzero Haar/coordinate constant,

    E(e) <-> L(q^(-1/2)z^-1).                             (F)

Write P(z)=z^(2g)L(q^(-1/2)z^-1)=product_(j=1)^(2g)(z-lambda_j).
It is monic with nonzero constant of absolute value1. Thus

    product_j |lambda_j|=1.                              (G)

## 4. The same curve gives the same source power sums

By unique factorization, as formal power series,

    [u^m] uL'(u)/L(u)
      =sum_(degP|m, P not dividingD) degP chi_P(P)^(m/degP)
      =sum_(a in F_(q^m)) eta_m(D(a)).

The second equality follows by grouping elements by their irreducible minimal
polynomial: a degree-d orbit contributes d times its residue character raised
to m/d. Ramified elements contribute0. Counting the two-sheeted affine fibers
and the one point at infinity gives

    #X(F_(q^m))=q^m+1+sum_a eta_m(D(a)).

Since (D) factors as product_j(1-sqrt(q)lambda_j u), we obtain exactly

    p_m:=sum_j lambda_j^m
        =q^(-m/2)(q^m+1-#X(F_(q^m))).                    (H)

This is the explicit source-to-curve dictionary. It uses no assumed location
of the roots and no substitution of the genus of X for the base genus.

## 5. Hodge is the additional sign-producing input

Use the primitive projection of Frobenius graphs on XxX. With H,V the two
fiber classes, p(Γ)=Γ-(Γ.V)H-(Γ.H)V. Hodge index makes the negative
intersection pairing positive definite on their orthogonal complement.
Set gamma_m=q^(-m/2)p(Γ_(Frob^m)). The intersection calculation gives

    ||gamma_m||^2=2g,
    <gamma_0,gamma_m>=p_m.                               (I)

This is Hallouin–Perret, Theorem1 and Lemma3, printed pages5–6, with their
primitive projection and our explicit q^-m/2 normalization. Their later
unit-norm gamma convention has an additional sqrt(2g); it is not used here.
The underlying self-intersection is Γ_m^2=(2-2g)q^m, so its primitive
self-intersection is -2g q^m. This also avoids importing a typographical
self-intersection slip in the displayed proof text of the preprint.

Cauchy–Schwarz in this genuine positive space yields |p_m|<=2g for every m.
Here is a direct algebraic-analytic extraction of the root bound. The series
sum_(m>=1) p_m w^m is holomorphic for |w|<1 by that bound. Near w=0 it equals

    sum_j lambda_j w/(1-lambda_j w).

If a root had |lambda|>1, this rational function would have a pole inside
the unit disk at1/lambda. Its multiplicity coefficient is a positive integer,
so equal roots add residues and distinct roots cannot cancel that pole.
Analytic uniqueness contradicts the holomorphic series. Thus all |lambda_j|<=1.
Combining with(G) gives

    |lambda_j|=1 for every j.                             (J)

This is where geometry pays the missing inequality. Positivity of the cutoff
projector, its rank, and polynomial division do not replace(I).

## 6. Exact global and localized cutoff image

For any Schwartz-Bruhat f with f(0)=f-hat(0)=0 and both norm supports<=q^N,
Poisson gives E(f) norm support in[q^-N,q^N]. The Tate–Mellin identity in
Connes AppendixI Lemma3 factors its chi-component Mellin transform as
c L(chi,s) Delta'_s(f), c nonzero, with Delta'_s holomorphic for Re s>0.
By(J), every normalized root corresponds to Re s=1/2. Differentiating through
its full multiplicity shows that F_xi(z) vanishes to the same order there.
The finite-dimensional closure preserves these jet conditions.

Conversely let e_j(x)=q^(-j/2)e(pi^-j x). Then E(e_j)=V^j E(e), and(E) gives

    supp e_j norm<=q^j,
    supp e-hat_j norm<=q^(2g-j).

Both are<=q^N exactly when 2g-N<=j<=N. Their M-2g Mellin polynomials, M=2N+1,
are nonzero constant multiples of z^(j-2g)P(z). They form a basis of every
Laurent polynomial on[-N,N] divisible by P: its quotient has exponents
between -N and N-2g. Thus they fill the full jet kernel, with no N shift.

For barE_S, extend a source by1_O outside S. Because the additive conductor
is supported at infinity, this extension preserves both supports and both
zero conditions, and the global E equals barE_S under Deitmar Lemma2.2.
All e_j already factor in this way. We have both inclusions and therefore(A).
The norm-one group has no extra Pic0 characters for P1; this also makes the
unit-character coordinate J the specified entire chi-component.

## 7. Both traces and the zero-shift term

Apply the independently checked finite Mellin-defect trace lemma in
REPORT_2026-09-12_DEFECT_TRACE_ROOTS.md. It handles confluent roots and fixed
shift m. By(J), its outside-root reflection case is absent and(B) follows.
For m nonzero, Tr(S_N V^m)=0, so

    Tr(barQ U(h_m)) -> -p_(|m|).

For negative m use self-adjointness of R_N and the reality of p_m from(H).
Deitmar Theorem3.1 evaluates the other projector Q. For m nonzero, h_m(1)=0
and both pole averages vanish by the nontrivial compact character. Each
unramified place of degree d dividing |m| contributes

    d q^(-|m|/2) chi_P(P)^(|m|/d).

Every such place is in S. The ramified-place integrals average to0 over
units. For negative m the denominator |u-1| and test amplitude give the
same factor, since chi is quadratic. The Euler/logarithmic identity in
section4 says the total is -p_(|m|). The theorem therefore gives

    Tr(Q U(h_m))=-p_(|m|)+o(1).

Subtracting proves(C) for m nonzero. For m=0 use Deitmar's exact compact-
invariant-space bijection in section6. Take the compact open subgroup
C=ker(chi|O_S*) in A_S*. Its image is the kernel of chi in K_S because a
degree-zero S-divisor on P1 is principal. The bijection commutes with the
compact group, and so preserves the chi-isotypic dimensions. Both traces
selected by h_0 are therefore exactly M-2g in this chi-component.
Linearity proves(C) for the stated finite tests.

## 8. Verified source boundaries and what is still open

Primary sources read in this task; the Hodge intersections and Deitmar Haar
normalization were reread for this argument:
- Hallouin–Perret https://arxiv.org/pdf/1409.2357, Theorem1/Lemma3,
  primitive projection and intersections, printed pp5–6. PDF SHA256
  92e76be3eefbd7af38b6dc035c28d0166390324675087b049b545098ff22736e.
- Deitmar https://arxiv.org/pdf/math/0111108, definitions, Haar normalization,
  Lemma2.2, Theorem3.1 and section6. PDF SHA256
  7080383fb5c197e9b71d60ce5a8f3865fdc19964f243386a8593f1849674422c.
- Connes https://arxiv.org/pdf/math/9811068, AppendixI Lemma3 and its
  normalized Mellin-factor holomorphy, printed pp51–59. PDF SHA256
  dfd4e9924d8980f82e3da11fdea861d318fda8f5c7ba57ee659baf8631975053.

The finite-field character/resultant argument, Fourier leading-coefficient
calculation, point-count/Euler identity and polynomial root argument are
spelled out above. Riemann-Hurwitz and Hodge index are classical geometric
theorem inputs, not Lean theorems supplied by this package.

Still open: all other Hecke components/base curves; an archimedean image/defect
identification; a source-preserving number-field geometric inequality; the
full SL20/DN20 sign and classical RH. The proof explicitly needs geometric
positivity(I); it neither derives that positivity from a cutoff projection
nor turns the numerical constant c in(13,17) into a defect dimension.
The overall SIBLING5 request remains partial.

## Parent exact finite-field controls

Two small integer enumerations over F5 checked coefficient/sign orientation:
D=t(t-1)(t+1) gives L=1+2u+5u^2; D=t^5-t gives
L=1-10u^2+25u^4. The enumeration used the character product in section2
on all monic polynomials only up to degree degD-1. Its outcomes agree with
|a_(2g)|=q^g. The general proof is sections2-7, not these finite checks.
For D=t(t-1)(t+1), the ramified uniformizer at t-1 has character
eta(D/(t-1) mod(t-1))=eta(2)=-1; this checks why those uniformizer
factors, absent in the special F9 example, must be retained.
The preliminary guessed +10 middle coefficient for t^5-t failed the exact
enumeration; the actual coefficient is -10. No part of the general proof
or leading-coefficient claim used that guess.

## Completed independent PAPER review

CURRENT_DISPOSITION: ACCEPTED_FOR_THE_STATED_QUADRATIC_CHARACTER_FAMILY.
The preceding candidate header records the creation state. The unchanged
preceding 14865 bytes have SHA256 80b1960b0c4d51a088ad2eeca443e28f3646983599f2cae8cf2921f8236c535c.
The read-only checker /root/sibling5_check independently confirmed this digest
and returned CLEAN. Its audit covered local characters/resultants, conductors,
Fourier supports and amplitudes, c/D uniqueness, leading coefficient, point
counts, Hodge root bounds, exact source-vector span, and both trace cases.
The final clarification explicitly restricts the m=0 trace to h_0-selected
chi. Parent separately checked the F5 controls printed above.

This is a source-dependent PAPER theorem for the stated family. It is not a
Lean certificate, canonical admission, general all-character Deitmar theorem,
number-field transfer, classical RH proof, or a novelty claim.
