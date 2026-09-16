# Source-generated reflection spaces: a negative direction and a positive carrier mismatch

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed R1--R12.
SOURCE_BASE: f736bbe6feff383bd8fc76b72cc5a7cab031fe27.
Original all-finite complex V positivity and RH remain open.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated research only.

## 1. Return point and exact candidates

The previous C1--C18 report straightens conditional projections but does not
improve the original scalar flux. Its radial rigidity cannot imply sign by
itself. Here we test two specific reflection constructions on the actual
source-generated signal family, not on arbitrary odd functions.

Read inputs under docs/Codex:

- REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md, (1)--(8): full
  measure, two-factor likelihood, physical weight and unchanged V;
- REPORT_2026-09-13_BROWNIAN_PRIMITIVE_FORM.md, B8: the normalized full-V
  correlation tends to sech(d) at either end, for each fixed offset d;
- REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md, A1--A2: the
  all-rank positivity continuation lemma and actual V analyticity;
- REPORT_2026-09-15_WEIL_ROSATI_TRANSFER_AUDIT.md, sections 2--3:
  inversion and total nonnegativity are not positive Hermitian pairings;
- REPORT_2026-09-17_CONDITIONAL_CONNECTION.md, C8--C18: complete
  conditional geometry and scoped radial compatibility.

Also read NULLVAR, equations (8)--(17), for both complete h series and
endpoint bounds. Source hashes are retained in the accompanying certificate.
No new external theorem or numerical sign test is used. The local mgrep
reflection-positivity query failed with exit 1: JWT token expired, login
required. Search coverage is INCOMPLETE, not a no-hit or absence result.

Keep U=sum Exp(1)/(pi n^2), h its positive density, r=h*h,
Phi(X)=exp(5X/2)r(exp(2X)), A=||Phi||_2, Z=integral Phi, f=Phi/A.
The source is even and strictly positive, with complete double-exponential
tails. The original interval is I=(-log(2)/2,0).

For a=exp(2x), t=exp(2X), s=u/t, the exact likelihood and conditional law are

    g_x(X,s)=a^(9/4) h(ats)h(at(1-s))/(h(ts)h(t(1-s))),
    p_X(s)=t h(ts)h(t(1-s))/r(t).

The target remains

    V(x,y)=integral_0^infinity (2X+x+y)f(X+x)f(X+y)dX.   (R1)

## 2. Inversion remains indefinite on two actual projected signals

Let dnu_X=Phi(X)dX/Z, Jv(X)=v(-X), and

    m_x(X)=f(X+x)/f(X).

These are exactly the conditional means of the two-factor g_x. For x in
a neighborhood of zero contained in (-log(2)/2,log(2)/2), m_x lies in
L2(nu_X), and x -> m_x is continuously differentiable there. Indeed the
full tails of f and its derivatives provide integrable majorants for
f(X+x)^2/f(X) and f'(X+x)^2/f(X): choose delta<log(2)/2, so the leading
double-exponential coefficient 2exp(-2delta)-1 is strictly positive.
Polynomial factors in exp(2|X|) are harmless. Compact X causes no issue.

At zero, m_0=1 and m'_0=q=f'/f. Since f is even, Jq=-q; moreover

    0<I_rad=integral q(X)^2 dnu_X<infinity.

Strict positivity follows from the nonconstant positive source. Set

    v_h=(m_(-h)-m_(-2h))/h, h>0.

Differentiability in L2 gives v_h -> q. J is unitary, so

    <v_h,Jv_h> -> -I_rad<0.                            (R2)

For every sufficiently small h, -h and -2h are admissible nodes. Thus
inversion's reflected form is negative on the span of two actual projected
likelihoods. The previous arbitrary-odd-function obstruction is not cured
by restricting to the natural source-generated signal span. This is not
a negative V row; it excludes this reflected pairing as V's positive
realization. The full target's two-node positivity remains intact.

## 3. Copy exchange is positive on the full likelihood family

Exchange u and v in the original two-energy space. Both the probability
measure and the physical weight are symmetric, and every g_x is symmetric.
Hence the reflected pairing on their span is their ordinary positive Gram
kernel

    K(x,y)=integral_0^infinity f(X)^2 E_(p_X)(g_x g_y)dX. (R3)

This is the complete physical weight, not its first mode or an unweighted
surrogate. Its diagonal is positive. We next check an exact identity to V,
allowing arbitrary nonzero node normalizations.

In fact R3 is well defined for ALL x,y<0, not only I. Changing variables
u=ts, v=t(1-s), T=u+v, retains the exact sharp cutoff T>=1 and gives

    K(x,y)=(ab)^(9/4)/(2 A^2)
      * integral_(u,v>0,T>=1) T^(3/2) r(T)
        h(au)h(av)h(bu)h(bv)/(h(u)h(v)) du dv.          (R4)

Use h(u)=2pi exp(-pi u)chi(u), 0<chi<=1 nondecreasing, chi->1, and
r(T)=4pi^2 exp(-pi T)J(T), J(T)<=T, J(T)/T->1.
For 0<a,b<=1, monotonicity gives h(au)/h(u)<=exp(pi(1-a)u).
Alternatively the two exact endpoint series directly show convergence
of R4: at infinity its total exponential decay is exp(-pi(a+b)T);
at either zero endpoint the reciprocal exponent has positive coefficient
(1/a+1/b-1). The polynomial weights are integrable against these bounds.

R4 is holomorphic in x,y on

    Omega={z: Re z<0, |Im z|<pi/6}

in each unbarred variable. For a=exp(2z) in this set, Re a>0 and
Re(1/a)>1/2. On compact pairs the complete small-argument series give
Re(1/a+1/b)-1 bounded strictly away from zero; the large-argument series
give Re(a+b)>0 uniformly. Applying these bounds to R4 gives an integrable
common majorant. Thus the integral is jointly holomorphic. This also
justifies local real analyticity of its strictly positive diagonal.

## 4. Exact limiting overlap of this positive carrier

Fix d real and kappa=exp(2d)>0. Put b=kappa a and let a decrease to zero.
In R4 substitute (u,v)=(U/a,V/a) and write T=U+V. Then exactly

    K(x,x+d)=kappa^(9/4)/(2 A^2)
      * integral_(U,V>0,T>=a) T^(3/2)
        [a J(T/a)/(chi(U/a)chi(V/a))]
        h(U)h(V)h(kappa U)h(kappa V) dU dV.             (R5)

For fixed U,V>0 the bracket tends to T. When a<=1, J(T/a)<=T/a and
chi(U/a)>=chi(U), chi(V/a)>=chi(V). Therefore the integrand in R5,
apart from its fixed prefactor, is bounded by

    4pi^2 T^(5/2) exp(-pi T) h(kappa U)h(kappa V),

which is integrable: h is bounded and decays at infinity. This pays the
full limit with the cutoff included, by dominated convergence.

Define finite positive numbers

    L(kappa)=kappa^(9/4) integral_(U,V>0) (U+V)^(5/2)
                     h(U)h(V)h(kappa U)h(kappa V)dU dV.

Then the normalized overlap has the exact limit

    lim_(x->-infinity) K(x,x+d)/sqrt(K(x,x)K(x+d,x+d))
          =L(kappa)/L(1)=:C(d).                         (R6)

Both diagonal limits equal L(1)/(2A^2), regardless of the fixed d.
The corresponding already proved original-source limit is

    lim_(x->-infinity) V(x,x+d)/sqrt(V(x,x)V(x+d,x+d))
          =sech(d).                                    (R7)

## 5. The two limits cannot agree: a paid overlap bound

The full h endpoint asymptotics imply a global bound

    h(u)<=C exp(-alpha/u-beta u), u>0,
    alpha=pi/8, beta=pi/2, C finite.                    (R8)

At zero the gap between pi/4 and alpha absorbs u^(-5/2); at infinity
the gap between pi and beta absorbs the bounded prefactor. A positive
compact interval is covered by continuity.

For kappa>=1 set A_k=alpha(1+1/kappa), B_k=beta(1+kappa).
Since A_k/u+(B_k/2)u>=sqrt(2A_k B_k), R8 gives

    h(u)h(kappa u)
      <= C^2 exp(-sqrt(2alpha beta kappa)) exp(-beta u/2).

Apply this to U and V. The remaining integral of
(U+V)^(5/2)exp(-beta(U+V)/2) is Gamma(9/2)(2/beta)^(9/2).
Consequently, with a finite kappa-independent constant C_1,

    0<L(kappa)<=C_1 kappa^(9/4) exp(-c sqrt(kappa)),
    c=2sqrt(2alpha beta)>0.                             (R9)

In particular C(d)/sech(d) ->0 as d->+infinity, because
sech(d)=2sqrt(kappa)/(1+kappa). There exists a fixed positive d for which
C(d)<sech(d). No numerical choice of d is needed or claimed.

## 6. Node normalization and a positive tensor multiplier cannot repair it

Suppose first that V(x,y)=conjugate(eta(x))eta(y)K(x,y) on I, with nonzero
node factors. Normalized absolute overlaps remove these factors. Since
both real kernels have strictly positive entries, this would make their
normalized overlaps equal on I x I. Both are real analytic on the connected
negative quadrant, so equality extends to all x,y<0. R6--R9 contradict it.

More generally suppose

    V(x,y)=conjugate(eta(x))eta(y)K(x,y)M(x,y), x,y in I, (R10)

where M is an arbitrary PSD kernel. This is the Gram kernel produced by
adjoining independent positive auxiliary features by tensor product.
All diagonal M(x,x) are positive, because V and K have positive diagonal.
After normalizing, the explicit ratio

    R(x,y)=[V(x,y)/sqrt(V(x,x)V(y,y))]
             /[K(x,y)/sqrt(K(x,x)K(y,y))]               (R11)

must be PSD on I: it is the normalized M after unit-modulus node factors.

For any compact negative interval J, V and K are holomorphic near
J x J. Their diagonals and all real K(x,y) are strictly positive.
Compactness permits a sufficiently thin complex rectangle around J
whose product has no K zero, and on which both diagonal square roots
extend from their positive branches. Thus R11 is holomorphic on that
product. The accepted A1 positivity-propagation lemma extends its supposed
PSD from a fixed subinterval of I to any desired finite negative nodes.
In particular its diagonal is one and its two-node matrices require

    |R(x,y)|<=1 for every x,y<0.                        (R12)

Choose a fixed d with C(d)<sech(d). R6--R7 yield
R(x,x+d)->sech(d)/C(d)>1 as x->-infinity, contradicting R12.
Hence R10 is impossible even with an arbitrary PSD multiplier M on I.
No regularity of eta or of an initially given M was assumed: their
normalized product is forced to equal the analytic R11 on I.

This excludes the specified copy-symmetric likelihood Gram and independent
positive tensor additions. It does NOT exclude a different source-defined
map, a nonlocal operator mixing the signals/scales, a direct sum with other
fields, or positivity of original V. No negative row of original V follows.

## 7. Decision

The two simple source reflections fail at different exact places. Inversion
is already negative on two projected source signals. Copy exchange is
positive on the complete two-factor family, but its normalized interaction
loses the slow sech(d) coupling which original V retains at extreme scales.
Node rescaling and positive tensor additions cannot restore that coupling.

Do not dispatch another generic reflection-positive-carrier request using
these maps. A replacement using this carrier needs an actual nonlocal
intertwining map or a different full-energy identity; existence of a
positive carrier, and the new rigidity C15--C18, cannot supply that map.
This is a scoped transfer obstruction, not improved full-V sign control.

## Independent acceptance

Candidate SHA256: `0740c57d7804ad7d0bb616f21240eed52e61de2dda7945367b2a8389e9571615`.
Review SHA256: `abaa81804bbda7aca08a87786ec172bd95e4fd192ca701e98ec8f59e49af1a1b`.
Verdict: `ACCEPT_SPECIFIED_SOURCE_REFLECTION_OBSTRUCTIONS_ONLY`.
The parent independently recomputed the physical Jacobian, scaling,
complete integral majorant, exponential overlap bound and analytic
positivity continuation for the normalized quotient. The negative
far-shift two-node quotient test does not assert a two-node quotient
failure inside I: A1 gives an all-rank obstruction there without a rank
bound. Full V positivity and RH remain open. The review is embedded in
the paired certificate; no Lean or canonical admission is claimed.
