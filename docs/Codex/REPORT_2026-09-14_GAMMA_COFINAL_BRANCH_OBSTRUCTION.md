# Branch obstruction for the reciprocal finite-gamma family

STATUS: INDEPENDENTLY_REVIEWED_PAPER_RESULT; COAUTHOR_AUDIT_PENDING.
SOURCE: gamma reciprocity bridge at 65c4a563ce4319a595a17e7c264dbbd77f1672e1,
SHA256 7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; no RH or canonical admission.

Proposed result: for every integer N>=13 the exact auxiliary transform M_N
has infinitely many nonreal zeros. If the proof below survives review, the
cofinal real-zero criterion for this particular family is unavailable, even
though its analytic convergence to the actual xi function remains correct.
This is not a negative witness for the actual theta form and does not refute
RH. No numerical zero search, quadrature, or finite-grid sign test is used.

The semantic return from the scalar-lift failure is to the geometric square
root itself: it preserves the real source limit, but may create algebraic
branch points in the complex source variable. The worked mechanism is a
contour shift to the nearest branch points, Watson endpoint asymptotics,
Jensen's formula to count real zeros, and Hadamard factorization to compare
that count with growth on the imaginary axis. All four maps are spelled out.

## B1. The relevant finite exponential polynomial

Fix N>=13 and lambda_n=pi n^2. The Laplace transform of r_N is
product_(n=1)^N [lambda_n/(z+lambda_n)]^2. Partial fractions at its distinct
double poles give the entire continuation

    r_N(t)=sum_(n=1)^N (d_n t+e_n) exp(-pi n^2 t),
    d_n=lambda_n^2 product_(m!=n)[lambda_m/(lambda_m-lambda_n)]^2
       =4pi^2 n^4 (N!)^4/[(N-n)!(N+n)!]^2 >0.          (B1)

The constants e_n are real; their values will not be needed. Write

    D_N(w)=sum d_n w^(n^2)=w P_N(w),
    P_N(w)=sum d_n w^(n^2-1),
    E_N(w)=sum e_n w^(n^2).

Then r_N(t)=t D_N(exp(-pi t))+E_N(exp(-pi t)).
The coefficient ratios satisfy

    d_2/d_1=16[(N-1)/(N+2)]^2 >=256/25,
    d_n/d_2 <= n^4/16,  n>=3.                          (B2)

The second inequality follows by writing the extra factorial ratios as
product_(j=2)^(n-1)[(N-j)/(N+j+1)]^2 <=1.

## B2. A simple negative root of P_N inside the unit disk

Put r=1/2. In P_N(-r), even n give negative terms and odd n positive ones.
Using (B2), dropping the negative terms n>=4, and bounding the odd tail by
all n>=5,

    P_N(-1/2)/d_2
      <=25/256-1/8+81/4096
                         +sum_(n>=5) (n^4/16)2^(-(n^2-1))
      <=-31/4096 +(256/255)625/2^28 <0.                 (B3)

For the last bound the ratio of consecutive positive tail terms is at most
(6/5)^4 2^(-11)=81/80000 <1/256.
As P_N(0)=d_1>0, a negative root w_0=-r_0 exists with 0<r_0<1/2.
It is simple: for every 0<r<=1/2,

    (d/dr)P_N(-r)/(3d_2 r^2)
       <=-1+(27/2)r^5
          +sum_(n>=5) [(n^2-1)n^4/48] r^(n^2-4)
       <=-1+27/64+(256/255)625/2^22 <0.                (B4)

The ratio of consecutive terms in the latter tail is at most
(35/24)(6/5)^4 2^(-11)=189/128000 <1/256. Thus the real root is simple.
For transparency the positive rational margins in (B3) and (B4) are,
respectively, 404611/53477376 and 482947/835584. These are exact rational
inequalities, not a numerical approximation to a zero or integral.

## B3. Simple zeros of r_N in Re(t)>0, and nonremovable square roots

Let sigma=-log(r_0)/pi>0, t_j=sigma+i(2j+1). Then exp(-pi t_j)=w_0.
For t=t_j+zeta in a fixed small disk about t_j,

    r_N(t)/t = D_N(w_0 exp(-pi zeta))
                         + E_N(w_0 exp(-pi zeta))/(t_j+zeta).

The first term has a simple zero at zeta=0; the second converges uniformly
to zero as j->infinity. Rouche's theorem on a sufficiently small fixed
circle, followed by the local simple-root estimate, gives exactly one
simple zero t_j^*=t_j+O(1/j). In particular Re(t_j^*)>0 for large j.
At zero, r_N(t)=c_N t^(2N-1)(1+O(t)) with c_N>0, so r_N has no nonzero
zeros in a fixed punctured disk. Thus r_N(1/t_j^*)!=0 for large j.

Let x_j=(1/2)Log(t_j^*) using the principal logarithm. Then
0<Im(x_j)<pi/4 and the entire function

    F_N(x)=r_N(exp(2x))r_N(exp(-2x))

has a simple zero at x_j. Its square root G_N, continued from the positive
real axis, therefore has a genuine algebraic branch point there. Conjugation
provides such a point below the real axis as well. This step specifically
checks that reciprocal pairing does not cancel the branch.

## B4. Only finitely many singularities in every strictly smaller strip

For any fixed b<pi/4, the finite exponential polynomial (B1), uniformly in
|Im(x)|<=b as Re(x)->infinity, gives

    r_N(exp(2x))=(d_1 exp(2x)+e_1)exp(-pi exp(2x))(1+o(1)),
    r_N(exp(-2x))=c_N exp(-2(2N-1)x)(1+o(1)).          (B5)

Indeed Re(exp(2x))>=cos(2b)exp(2Re(x)), so all higher rates are uniformly
suppressed. Both factors are nonzero outside a sufficiently large compact
rectangle. By reflection the same holds at Re(x)->-infinity. Hence F_N has
only finitely many zeros in that closed strip. It has none on the real axis.

By B3 there is an odd-order zero at distance less than pi/4 from the axis.
Consequently the smallest such distance a is positive and attained by a
finite nonempty set of lower-half-plane zeros

    x_l=b_l-i a,  l=1,...,L, with distinct real b_l.

Choose epsilon>0 so a+epsilon<pi/4 and no other odd-order zero lies between
those zeros and Im(x)=-(a+epsilon). Even-order zeros are removable for the
analytic square root and need no cut. Continue G_N into this lower strip
with vertical cuts from each x_l down to its lower boundary. On this slit
strip it is holomorphic and has the uniform double-exponential tail bound

    |G_N(x+iy)|<=C exp(C|x|-c exp(2|x|)),               (B6)

away from the finite cuts; the corresponding boundary values obey the same
bound. This follows directly by taking the modulus of the square root of
(B5). All constants here may depend on the fixed N, a and epsilon.

## B5. Contour asymptotics in every fixed spectral horizontal band

Let an odd zero at x_l have multiplicity 2m_l+1. In a local branch,

    G_N(x)=c_l(x-x_l)^alpha_l(1+O(x-x_l)),
    alpha_l=m_l+1/2,  c_l!=0.

Move the Fourier contour down to Im(x)=-(a+epsilon), retaining the two
banks of each vertical cut. The vertical sides at Re(x)=+/-R tend to zero
by (B6). Each cut contribution has the form

    exp(-iz x_l) integral_0^epsilon exp(-z t) J_l(t)dt,
    J_l(t)=k_l t^alpha_l(1+O(t)),  k_l!=0.              (B7)

Orientation and the square-root jump are absorbed into k_l; its nonzero
value follows from odd monodromy. Local cuts can be shortened and their
remaining segments included in exponentially smaller errors. Watson's
lemma, or direct scaling t=u/z with a Taylor remainder estimate, now gives
k_l Gamma(alpha_l+1) z^(-alpha_l-1) times exp(-iz x_l).
The lower horizontal integral is exponentially smaller. These estimates
are uniform as Re(z)->infinity with |Im(z)|<=B, for each fixed finite B:
(B6) controls the horizontal integral and exp(B|Re(x_l)|) is a constant.

With alpha=min_l alpha_l, after division by the positive constant Z_N,

    exp(a z) z^(alpha+1) M_N(z)=P(z)+O(1/Re(z)),        (B8)
    P(z)=sum_(alpha_l=alpha) C_l exp(-i b_l z),
    C_l!=0.

The principal power of z is holomorphic and nonzero in Re(z)>0. Higher
alpha_l differ from alpha by positive integers; this gives the stated
O(1/Re(z)) remainder. Distinct b_l ensure P is not identically zero.
This is an explicit application, not an inference from a picture of zeros.
For the endpoint method see NIST DLMF 2.4(i), equation 2.4.1, and 2.3(ii).
The contour construction and all input hypotheses needed here are above.

## B6. There are only O(T) real zeros

Write U(z)=exp(a z)z^(alpha+1)M_N(z), holomorphic for Re(z)>0.
There are constants L_0,c>0 such that every real interval [A,A+L_0]
contains a point s with |P(s)|>=c. To prove this, integrate |P|^2: the
diagonal part is L_0 sum|C_l|^2, while the cross terms are bounded by
sum_(l!=j)2|C_l C_j|/|b_l-b_j| independently of A. Choose L_0 large enough
that the diagonal exceeds twice that bound.

For large A, (B8) gives a point s in that interval with |U(s)|>=c/2.
On the disk of radius 2(L_0+2) about s, U is bounded above by a constant
independent of A: use (B8) uniformly in that fixed horizontal band and the
boundedness of the finite exponential sum there. Jensen's formula bounds
the number of zeros in the concentric disk of radius L_0+2 by a fixed
constant, independent of A. That disk includes [A,A+1]. Thus the number of
positive real zeros up to T, counted with multiplicity, is O(T).
Evenness gives the same conclusion for all real zeros. The bounded initial
segment contains finitely many zeros because M_N is entire and M_N(0)=1.

## B7. Growth forbids all but finitely many zeros being real

The real-tail bound in G4 implies

    log max_(|z|<=R)|M_N(z)|=O(R log(R+2)),              (B9)

so M_N has order at most one. Conversely the fixed-N tail in G6 gives
G_N(x)>=c exp(-A exp(2x)-B x) for all sufficiently large positive x.
Integrate exp(Tx)G_N(x) over
[(log T)/2, (log T)/2+1] to get

    log M_N(iT)>=(T/2)log T-C T-C log T.               (B10)

Suppose only finitely many zeros of M_N were nonreal. Hadamard factorization
for an even entire function of order at most one, grouping opposite roots,
then gives

    M_N(z)=P_0(z) product_(rho_j>0)(1-z^2/rho_j^2),    (B11)

up to a nonzero constant absorbed into the even polynomial P_0. All
nonreal roots are in P_0, with multiplicities. There is no linear exponential
factor, by evenness. There is no root at zero. The paired product converges
since the real zero count is O(T). For its logarithmic growth on iT,

    sum_j log(1+T^2/rho_j^2)=O(T),                     (B12)

as follows by Stieltjes integration with n(t)<=C(1+t), using separately a
fixed interval below the first positive root. The finite polynomial adds
only O(log T), contradicting (B10). Thus M_N has infinitely many nonreal
zeros for every N>=13, provided B1--B6 withstand independent review.

This conclusion excludes every unbounded real-zero subsequence of this
specific geometric finite-gamma family. It leaves M_2 through M_12 undecided
and does not alter the proven N=1 Bessel case. The convergence to xi remains
true: nonreal zeros can move with N, and no zero of the limit off the real
axis has been supplied. Full V, IC, ODD2 and RH remain OPEN.

## B8. Fixed Gaussian multipliers do not repair the obstruction

For every fixed real h, replace G_N(x) by exp(h x^2)G_N(x), with its positive
integral as normalization. For N>=13 its Fourier transform again has
infinitely many nonreal zeros. The multiplier is entire and nowhere zero,
so all branch points and their orders in B3--B5 are unchanged. On each
horizontal source strip it adds at most exp(|h|x^2+C), still dominated by
the double-exponential tail. Thus the fixed spectral-band asymptotic in equation (B8) and
B6's real-zero count apply without change, with different nonzero constants.
The imaginary-axis lower bound loses at most O_h((log T)^2), which is o(T),
and the maximum-modulus upper bound is still O_h(R log(R+2)). The Hadamard
contradiction therefore repeats for this fixed h.

No finite choice h=h_N for each N can provide a cofinal all-real-zero family
by this multiplication. This excludes only the stated Gaussian multiplication
of this auxiliary family, not arbitrary source deformations or a conclusion
about the de Bruijn--Newman constant of the actual xi function.
