# Actual ODD2 near the origin — interval-assisted PAPER candidate

Status: ACCEPT_ORIGIN_CORNER_ODD2_INTERVAL_ASSISTED_PAPER.
Consumer: actual ODD2 on a whole positive square near (0,0), including
arbitrarily close nodes, after removing the structural zero factors.
No global IC, global ODD2, higher-rank positivity, Lean or RH claim.

## Exact inputs and reproducibility

The same source f=Phi/A, A>0, full V and K=V(s,t)-V(s,-t) are used.
Smoothness, parity and all fixed derivative tails are inherited from the
accepted ODDCURV response, SHA256
3309c6fb3f5c3a0e20979c14b9a36471e753feed18a42017b4f211fafe6ea840,
and the accepted compact-localization proof, SHA256
ff3a515fd259b1e2b7e22d98f3aa0faba196e9217c65fa384ed666bcedc03648.

Numerical arithmetic is performed on raw Phi only to remove the common
positive A scale. A raw kernel derivative is A^2 times its actual f-kernel
derivative. A raw two-by-two determinant is A^4 times the actual one. The
normalization is restored explicitly in every mathematical conclusion.

Certificate script: certificates/ODD2_ORIGIN_JET_20260912.py,
SHA256 8faa791349fba23f76c9b2394f8c9bfd2a73c81b25f3f50ae109f05e4c34f1d1.
Output: certificates/ODD2_ORIGIN_JET_20260912.json,
SHA256 4c543719a6b2e8330be6b82a705470b4bfac425c07aed9db137b1083cf30ae07.
Reproduce with Python3 standard library only:

    python3 docs/Codex/certificates/ODD2_ORIGIN_JET_20260912.py --cells 131072

The emitted elapsed seconds may differ. Mathematical intervals must match
under the same decimal implementation, or independently enclose the target.
The recorded runtime is Python3.14.7, decimal precision40. No external
package, floating-point quadrature rule or sampled-sign inference is used.
One preliminary double-precision diagnostic and the inconclusive16384-cell
enclosure selected the final resolution; neither is evidence for the sign.

## 1. Exact derivative identities

Put F=Phi and I_j=integral_0^infinity v F^(j)(v)^2 dv, j=1,2,3.
Let k,a,b denote respectively the raw K_11(0,0), K_13(0,0), K_33(0,0).
Subscripts here count derivatives, not matrix entries. Directly,

    partial_s^r partial_t^q V(s,t)
      =integral_0^infinity [(s+t+2v) f^(r)(s+v)f^(q)(t+v)
          +r f^(r-1)(s+v)f^(q)(t+v)
          +q f^(r)(s+v)f^(q-1)(t+v)] dv.                 (1)

For odd q, the corresponding K derivative is twice this expression at
t=0. Evenness gives F'(0)=F'''(0)=0. Integration by parts, with the full
derivative decay at infinity, gives

    k=4I_1-2F(0)^2,
    a=-4I_2-2F(0)F''(0),
    b=4I_3-6F''(0)^2.                                    (2)

For the middle identity, integral v F'F'''=-I_2,
integral F F'''=-F(0)F''(0), and integral F'F''=0.
For the last identity, integral F''F'''=-F''(0)^2/2.
These explain all boundary terms and factorial-independent coefficients.

## 2. Full theta and integration-tail bounds

For v>=0, z_n=pi n^2 exp(2v), the exact series is

    F^(j)(v)=exp(v/2) sum_{n>=1} P_j(z_n) exp(-z_n),
    P_0=4z^2-6z,
    P_1=-8z^3+30z^2-15z,
    P_2=16z^4-112z^3+165z^2-75z/2,
    P_3=-32z^5+360z^4-1058z^3+1635z^2/2-375z/4.          (3)

They follow from P_(j+1)=(1/2-2z)P_j+2zP'_j. Let B_j be the sum of
absolute coefficients and nu_j=j+9/4. Use the deliberately loose rational
constant

    D_j=(16/15) B_j nu_j^ceil(nu_j).                       (4)

Indeed exp(v/2)<=z_n^(1/4), |P_j(z_n)|<=B_j z_n^(j+2), and
z^nu exp(-z/2)<=(2nu/e)^nu<=nu^ceil(nu) for z>=0, nu>=1.
The geometric bound n^2-1>=3(n-1), pi>3 and exp(3)>16 imply

    |F^(j)(v)|<=D_j exp[-pi exp(2v)/2].                   (5)

Let F_N^(j) be (3) truncated to n<=4. Since
n^2>=25+11(n-5) for n>=5, the same calculation proves

    |F^(j)(v)-F_N^(j)(v)|<=T_j:=D_j exp(-25pi/2), v>=0.  (6)

If M_j bounds |F_N^(j)| on [0,2], then the difference between the full
and truncated squared integrals over that entire interval is at most

    2(2M_j T_j+T_j^2),                                    (7)

because integral_0^2 v dv=2. For v>=2, v<=exp(2v) and (5) give

    integral_2^infinity v F^(j)(v)^2 dv
        <=D_j^2 exp[-pi exp(4)]/(2pi).                    (8)

The endpoint values F(0),F''(0) are likewise enclosed using (6). Thus all
theta modes and the entire infinite integration tail are included.

## 3. Arithmetic and whole-cell enclosure

All constants in the script are integers, exact decimal fractions, or
Fractions. Pi is enclosed by the alternating rational series for
16 arctan(1/5)-4 arctan(1/239), with60 and20 terms. In each alternating
series the true value lies between the partial sum and that sum plus the
next term. The Machin identity follows by the tangent addition formulas:
4 arctan(1/5)-arctan(1/239)=pi/4 in the first quadrant.

The B interval class directs every addition, multiplication and division
outwards through decimal ROUND_FLOOR/ROUND_CEILING. Squaring includes0
when its input interval contains0. Decimal exp is correctly rounded to
nearest; widening the endpoint result to its two adjacent representable
values gives an outward enclosure. This uses the documented contract of
[Python decimal](https://docs.python.org/3/library/decimal.html#decimal.Decimal.exp).
No noninteger Decimal power operation is used. Negation changes signs
exactly, without silently applying a lower default precision.

Partition [0,2] into131072 equal dyadic intervals. On each entire interval,
evaluate (3) for n<=4 by interval Horner arithmetic and exp. Multiplying
the enclosure of v F_N^(j)(v)^2 by the exact interval width bounds that
cell's integral. Sum with directed arithmetic. The maxima M_j in (7) are
upper bounds over these same complete cells. Then add (7) and (8), rather
than treating a finite truncation or Simpson convergence as proof.

The final full-source enclosures are contained in these wider readable
intervals (the JSON stores all40 digits):

    I_1 in [0.4206905728937, 0.4209911708800],
    I_2 in [8.9819619539967, 8.9917050819491],
    I_3 in [526.9544875613, 527.8743063737],
    k   in [0.0864573244793, 0.0876597164244],
    a   in [-6.0729689705130, -6.0339964586883],
    b   in [428.3600132103, 432.0392884615].

Applying (2) to the full40-digit intervals, with outward arithmetic, gives

    k b-a^2 in [0.1539085393115,1.4633282472636].           (9)

In particular the raw determinant exceeds1/10. Restoring f=F/A gives

    K_11(0,0)K_33(0,0)-K_13(0,0)^2 > 1/(10 A^4).         (10)

The weaker readable intervals above are for presentation, not the inputs
to the final arithmetic. The rigorous computer-assisted claim depends on
the reviewed enclosure code, source bounds and the standard decimal
arithmetic implementation; it is not a Lean-kernel certificate.

## 4. A whole ODD2 corner, including the diagonal

Oddness of K in each variable implies that

    T(u,v)=K(sqrt(u),sqrt(v))/sqrt(uv), u,v>0,

extends smoothly to u,v>=0 near zero. One first divides by s and t using
integral remainders, obtaining a smooth function even in each coordinate;
an even smooth function has a smooth squared-coordinate extension on the
closed positive halfline. Only finitely many derivatives are needed here,
all supplied by (3) and the full-source derivative bounds.

At the corner T(0,0)=K_11, T_1(0,0)=K_13/6,
T_12(0,0)=K_33/36. Set

    N(u,v)=T(u,u)T(v,v)-T(u,v)^2.

Symmetry and N(u,u)=0 make its first normal derivative zero as well.
Taylor's formula with integral remainder therefore makes
R(u,v)=N(u,v)/(u-v)^2 extend continuously across u=v, with

    R(0,0)=[K_11 K_33-K_13^2]/36 > 1/(360 A^4).           (11)

By continuity there exists epsilon>0 such that R(u,v)>=1/(720 A^4)
for 0<=u,v<=epsilon^2. Consequently for 0<x,y<=epsilon,

    Delta(x,y)>=x^2 y^2 (x^2-y^2)^2/(720 A^4).            (12)

It is strictly positive when x!=y, and zero at x=y as required. With
OD1's positive diagonals this proves actual ODD2 on all complex two-node
coefficients throughout this corner. The corresponding odd four-node V
form retains the usual factor2. No numeric epsilon is supplied.

Proposed delta: a source-specific positive coefficient, certified with
both infinite remainders, excludes a whole neighborhood of the origin;
it is not merely the known identity Delta(x,x)=0 or an unsigned Taylor
rewrite. The rest of the previously localized bounded square is open.

## Acceptance receipt

The sole read-only independent checker /root/sibling5_check accepted the
185-line, 8222-byte report candidate with SHA256
56044babb802969d8e9c4ab1f25820ccac29e90b5e8f12263c564812f900d922,
and the exact script/JSON hashes above. The checker independently reran
the131072-cell script and obtained the same mathematical enclosure. It
audited directed arithmetic, the exponential contract, Machin pi, both
infinite remainders, the derivative/IBP identities, the squared-coordinate
extension, factorials, A normalization and the whole-corner implication.

The parent separately reconstructed P0 through P3 using exact Fractions
and checked the interval arithmetic against441 exact rational interval
pairs, including mixed-sign multiplication, squaring and positive-denominator
division. Its analytic audit agrees with the checker. The author and
independent reviewer are distinct. Only the status and this receipt were
added after review; the mathematical candidate and certificate bytes remain
unchanged. Accepted scope is the interval-assisted PAPER result (10)-(12),
with its stated standard-decimal dependency and existential epsilon.
