# Full-source curvature and the small-node ODD2 tail at x=5

Status: ACCEPTED_PAPER_SOURCE_CURVATURE_AND_SMALL_NODE_ODD2_TAIL5.
Parent mathematical task, 2026-09-12. No Lean or canonical admission.
The fixed mathematical consumer is all x>=5, 0<y<=1, and its transpose,
with the original full theta source and all complex odd coefficients.
The independently reviewed theorem is

    Delta(x,y)>=x y^2 f(x)^2 f(y)^2/(168000 alpha_x)>0,       (T)
    alpha_x=pi exp(2x).

Together with accepted S=20 and min1/gap3 this excludes every ODD2
negative pair with max(x,y)>=23. Global ODD2, IC, higher odd/even PSD and
RH remain open. This refines the accepted x>=2000 small-node tail.
No source sign grid or quadrature is used in this refinement.

Keep F=Phi, A=||Phi||_2, f=F/A, Kraw=A^2 K and Deltaraw=A^4 Delta.
Let h(u)=log F(sqrt(u)), with its even analytic extension at u=0.
The earlier accepted dependencies are:

- REPORT_2026-09-12_ODD2_SMALL_NODE_EFFECTIVE_TAIL.md, SHA256
  918ebee2be455792c45012d852c23126907dcbdb3a72233a24b80928f268f138:
  h''<=-1 for u>=1, the exact mixed/diagonal integrals, the full derivative
  envelope M2<=938525477/1920<3^20, and F(y)>3^-36 on[0,1].
- REPORT_2026-09-12_ODD2_REGIONAL_MIN1_GAP3.md, SHA256
  9d568cc75aa42d2e9ee30cee62869eafa9f93bea825ddbcbe8bf6afb16011050:
  0<H(q)<=1, H(q)>=1-3/(2q) for q>=pi, and the full diagonal lower bound
  Kraw(x,x)/F(x)^2>=x/(6 alpha_x) for every x>=1.
- REPORT_2026-09-12_ODD2_ORIGIN_QUARTER_BOX.md, SHA256
  d694654cf04951289ccf49cb828a8fbcce24ad07d70ab3823ea7c7ebe3ab2f72:
  the full complex source bound |F(z)|<=1050 on |z|<=1/2 and the
  derivative theta tail used in the pinned endpoint evaluator below.
- PROSHKA_RESPONSE_GOAL058_ODD2EFFECTIVE_2026-09-12.md, SHA256
  06a009eae972027f01f8e0e2d096b7a1e6a453e7b03e55f4a5b7cbd217a29f94,
  accepted in REPORT_2026-09-12_ODD2EFFECTIVE_INTAKE.md, SHA256
  af008a34ad1bd1e4419272797ee7422653005011167a5744defd53d382a3f672:
  all x,y>=20 satisfy ODD2, including their diagonal.

## 1. Complete source certificate on 0<=u<=1/16

Fix delta=1/4, xi=u/delta^2 in[0,1], a(xi)=F(delta sqrt(xi)).
The source is even and holomorphic on the closed half-unit disk;
Cauchy gives |a_i|<=1050 rho^i, rho=1/4. Its degree32 polynomial a0
has full interval coefficients

    a_i=F^(2i)(0) delta^(2i)/(2i)!, 0<=i<=32.

certificates/SOURCE_HCURV_20260912.py imports the exact evaluator from
ODD2_ORIGIN_BOX_20260912.py, SHA256
545f60cd85a38ee81c01fbfe498e5ab0b6709f5fa2b5f0564d456425510b9b7c.
It calls only fvals(0,64), using20 theta modes with the entire n>=21
derivative remainder at every order and directed Decimal precision100.
No moment integration or kernel quadrature is called.

For k=33 the whole Taylor remainders for a,a',a'' on[0,1] satisfy

    e0=1050 rho^k/(1-rho),
    e1=1050 k rho^k/[1-rho(k+1)/k],
    e2=1050 k(k-1)rho^k/[1-rho(k+1)/(k-1)].                 (1)

These follow from the respective decreasing successive term ratios.
Form the exact coefficient polynomial

    p=a0'^2-a0 a0''-a0^2/1024.

Convert it to a univariate Bernstein basis of degree64 on the full[0,1].
The min/max outward coefficient endpoints bound the polynomial everywhere.
If A0,A1,A2 are coefficient triangle bounds for a0,a0',a0'', the complete
additional numerator error is at most

    2A1 e1+e1^2+A0 e2+A2 e0+e0 e2
                      +(2A0 e0+e0^2)/1024.               (2)

All computed coefficient uncertainties are already kept in the polynomial.
The fixed candidate execution gives the full numerator enclosure

    0.01024452832943437 < a'^2-a a''-a^2/1024
                       < 0.03637801767845969.              (3)

The whole uncomputed contribution (2) is less than 3.313e-14.
Since delta^4/4=1/1024, (3) implies h''(u)<=-1/4 on[0,1/16].
The same full endpoint certificate has a(0)>0 and a'(0)<0, so h'(0)<0.
Target interval, degree32,20 modes and precision100 were fixed in the
preregistration before this source computation. A source curvature result
alone is not ODD2; its full-integral consumer is proved in sections4-6.

## 2. Analytic source curvature on 1/16<=u<=1

Write x=sqrt(u) in[1/4,1], q=pi e^(2x), D=2q partial_q and

    F(x)=4pi^2 exp(9x/2-q) H(q),
    H(q)=sum_(n>=1)(n^4-3n^2/(2q))exp[-(n^2-1)q].

Here q>5: pi>25/8 and sqrt(e)>41/25, the latter from e>19/7.
Put H1=1-3/(2q) and E=H-H1. For j=0,1,2 the n=2 summand satisfies

    |D^j H2|<=(576q^2+408q+72+24/q)e^(-3q).

For n>=3 all three derivative orders are bounded by

    |D^j Hn|<=5 q^2 n^8 exp[-(n^2-1)q].

Indeed for a=n^2-1 the absolute coefficients of D^2 Hn give
6n^2/q+4a n^4 q+6a n^2+4a^2 n^4 q^2+6a^2 n^2 q;
after division by q^2 n^8 these sum to at most
4+1/5+3/200+3/10+3/4000<5 for q>=5,n>=2.
The lower derivative orders obey the same bound directly.
The successive n>=3 ratio is at most (4/3)^8 e^(-7q)<1/2.
All q-polynomial factors times their exponentials decrease from q=5.
Consequently the full source remainder, with derivatives, satisfies

    |D^j E|<=E*=(82584/5)(7/19)^15
                           +1640250(7/19)^40 <1/128.       (4)

Every n>=2 summand is nonnegative here, hence E>=0.
With b=1/H1 one has

    0<b<=10/7, |Db|<=60/49, |D^2 b|<=1560/343.

For e0=E/H1 (this e0 is a function, distinct from the section1 tail),
e0>=0 and product differentiation gives

    |D e0|<=130/(49*128)<1/48,
    |D^2 e0|<=2890/(343*128)<1/15.

Thus deltaell(x)=log H(q)-log H1(q)=log(1+e0(q)) satisfies

    |deltaell'|<=1/48,
    |deltaell''|<=1/15+1/48^2<1/14.                        (5)

All denominators 1+e0 are >=1; nothing is inferred from a first-mode sign.
Let g=log F and J=xg''-g'. Exact first-mode differentiation gives

    J1=-(4x-2)q-9/2-6xq/(q-3/2)^2-3/(q-3/2),
    J<=J1+x/14+1/48,        h''(x^2)=J/(4x^3).             (6)

The following three whole interval bounds establish J<=-x^3.
On[1/4,3/8], (2-4x)q decreases, with derivative -8x pi e^(2x),
so it is at most pi sqrt(e)<110/21. Also q<187/28 using
pi<22/7 and exp(3/4)<17/8. Since q/(q-3/2)^2 is decreasing,

    J<=110/21-9/2-84/145-7854/21025+1/21
      =-49201/294350 < -27/512 <=-x^3.                    (7)

On[3/8,1/2] the same decreasing positive term is at most187/56.
Dropping the other negative rational terms,

    J<=187/56-9/2+1/28+1/48 < -1/8 <=-x^3.               (8)

On[1/2,1] its sign is nonpositive, so

    J<=-9/2+1/14+1/48 < -1 <=-x^3.                       (9)

The elementary exp(3/4) upper bound follows from its first five Taylor
terms and the n>=5 remainder: successive ratios there are <=1/8.
Equations(6)-(9) prove h''<=-1/4 on[1/16,1]. Together with section1
and the accepted h''<=-1 for u>=1 this proves the global source bound

    h''(u)<=-1/4 for every u>=0.                           (10)

## 3. A bounded logarithmic slope near the mass of the source

Equation(10) and h'(0)<0 give h'<=0 everywhere. Set b=17/16.
Using e<11/4 and exp(1/8)<=8/7 gives

    q_b=pi e^(17/8)<(22/7)(11/4)^2(8/7)<28.

The accepted x>=1 estimate |(log H(pi e^(2x)))'|<1/3 gives
g'(b)>9/2-56-1/3. Hence h'(b^2)=g'(b)/(2b)>-32.
Monotonicity of h' therefore proves the entire interval bound

    -32<=h'(u)<=0,          0<=u<=(17/16)^2.               (11)

## 4. A uniform small-node diagonal budget

The exact full integral, retaining both reflected signs, is

    Kraw(y,y)=integral_0^infinity [F(sqrt(r+y^2))^2
                            -F(sqrt(r)+y)F(sqrt(r)-y)]dr. (12)

For c=r+y^2 and a=2y sqrt(r), the interval[c-a,c+a] is nonnegative.
Integrating(10) symmetrically yields

    2h(c)-h(c+a)-h(c-a)>=a^2/4=r y^2.

The integrand in(12) is thus nonnegative everywhere. Restrict it to
0<=r<=1/32, where c<=33/32<(17/16)^2 if 0<y<=1.
Equation(11) gives F(sqrt(c))^2/F(y)^2>=exp(-64r).
Since z=r y^2<=1/32, 1-exp(-z)>=z/2. Consequently

    Kraw(y,y)/F(y)^2
      >=(y^2/2) integral_0^(1/32) r exp(-64r)dr
      =y^2(1-3e^-2)/8192
      >y^2*107/1478656 > y^2/14000,     0<y<=1.            (13)

The strict rational bound uses e>19/7. This retains y^2 uniformly at
the axis; no positive lower cutoff for y has been introduced.

## 5. The entire mixed entry with a small local and remote tail

For x>=4 set alpha=pi e^(2x), beta=2alpha-9/2.
The accepted full H estimates imply

    F(x+v)/F(x)<=(14/13)exp(-beta v), v>=0.

Let D(v,y)=F(v+y)-F(v-y). The exact original mixed integral is

    Kraw(x,y)=integral_0^infinity F(x+v){(x+2v)D(v,y)
                                      +y[F(v+y)+F(v-y)]}dv. (14)

On0<=v<=1/16,0<y<=1, all |v+-y|<=17/16. Equation(11) and
the squared-coordinate mean value formula yield

    |D(v,y)|<=128vy F(y)exp(64v),
    F(v+y)+F(v-y)<=2F(y)exp(64v).                          (15)

For detail, the squared-argument interval has length4vy and the derivative
of F(sqrt(u)) is h'(u)F(sqrt(u)). Its largest source value is at |y-v|.
If |y-v|<y, its ratio to F(y) is <=exp(32[y^2-(y-v)^2])<=exp(64v);
otherwise that ratio is <=1. This covers v>y as well as v<=y.
Define gamma=beta-64=2alpha-137/2. Extending the nonnegative upper
integrands in(15) to infinity bounds the local contribution by

    |Klocal|/[F(x)F(y)]
      <=(28/13)y[64x/gamma^2+256/gamma^3+1/gamma].         (16)

For every x>=4, alpha>4096, x/alpha<1/1024 and
gamma>=(19/10)alpha. The first bound follows from pi>3,e>8/3;
x/alpha decreases there and 3(8/3)^8>4096.
The coefficient of y/alpha in(16) is less than

    (28/13)[6400/(361*1024)+256000/(6859*4096^2)+10/19]
      =213822315/182614016 <6/5.                          (17)

For v>=1/16 retain the complete remote tail of(14). Globally,
M0=sup|F|<=1050<3^7, M2=sup|F''|<3^20 and F(y)>3^-36.
Evenness gives D(0,y)=0 and |partial_v D|<=2y M2, hence
|D|<=2vy M2. Since beta>=alpha and

    exp(-alpha v)<=exp(-alpha/32)exp(-alpha v/2)

on this tail, its full integral is at most

    |Ktail|/[F(x)F(y)]
     <=(28/13)y 3^36 exp(-alpha/32)
                   [M2(4x/alpha^2+32/alpha^3)+2M0/alpha]
     <3^61 exp(-alpha/32)y/alpha.                         (18)

Indeed x/alpha<=1, alpha>=1, and 36M2+2M0<38*3^20<3^24.
Since alpha/32>128, e>2 and 3^61<2^98, (18) is less than
2^-30 y/alpha. Adding both complete pieces proves

    |Kraw(x,y)|/[F(x)F(y)] < (5/4)y/alpha,
                        x>=4, 0<y<=1,                    (19)

because 6/5+2^-30<5/4. No reflected or integration tail is discarded.

## 6. The determinant, normalization and all complex coefficients

Combine the accepted x-diagonal lower bound x/(6alpha), (13) and(19):

    Deltaraw/[F(x)^2 F(y)^2]
       >=y^2[x/(84000alpha)-25/(16alpha^2)].               (20)

For x>=5, x alpha>=5pi e^10>15(19/7)^10>262500.
The last constant is 12*(25/16)*14000. Thus the second term in(20)
consumes less than half the first, and dividing by A^4 proves(T).
For a=K(x,x)>0,b=K(x,y) and all c1,c2 in C one has exactly

    c* K2 c=a|c1+(b/a)c2|^2+[Delta(x,y)/a]|c2|^2>=0.

The full V form on(x,y,-x,-y) with coefficients(c1,c2,-c1,-c2)
is exactly twice this expression. There is no restriction on phases.
Symmetry supplies the transposed region.

## 7. New outer localization and remaining unpaid domains

Order nodes x>=y>0. If x>=23 there are three exhaustive cases:

- y<=1: theorem(T) applies since x>=5.
- 1<y<20: x-y>3, so the accepted min1/gap3 theorem applies.
- y>=20: the accepted S20 theorem applies, including x=y.

Thus every ODD2 negative pair, if one exists, has max(x,y)<23.
For distinct ordered nodes, a more precise unpaid covering is

    Omega_low: 0<y<1, y<x<5, x>1/4,
    Omega_mid: 1<=y<20, 0<x-y<3.                          (21)

The x>1/4 restriction removes the accepted whole quarter square.
The accepted tiny AX and DG regions may additionally be removed from(21).
All x=y are exactly nonnegative rank-one forms. A bounded unpaid domain
is not a proof of its sign, and neither(10) nor(T) proves global IC/ODD2.
Higher odd rank, even sector, full V/Q positivity and RH remain open.

## 8. Independent acceptance and parent readback

The sole reserved checker /root/sibling5_check read and independently
reviewed the complete12291-byte,304-LF candidate, SHA256
8ad4e59c250116a11d7c80b2aee7667118c121524a0c84654e3af7cfb72dccae.
It also reviewed and independently executed the final portable certificate,
SHA25673cc93f0fbe6bb44526ed1e44d8adfc46772d79814a6227a0b9fb508d1c13aaa.
Its complete unchanged output is certificates/SOURCE_HCURV_20260912.json,
SHA256ee0d03ac11775bdc3f96519077ab0c1f0617852098b573b71764c11c2e964dd2.

The checker returned ACCEPT for global h''<=-1/4, the full-integral theorem(T)
with all complex coefficients, and the max-node23 corollary and exhaustive
residual domains(21). It checked the local source polynomial and full mode/
Cauchy tails, the analytic middle-source region and inherited far region,
the exact positive-integrand restriction, uniform small-node diagonal,
local mixed cancellation, entire remote tail, determinant and normalization.

The parent separately compared every top-level and nested certificate field
against its earlier full-source candidate. All numerical fields match
exactly. Only script_sha256 differs, from replacing the scratch absolute
import path by the portable sibling import. The parent checked the exact
decimal endpoints against(3), the error bound, and a(0)>0,a'(0)<0 using
fractions.Fraction. A separate23-comparison exact rational/integer audit
confirms the analytic constants, including(4),(7)-(9),(13),(17) and(20).
No extra source sampling or quadrature was performed.

The preregistration is preserved byte-for-byte in
certificates/SOURCE_HCURV_PREREG_20260912.txt. The separate rational audit
and its complete PASS output are certificates/ODD2_TAIL5_RATIONAL_20260912.py
and certificates/ODD2_TAIL5_RATIONAL_20260912.json. Reproduce by

    python3 docs/Codex/certificates/SOURCE_HCURV_20260912.py
    python3 docs/Codex/certificates/ODD2_TAIL5_RATIONAL_20260912.py

The raw executable deliberately retains accepted:false and its CANDIDATE
label: computation does not grant its own independent admission. This
receipt records the independent mathematical review at PAPER scope.
After review only the status/introduction and this receipt were updated;
the mathematical argument and portable code are unchanged. No Lean or
canonical admission, global IC/ODD2, higher odd/even PSD or RH is claimed.
