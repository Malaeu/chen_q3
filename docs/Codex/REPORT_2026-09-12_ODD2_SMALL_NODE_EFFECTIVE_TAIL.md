# An explicit full-source ODD2 tail uniform down to a zero node

Status: ACCEPTED_PAPER_EXPLICIT_SMALL_NODE_ODD2_TAIL.
Parent mathematical task, 2026-09-12. No Lean or canonical admission.
Fixed consumer: x>=2000, 0<y<=1, and the transposed region;
all complex two-node odd coefficients, with no positive lower cutoff on y.
The independently reviewed theorem is

    Delta(x,y)>= x y^2 f(x)^2 f(y)^2/(12*3^1960*alpha_x)>0,       (T)
    alpha_x=pi exp(2x).

This makes the small-node tail effective. It does not assert global ODD2,
a numeric cutoff for the remaining joint tail, global IC or RH.
No new physical sign grid or quadrature is used. The constants are chosen
for a short exact proof, not optimized as numerical thresholds.

Source: F=Phi, A=||Phi||_2, f=F/A, Kraw=A^2 K,
K(s,t)=V(s,t)-V(s,-t), Delta=K(x,x)K(y,y)-K(x,y)^2.
Dependencies already independently accepted in this isolated branch:

- REPORT_2026-09-12_ODD2_REGIONAL_MIN1_GAP3.md, SHA256
  9d568cc75aa42d2e9ee30cee62869eafa9f93bea825ddbcbe8bf6afb16011050:
  the exact H representation, 0<H<=1 globally, H(q)>=1-3/(2q) for q>=pi,
  and Kraw(x,x)/F(x)^2>=x/(6 alpha_x) for every x>=1.
- The source squared-variable strict log concavity and positive-integrand
  representation in docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md, SHA256
  14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc.
- The full derivative theta remainder from the accepted ODD2COMPACT source,
  response SHA256 819511db9d46801e87b54e728faf7c55e7ce21e4e20e48d9d95d49a71b175e07.
- The full source bound |F(v)|<=1050 for real v>=0 in section3 of
  REPORT_2026-09-12_ODD2_ORIGIN_QUARTER_BOX.md, commit
  ef472574a339d3b4ee68ebb607bda79cba1cd9bd.

## 1. Quantitative squared-variable concavity away from zero

For x>=1, q=pi e^(2x)>21 and

    F(x)=4pi^2 exp(9x/2-q) H(q),
    H(q)=sum_(n>=1)(n^4-3n^2/(2q))exp[-(n^2-1)q].

Write D=2q partial_q. For n>=2, a=n^2-1, the summand H_n satisfies

    D H_n=(3n^2/q-2a n^4 q+3a n^2)e^(-a q),
    D^2 H_n=(-6n^2/q-4a n^4 q-6a n^2
                    +4a^2 n^4 q^2-6a^2 n^2 q)e^(-a q).

For j=0,1,2, the absolute value of D^j H_n is at most
32 q^2 n^8 e^[-(n^2-1)q]. Each term of the n^8 sum has successive
ratio <=(3/2)^8 e^(-5q)<1/2. The whole n>=2 remainder is therefore
bounded by

    E(q)=16384 q^2 e^(-3q)<=16384*441 e^(-63)<1/1000.

The last inequality uses e>2 and exact integer arithmetic; q^2 e^(-3q)
is decreasing for q>=21. In particular, termwise derivatives and all
omitted modes are paid. Since H>=13/14 and the n=1 derivatives are
3/q and -6/q,

    |D H|<=1/7+1/1000<1/4,
    |D^2 H|<=2/7+1/1000<1/2.

For ell(x)=log H(pi e^(2x)), these imply

    |ell'|<=7/26<1/3,
    |ell''|<=7/13+(7/26)^2<2/3.

Let g=log F and h(u)=g(sqrt(u)). Then for x>=1,

    4x^3 h''(x^2)=x g''(x)-g'(x)
       =-(4x-2)q-9/2+x ell''-ell'
       <=-(4x-2)q+2x/3-25/6 <=-4x^3.

For the last bound, 4x-2>=2x, pi>3 and e^(2x)>=2x^2 give
(4x-2)q>12x^3, which is more than required when x>=1. Thus

    h''(u)<=-1 for every u>=1.                              (1)

This is an explicit source-specific bound, not an assumption of IC for K.

## 2. A uniform small-node diagonal budget

The exact full-integral substitution gives

    Kraw(y,y)=integral_0^infinity [F(sqrt(r+y^2))^2
                           -F(sqrt(r)+y)F(sqrt(r)-y)] dr.    (2)

The source squared-variable log concavity makes the integrand nonnegative
for all r>=0 and y>=0. Consequently we may restrict (2) to r in[4,5].
For 0<y<=1 put c=r+y^2 and a=2y sqrt(r). The entire interval[c-a,c+a]
lies in[1,infinity). Integrating (1) on this interval yields

    2h(c)-h(c+a)-h(c-a)>=a^2=4r y^2>=16y^2.

At u=sqrt(r+y^2), we have 2<=u<=sqrt(6)<5/2. The exact first theta
mode and q_u<4e^5<972 give F(u)>e^(-972)>3^(-972): the prefactor
4pi^2 exp(9u/2)H(q_u)>1. Therefore the restricted integrand is at least

    3^(-1944)(1-e^(-16y^2)) >= y^2/(2*3^1944).

Here 1-e^(-16z)>z/2 for 0<z<=1 follows by concavity and 1-e^(-16)>1/2.
Integrating over the unit interval and dividing by F(y)^2<=1050^2 gives

    Kraw(y,y)/F(y)^2 >= y^2/(2*1050^2*3^1944)
                          >=3^(-1960) y^2,  0<y<=1.        (3)

The last integer inequality is 2*1050^2<3^16. This bound is uniform at
y=0 after dividing by y^2; no unresolved minimum over a compact set remains.

## 3. A full mixed-entry bound retaining cancellation at the axis

For 0<=y<=1 the first-mode bound gives

    F(y)>=4pi^2 exp(9y/2-pi e^(2y))(1-3/(2pi e^(2y)))
         >18e^(-36)>3^(-36).                               (4)

Let M0=sup_R |F| and M2=sup_R |F''|. Evenness and the accepted full
source bounds give M0<=1050<3^7 and M2<=D2<3^20. Explicitly the polynomial
recursion P_(j+1)=(1/2-2z)P_j+2zP_j' starting with 4z^2-6z yields

    D2=(16/15) sum|coeff(P2)| (17/4)^5=938525477/1920.

The full derivative remainder with N=0 bounds all theta modes by
D2 exp[-pi e^(2|v|)/2]<=D2, so this controls the entire real line.

Set D(v,y)=F(v+y)-F(v-y). Since D(0,y)=0 and
|partial_v D(v,y)|<=2y M2, one has |D(v,y)|<=2vy M2. This is the
cancellation that removes an unnecessary factor x in the leading integral.
The exact mixed kernel is

    Kraw(x,y)=integral_0^infinity F(x+v){(x+2v)D(v,y)
                                      +y[F(v+y)+F(v-y)]}dv.

For x>=1 put alpha=pi e^(2x), beta=2alpha-9/2>=alpha. The full H bounds give
F(x+v)/F(x)<=(14/13)e^(-beta v). Thus, with no integration truncation,

    |Kraw(x,y)|/[F(x)F(y)]
      <=(28/13)y/F(y){M2[x/beta^2+4/beta^3]+M0/beta}
      <=3^59 y/alpha.                                      (5)

Indeed alpha>=x and alpha>=1 imply x/beta^2<=1/alpha and
4/beta^3<=4/alpha. Then 5M2+M0<=6*3^20<3^22, 28/13<3 and (4) pay (5).
Both reflected signs and the entire v>=0 range were retained.

## 4. The exact determinant and all complex coefficients

For x>=1 use the accepted diagonal estimate x/(6alpha) and combine (3),(5):

    Deltaraw/[F(x)^2 F(y)^2]
       >= y^2[x/(6*3^1960*alpha)-3^118/alpha^2].             (6)

If x>=2000, then alpha*x>2^4000>12*3^2078. The final inequality follows
from 3^5<2^8: 3^2078<2^3325 and 12*2^3325<2^3329<2^4000.
The second term in (6) consumes at most half the first. Hence

    Deltaraw/[F(x)^2 F(y)^2]>= x y^2/(12*3^1960*alpha).

Dividing by A^4 proves (T). For a=K(x,x)>0 and b=K(x,y), every complex pair
satisfies exactly

    c* K_2 c=a|c1+(b/a)c2|^2+[Delta(x,y)/a]|c2|^2>=0.

The original V form on(x,y,-x,-y), with coefficients(c1,c2,-c1,-c2),
is exactly twice this form. The transposed region follows by symmetry.

## 5. Check and scope

The parent checked the two D derivatives symbolically by direct
product differentiation, every source domain and both improper integrals.
Separate exact fractions.Fraction/integer calculations verify D2, all
rational derivative margins, 2*1050^2<3^16, the complete theta-tail
integer bound and 12*3^2078<2^4000. No floating-point sign evaluation,
node sampling or user-selected finite list is involved.
Independent review of the complete argument was accepted; see section6.

This is a quantitative refinement of the accepted small-node tail family.
It is complementary to a joint-tail cutoff min(x,y)>=S, not interchangeable
with it. If such an explicit S is independently accepted, this result and
the accepted min>=1/gap>=3 region give an explicit max-node cutoff
L=max(2000,S+3) for global ODD2 localization. That last statement is
conditional until an explicit joint-tail S is accepted. Every pair inside
the residual region still needs proof; full ODD2, IC and RH remain open.

## 6. Independent acceptance receipt

The sole reserved checker /root/sibling5_check read and independently
reviewed the complete7471-byte,181-LF candidate, SHA256
7d2835d7085761797bccc07a0424df44bc95ef85412b4c8398962f3451dfeee5.
It returned ACCEPT for exactly x>=2000, 0<y<=1 and the transposed region.
The checker independently verified the D derivatives and infinite mode
tails, h'' bound, positive-integrand restriction, small-node uniformity,
full mixed integrals, determinant normalization and complex Schur passage.
Its exact rational checks reproduced sum|coeff(P2)|=661/2 and
D2=938525477/1920, the integer bounds and all displayed constants.

The parent separately reread the accepted dependency proving the derivative
bound for every N>=0 (in particular N=0), the full-source diagonal bound
for every x>=1, and the squared-variable source concavity plus exact
integral substitution. The operative source bytes/hashes match the pins.
Only status, a source path, the review sentence and this receipt changed
after review. The mathematical proof is unchanged.

Acceptance is local to this explicit unbounded ODD2 region at PAPER scope.
It supplies neither an accepted explicit joint-tail S nor global ODD2,
IC, larger odd/even PSD, canonical admission, Lean certification or RH.
