# An explicit radius for the accepted origin corner

STATUS: ACCEPT_EXPLICIT_ORIGIN_RADIUS_REFINEMENT_ONLY
SCOPE: QUANTITATIVE_REFINEMENT_OF_ACCEPTED_ORIGIN_CORNER_ONLY
SOURCE_THETA_ODD2: OPEN
PX_RH_CLAIM: NOT_MADE

This removes an existential constant from the accepted origin-corner
theorem. It neither establishes a new global sign nor evaluates the
large-square threshold L. The deliberately small radius is a valid
boundary for a future complete-domain certificate, not an efficient one.

Dependency: REPORT_2026-09-12_ODD2_ORIGIN_CORNER.md, SHA256
1b507d7c22480de44e4215131d34c3d1f8211b3715556fa7d96aa55cf97a7b2a,
including its reviewed code/output and standard-decimal dependency.
That theorem proves the raw origin jet determinant exceeds 1/10.
The present argument uses only exact rational arithmetic in addition.

Work with raw F=Phi, K0=A^2 K and Delta0=A^4 Delta. Define

    D=81764454102531481,
    M=66D^2=441238113009208490848319871339521826,
    epsilon=1/(128M)
      =1/56478478465178686828584943531458793728.          (1)

The claim is, for all 0<x,y<=epsilon,

    Delta(x,y)>=x^2 y^2 (x^2-y^2)^2/(720 A^4).          (2)

Together with the previously accepted positive diagonals, this includes
all complex two-node coefficients and the usual factor2 for the odd
four-node V form. Equality on the diagonal is preserved.

## 1. Global bounds for the necessary source derivatives

Let P0(z)=4z^2-6z and

    P_(j+1)(z)=(1/2-2z)P_j(z)+2zP'_j(z).

Then for v>=0,

    F^(j)(v)=exp(v/2) sum_(n>=1) P_j(pi n^2 exp(2v))
                                      exp(-pi n^2 exp(2v)).

Put B_j equal to the sum of the absolute coefficients of P_j,
nu_j=j+9/4 and D_j=(16/15) B_j nu_j^ceil(nu_j). The full-theta
bound from the origin report applies without change for 0<=j<=7:

    |F^(j)(v)|<=D_j exp[-pi exp(2v)/2].                 (3)

Indeed deg P_j=j+2, z>=pi>1, exp(v/2)<=z^(1/4), and
z^nu exp(-z/2)<=(2nu/e)^nu<=nu^ceil(nu). The remaining exponential
series is bounded geometrically using n^2-1>=3(n-1), pi>3 and e^3>16.
Evenness of F gives the analogous absolute bound with |v| for v<0.

Exact rational recurrence gives the following ceilings of D_j:

    j:         0,    1,      2,        3,
    ceil D_j:122, 6308, 488816, 52738348,

    j:                     4,             5,               6,                 7
    ceil D_j:     7513612509, 1359827644774, 303637100565646, 81764454102531481.

Thus D in (1) bounds every D_j needed. The coefficient absolute sums are
10,53,661/2,9445/4,151269/8,2672213/16,51450613/32,1069789829/64.
These constants can be independently reconstructed with the recurrence;
no floating-point fit or finite theta truncation enters (3).

For |s|,|t|<=1 and v>=2 both |v+s| and |v+t| exceed v-1. By (3) the
product of any two required derivatives is bounded by
D^2 exp[-pi exp(2(v-1))]<=D^2 exp[-3(v-1)]. On 0<=v<=2 it is at most D^2.
Consequently the full weighted and unweighted majorants satisfy

    integral_0^2 (2+2v)dv
        +integral_2^infinity (2+2v)exp[-3(v-1)]dv <9,
    2+integral_2^infinity exp[-3(v-1)]dv <3.             (4)

The first tail equals (20/9)e^-3<1; the second equals e^-3/3<1.
For r,q>=1, r+q<=8, differentiate the full V integral as in the origin
report. The three terms have weights (s+t+2v), r and q. Applying (4),
then including V(s,-t), proves on the whole square [-1,1]^2

    |partial_s^r partial_t^q K0(s,t)|
        <=2[9+3(r+q)]D^2<=M.                           (5)

This includes all derivatives with r=2a+1,q=2b+1,a+b<=3.
The same full-integral majorants justify differentiation; no reflected
integration tail is omitted.

## 2. Squared coordinates with controlled derivatives

Let g(s,t)=K0(s,t)/(st), smoothly extended by oddness. Its integral
quotient representation is

    g(s,t)=integral_0^1 integral_0^1 K0_st(as,bt) da db.

It is even in each variable. If h is even and H(u)=h(sqrt(u)), then,
for k>=1, the ordinary one-variable integral identity is

    H^(k)(u)=1/[2^(2k-1)(k-1)!]
       integral_0^1 (1-a^2)^(k-1) h^(2k)(a sqrt(u)) da. (6)

It follows by repeated differentiation and integration by parts; for k=1
it is h'(s)/(2s)=(1/2) integral_0^1 h''(as) da. Its positive kernel has
mass k!/(2k)!. This also proves the derivative extension at u=0.
Apply it in each variable to g and set T(u,v)=g(sqrt(u),sqrt(v)).
For a,b>=0,a+b<=3, the quotient integrals and (5) give

    |partial_u^a partial_v^b T(u,v)|
        <=[a! b! / ((2a+1)!(2b+1)!)] M <=M,
                       0<=u,v<=1.                     (7)

For a=0 or b=0, the respective even-variable operation is the identity.
Only derivatives up to total order3 in T, hence up to order7 in one
original coordinate and total order8 in K0, are required.

## 3. A quantitative bound for the divided determinant

Write h(u)=T(u,u) and

    N(u,v)=h(u)h(v)-T(u,v)^2.

From (7), |h^(k)|<=2^k M, k<=3. Direct differentiation gives

    |N_uvv|<=16 M^2,    |N_vvv|<=16 M^2.               (8)

For clarity the four terms of N_uvv are h'(u)h''(v),
-4T_v T_uv, -2T_u T_vv, -2T T_uvv, bounded respectively by
8,4,2,2 times M^2. The three terms of N_vvv are h(u)h'''(v),
-6T_v T_vv, -2T T_vvv, bounded by 8,6,2 times M^2.

Symmetry gives N(u,u)=N_v(u,u)=0, so the divided determinant extends as

    R(u,v)=N(u,v)/(u-v)^2
       =integral_0^1 (1-a) N_vv(u,(1-a)u+av) da.       (9)

Differentiating this exact integral and using (8) yields

    |R_u|<=16 M^2 integral_0^1 (1-a)(2-a)da
           =(40/3)M^2,
    |R_v|<=16 M^2 integral_0^1 a(1-a)da
           =(8/3)M^2.                                (10)

The accepted origin jet certificate gives R(0,0)>1/360 in raw
normalization. For 0<=u,v<=epsilon^2, (10) therefore implies

    R(u,v)>1/360-16M^2 epsilon^2
            =1/360-1/1024 >1/720.                     (11)

Indeed 16M^2 epsilon^2=1/1024<1/720. Since
Delta0(x,y)=x^2y^2(x^2-y^2)^2 R(x^2,y^2), restoring A^4 proves (2).

The numerical radius is extremely conservative. This refinement makes
the accepted corner explicit; it does not exclude a witness elsewhere
in the bounded region, prove a global IC inequality, or close larger
odd/even matrices or RH. It must not be counted as a new global sign
family beyond the previously accepted existential corner.

## Acceptance receipt

The sole read-only independent checker /root/sibling5_check accepted the
6209-byte,157-LF candidate SHA256
315d1b3080b41cc964f210aef03b702199752b504b94d9b3f4e8b3d1096a0e47
as ACCEPT_EXPLICIT_ORIGIN_RADIUS_REFINEMENT_ONLY. It independently
reconstructed the rational polynomial recurrence and constants, and
checked all derivative, quotient, remainder, and normalization steps.

The parent separately checked the general even-coordinate identity by
integration by parts, the full derivative majorants, and the divided
remainder derivatives. Exact rational monomial checks39/39 additionally
confirmed the prefactors, without substituting for the general proof.
The inherited origin interval certificate was not rerun unnecessarily.
Only the status and this receipt were added after independent review.
The mathematical refinement and its explicitly limited scope are unchanged.
