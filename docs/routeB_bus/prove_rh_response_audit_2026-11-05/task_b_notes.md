# Task B — literal return and a deliberately coarse global bound

DIAG only. The values in `task_b.json` are numerical evaluations, not intervals.
The window coordinates are exactly (6.1), without graph normalization. In
particular the reported q is w*Aw, not the z*Az of (6.5).

The source is the pinned unchanged `analytic_source.py`. At m=16,64,300 its
`build(m,256)` is executed freshly and its actual zeta EVEN matrix contracted
against the fixed binary64 v, vtilde, w vectors promoted exactly to MPFR. At
larger m no A matrix is built: the literal full-line form is evaluated on the
finite cosine polynomial, including zero extension, every prime power n<m,
the complete Gamma tail and pole. For coefficients b_j=d_j c_j/sqrt(L),
k_j=2pi j/L in the shifted y=x+L/2 coordinate, its exact overlap is

    R(s)=(L-s)[b_0^2+sum_(j>0) b_j^2 cos(k_j s)/2]
            +sum_(j>0) r_j sin(k_j s), 0<=s<=L,
    r_j=-b_j^2/(2k_j)-2b_0 b_j/k_j
            -2k_j b_j sum_(i>0,i!=j) b_i/(k_j^2-k_i^2).

It is zero beyond L. The function evaluator integrates
2j(s)(||f||²-R(s)) on [0,L], adds 2||f||²(atanh(e^-L/2)+atan(e^-L/2)),
subtracts c_*||f||² and 2 sum Lambda(n)n^-1/2 R(log n), and adds (p*c)^2.
At m=300 its three stage values differ from the actual matrix by at most
2.91e-12. At m=64 the worst crosscheck is 3.11e-9 (adaptive quadrature
estimate 3.44e-9); the matrix value, not that quadrature, is reported there.

The cutoff-only stage uses direct Gauss-Legendre overlap integrals of chi f,
repeated at 768 and1024 nodes. The cosine coefficients use a periodic FFT
trapezoidal rule at65536 nodes, repeated at32768. These repeats are diagnostic
precision checks. Stage differences telescope as cutoff, projection, e0, e1.
The reference 2W[g]+2h(L/2) is evaluated from Gaussian zero sums, solely as a
reference; none of the source forms uses a zero Gram. The fixed Task A prime
cutoff is not silently used as a full-line reference after its failed gate.

## An explicit conservative bound, L>=1

This bound concerns the literal mathematical functions, separately from the
floating quadratures. It is intentionally vastly larger than measured errors.
For a zero-extended piecewise H1 function on one interval (or a global H1
function), use

    X(f)^2=||e^{|x|}f||_2^2+||e^{|x|}f'||_2^2
               +|f(left)|^2+|f(right)|^2.

Derivative here is the interior derivative; jump traces are included explicitly.
For sums/differences the trace is taken at each actual support discontinuity.
For the present functions all finite support boundaries are +/-L/2, whereas
f_m is smooth on the full line. The X triangle inequality applies.

A direct source estimate gives |W(f,k)|<=27 X(f)X(k) for zeta. Details:

* For 0<s<1, j(s)<=1/s. Splitting the translation overlap and the two endpoint
  strips gives ||f-T_s f||²<=5s²||f'||²+2s(sum endpoint traces²).
  Thus this portion of Gamma is bounded by (5/2)||f'||²+2 traces².
* For s>=1, j(s)<=e^-s/2/(1-e^-2), and ||f-T_sf||²<=4||f||².
  The resulting contribution is less than5.62||f||². Together with
  c_*<5.38 this costs less than11||f||².
* Cauchy-Schwarz and |x|+|x+s|>=s give
  |<f,T_s k>|<=e^-s ||e^{|x|}f|| ||e^{|x|}k||.
  Hence the two prime shifts cost <=2 sum Lambda(n)n^-3/2<9, using
  Lambda(n)<=log n and sum_(n>=2) log(n)n^-3/2<4.5 (integral comparison).
* Each pole moment costs sqrt(4/3)||e^{|x|}f||, and the two crossed moments
  cost8/3. Combining the positive component Cauchy-Schwarz estimates costs
  less than27 in X. This argument uses all prime powers, not a truncated
  prime-source mass bound.

For the quartet a=1/3,gamma=7 each of four Laplace moment functionals has
weighted L2 norm <=sqrt(1/(1-a²))=sqrt(9/8). Its additional bilinear form
therefore costs at most4.5 X(f)X(k). Use32 instead of27 in that world.

The elementary Gaussian polynomial integrals give X(g)<1e5, hence
X(f_m)<=2e5 exp(L/4). The following intentionally loose intermediate bounds
hold for this particular cutoff and all L>=1:

    delta=(chi(2x/L)-1) f_m,
    X(delta)<=1e21 exp(L/4-L²/256),
    u=chi(2x/L) f_m,
    ||u'''||_2<=1e20,
    r=P_m^cos u-u,
    X(r)<=1e22(1+L)^3 exp(-3L/2).

Here is an elementary way to verify the loose constants, without importing an
unspecified big-O constant. For b(v)=exp(-1/v), v>0, its first three derivatives
are exp(-1/v) times polynomials in1/v, bounded by maxima
max_(z>=0) z^k exp(-z)=(k/e)^k. On0<=v<=1,
b(v)+b(1-v)>=e^-2. The quotient rule consequently gives
||chi'||_infinity<1e6 and ||chi^(j)||_infinity<1e12 for j=1,2,3.
Gaussian differentiation through order3 gives
||g^(j)||_2<1e5 and |g(y)|+|g'(y)|<1e6(1+|y|)^5 exp(-y²).
The binomial and Gamma-integral estimates proving these numbers are far below
the displayed constants. For example (1+y)^5 exp(-y²/4)<1e6,
y-y²/4<=1, and on |y|>=a the L2 Gaussian tail can be bounded by
exp(-a²/4)*(integral exp(-y²/2)dy)^1/2. The cutoff error is confined to
|x +/- L/4|>=L/8; applying those inequalities with a=L/8 proves its bound.
Leibniz' rule for u''' has at most the four terms with coefficients1,3,3,1;
scaling chi derivatives by(2/L)^j and L>=1 gives ||u'''||<1e20.

For the projection estimate, all u endpoint derivatives vanish. Parseval and
three integrations by parts give
||r||_(H1_int)<=2 Omega_m^-2 ||u'''|| for Omega_m>=1,
Omega_m=2pi m/L. Multiplication of the interior norms by exp(L/2) pays the
weight. Cauchy-Schwarz on the boundary cosine series gives
|r(endpoint)| <=sqrt(2/L)*(L/(2pi))^3*(sum_(j>m)j^-6)^1/2 ||u'''||,
with sum_(j>m)j^-6<=1/(5m^5). These bounds imply the displayed X(r).

For completeness, the moment correction amplification is explicit. In the
literal basis, for L>=1,

    X(phi_0)<=3exp(L/2), X(phi_1)<=30exp(L/2),
    p_0<=6exp(L/4)/sqrt(L),
    p_1>=exp(L/4)/(200sqrt(L)).

These follow directly from the displayed source p_j formula and
sinh(L/4)>=.19exp(L/4). Since integral f_m=0 and its pole moment is zero,
|v_0|<=X(delta)/sqrt(L), and the remaining pole residual after removing e0 is
at most 2[X(delta)+X(r)]+|v_0|p_0. Therefore

    X(S_m w_m-f_m)
      <=(1+40000exp(L/2))X(delta)
           +(1+12000sqrt(L)exp(L/4))[X(delta)+X(r)]
      <= E(L),
    E(L)=1e27(1+L) exp(3L/4-L²/256)
               +1e27(1+L)^4 exp(-5L/4).

The loose first inequality counts delta twice, harmlessly. The second follows
term by term for L>=1. Finally the explicit global return budget is

    B_zeta(L)=27 E(L)[4e5 exp(L/4)+E(L)],
    B_plant(L)=32 E(L)[4e5 exp(L/4)+E(L)].

These are continuity bounds, not empirical fits; no growth exponent was fit.
Their useful regime is extremely far beyond m<=3000. The threshold table uses
this bound and reports its L crossing, rather than asserting small observed
finite-window errors. No RH claim and no assertion of (7.4) follows.

The equality B(L)=1e-30 occurs at
L=363.8803637220105739696838156654838455496796911793438726940441812
(zeta) and
L=363.97267829718303202572071782351746285024415007064505712144180621
(plant). The strict bound is below1e-30 for L strictly above the corresponding
crossing; the smallest integer L is364 in either world. Thus, strictly speaking,
there is an infimum rather than a smallest real L for this strict inequality.
For1<=L<=130 the Gaussian term alone makes B much larger than1e-30.
For L>=130 each E summand has logarithmic derivative less than-1/4, so
both E exp(L/4) and E² decrease; this proves the crossing is unique.
