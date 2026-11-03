# STATUS: TRY_FIRST_STEP_LOG3_SOURCE_MATCHED_GEOMETRIC_SOS

```yaml
OPERATIVE_CLASS: TRY_FIRST_STEP_LOG3_SOURCE_MATCHED_GEOMETRIC_SOS
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_FIRST_STEP_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: a1d2a97350e61f1697744056e26f95a1c8baf3de
INBOX_SOURCE: 11f6368323d8aaac3d3c0a6a95873b86294cc540
SOURCE_BLOB: 755c8535d18a9ea68d366934f4158981a50c0728
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
RESULT: BOUNDED_SUPPORT_POSITIVITY_WITH_EXACT_SOS_AND_COMPUTER_ASSISTED_CERTIFICATE
SUPPORT_LENGTH: at_most_log_3
FUNCTION_CLASS: ALL_COMPLEX_FINITE_FORM_ENERGY_L2_INPUTS
LOWER_BOUND: 2^-30_times_physical_L2_norm_squared
KERNEL_SCOPE: REANCHORED_SHORT_INTERVAL_OR_FIXED_ANCHOR_0_INSIDE_THE_INTERVAL
FIXED_ANCHOR_KERNEL_ON_ARBITRARY_DISTANT_SHORT_INTERVALS: NOT_CLAIMED
PRIME_2: RETAINED_EXACTLY
PRIME_3_ENDPOINT: ZERO_CORRELATION_NOT_OMITTED_ERROR
HIGHER_PRIME_POWERS: ZERO_BY_SUPPORT
POSITIVE_HIGH_FREQUENCY_REMAINDER: EXPLICIT
FINITE_SIGN_METHOD: EXACT_INTEGER_SYLVESTER_AND_RATIONAL_LDL
INTERVAL_ENGINE: MPMATH_IV_ELEMENTARY_OPERATIONS_WITH_PROVED_SPECIAL_FUNCTION_REMAINDERS
INTERVAL_DPS: 70
REFINEMENT_DPS: 90
GAUSS_ORDERS: [40,48]
FINITE_PARITY_DIMENSIONS: [31,30]
SOURCE_TO_COMPARISON_OPERATOR_ERROR_UPPER: 2^-40
RATIONAL_CERTIFICATE_SHA256: 8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0
REFINED_RATIONAL_MATRIX_IDENTICAL: true
NEGATIVE_CONTROL: DOUBLED_PRIME_2_WEIGHT_HAS_CONSTANT_TEST_UPPER_BELOW_MINUS_23_OVER_100
VERIFIER: PAPER
VERIFIER_DETAIL: COMPUTER_ASSISTED_INTERVAL_ENCLOSURE_PLUS_EXACT_INTEGER_ARITHMETIC
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_EXECUTED: false
PURELY_NONCOMPUTATIONAL_GEOMETRIC_PROOF: NOT_CLAIMED
RH_ASSUMED: false
RH_PROVED: false
GLOBAL_PASSIVE_SECTION_P_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: ALL_TESTS_ON_THE_FIRST_BOUNDED_SUPPORT_STEP
```

## 0. Result and the meaning of a short screw segment

Ы. The first bounded-support step is obtained with an exact sum-of-squares identity and an explicitly executed finite certificate. The geometric mechanism is orthogonal time-band projection, not an assumed positive Hamiltonian and not a numerical list of CCM eigenvalues. A finite rational positivity check is part of the proof; this is not advertised as a purely noncomputational trace-formula proof.

Let L=log(3), b=L/2, and I=[-b,b]. For every complex f supported in I with finite Weil form energy,

    W[f] >= kappa ||f||_2^2,       kappa=2^-30.                 (A)

Translation invariance and zero extension give the same result for support in any interval of length at most L. Infinite-energy inputs are understood in the extended-form sense; the quadratic-form domain is not silently replaced by all L2 with finite values.

Consequently the requested original kernel is positive on [0,L], on [-L/2,L/2], and on every shorter interval containing its anchor 0. More generally, for u in an interval I0 of length <=L,

    K_u(s,t)=g(s-t)-g(s-u)-g(u-t),    s,t in I0,

is positive. This is the natural reanchored screw segment.

The fixed kernel K_0 restricted to every arbitrarily translated short interval is a different, global assertion: its one-point diagonal would give 2Psi(t)>=0 for every real t. No such assertion is claimed. Likewise this result does not prove continuation of an arbitrarily long positive past through a new short section.

## 1. Source lock, imports, and claim ledger

The protocol was read from rh_clean through GitHub. The preceding PASSIVE_SECTION_P file was read at inbox commit 11f6368323d8aaac3d3c0a6a95873b86294cc540, blob 755c8535d18a9ea68d366934f4158981a50c0728. That file is not present at the supplied rh_clean base path; the explicitly supplied inbox pin is the source used. Base a1d2a973 exists and records diagnostic extension margins, not a source positivity theorem.

Primary imports:

S1. M. Suzuki, arXiv:2206.03682v4, (1.1), (1.3), (1.4), source normalization and the unconditional explicit formula. The PDF and the formula page were read, including a web screenshot. No positive zero measure is imported.

S2. A. Connes and C. Consani, arXiv:2006.13771v1, Theorem 1 and Corollary 2, printed p.3. The page was read and viewed. Its test support [2^-1/2,2^1/2] corresponds to logarithmic length log(2), with additional transform-vanishing conditions. It does not itself prove this all-test log(3) statement with the p=2 atom. Its geometric approach motivates, but is not substituted for, the construction below.

S3. NIST DLMF 5.9 (Binet integral for the digamma function), 10.54.1-2 (spherical Bessel integrals). All quantitative remainder bounds used below are also derived here.

S4. mpmath 1.3.0 documentation, interval context: elementary operations have enclosing semantics; the interface is experimental. Only elementary interval operations are used. The unsupported interval digamma and Bessel routines are not used: they are replaced by proved finite expansions. Exact matrix signs are checked with integers, independently of floating eigenvalue routines.

| Claim | Scope | Verifier | Inputs |
|---|---|---|---|
| Full source symbol and pole pair | ABSTRACT | PAPER | E,F,I,A |
| Positive out-of-band remainder for T=40 | ABSTRACT | PAPER | A,F,E; one interval scalar enclosure |
| All-mode projection-tail estimate | ABSTRACT | PAPER | LA,A |
| Two rational matrices minus 2^-29 I are positive | FINITE_CELL | PAPER | Exact integer arithmetic; interval source return |
| Exact SOS and (A), for all bounded-support inputs | ABSTRACT | PAPER | Previous independently stated budgets |
| All-node first screw segment | ABSTRACT | PAPER | LA,A and exact source pullback |
| Global P or RH | COFINAL_FAMILY | CONDITIONAL | Not supplied by this result |

No Z input, zero table, RH premise, or hypothetical zero location enters the proof. E denotes the actual Lambda weights; F the actual gamma/pole completion; I the ordinary integer support; A analysis; LA Hilbert-space and finite-matrix algebra.

## 2. Full source, including p=2 and both poles

Use F_f(t)=integral_I f(x)exp(-itx)dx and the physical L2 norm. Set

    a(t)=Re psi(1/4+it/2)-log(pi),
    c2=log(2)/sqrt(2),
    s(t)=a(t)-2c2 cos(t log(2)),
    p(x)=sqrt(2) cosh(x/2),  r(x)=sqrt(2) sinh(x/2).

The exact form on I is

    W[f]=(1/(2pi)) integral_R s(t)|F_f(t)|^2 dt
          +|<p,f>|^2-|<r,f>|^2.                            (1)

Indeed, the prime term is -c2 Q_f(log 2), Q_f(u)=2Re integral conj(f(x))f(x+u)dx. For n>=3 the supports do not overlap in positive measure; at n=3 equality of the support length still gives Q_f(log 3)=0. All higher weights are therefore zero contributions by support, not an arithmetic truncation error.

For general complex f the pole is 2Re(A_+(f) conjugate(A_-(f))), equal to the difference in (1). The negative odd pole is retained. Reflection splits the full complex space into even and odd orthogonal sectors, and (1) has no mixed-parity terms.

The preceding inbox gives the exact derivative-measure pullback from K_g. It applies to the compact step functions used for all-node Gram matrices; their archimedean energy is finite. No Fourier-carrier dimension is changed in claiming a consequence for the original A_m: (A) is a stronger, full supported-space theorem, which can then be restricted to any original finite carrier lying in the window.

## 3. Geometric separation: time-limited inputs and a positive frequency exterior

Fix the exact constants

    T=40, beta=4/5, kappa=2^-30.

For t>=0, the convergent digamma difference series shows that a(t) is increasing:

    a(t)=a(0)+sum_(k>=0) (t/2)^2 /
               [(k+1/4)((k+1/4)^2+(t/2)^2)].

An elementary interval evaluation, with its explicit Binet remainder specified in section 6, gives

    a(40)-2c2 = 0.8707181997201305010775639... > 4/5.

Hence, unconditionally,

    s(t)-beta >= 0,                  |t|>=40.               (2)

Let e_t(x)=exp(itx), x in I, and define the bounded self-adjoint operator

    C_beta=beta I+p tensor p-r tensor r
           +(1/(2pi)) integral_(-T)^T
                        (s(t)-beta) e_t tensor e_t dt.       (3)

The rank-one convention is (v tensor v)f=v<v,f>. Then, exactly,

    W[f]=<f,C_beta f>+||T_out f||^2,
    (T_out f)(t)=1_(|t|>T) sqrt((s(t)-beta)/(2pi)) F_f(t).  (4)

The last norm is manifestly nonnegative; it contains the entire omitted frequency region. It is not an error estimated from sampled zeros. The operator T_out is defined on the original form domain.

## 4. A finite geometric projection, with the whole complement paid

Take the orthonormal Legendre functions

    phi_n(x)=sqrt((2n+1)/L) P_n(x/b),  n>=0,

and let P project onto n=0,...,60, Q=I-P. This is an auxiliary orthogonal projection in the SAME physical L2 space, not a replacement source matrix. Its Fourier columns are

    F_phi_n(t)=(-i)^n sqrt(L(2n+1)) j_n(bt).

For real t let

    v_n(t)=(-1)^floor(n/2) sqrt(L(2n+1)) j_n(bt),
    h_n=sqrt(2L(2n+1)) i_n(b/2),

where j_n and i_n are spherical Bessel and modified spherical Bessel functions. In each parity block the exact finite matrix is

    C_nm=beta delta_nm
          +(1/pi) integral_0^T (s(t)-beta)v_n(t)v_m(t)dt
          +epsilon h_n h_m,                                (5)

with epsilon=+1 for even n,m, epsilon=-1 for odd n,m. There are 31 even and 30 odd columns.

### 4.1. Infinite Legendre tail

The positive-weight Bessel integral gives, for real x,

    |j_n(x)| <= |x|^n/(2n+1)!!.

Put n0=61, X=Tb and

    tau=L(2n0+1)X^(2n0)/((2n0+1)!!)^2
              /[1-X^2/((2n0+1)(2n0+3))].                 (6)

The ratio bounds all subsequent terms. Uniformly for |t|<=T,

    ||Q e_t||^2 <= tau < 2^-132.

Using |s-beta|<8 on [0,40] and ||e_t||=sqrt(L), the band contribution to
||C_beta-(PC_beta P+beta Q)|| is at most

    (8T/pi)(2 sqrt(L tau)+tau).                            (7)

The scalar bound |s-beta|<8 follows from a(0)>-27/5, a(40)<2, c2<1/2; these scalar inequalities are enclosed by the same interval calculation. There is no bound assumed on a Galerkin tail eigenvalue.

Similarly i_n(x)<=exp(x)x^n/(2n+1)!! for x>=0. Thus the sum of squared omitted pole coefficients is at most

    tau_p=2L exp(b)(2n0+1)(b/2)^(2n0)/((2n0+1)!!)^2
              /[1-(b/2)^2/((2n0+1)(2n0+3))] < 2^-700.

A safe pole-operator error is 8sqrt(tau_p)+2tau_p. Both signs of the poles are included.

### 4.2. Analytic quadrature, not numerical quadrature without a remainder

Each integral in (5) is divided into 80 intervals of length 1/2, with the 40-point Gauss-Legendre rule on each. On the Bernstein ellipse rho=2 of each interval, |Im t|<=3/16, Re(1/4 +/- it/2)>1/8, and |1/4 +/- it/2|<22. From

    psi(z)=-gamma_E-1/z+sum_(n>=1) z/[n(n+z)]

one gets |psi(z)|<53. The complexified symbol and the Bessel/Legendre evaluation vectors consequently give an operator-norm bound M=512 for the analytic matrix integrand. The norm of the latter evaluation vector is bounded by sqrt(L)exp(b|Im t|), independently of the finite dimension.

Truncate the Chebyshev series at degree 79. Its tail is <=2M rho^-80/(1-rho^-1). Both the integral and the positive Gauss rule have norm equal to their total mass. Exactness on degree 79 therefore bounds the total quadrature error by

    epsilon_GL <= 8 T M/(pi 2^80).                         (8)

This proves an operator bound, not only entrywise agreement between two quadratures.

### 4.3. Rational approximation and exact finite signs

The executable appendix isolates each Gauss root in a rational interval by exact signs of its degree-40 Legendre polynomial at the two endpoints. Forty disjoint sign-changing intervals certify all forty roots. Interval recurrence encloses their exact weights.

The scalar quadrature coefficient and each real Fourier column value are rounded to multiples of 2^-100, each with a checked interval error <2^-90. The resulting outer products are accumulated with integers. Pole vectors are treated identically. The final symmetric matrices G_even,G_odd are rounded to multiples of 2^-80.

Since an exact evaluation vector has norm <2, its rounded error has norm <8*2^-90, and each scalar quadrature coefficient has modulus <4, a safe total scalar-rounding error is

    1000*(3200+1)*2^-90.

Matrix rounding costs at most 61*2^-80. All these are errors from exact source expressions to explicitly defined dyadic rationals.

The matrices

    R_even=G_even-2^-29 I,  R_odd=G_odd-2^-29 I              (9)

have all leading principal determinants strictly positive. This was checked by fraction-free Bareiss elimination on INTEGER matrices, with every division checked exact. A separate SymPy rational LDL computation reproduced positivity and the equality L D L^T=R exactly. This second implementation is not an independent analytic review.

Certificate metadata:

| Block | Dimension | Smallest LDL diagonal, for information | Exact determinant numerator SHA-256 |
|---|---:|---:|---|
| even | 31 | 0.00309751051730317091009157... | d1fd3e6a268b545d0c672d6bc64ac84c9be08ec6b6368c4a74d848319f998967 |
| odd | 30 | 0.01940871944159910099675748... | 5895d0a4661b117dadfbd979a6bfd4e474d8c21d1b29b368486e47d53c84362d |

The LDL diagonals are NOT eigenvalue bounds. It is the exact positivity of (9) that supplies G>=2^-29 I. The dyadic matrix payload is deterministically regenerated by the appendix; its canonical JSON SHA-256 is

    8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0.

### 4.4. Complete error budget

Write G=G_even direct_sum G_odd in the corresponding orthonormal coordinates, and

    E=C_beta-[P G P+beta Q].

Here PGP denotes synthesis of G on ran(P). The combined bound gives

    ||E|| < 2^-40 < kappa.                                (10)

Executed interval upper budgets, displayed only as decimal summaries:

| Contribution | Size |
|---|---:|
| Infinite band-projection tail | <1.738e-18 |
| Both pole tails | <9.728e-136 |
| Analytic Gauss remainder | <4.314e-20 |
| Scalar interval-to-dyadic rounding | <2.586e-21 |
| Matrix rounding | <5.046e-23 |
| Total | <1.784e-18 |

The operative bound used in the proof is the checked rational threshold 2^-40, not rounded decimal subtraction. At 90 interval digits and Gauss order 48, the generated dyadic matrices were IDENTICAL, with a smaller analytic error bound. No large-m experiment enters the proof.

## 5. The requested exact sum of squares

Let V f be the 61 orthonormal coefficients in parity order. Exact rational LDL gives

    G-2kappa I = L_D D_D L_D^*,        D_D strictly positive diagonal.

Define, BEFORE making any positivity inference about W,

    B=sqrt(kappa) sum_(j>=0) binom(1/2,j)(E/kappa)^j.        (11)

This norm-convergent series is justified by the independently proved ||E/kappa||<2^-10. It is self-adjoint and B^*B=kappa I+E. It is not the circular instruction to take a square root of an operator whose positivity is the target.

Combining (4), (9), and (10) gives the exact identity

    W[f] = kappa ||f||^2
           +sum_j (D_D)_jj |(L_D^* V f)_j|^2
           +(beta-2kappa)||Q f||^2
           +||B f||^2
           +||T_out f||^2.                               (12)

Every coefficient and norm on the right is nonnegative. Each operator is explicitly constructed from the original source, fixed projections, and the certified rational matrices. Identity (12) proves (A).

Equivalently, collect the five displayed components into a linear map R. Then W[f]=||R f||^2. This supplies an actual Hilbert-space geometric realization on the segment, not a postulated passivity property. It can also be written as the trace of the positive rank-one operator |R f><R f|. The construction is different from the Sonin trace in Connes-Consani; no equality to that particular trace is claimed.

## 6. Why the elementary interval computations enclose the source

For z=1/4+it/2, 0<=t<=40, put w=z+64. The digamma recurrence and Binet integral give, with P0=14,

    psi(z)=log(w)-1/(2w)
           -sum_(k=1)^(P0-1) B_(2k)/(2k w^(2k))
           -sum_(k=0)^63 1/(z+k) + R,
    |R| <= 2 |B_(2P0)|/[2P0 64^(2P0)].                    (13)

Proof of the bound: expand 1/(u^2+w^2) in the Binet integral through the appropriate finite geometric sum. Since |Im w|<=Re(w)/2, Re(w^2)>=3|w|^2/5. Use

    integral_0^infinity u^(2P0-1)/(exp(2pi u)-1)du
       = |B_(2P0)|/(4P0).

The factor 2 in (13) is conservative. Each complex remainder component is enclosed by +/- this real bound. The Bernoulli numbers and all recurrence coefficients are exact rationals.

The spherical-Bessel seed uses

    j_n(x)=x^n/(2n+1)!! * sum_(k>=0) a_k,
    a_0=1, a_(k+1)/a_k=-x^2/[2(k+1)(2n+2k+3)].

For i_n change the sign to plus. After 120 terms the remaining ratios decrease and are <1/2; the next term divided by one minus its ratio bounds the whole absolute tail. Backward recurrence j_(n-1)=(2n+1)j_n/x-j_(n+1) then encloses all needed columns. Only interval +,-,*,/,sqrt,exp,log,cos are used; no unverified special-function interval routine or black-box quadrature sign is used.

## 7. All finite node sets and the atom-2 negative control

For nodes 0<=t_i<=ell<=L and arbitrary complex c_i, let

    f_c(x)=sum_i c_i 1_(0,t_i)(x).

The exact measure pullback gives

    sum_(i,j) conjugate(c_i) K(t_i,t_j)c_j = W[f_c]
       >= kappa sum_(i,j) conjugate(c_i)min(t_i,t_j)c_j.     (14)

Thus K >= kappa M on ALL finite configurations in the first segment; there is no fixed mesh, node separation, or mode cutoff in this conclusion. Distinct positive nodes give strict positivity, while the anchor 0 and repetitions give the correct zero directions. Reanchoring and translation prove the corresponding statement on every short screw segment. For a centered interval, use the oriented indicators between 0 and t; the lower comparison kernel is (|s|+|t|-|s-t|)/2.

The entire principal block for old and new nodes inside this first segment is positive. Hence all its guarded Schur complements are nonnegative. This is the first bounded-support instance of (P), not (P) after an arbitrary remote old history.

The positivity is sensitive to the arithmetic weight. Replace c2 by 2c2 while preserving all other terms. For the unit constant f=L^-1/2 1_I, direct evaluation of the SAME source gives the interval

    -0.23991071814 < W_doubled[f] < -0.23945525737.

The proof uses only 1000 positive exponential terms for the archimedean constant test and an explicit integral upper tail. The checked coarse upper is below -23/100. Therefore the construction does not declare arbitrary positive prime weights passive. It retains the actual c2, and its negative control fails as required.

A planted complex quartet changes the smooth source and cannot be fed to the certificate while retaining the zeta symbol. Local positivity may survive small planted perturbations; this finite first step is not claimed as a global zeta discriminator.

## 8. Closeout and verification handoff

DOWNSTREAM_CONSUMER: initialize the exact screw kernel on the first bounded-support interval, with all finite node configurations.
ACTUAL_CONSUMER_REQUIREMENT: kernel positivity on [0,log(3)], or equivalently its reanchored segment formulation.
ORIGINAL_REQUESTED_OBJECT: exact source-matched positive geometric identity including p=2.
ORIGINAL_OBJECT_IS: supplied as (12), with a finite computer-assisted rational certificate; a purely noncomputational Sonin-space derivation is not supplied.
KNOWN_WEAKER_INTERFACES: nonnegative source form without explicit coercivity would suffice for initialization; (A) is stronger on this fixed support.
FAILURE_TYPE: OTHER for the unproved global extension; no obstruction to this local theorem is asserted.
EPISTEMIC_STATUS: local computer-assisted PAPER result; global P remains RESEARCH_DEBT.
NOVELTY_AXIS: this response's source-matched SOS/certificate; no historical priority claim.
CLOSES: first-step all-node positivity, including the first prime atom and both pole sectors.
OPENS: no new mathematical supplier for this local statement.
REOPEN_TRIGGER_FOR_GLOBAL_P: a same-source argument controlling the growing old-history response, not an unbounded extrapolation of (14).

Predictions registered before the certified run: positive exact finite blocks; full operator error below 2^-40; nonnegative exterior symbol; negative doubled-prime control; correct anchor scope. All five passed. Exploratory binary64 matrices preceded registration and were used only to choose T and projection degree, not as proof.

Independent checks performed by this author: 90-digit/order-48 interval rerun, identical dyadic matrices; separate exact rational LDL reconstruction of both matrices. These are not an independent author's review. No Lean toolchain or Arb calculation is claimed.

CODEX DIRECTIVE (one audit, not a new mathematical subproblem): independently reproduce the appendix and check source parity/pole normalization, Binet and Bessel remainders, operator-norm projection/quadrature bounds, and the fixed-anchor restriction. Acceptance requires all exact determinants positive AND all source-to-matrix bounds; reproducing only the finite spectrum is insufficient.

WORKDIR: a writable directory containing the extracted appendix as certify.py.
COMMAND: uv run --with mpmath==1.3.0 --with sympy==1.14.0 python certify.py
EXPECTED: both exact Sylvester PASS lines, full remainder PASS, doubled-prime negative PASS, and the canonical certificate SHA-256 in the header.
Lean axiom profile: not applicable; no Lean source was written.

Delivery: this new verdict is intended for docs/routeB_bus/proshka/ on proshka_inbox_2026-10-31. No old verdict, route-state file, rh_clean pointer, or Lean declaration is changed. Commit SHA is returned after remote readback; repository delivery is not an additional mathematical verification.

## Appendix: complete certificate generator and exact verifier

The program writes the canonical dyadic matrices and the execution report next to itself. All constants needed to reconstruct them are present. The output matrices are not taken from a numerical eigensolver.

```python
#!/usr/bin/env python3
"""Source-exact all-vector certificate. Requires mpmath, sympy.
Elementary iv intervals + proved Binet/Bessel remainders + integer Bareiss.
No interval eigenvalues, Arb, Lean, or RH premise is used.
"""
from __future__ import annotations
import hashlib,json,math,time
from fractions import Fraction
from pathlib import Path
import mpmath as mpm
import sympy as sp
OUT=Path(__file__).resolve().parent
mp=mpm.mp;iv=mpm.iv;mp.dps=90;iv.dps=70
N=60;Q=40;PANELS=80;T=40;BITS=100;MBITS=80
SCALE=1<<BITS;MSCALE=1<<MBITS;EPS=iv.mpf(2)**-90
beta=iv.mpf(4)/5;length=iv.log(3);b=length/2;log2=iv.log(2);c2=log2/iv.sqrt(2)
START=time.monotonic()
def end(x,hi=False):return mp.mpf(x._mpi_[int(hi)])
def itext(x):return [mp.nstr(end(x),25),mp.nstr(end(x,True),25)]
def quant(x):
 n=int(mp.nint((end(x)+end(x,True))*SCALE/2))
 assert abs(x-iv.mpf(n)/SCALE)<EPS,('quant',itext(x))
 return n
def lp(n,x):
 p0=iv.mpf(1);p1=x
 if n==0:return p0,iv.mpf(0)
 for k in range(1,n):p0,p1=p1,((2*k+1)*x*p1-k*p0)/(k+1)
 return p1,p0
def gauss(n):
 approx,_=mp.gauss_quadrature(n,'legendre');den=1<<200;out=[];last=None
 for v in approx:
  cen=int(mp.nint(v*den));lo=iv.mpf(cen-2)/den;hi=iv.mpf(cen+2)/den
  
  def exact_p(y):
   p0=Fraction(1);p1=y
   for k in range(1,n):p0,p1=p1,((2*k+1)*y*p1-k*p0)/(k+1)
   return p1
  assert exact_p(Fraction(cen-2,den))*exact_p(Fraction(cen+2,den))<0
  x=iv.mpf([end(lo),end(hi,True)])
  if last is not None:assert last<x
  assert x>-1 and x<1
  pn,pm=lp(n,x);der=n*(pm-x*pn)/(1-x*x);assert abs(der)>0
  w=2/((1-x*x)*der*der);assert w>0 and w<2
  out.append((x,w));last=x
 return out
P=14;BERN=[Fraction(sp.bernoulli(2*k)) for k in range(1,P+1)]
REM=iv.mpf(2*abs(BERN[-1].numerator))/(BERN[-1].denominator*(2*P)*64**(2*P))
def psi(z):
 w=z+64;assert w.real>=64 and abs(w.imag)<=32
 v=iv.log(w)-1/(2*w)
 for k,B in enumerate(BERN[:-1],1):v-=iv.mpf(B.numerator)/B.denominator/(2*k*w**(2*k))
 for k in range(64):v-=1/(z+k)
 rr=iv.mpf([-end(REM,True),end(REM,True)])
 return v+iv.mpc(rr,rr)
def symbol(t):return psi(iv.mpc(iv.mpf(1)/4,t/2)).real-iv.log(iv.pi)-2*c2*iv.cos(log2*t)
def df(n):return math.prod(range(1,2*n+2,2))
def seed(n,x,modified=False):
 term=iv.mpf(1);total=term
 for k in range(120):
  term*=x*x/(2*(k+1)*(2*n+2*k+3))
  if not modified:term=-term
  total+=term
 nxt=abs(term*x*x/(2*121*(2*n+243)))
 rat=x*x/(2*122*(2*n+245));assert rat<iv.mpf(1)/2
 rr=nxt/(1-rat);total+=iv.mpf([-end(rr,True),end(rr,True)])
 return x**n/df(n)*total
def jvals(x):
 assert x>0 and x<22
 vals=[None]*(N+3);vals[N+1]=seed(N+1,x);vals[N+2]=seed(N+2,x)
 for k in range(N+1,0,-1):vals[k-1]=(2*k+1)*vals[k]/x-vals[k+1]
 return vals[:N+1]
def bareiss(M):
 A=[r[:] for r in M];n=len(A);prev=1;ds=[]
 for k in range(n):
  p=A[k][k];assert p>0,('pivot',k,p);ds.append(p)
  if k<n-1:
   for i in range(k+1,n):
    for j in range(i,n):
     v,r=divmod(p*A[i][j]-A[i][k]*A[k][j],prev);assert r==0
     A[i][j]=A[j][i]=v
   for i in range(k+1,n):A[i][k]=A[k][i]=0
  prev=p
 return ds
def progress(done,total):
 e=time.monotonic()-START;eta=e*(total-done)/max(done,1);n=30*done//total
 print('['+'#'*n+'-'*(30-n)+f'] {done}/{total} elapsed={e:.1f}s ETA={eta:.1f}s',flush=True)
def main():
 roots=gauss(Q);print('PASS certified algebraic Gauss nodes/weights',flush=True)
 lo=psi(iv.mpc(iv.mpf(1)/4,20)).real-iv.log(iv.pi)-2*c2
 assert lo>beta;assert c2<iv.mpf(1)/2
 a0=psi(iv.mpc(iv.mpf(1)/4,0)).real-iv.log(iv.pi)
 aT=lo+2*c2
 assert a0>-iv.mpf(27)/5 and aT<2 # proves |symbol-beta|<8 on [0,40]
 print('PASS tail symbol lower',itext(lo),flush=True)
 fac=[iv.sqrt(length*(2*n+1)) for n in range(N+1)]
 inds=[list(range(0,N+1,2)),list(range(1,N+1,2))]
 acc=[[[0]*len(ii) for _ in ii] for ii in inds]
 for panel in range(PANELS):
  for X,W in roots:
   t=iv.mpf(panel)/2+iv.mpf(1)/4+X/4
   aw=W/4*(symbol(t)-beta)/iv.pi;assert abs(aw)<4;ai=quant(aw)
   js=jvals(b*t);vs=[quant(fac[n]*js[n]*((-1)**(n//2))) for n in range(N+1)]
   for k,ii in enumerate(inds):
    vals=[vs[n] for n in ii];A=acc[k]
    for i in range(len(ii)):
     av=ai*vals[i]
     for j in range(i,len(ii)):A[i][j]+=av*vals[j]
  if panel%8==7:progress((panel+1)*Q,PANELS*Q)
 pole=[quant(iv.sqrt(2)*fac[n]*seed(n,b/2,True)) for n in range(N+1)]
 mats=[];details=[]
 for k,ii in enumerate(inds):
  sz=len(ii);G=[[0]*sz for _ in ii]
  for i in range(sz):
   for j in range(i,sz):
    x=acc[k][i][j]+(1 if k==0 else -1)*pole[ii[i]]*pole[ii[j]]*SCALE
    num=5*x+(4*SCALE**3 if i==j else 0);den=5*SCALE**3
    g=(num*MSCALE+den//2)//den;G[i][j]=G[j][i]=g
  shifted=[r[:] for r in G]
  for i in range(sz):shifted[i][i]-=1<<(MBITS-29)
  ds=bareiss(shifted);rs=[Fraction(d,(ds[i-1] if i else 1)*MSCALE) for i,d in enumerate(ds)];r=min(rs)
  mats.append(G);details.append({'parity':['even','odd'][k],'dimension':sz,'exact_leading_minors_positive':True,'min_LDL_pivot':mp.nstr(mp.mpf(r.numerator)/r.denominator,25),'determinant_digits':len(str(ds[-1])),'determinant_sha256':hashlib.sha256(str(ds[-1]).encode()).hexdigest()})
  print('PASS exact rational Sylvester',details[-1],flush=True)
 n=N+1;x=T*b;rat=x*x/((2*n+1)*(2*n+3))
 tail=length*(2*n+1)*x**(2*n)/df(n)**2/(1-rat);assert tail<iv.mpf(2)**-132
 eb=iv.mpf(8)*T/iv.pi*(2*iv.sqrt(length*tail)+tail)
 pt=2*length*iv.exp(b)*(2*n+1)*(b/2)**(2*n)/df(n)**2/(1-(b/2)**2/((2*n+1)*(2*n+3)));assert pt<iv.mpf(2)**-700
 ep=8*iv.sqrt(pt)+2*pt;eg=iv.mpf(8)*T*512/(iv.pi*2**(2*Q))
 eq=iv.mpf(1000)*(PANELS*Q+1)/2**90;er=iv.mpf(N+1)/2**80;ee=eb+ep+eg+eq+er;assert ee<iv.mpf(2)**-40
 # Negative source control: double exactly the weight at n=2.
 KK=1000;ss=iv.mpf(0)
 for k in range(KK):
  lam=iv.mpf(2*k)+iv.mpf(1)/2
  ss+=(1-iv.exp(-lam*length))/(lam*lam)
 lam=iv.mpf(2*KK)+iv.mpf(1)/2
 rr=1/(lam*lam)+1/(2*lam)
 ss+=iv.mpf([0,end(rr,True)])
 sh=(iv.exp(length/4)-iv.exp(-length/4))/2
 cc=-a0
 control=2*ss/length-cc-4*c2*(length-log2)/length+32*sh*sh/length
 assert control<-iv.mpf(23)/100
 print('PASS negative doubled-prime control',itext(control),flush=True)
 errs={n:itext(v) for n,v in [('Legendre_tail',tail),('band_tail_error',eb),('pole_error',ep),('quadrature_error',eg),('scalar_quantization_error',eq),('matrix_rounding_error',er),('total_error',ee)]}
 print('PASS full operator remainder <2^-40',errs,flush=True)
 payload={'matrix_dyadic_bits':MBITS,'LDL_shift':'2^-29','even':mats[0],'odd':mats[1]};txt=json.dumps(payload,sort_keys=True,separators=(',',':'))+'\n';(OUT/'rational_certificate.json').write_text(txt)
 summary={'parameters':{'L':'log(3)','T':T,'beta':'4/5','degree':N,'Gauss':Q,'panels':PANELS,'iv_dps':iv.dps},'engine':'elementary interval arithmetic + explicit analytic remainders + exact integer Bareiss','Arb':False,'Lean':False,'RH_assumed':False,'certificate_sha256':hashlib.sha256(txt.encode()).hexdigest(),'tail_symbol_lower':itext(lo),'parity_blocks':details,'bounds':errs,'negative_control':itext(control),'lower_bound':'2^-30','elapsed_seconds':time.monotonic()-START}
 (OUT/'result.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()

```
