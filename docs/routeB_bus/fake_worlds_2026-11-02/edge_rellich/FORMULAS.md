# Operators, Green terms and zero-side return

DIAGNOSTIC_NEVER_A_PROOF. All vectors and zero coordinates are the pinned
saved numerical inputs; no new eigenproblem or zero search is used.

## 1. The literal finite commutator

Let b=L/2, e0=1/sqrt(L), en=sqrt(2/L)(-1)^n cos(2pi n x/L), and
e_b=(d_n/sqrt(L)), d0=1,dn=sqrt2. P_m is physical orthogonal projection
onto this carrier. A_m is the full source matrix, retaining its actual
gamma factor, all logarithmic-derivative coefficients, and the zeta pole
only in zeta. Use D_int=x partial_x+1/2 on the interior and
D_m=P_m D_int P_m. This fixes a meaning of the requested finite commutator.

    D00=1/2, Dnn=1 (n>=1),
    Dij=d_i d_j j²/(j²-i²), i!=j,
    D+D^T=L e_b e_b^T.

The last equation is exactly integration by parts,
`<u,Dv>+<Du,v>=[xuv]_-b^b`. No f'(b) term occurs for this first-order
Green identity. Every saved cosine vector has f'(b)=0 EXACTLY, not merely
small numerically. Define K=(D-D^T)/2. For a unit real f,

    C=<f,[A,D]f>=V-B=2<Af,Kf>,
    V=2<Af,Df>,              B=L f(b)(Af)(b).             (F1)

Here (Af)(b) means synthesis of the FINITE modal vector A_m f, not an
assumed endpoint trace of an infinite source operator. A boundary formula
solely in f(b),f'(b) for a local second-order differential operator cannot
be imported for this nonlocal arithmetic A.

For the saved complement ground, Af=lambda f+r with r in J up to inherited
numerical residuals, so

    C=2<r,Kf>,
    V=lambda L f(b)²+2<r,Df>,
    B=lambda L f(b)²+L f(b)r(b).                          (F2)

The eigenvalue pieces cancel. The finite commutator measures leakage into
J. If both A and D are compressed to J-perp first, its expectation at the
compressed eigenvector is zero for ANY generator. These are algebraic
identities; they do not infer RH or an asymptotic edge law.

## 2. Physical weak dilation is a different test

Zero-extended f with f(b)!=0 is outside the domain of the global L²
dilation generator: its distributional derivative contains endpoint deltas.
Use instead the interior function g=D_int f, THEN zero-extend g. This is
a well-defined separate form test, generally outside the finite carrier.
For the physical Fourier transform F(z)=integral f(x) exp(izx) dx,

    H(z)=hat(g)(z)=L f(b)cos(bz)-F(z)/2-z F'(z).           (F3)

D_int f and the global distributional dilation must not be identified.
The actual weak variation is W=2q(f,g), not C. Its projection-return is

    W-V=2q(f,(I-P_m)D_int f).                             (F4)

This term is evaluated, not silently discarded.

For Q(s)=2 integral f(x)f(x+s)dx, 0<s<L, integration of a total derivative
over [-b,b-s] gives the symmetric mixed correlation

    Q_(f,g)(s)=L f(b)f(b-s)+(s/2)Q'(s),
    2<f,g>=L f(b)².                                     (F5)

Write the source as
`q(f)=c||f||²+integral_0^infty j(s)(2||f||²-Q(s))ds
       +pole(f)-sum_(2<=n<m) b(n)Q(log n)/sqrt(n)`.
The source weak split W=Bweak+Vweak used in the output is

    Bweak = c L fb²
       +2L fb [integral_0^L j(s)(fb-f(b-s))ds
                       +fb integral_L^infty j(s)ds]
       -2L fb sum b(n)f(b-log n)/sqrt(n)
       +2 L fb p(b)<p,f>,

    Vweak = -integral_0^L s j(s)Q'(s)ds
       -sum b(n)log(n)Q'(log n)/sqrt(n)
       -2<p,f><D_int p,f>.                              (F6)

The pole terms occur only for zeta, p=sqrt2 cosh(x/2).
Its exact source pair is j=exp(-s/2)/(1-exp(-2s)),
c=-EulerGamma-log(8pi)-pi/2. For DH j=exp(-3s/2)/(1-exp(-2s)),
c=-EulerGamma-log(8pi/5)+pi/2 and NO pole. DH includes every signed b(n),
including non-prime powers. No arbitrary continuum reference is subtracted.
The arch tail is analytic; n=m has zero overlap and no boundary atom is
manufactured. At s=0 the boundary integrand contains fb-f(b-s), not two
separately divergent integrals.

## 3. Finite zero heads and separately labeled balances

For each positive real zero gamma, the energy, finite commutator and weak
variation contributions are respectively

    2 F(gamma)²,
    4 F(gamma) hat(Kf)(gamma),
    4 F(gamma) H(gamma).                                 (F7)

For a DH reflected quartet represented by z=gamma+i eta they are

    4 Re(F(z)²),
    8 Re(F(z)hat(Kf)(z)),
    8 Re(F(z)H(z)).                                     (F8)

The saved census treats these zeros as simple; its numerical multiplicity
and completeness qualifications are inherited. Replacing the products
by absolute-value squares would destroy the DH signed metric.

Each finite zero block also admits the finite Green split
`V_block=2q_block(f,D_m f)`,
`B_block=L fb q_block(f,e_b)`, `C_block=V_block-B_block`.
The physical Fourier split from (F3) has

    W_boundary,line=4L fb F(gamma)cos(b gamma),
    W_volume,line=-2F(gamma)²-4gamma F(gamma)F'(gamma),
    W_boundary,quartet=8L fb Re(F(z)cos(bz)),
    W_volume,quartet=-4Re(F(z)²)-8Re(zF(z)F'(z)).          (F9)

These are finite-block identities. Do NOT identify their separate
infinite sums with the source Bweak,Vweak: F,H decay like 1/t, but the
separated boundary product in (F9) has only O(1/t) decay. Its infinite zero
sum is not absolutely convergent; cancellation with volume must occur
before summation or require a specified regularization.

Heads use gamma<=T, prefix T<gamma<=400 for zeta and <=310 for DH.
For energy, C, finite V/B and combined W, the output explicitly labels
`source balance above T` and `source balance beyond census`.
They are source minus finite sums, NOT independently evaluated or certified
infinite zero tails. No RH, zero completeness certificate or positivity
of the uncomputed zeta remainder is assumed.

## 4. One alternative, without fitting a generator to the answer

Let a(x)=x(1-x²/b²) and D_a=a partial_x+a'/2. It preserves parity and
a(±b)=0. Thus P_m D_a P_m is skew-symmetric and has zero Green boundary.
Its finite expectation is `2<Af,D_a f>=2<r,D_a f>`; on the compressed
complement it is again exactly zero at the eigenvector. This removes
the endpoint domain ambiguity but supplies no boundary-only lambda law.
The script evaluates it on the same fixed vectors. No A/f/lambda-fitted
generator, fitted coefficient or new optimization is used.

## 5. Owner-steered K1 and four-piece reading

The literal layer is a judge, not a candidate lambda law. Its additional
reported contractions are

    2<r,D_m f>=V-lambda Lfb²,
    <r,(D_m+D_m^T)f>=B-lambda Lfb²=Lfb r(b),
    ||D_m+D_m^T||=2m+1,
    <f,(D_m+D_m^T)f>=Lfb².

The four primary weak pieces are Varch, Varithmetic, Vpole, and the complete
Bweak from (F6), including its scalar term. Their sum is W. A direct
dilation identity has log(n)Q'(log n), because the partial derivative in
`[A,x partial_x]=[A,x]partial_x` remains. The even translation pair with
no derivative instead has an odd commutator whose real-even expectation
vanishes. The separate log-weighted Q probe in STEERING.json is therefore
NOT substituted for the derivative term.

For the arch piece one can integrate by parts, but it produces additional
terms, not a replacement by s*j*Q:

    -integral_0^L s*j(s)*Q'(s) ds
       =1+integral_0^L (s*j(s))'*Q(s) ds,

using ||f||=1, Q(0)=2, Q(L)=0 and s*j(s)->1/2.
The discrete prime derivative needs its own Stieltjes/distribution return
to eliminate Q'. At n=m, Q'(L-)=-2fb² and
`2Lfb f(b-L)+LQ'(L-)=0`; both weak birth pieces cancel exactly.

## 6. Owner-specified prolate operator, including its anomaly

Let p(x)=b²-x² and Wpro=-partial_x(p partial_x), without optional potential.
Its finite matrix is real symmetric. Thus f^T[A_m,Wpro_m]f=0 for ANY real
f, and for each real symmetric source component separately. The symmetric
form difference q(f,Wpro f)-q(Wpro f,f) is likewise exactly zero.

There is nevertheless a distinct interior maximal-expression anomaly.
For the original arch operator, near x=b-h,

    A_arch f(x)=(fb/2)log(1/h)+O(1),
    p(x)(A_arch f)'(x)->b fb,

with opposite flux -b fb at -b. This follows from j(s)~1/(2s): for x
approaching b, the removed right translate exposes fb*integral_h j(s)ds.
Since f'(b)=0, the derivative of the remaining interior translation of f'
has no competing endpoint flux. Both zeta and DH have this same small-s
kernel coefficient. Green's boundary is

    <f,Wpro_max A_arch f>-<Wpro f,A_arch f>
        =[p(f' A_arch f-f(A_arch f)')]_-b^b = -Lfb².

Consequently the interior strong arch commutator has expectation +Lfb².
A_arch f is outside the natural self-adjoint prolate domain because of
that nonzero endpoint flux. The outer distribution defect is -Lfb²,
restoring the zero symmetric-form value. Neither interpretation is silently
identified with the other.

For one atom A_s=-w(T_s+T_-s), 0<s<L, put a=b-s. The regular interior
prolate commutator has expectation +2w fb p(a)f'(a). The translated jump
of f0 at a gives Wpro(T_s f0) a delta-prime with coefficient fb p(a),
and the reflected jump supplies the other endpoint. Their commutator
contribution is -2w fb p(a)f'(a). Therefore each atom totals zero once
its shifted distributions are retained. At s=L, p(a)=0 and the overlap
is zero. Scalar and pole have zero prolate endpoint flux.

The prolate four-piece bookkeeping in STEERING.json is: arch interior
Lfb², arithmetic regular volume, pole zero, and jumps equal to minus the
arithmetic regular volume minus Lfb². Its total is exactly zero. The finite
and form zeros are algebraic values, not claims of newly measured tiny
CCM eigenvalues. Only the trace and regular arithmetic pieces are numerical.

The exact anomaly alone gives no log(T)/(pi*T) factor and no coefficient
four. Multiplying Lfb² by log(T)/(pi*T*L) would insert the empirical edge
scale by hand; the output reports this ratio only as the original R,
explicitly not an independent success. PROLATE_VALIDATION.json checks an
independent spatial projection, one shifted atom with its opposite jump,
and the endpoint kernel limit for both arch kernels.
