# The computed objects

DIAGNOSTIC_NEVER_A_PROOF. All source terms remain intact.

## 1. Native inverse evaluation

The carrier is e0=1/sqrt(L), en=sqrt(2/L)(-1)^n cos(2pi n x/L),
zero outside [-L/2,L/2]. Use the full literal source A_m, original gamma
and pole conventions, and native kappa=1.1. U has orthonormal columns
spanning J-perp, including the real and imaginary constraints from every
included DH reflected pair. No singular-value threshold changes rank.

    C=U* A_m U,
    t_n=e_n(b),             v_b=U*t,
    e_n(z)=integral e_n(x) exp(izx)dx,    v_z=U*e(z),
    K_b=v_b* C^-1 v_b,      K_z=v_z* C^-1 v_z.

The endpoint and Fourier evaluations are DIFFERENT functionals on the same
coefficient space. At z=iy they are real:

    e_n(iy)=d_n 2y sinh(yL/2)/(sqrt(L)(y²+(2pi n/L)²)).

Query systems are solved, not pseudoinverted. When C is positive these are
finite inverse-norm evaluation kernels. Otherwise they are signed inverse
forms. For y=1/2,1,2, the reported proxy is rho=1/(yK_z), with the arbitrary
proportionality constant fixed to1. It has NO identified Weyl-radius role.
rho² is nonnegative whenever defined, even for indefinite C. First negative
inertia, negative K diagonal, a zero K and a singular C are separate events.

## 2. Arithmetic births versus raw integer steps

For fixed carrier order N, vary L through L0=log n. Let Q_n(L) denote the
physical correlation matrix at shift log n. The newly overlapping interval
has length epsilon=L-log n and both endpoint traces are e_b. Hence

    Q_n(L0)=0,
    Q_n(L0+epsilon)=2epsilon e_b e_b*+O(epsilon²),
    jump(A'_L)=-2b(n)/sqrt(n) e_b e_b*.                   (B1)

Thus there is NO value jump. If rank is locally fixed and U,e vary smoothly,
only the displayed rank-one term jumps in C'_L. Differentiating its inverse
gives, without requiring C positive,

    jump(K'_z)=2b(n)/sqrt(n) |t*U C^-1 U*e(z)|².          (B2)

The same formula holds for endpoint evaluation. The reported cross entries
come from the four solved systems. For zeta this kink is nonnegative and
is supported on prime powers. DH has signed coefficients at other integers
too. This local sign statement is algebraic; it does not pay the smooth
flow or establish passive canonical sections.

The raw difference K_(m+1)-K_m changes N, L, the Fourier functional, the
constraint rows, and often rank. It is NOT (B2). raw_steps.csv labels both
the starting atom m and ending atom m+1. No difference is assigned solely
to a prime just because its integer label is a prime power.

## 3. Source flow of the actual screw function

With g=-Psi from SOURCE_AUDIT.md, for L>0 away from births,

    g'(L)=-c/2-integral_L^infinity j(s)ds
             +g'_pole(L)+sum_(n<=exp L)b(n)/sqrt(n),
    g'_pole=-4sinh(L/2) for zeta, and0 for DH.

At L=log n, g has zero value jump and g' has jump b(n)/sqrt(n).
For the section [log m,log(m+1)],

    delta g = delta g_smooth
       +log((m+1)/m) sum_(n<=m)b(n)/sqrt(n).

The new atom at the ending endpoint has exactly zero value contribution;
the starting atom is already active on the open section. source_sections.csv
records all these pieces at 85 dps. Gamma, pole and every older arithmetic
atom remain in the expression. This scalar identity is not an impedance
transfer law or a proof that the combined section is passive.

## 4. Genuine nested curve geometry

Use the source kernel G(t,u)=Psi(t)+Psi(u)-Psi(|t-u|), not the native C.
For fixed old nodes t1,...,tn let G_n=(G(ti,tj)), and choose ONE fixed target
tau beyond the largest sampled segment. Set k_tau=(G(tj,tau)).

    E_n=k_tau* G_n^-1 k_tau.

For a new node with cross column c, diagonal d and target entry k_new,

    s=d-c*G_n^-1c,
    E_(n+1)-E_n=|k_new-c*G_n^-1k_tau|²/s.                (G1)

This is the block-inverse/Schur identity. Positive s gives a nonnegative
increment. A negative s can reverse it. Unpivoted LDL records every s and
negative inertia on the same nested matrices. Inertia can only accumulate
under nesting for EITHER world; it is not itself a distinguishing monotonicity.
The property being tested is preservation of positivity and of the sign in
(G1). After positivity fails, E is an algebraic inverse form, not a squared norm.

Uniform nodes use h=log(240)/240, tj=jh, target tau=240.5h. The DH resolution
control uses480 nodes and the SAME target. Sparse endpoint nodes are log n;
the aligned control adds their union with the fixed uniform mesh. Earlier
nodes never move. m-rows select the existing prefix with tj<=log m.
First sampled failure is resolution-dependent and not the intrinsic onset
of the continuous form. The target is outside current prefixes: an upper
bound E<=G(tau,tau) additionally needs positivity of the augmented target
Gram, not just of the current prefix.

## 5. What would count as passive assembly

A finite positive sampled kernel is a necessary local judge, not a
source-derived canonical transfer. A true section map must be constructed
from this SAME g/A source, gamma/pole data, endpoints and arithmetic history,
and preserve the upper half-plane for every admissible Herglotz load and
every upper-half-plane frequency. No such finite-end m_t is asserted here.
In particular the generic Hermitian resolvent is positive-imaginary even
for DH and is a useless substitute.

The actual GLOBAL completed logarithmic derivative Q(z) is separately
evaluated in IMPEDANCE_CONTROL.json. The three imaginary-axis probes all
look passive for both worlds. At the predetermined upper-half-plane point
below DH's first off-line pole, Im Q_DH is negative. This is a global
negative control, not a section-local attribution or a finite-end response.
