# SCREW_LINE_v1: bounded primary-source and normalization audit

DIAGNOSTIC_NEVER_A_PROOF. No new numerical source calculation, source
eigensystem, route-state change, or RH export was performed for this audit.

## Primary sources actually read

1. Masatoshi Suzuki, *Aspects of the screw function corresponding to the
   Riemann zeta-function*, arXiv:2206.03682v4, 30 May 2023. Primary PDF text:
   https://arxiv.org/pdf/2206.03682v4 . Read the definitions and Theorems
   1.1–1.2 on printed pp.1–3, equations (1.1)–(1.10).
2. Masatoshi Suzuki, *The screw line of the Riemann zeta-function and its
   applications*, arXiv:2209.04658v3, 17 May 2023. Primary PDF text:
   https://arxiv.org/pdf/2209.04658v3 . Read printed pp.1–3, equations
   (1.1)–(1.10), Theorems 1.1–1.2 and their stated RH conditions.

The primary PDF text extracts were read through the web tool. No successful
local PDF byte hash or visual PDF inspection is claimed. This is a bounded
audit, not a literature-completeness claim.

## Findings that constrain the proposed identification

**CONFIRMED:** Suzuki's first paper defines the scalar g=-Psi and
G_g(t,u)=g(t-u)-g(t)-g(-u)+g(0), equation (1.4), printed p.2. Its Theorem 1.2,
printed p.3, says global screw-function membership is equivalent to RH.
Equation (1.9) gives the zero representation. Global positive definiteness
cannot be used as an unconditional input; the paper separately notes a
small-interval unconditional positive-definiteness result.

**CONFIRMED:** The second paper's Theorem 1.1, printed p.2, constructs the
Hilbert-space screw line under RH. Its equation (1.10), printed p.3, is the
derivative pullback

    <D psi_1, D psi_2>_(G_g) = <psi_1, psi_2>_Weil,
    D psi = psi'.

It is not a statement that a physical CCM matrix is the point-sampling
matrix [G_g(t_i,t_j)]. The displayed theorem is initially on smooth compact
tests; finite window profiles require the endpoint-preserving extension
described below.

**GAP:** No actual Weyl radius has been identified with the proposed finite
kernel diagonal. A canonical system, its positive Hamiltonian, initial
normalization, boundary parameter and the exact relevant kernel column or
RKHS normalization must be pinned before a formula proportional to
1/(Im(z) K(z,z)) can be called a Weyl radius. This bounded audit has not
verified such a map in either source. It neither supplies nor assumes the
missing proportionality constant. A numerically defined reciprocal-kernel
proxy must retain the word proxy.

## Source-compatible physical map and its extension boundary

The following is the source-compatible extension suggested by the cited
derivative identity in the physical CCM convention; it is not an assertion
that every matrix of the same dimensions is a screw-line Gram. Suzuki's
displayed identity is on smooth compact tests. Extending it to these finite
BV window profiles requires the relevant continuity/smoothing justification,
which is not re-proved in this bounded diagnostic audit.

Let I=[-b,b], L=2b, and let phi_n denote the original zero-extended physical
cosine basis. Its distributional derivative is the finite signed measure

    mu_n = phi'_n,int(x) 1_I(x) dx
           + phi_n(-b) delta_(-b) - phi_n(b) delta_b.

The measure has total mass zero. For the real-even basis the two ordinary
endpoint values agree, but the endpoint masses have opposite signs. Omitting
them changes the proposed map. The formal finite-window pullback is

    A_ij = double-integral G_g(t,u) d mu_j(u) d mu_i(t).

Subject to that extension guard, for a positive screw kernel this is the Gram matrix of **integrated
derivative-test vectors** int x(t) d mu_n(t), not a point Gram of x(t).
The signed-measure integral of a continuous screw line is meaningful on the
compact interval. Differentiability of x(t) as a Hilbert-space curve must
not be assumed; the measure expression avoids that assumption.

The normalization is checked on the constant window chi_I. Its derivative
is delta_(-b)-delta_b, so its kernel energy is

    G_g(-b,-b)+G_g(b,b)-2G_g(-b,b) = -2 g(L),

using evenness and g(0)=0. Thus the original constant-source form gives

    g(L) = -K_source[chi_I]/2.

This also fixes the factor two and the interpretation of length L. A finite
interval of screw-line parameters has length L=log m, but the m+1 cosine
tests are not m+1 equally spaced points on that curve.

Conditional positivity of all these Gram matrices under RH is consistent
with this map. Treating that conditional positivity as already proved on
all lengths would assume the desired global screw-function property. The
discrete V_m and moving J_m-perp are not nested merely because m increases.

## Source formula for g and the arithmetic jumps

For t>=0 set a_k=2k+nu. The full constant-window source form is

    K_source[chi_(0,t)]
      = c_mat t + 2 sum_(k>=0) (1-exp(-a_k t))/a_k^2
        - 2 sum_(log n<t) b(n)/sqrt(n) (t-log n) + Pole(t).

This follows directly from the full source jump kernel
j(s)=sum_(k>=0) exp(-a_k s): the two archimedean terms combine as
2 integral_0^t s j(s) ds + 2t integral_t^infinity j(s) ds.
The displayed series is convergent and contains the full arch tail.

For zeta: nu=1/2, c_mat=-gamma-log(8pi)-pi/2, b(n)=Lambda(n), and
Pole(t)=32 sinh^2(t/4). Then g=-K_source/2 reproduces Suzuki's (1.1),
including its pole, linear constant, and positive prime-hinge term.

For the source-correct DH control: nu=3/2,
c_mat=log(5/pi)+psi(3/4), every signed logarithmic-derivative coefficient
b_D(n) is retained, and Pole=0. This defines a source-aligned scalar g_D;
it does not assert that g_D is a global positive screw function.

At an arithmetic threshold t=log n, g itself is continuous and its one-sided
derivative has the jump

    g'(log n +)-g'(log n -)=b(n)/sqrt(n).

For zeta this vanishes at non-prime-powers and is positive at prime powers.
For DH its sign follows the actual b_D(n), including non-prime-powers.
It is a derivative jump, not a jump of g. This sign agrees with the
constant-window endpoint atom and must not be reversed by changing between
g and -g.

## Genuine finite curve-geometry diagnostic and its limits

For fixed mesh Delta, consecutive screw-line increments have Toeplitz
covariances

    H_k = 2g(k Delta)-g((k-1)Delta)-g((k+1)Delta),
    H_0 = -2g(Delta).

This is obtained by taking four differences of G_g. Prefixes of this one
fixed-mesh Toeplitz matrix are genuinely nested. If the covariance matrix
is positive definite, the innovation variance e_n is the Schur complement
of its previous prefix. The Durbin/Levinson identity is

    e_n = e_(n-1) (1-|reflection_n|^2).

Therefore positivity implies a nonnegative, nonincreasing innovation
sequence. The implementation must stop or label a loss of positive
definiteness; taking absolute values of negative pivots would erase the
control failure. This is a valid finite diagnostic of the actual curve
kernel and does not depend on a fabricated Weyl-radius identification.
Separate meshes are separate nested sequences, not themselves a proof of
continuum monotonicity or RH.

## Evaluation variables: two different finite kernels

Suzuki's z in the spectral constructions is a Fourier/Mellin spectral
variable. It must not silently be replaced by a complex physical coordinate
inside a cosine. For a physical orthonormal synthesis U of S=J-perp:

1. Fourier evaluation uses v_n(z)=hat(phi_n)(z), an entire sinc transform
   of the zero-extended window. Its physical L2 kernel is
   K_phys(z,w)=(U^T v(z))^T conjugate(U^T v(w)).
2. Continuing the *interior* cosine to a complex spatial point uses instead
   v_n(x)=d_n(-1)^n cos(omega_n x)/sqrt(L). It is a different evaluation map;
   the zero-extended physical function has no such global spatial analytic
   extension across its endpoints.

If a positive compressed source metric B=U^T A U is explicitly selected,
the corresponding finite evaluation kernel is a(z)^T B^(-1) conjugate(a(w)).
This is a finite metric-dependent kernel. DH native B can be indefinite,
so its inverse expression is not then a positive RKHS kernel. Neither
finite kernel is automatically Suzuki's de Branges/model-space kernel or
a canonical-system Weyl disk. The exact feature/norm/evaluation crosswalk
remains required.

Verdict: Suzuki's smooth derivative-test pullback and the constant-window
g normalization **CONFIRMED**; the full finite-BV pullback retains the stated
extension guard;
unconditional global positive-Gram interpretation **NOT AVAILABLE**;
direct point-Gram identification and actual Weyl-radius identification
**GAP**. The fixed-mesh increment/innovation diagnostic is source-aligned
and feasible without claiming those missing identifications.
