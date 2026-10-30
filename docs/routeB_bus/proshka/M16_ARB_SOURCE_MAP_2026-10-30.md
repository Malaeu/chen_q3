# Closed Arb entries versus the literal window kernel

Status: independently checked bounded PAPER source map. This checks
analytic formulas, not just matching floating values. The eigensolver/library
enclosure guarantee is a separate trusted numerical input, not Lean.

Targets: phase5_scripts/edge_ledger_build.py CCMArbBuilder, and the literal
form used by full_center_probe.matrix_K and NOESCAPE, at m=N=16.
Let L=log16,z=exp(-2L)=1/256, omega_n=2pi n/L,
j(s)=exp(-s/2)/(1-exp(-2s)), a=1/4+i omega_n/2.
Use Phi(z,k,a)=sum_{r>=0}z^r/(r+a)^k.
The elementary hypergeometric identity is
Phi(z,1,a)={}_2F_1(1,a;a+1;z)/a.

## Off-diagonal sine moment

Since j(s)=sum_{r>=0}exp(-(2r+1/2)s), and omega_n L is an integer multiple
of2pi, integrating each summand gives

 M_n=int_0^L j(s)sin(omega_n s)ds
    =(1/2)Im psi(a)+(exp(-L/2)/2)Im Phi(z,1,a).

Termwise integration is justified, for fixed n, by
sum_r int_0^L exp(-(2r+1/2)s)|sin(omega_n s)|ds<infinity,
using |sin(omega_n s)|<=|omega_n|s near0.
The digamma identity is Im psi(x+iy)=sum_{r>=0}y/((r+x)^2+y^2).
The builder's `term=2L/(L+4pi*i*n)*hyp` is exactly Phi(z,1,a)/2.
Thus its alpha_n equals M_n/pi, with odd extension and M_0=0.
Its off-diagonal wr=(alpha_j-alpha_n)/(n-j) is the literal moment expression.

## Diagonal cosine and weighted cosine

Define C_n=int_0^L j(s)(cos(omega_n s)-1)ds and
B_n=(1/L)int_0^L s j(s)cos(omega_n s)ds.
The same absolutely integrable geometric expansion gives

 C_n=-(Re psi(a)-psi(1/4))/2
     -(exp(-L/2)/2)Re[Phi(z,1,a)-Phi(z,1,1/4)],

 B_n=(1/L){Re psi_1(a)/4
     -exp(-L/2)Re Phi(z,2,a)/4
     -(L exp(-L/2)/2)Re Phi(z,1,a)}.

For B_n use int_0^L s exp(-u s)ds=[1-exp(-uL)(1+uL)]/u²;
the real part is unchanged by conjugating a. This derives B_n directly,
without differentiating an identity valid only at integer Fourier modes.
For n=0, the builder instead uses the equivalent removable-singularity
integrand s j(s)=exp(s/2)/(2 sinc(i s)).

In `_cos_minus_one`, Phi(z,1,1/4)=4*{}_2F_1(1/4,1;5/4;z), so the
three code terms equal C_n. In `_beta`, the rational factor
2L/(4pi*n-iL)=i/(2a), hence its imaginary part after multiplying hyp is
(1/2)Re Phi(z,1,a), exactly as in the displayed B_n.

Let D=int_0^L (1-exp(-s/2))j(s)ds. The code's exp_correction integrand
exp(s)/[(exp(s/2)+1)(exp(s)+1)] equals this integrand identically.
Its constant is c/2, c=EulerGamma+log(4pi tanh(L/2)), since
tanh(L/2)=(16-1)/(16+1). Thus gamma_n=C_n+D+c/2 and

 2gamma_n-2beta_n
   =c+int_0^L [2exp(s/2)(1-s/L)cos(omega_n s)-2]/[2sinh(s)]ds,

which is exactly the literal diagonal wr term.

## Pole, primes and parity

Both implementations use the same explicit rational W02(n,j), the result
of the two source pole integrals on the window. Both subtract
sum_{k=p^r<=16}log(p)/sqrt(k)*Q_{n,j}(log k), with the same piecewise Q:
2(1-s/L)cos(omega_n s) on the diagonal, and
[sin(omega_j s)-sin(omega_n s)]/[pi(n-j)] off it.
No prime powers above16 contribute when both tests are window-supported.
This assertion is not applied to the separate h_out pairing.
Finally the even compression is the unit basis e0,(e_j+e_-j)/sqrt2;
the builder entries K00, sqrt2 K0j, Kij+Ki,-j are exactly that compression.

Conditional on the inherited literal Q and W02 formulas, this proves that
the Arb builder encloses the intended raw even CCM matrix whenever its
special-function/quadrature operations return valid enclosures. It does not
use the numerical entrywise comparison as an analytic premise.

Independent read-only review found no sign/factor defect in alpha, C_n, B_n,
D, diagonal assembly, prime powers or orthonormal parity compression. Scope
is the literal m=N=16,L=log16 builder, not its separate L_override mode.
Reviewed pre-status SHA256:
22560423f96900d8a3df30efdcb9563bbe07518370a593e0d499e36b6ac8901e.
The inherited W02,Q formulas and trusted library enclosure semantics remain
explicit premises; this is not a fresh Lean certificate.
