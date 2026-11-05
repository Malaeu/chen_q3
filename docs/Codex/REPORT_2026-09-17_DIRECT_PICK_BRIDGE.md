# A direct Pick consumer for the same full theta quotient

STATUS: ACCEPTED_LIMITED_PAPER; growth proved, Pick-to-RH transfer conditional.
Date: 2026-09-17. Base: 8d3a63ae28c1ac92f06f433cd7e1b8d4ec266679.
Isolated analytic research. No actual Pick membership or original V sign
is asserted. This checks a weaker sufficient entrance for the SAME forced
quotient; it does not construct another source or send another proof job.

## Inputs and the exact claim

Keep q=Phi/int_R Phi, rho(s)=q(sqrt(s)),
D(u)=int_0^infinity s^(u-1/2)rho(s)ds initially Re u>-1/2,
H(u)=D(u)/Gamma(u+1/2), phi_*(u)=4H(u-1)/H(u), and
F(z)=int_R exp(izx)q(x)dx=xi(1/2+iz)/xi(1/2).
The physical V still uses its original L2 normalization and all finite
admissible complex families. Its accepted transfer is not reproved here.

Pinned project inputs:
- REPORT_2026-09-17_KPS_MELLIN_DIVISOR_AUDIT.md, SHA256
  00cb5a4b3739314a8a584469179ee5cc8e72238a48f186f12d28cba2f4383528.
  S1 supplies entire real H and H(v)>0 for real v>-3/2; S3 is the
  independent control where Pick holds but KPS unit separation fails.
- REPORT_2026-09-17_KPS_MOMENT_INTERFACE.md, SHA256
  8db1503625708a8271f63ea9b1ff33ed5d38ecbe131718ab152688b322e528a0.
  Full source, Fourier normalization, and moments.
- PROSHKA_RESPONSE_GOAL058_KPSQUOTIENT_2026-09-17.md, SHA256
  14dcccc1270d83595d03dfcdb784c0b419e946b8fe2a966bfdaa153d5cd6647d.
  KQ14 is a REQUIRED independently accepted dependency:
  any nonreal D zero would prevent Pick membership, including initial
  numerator/denominator cancellation. Review SHA256
  fde1b165acc3fb4adc9ef436b69296af1301e25c60cb0884e53c2cf56ddf8a0e,
  verdict ACCEPT_KPSQUOTIENT_DENOMINATOR_FILTER_ONLY. Its full review and
  the independent parent check were read; no class membership is imported.

Claim R1 (unconditional from accepted source inputs): H has entire
order at most one, with max_(|u|<=r)|H(u)| <= exp(C(r+1)log(r+2)).
Claim R2 (conditional): if all zeros of this exact H are real, all zeros
of F are real. Their multiplicities are unrestricted.
Claim R3 (conditional on KQ14 and R1-R2): if this exact phi_* is a Pick
function, RH follows. No separate unit-separation assumption is needed
for this sufficient implication. Actual Pick membership remains OPEN.
Pick here means that the meromorphic source quotient extends holomorphically
to the entire open upper half-plane with nonnegative imaginary part.
Real-axis positivity alone, a truncated region, or discrete samples do not
satisfy this premise. This is not a necessary condition for RH.

## R1. The existing entire H has growth order at most one

The full source bound can be obtained directly, without any sign premise.
For x>=0, t=exp(2x)>=1, the defining series gives

 |q(x)| <= C t^(9/4) exp(-pi t)
                 sum_(k>=1) k^4 exp[-pi(k^2-1)]
          <= C' exp(-pi exp(2x)/2).

The k^2 terms are bounded by k^4 and t>=1; polynomial powers of t are
absorbed into half the exponential. Hence, for a finite C_0,

 |rho(s)| <= C_0 exp(-s), s>=0.                         (R1)

Indeed s-(pi/2)exp(2sqrt(s)) is bounded above on [0,infinity).
The full series near t=1 and evenness give local analyticity of rho,
already proved in the Mellin divisor audit. Choose 0<R<1 inside its
analytic disk, B bounding |rho| on |s|<=R, epsilon=R/2, and write
rho(s)=sum_(k>=0) a_k s^k. Cauchy gives |a_k|<=B R^(-k), and

 |rho(s)-sum_(k=0)^(M-1) a_k s^k| <= 2B(s/R)^M,
                  0<=s<=epsilon.                     (R2)

For an integer n>=1 and |u|=n choose M=n+1 in the already accepted
Taylor-subtracted continuation of D. Put sigma=Re u, so -n<=sigma<=n.
Every explicit simple fraction has denominator bounded away from zero:

 |u+k+1/2| >= ||u|-(k+1/2)| >= 1/2.

Its finite sum has modulus at most

 2B epsilon^(-n+1/2) sum_(k=0)^n (epsilon/R)^k
 <= 4B epsilon^(-n+1/2).                               (R3)

The remainder integral has modulus at most

 2B R^(-M) epsilon^(sigma+M+1/2)/(sigma+M+1/2)
 <= (4B/3) R^(-n-1),                                  (R4)

since sigma+M+1/2>=3/2 and epsilon<1. The tail integral from epsilon
to infinity is bounded, using (R1), by

 C_0 epsilon^(-n) int_epsilon^1 s^(-1/2)ds
       + C_0 int_1^infinity s^(n-1/2)exp(-s)ds
 <= C_1 epsilon^(-n)+C_0 n!.                           (R5)

Consequently |D(u)|<=exp(C_2(n+1)log(n+2)) on these integer circles.
They contain none of the possible real half-integer poles.

The standard reciprocal-Gamma product (DLMF 5.8.2) gives
|1/Gamma(u+1/2)|<=exp(C_3(n+1)log(n+2)) there: split the product
at k=ceil(2(n+1)); the finite logarithms are O(n log(n+2)), while
log|(1+w/k)exp(-w/k)|=O(|w|^2/k^2) for the tail, w=u+1/2.
Thus the same form of bound holds for H on each circle. H is already
entire, so maximum modulus extends it to the disk; taking n=ceil(r)
proves R1. In particular its order is at most one, hence strictly less
than two. No location of complex zeros has been used.

## R2. Direct classical transfer, with coefficients fixed exactly

For every integer n>=0, changing s=x^2 yields D(n)=mu_(2n).
Since mu_0=1 and Gamma(n+1/2)=(2n)!sqrt(pi)/(4^n n!),

 H(0)=1/sqrt(pi),
 H(n)/H(0)=4^n n! mu_(2n)/(2n)!.

Define the entire function

 G(w)=sum_(n>=0) H(n)w^n/[H(0)n!].                      (R6)

It is entire by the known full Fourier moment bounds, or immediately by
its exact coefficient relation to the even entire F:

 F(z)=G(-z^2/4).                                       (R7)

External classical input, not a newly proved theorem here: the Laguerre
coefficient-transform theorem says that a real entire function of order
less than two having only negative real zeros gives an exponential
coefficient transform sum A(n)w^n/n! with only negative real zeros.
The statement is reproduced as Lemma 1, printed p2, of Baricz--Singh,
*Zeros of some special entire functions*, arXiv:1702.00626v2; it is used
there for their special-function theorems. Lemma 4, p3, also states
Runckel's related canonical-product multiplier theorem. The original
1898 proof and Runckel's 1969 proof have not been independently audited.

Under the conditional real-zero premise for H, its previously proved
positivity on real u>-3/2 puts all its zeros strictly on the negative
axis. R1 pays the growth condition; H is real entire and H(0)>0.
Applying the named Laguerre theorem to H/H(0) gives negative real zeros
of G. If F(z)=0, then -z^2/4 is such a zero, so z^2 is strictly positive
real and z itself is real. F(0)=1 excludes a zero at zero.
This proves R2 as a closed CONDITIONAL transfer.

## R3. How the new zero-propagation result reduces the entrance

Use the independently accepted KQ14 and suppose the actual phi_*
is Pick. KQ14 excludes every nonreal zero of the continued D. At every
nonreal point Gamma(u+1/2) is finite and nonzero, so H and D have exactly
the same zeros with the same multiplicities. Therefore H has only real
zeros. R1 and R2 imply that F has only real zeros, which puts every xi
zero on Re s=1/2 through the exact Fourier identity.

Thus the sufficient chain is

 actual phi_* Pick -> H has only negative real zeros
                   -> G has only negative real zeros
                   -> F has only real zeros -> RH.    (R8)

This chain uses no claim that the surviving zeros/poles of phi_* are a
unit distance apart. It does not infer Pick from the formal unit shift,
from H's finite order, from the parabolic zero-free region, or from
positivity of rho. Ordinary Bernstein membership is also not substituted
for Pick. The older ordinary-BF control remains a counterexample to that
substitution; the polynomial H_c control illustrates why requiring unit
separation would discard some valid real-zero examples.

## Scope and dependency outcome

The KPS paper provides Theorem 4.4 as an external sufficient theorem;
its sketch on pp416-417 refers to a 2022 working paper [25] for details.
The bounded primary search did not locate that working paper. This does
not establish that it is unavailable or refute the published theorem.
R2 instead uses the explicitly stated classical coefficient-transform
input, with every actual-source growth and normalization condition paid
here. It does NOT independently reprove the classical theorem.

The newly isolated sign premise is global Pick membership of the very
same phi_*. No independent theta argument pays it here. Finite order is
a genuine additional source fact, but R8 is only a sufficient conditional
interface, not a source-sign improvement or proof of RH. The additive
PF property and the arithmetic placement of the square rates have not
been used to obtain that missing Pick sign. Do not reset any source-sign
stall counter, launch another same-premise proof job, or promote this
note to a canonical or Lean result.

Sources read:
- Baricz--Singh authors' PDF https://arxiv.org/pdf/1702.00626,
  version 2, Lemma 1 p2 and Lemma 4 p3, text and both rendered pages read.
  PDF SHA256 992a42316a41b39027377cbb2690b908ee14f3c1e2464b23c9727316d882abc7.
  Published paper: Proc. AMS 146(5) (2018), 2207-2216,
  DOI https://doi.org/10.1090/proc/13927.
- https://dlmf.nist.gov/5.8.E2, reciprocal-Gamma product.
- KPS journal PDF SHA256
  05f75d661af5d94d64c5c66b6a9c1ee22a73d53e13c5afd8ceb7a76a5cf14a19,
  Theorem 4.4 and its proof sketch, printed pp396,416-417.

CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET.
FULL_V_SIGN: OPEN. RH: OPEN. ACTUAL_PICK_MEMBERSHIP: OPEN.

## Independent acceptance

Candidate SHA256: `2bf161414992d7a50d3bba60c0aa99c18e34a9862bc3c0ecff157411dd4a1239`.
Review SHA256: `0114844dd53e95aadecf58d080d138939452832d6e186702f41ac1367b62db24`.
Verdict: `ACCEPT_ENTIRE_H_GROWTH_AND_DIRECT_CONDITIONAL_PICK_BRIDGE_ONLY`.
Reviewer `/root/pairzero_geometry_review` independently checked every R1--R3
step and the exact external Laguerre statement. The full review and parent
check are embedded in the paired certificate. The producer KQ14 dependency
was separately accepted in REPORT_2026-09-17_KPSQUOTIENT_INTAKE.md.
Actual global Pick membership remains unproved, and no full-V sign delta,
canonical/Lean admission, source-sign counter reset or RH claim is made.
