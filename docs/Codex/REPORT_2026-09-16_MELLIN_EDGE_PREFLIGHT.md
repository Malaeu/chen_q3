# Raw finite-source Mellin edge: exact arithmetic formula and a closed sufficient target

STATUS: INDEPENDENTLY_ACCEPTED_PAPER_PREFLIGHT_AND_SUFFICIENT_TARGET_ONLY.
Base: 631b15d506fde2188394e51f825d170d5923cf46.
This is a bounded source-route preflight. No RH/full-V sign, canonical
admission, or positivity of a finite-source replacement V is asserted.

## E0. Why this object, and what is preserved

The renewal, coupled-flux and nonlocal-transmutation tests did not supply
the sign of the physical V. Instead of appending levels to those fields,
return to the exact finite gamma source BEFORE geometric or arithmetic
reciprocal assembly. No positive energy is substituted for V.

Pinned inputs:
- REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md G1-G4, SHA256
  7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621;
- REPORT_2026-09-15_ARITHMETIC_RECIPROCITY.md AR1-AR4, SHA256
  b128c925d794693fdbc5b1e8257e5587060c92d60770a650f2f8d26ee6838f53;
- REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, SHA256
  1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.

Let r_N be the density of T_N=sum_(n=1)^N Gamma(2,1)/(pi*n^2), and

    M_N(s)=int_0^infinity t^(s-1)r_N(t)dt, Re s>1-2N.

Here N counts finitely many rates. It is NOT the alpha indexing convolution
powers of the full source in COUPLEDFLUX. Its limit r is the original full
source, whose Mellin transform is M(s)=2 xi(2s-2). The target critical line
is Re s=5/4. Finite r_N does not obey the full reciprocal identity.

## E1. Limit on the needed half-plane and exact sufficiency

The pinned full-source estimates give r_N(t)<=C exp(-pi*t/2) uniformly in N,
and uniform real convergence r_N->r. For a compact subset of Re s>0, choose
0<a<=Re s<=b. On (0,1), C*t^(a-1) dominates t^(s-1)r_N(t); on [1,infinity),
C*t^(b-1)exp(-pi*t/2) does. The same bounds with powers of |log t| justify
holomorphy and derivatives. Dominated convergence, applied to the supremum
over the compact parameter set, gives

    M_N -> M=2 xi(2s-2) locally uniformly on Re s>0.       (E1)

One sufficient property is

    there exists an unbounded sequence N_j such that
    M_(N_j)(s)!=0 for every Re s>5/4.                    (EDGE)

If EDGE holds, Hurwitz on that half-plane makes M zero-free there: its
identically-zero alternative is excluded by M(2)=E T=pi/3>0. Hence xi has
no zero with Re z>1/2. Its exact functional equation xi(z)=xi(1-z) excludes
Re z<1/2 as well. This proves RH, and the independently established full-sign
transfer then gives the ORIGINAL V>=0 for all finite complex rows in I.
There is no additional unproved energy, boundary or density transfer after
EDGE. This is sufficiency only; RH need not force EDGE for this sequence.

This differs from a real-zero theorem for the geometric G_N or arithmetic
H_N Fourier assemblies. Their known failures/limitations do not prove or
disprove EDGE. No finite M_N is called self-reciprocal or entire.

## E2. The complete finite formula, using the exact square spacing

Write lambda_n=pi*n^2, H_j=sum_(k=1)^j 1/k, H_0=0, and

    w_(N,n)=(N!)^4 / ((N-n)!^2 (N+n)!^2),
    d_(N,n)=n[H_(N+n)-H_(N-n)]-3/2.

Then, for Re s>0,

    M_N(s)=4 pi^(1-s) Gamma(s) D_N(s),
    D_N(s)=sum_(n=1)^N w_(N,n) n^(2-2s) [s+d_(N,n)].      (E2)

Proof: the rational Laplace transform has only double poles:

    product_(j=1)^N (lambda_j/(q+lambda_j))^2
      =sum_(n=1)^N [A_n/(q+lambda_n)^2+B_n/(q+lambda_n)],
    A_n=lambda_n^2 product_(j!=n)(lambda_j/(lambda_j-lambda_n))^2,
    B_n=-2 A_n sum_(j!=n)1/(lambda_j-lambda_n).

Factoring j^2-n^2=(j-n)(j+n) gives A_n=4pi^2 n^4 w_(N,n). Also

    sum_(j!=n)1/(j^2-n^2)
       =[H_(N-n)-H_(N+n)]/(2n)+3/(4n^2),
    lambda_n B_n/A_n=d_(N,n).

Inverse Laplace transformation gives
r_N(t)=sum (A_n*t+B_n)exp(-lambda_n*t). Each term is Mellin integrable for
Re s>0, so ordinary gamma integration proves E2. This does not require
integrating individually divergent terms closer to Re s=1-2N.

Because Gamma(s) has no zeros or poles on Re s>0, the zeros relevant to EDGE
are exactly those of the explicit entire exponential polynomial D_N. The
standard Gamma fact is recorded in DLMF 5.2(i), paragraph after equation
5.2.1: https://dlmf.nist.gov/5.2 . No zero theorem for D_N is imported.

The coefficients expose exact square-rate arithmetic, not just min lambda=pi.
In particular

    w_(N,n)=[binom(2N,N-n)/binom(2N,N)]^2.                 (E3)

Positive binomial weights do not by themselves give complex non-cancellation.
No independent property of primes is yet spent by E2-E3; the multiplicative
frequencies log n remain explicit rather than being replaced by absolute values.

## E3. Two complete base cases, not a cofinal theorem

For N=1, M_1(s)=pi^(1-s)Gamma(s+1), so M_1 is zero-free on Re s>0.
For N=2, the exact expression is

    M_2(s)=(16pi/27)Gamma(s)pi^(-s)
             [(3s-2)+4^(-s)(3s/4+2)].                  (E4)

This agrees with the pinned literal finite two-rate density G12. For Re s>=1,
write

    (3s/4+2)/(3s-2)=1/4+(5/6)/(s-2/3).

Its modulus is at most 1/4+(5/6)/(1/3)=11/4; |4^(-s)|<=1/4. Therefore

    |4^(-s)(3s/4+2)/(3s-2)|<=11/16<1.                 (E5)

The bracket in E4 cannot vanish, and neither can its other factors.
Thus the entire closed half-plane Re s>=1 is zero-free for this N=2 Mellin
transform. This proves the two starting cases of the stronger all-N EDGE
proposal. It does NOT bound zeros for N>=3 or supply the unbounded sequence.

## E4. A naive extension is already excluded

Do not ask to repeat E5 using an N-independent absolute first-term budget.
For a fixed real sigma in (5/4,3/2], consider the ratio of the sum of moduli
of n>=2 terms in D_N(s) to the modulus of its n=1 term at s=sigma+i*tau.
As |tau| tends to infinity with N fixed, its limit is

    B_N(sigma)=sum_(n=2)^N [w_(N,n)/w_(N,1)] n^(2-2sigma). (E6)

For every fixed n, w_(N,n)/w_(N,1)->1 as N->infinity; this follows directly
from the finite factorial ratio. Every term is nonnegative. Given any finite
L, liminf_N B_N(sigma)>=sum_(n=2)^L n^(2-2sigma), and the latter tends to
infinity as L->infinity when sigma<=3/2. Consequently

    B_N(sigma)->infinity for each sigma in (5/4,3/2].     (E7)

So even inside the requested right half-plane, the first term cannot dominate
the sum of absolute values for all sufficiently large N and all imaginary
heights. E7 is a failure of THAT estimate, not a zero of D_N, M_N, xi or V.
It demonstrates precisely why the complex relations among the remaining
arithmetic frequencies must be retained by a successful proof of EDGE.

## Decision for the next bounded joint attempt

The next candidate is raw finite-source Mellin stability (EDGE), with its
explicit E2 coefficient structure. The two base cases and the complete
downstream implication have been paid. The uniform stability mechanism
remains UNVERIFIED; neither total positivity of r_N nor E3 establishes it.

The global task is to exploit the coupled binomial/harmonic coefficients and
the multiplicative log-n frequencies to prove a cofinal right-edge bound, or
derive a scoped analytical obstruction for this family. A finite off-edge
zero rejects all-N stability only. To reject EDGE itself one must show such
zeros for every sufficiently large N (or otherwise exclude every unbounded
zero-free subsequence). No claim about RH follows from rejecting EDGE.

Do not launch a serial N=3,4,5 campaign, use a finite grid as evidence for
EDGE, reopen geometric all-plane real zeros, or erase the harmonic term.
If the available argument only restates EDGE, record INCOMPLETE with the
missing source-level operation and stop that attempt. This is one concrete
candidate to test with Proshka, not a claim that RH is now easier or proved.

AUTOPSY: dropped=COUPLING; note=The absolute first-pole domination budget diverges with N inside the required half-plane; a cofinal Mellin argument must keep arithmetic phase interactions.

## Independent acceptance

Candidate SHA256: `0fb0395993bb99f4c89893bed156b3cab5e7a340c52c46a7c64c0f8513907e40`.
Read-only reviewer `/root/sibling5_check`; review SHA256: `3676cedda926ab7a06454a34553cd1a7f4b4ff6bf75906991819da30493b2c9b`.
Parent independently derived and checked E1-E7. Only the status and this receipt were added after review. EDGE remains unproved. No canonical admission or Lean verification.
