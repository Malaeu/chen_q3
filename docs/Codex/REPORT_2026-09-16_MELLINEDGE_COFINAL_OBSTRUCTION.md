# Raw finite-source Mellin edge: a cofinal obstruction from prime phases

STATUS: INDEPENDENTLY_ACCEPTED_PAPER_COFINAL_RAW_MELLIN_OBSTRUCTION_ONLY.
Source base: aeb9ec3081f4f38e0190786fbd67fbcf9f2516af.
Scope: raw finite gamma Mellin family only. No negative original V,
zero off the critical line of xi, or RH claim is made.

## C0. Inputs and claim

Use the exact E2 formula in the independently reviewed
REPORT_2026-09-16_MELLIN_EDGE_PREFLIGHT.md, SHA256
a7dfba76bd7018100d312f198987a35e4a08ed163d8f5ade43d0f9244b14c1ff:

    D_N(s)=sum_(n=1)^N w_Nn n^(2-2s)(s+d_Nn),
    w_Nn=(N!)^4/[(N-n)!^2(N+n)!^2],
    d_Nn=n(H_(N+n)-H_(N-n))-3/2,
    M_N(s)=4 pi^(1-s)Gamma(s)D_N(s), Re s>0.

Claim: for EVERY sufficiently large integer N, D_N has zeros with
arbitrarily large positive imaginary part and real parts approaching
sigma_0=11/8. Consequently each such N has a zero in Re s>5/4, and
the proposed cofinal EDGE is false for this family.

This uses unconditional prime-count asymptotics, not RH. The published
input pi_count(x)~x/log x is recorded in NIST DLMF 27.12.4 (leading term),
https://dlmf.nist.gov/27.12.E4 . The RH-dependent error in 27.12.7 is NOT used.
All transfers from that standard theorem to this finite source are proved below.
An attempted original Mertens PDF link redirected to a discontinued service;
no statement is treated as read from that inaccessible PDF.

## C1. Torus cancellation DOES transfer to actual high zeros

Fix N. For a unit complex number z_p for each prime p<=N, put

    P_z(s)=sum_(n=1)^N w_Nn n^(2-2s) product_(p<=N) z_p^v_p(n).

If P_z(s_0)=0 at some Re s_0>5/4, then D_N has zeros with real parts
approaching Re s_0 and imaginary parts tending to +infinity.

Indeed, the logs of distinct primes are rationally independent by unique
factorization. There are tau_j->+infinity such that
exp(-2i tau_j log p)->z_p simultaneously for all p<=N. For completeness,
the continuous-time average of any nonconstant torus character along this
orbit tends to zero, since it is the average of exp(-2it sum k_p log p)
with a nonzero frequency. Uniform trigonometric approximation then gives
the Haar average for every continuous torus function. A nonnegative bump
supported in any specified nonempty open neighborhood has positive Haar
average, so the orbit enters it at arbitrarily large positive times.
Shrinking neighborhoods gives the required sequence; no quantitative rate
is assumed.

Locally uniformly for complex s,

    D_N(s+i tau_j)/(i tau_j) -> P_z(s).                 (C1)

This follows term by term from the FINITE sum: (s+i tau_j+d_Nn)/(i tau_j)
tends to one, uniformly on every compact. The harmonic terms are present
before this fixed-N limit; they are not erased in any N-uniform estimate.
P_z is not identically zero, since P_z(s)->w_N1>0 as real s->+infinity.
Choose a small circle about s_0 entirely in Re s>5/4 with no P_z boundary
zeros. Rouche and C1 put a zero of D_N(s+i tau_j) inside the circle for
all sufficiently large j. Use successively shrinking circles to obtain
the asserted approach to s_0. Multiple zeros cause no difficulty.

Thus an exact prime-torus zero is enough. No additional transversality
assumption or quantitative simultaneous approximation is needed here.

## C2. Exact weights have a Gaussian summation scale

Fix a=3/4, so 2-2sigma_0=-a. Let L=sqrt(N) and

    S_N=sum_(n=1)^N w_Nn n^(-a),
    C_a=int_0^infinity u^(-a)exp(-2u^2)du>0.

The product expression

    w_Nn=product_(k=0)^(n-1)[(N-k)/(N+k+1)]^2

gives, for 1<=n<=N,

    log w_Nn <= -2 n^2/(N+n) <= -n^2/N.               (C2)

Here log(1-v)<=-v and sum_(k=0)^(n-1)(2k+1)=n^2 were used.
For n<=K sqrt(N), a Taylor estimate in that same product gives
log w_Nn=-2n^2/N+o(1), uniformly for every fixed K. Riemann summation,
the integrable singularity u^(-a) at zero, and the bound C2 give

    S_N ~ C_a L^(1-a),
    sum_(n>=1) n^(-a)|w_Nn-exp(-2n^2/L^2)|=o(L^(1-a)), (C3)

where w_Nn=0 for n>N. To see the second statement without interchanging
an uncontrolled tail, first restrict n/L to [epsilon,K], use the uniform
Taylor estimate there, and bound the two excluded pieces by the integrals
of u^(-a)(exp(-u^2)+exp(-2u^2)). Then let epsilon decrease to zero and K
increase to infinity. This also proves the first statement.

## C3. More than half the mass is linear in freely selectable large primes

Set y=N^(2/7)=L^(4/7), and let Omega_y(n) count prime factors greater than
y WITH multiplicity. Fix z_p=1 for p<=y and retain the other prime phases.
At s=sigma_0 the exact torus polynomial decomposes as

    F_N(z)=R_N+sum_(y<p<=N) b_Np z_p+H_N(z),           (C4)

where R_N sums weights w_Nn n^(-a) with Omega_y(n)=0,
b_Np sums those with Omega_y(n)=1 and their unique large prime equal to p,
and H_N contains precisely Omega_y(n)>=2. All coefficients are positive.
This is a partition of the complete finite polynomial, not a replacement.

If Omega_y(n)>=2 then n>y^2=N^(4/7). C2 implies

    h_N:=sum_(Omega_y(n)>=2)w_Nn n^(-a)
        <=N exp(-N^(1/7))=o(S_N).                    (C5)

Moreover Omega_y(n)<=3 for n<=N, since y^4>N. Thus H_N and its first
angle derivatives, after setting any groups of prime phases equal, have
absolute bounds h_N and 3h_N respectively. The higher prime interactions
are small together with the needed derivatives; they do not vanish identically.

Write A_N=sum_p b_Np. We prove

    A_N/S_N -> alpha=log(7/4)>1/2,
    R_N/S_N -> 1-alpha,
    max_p b_Np/S_N ->0.                              (C6)

First, counting a multiple of each distinct prime p>y gives

    A'_N=sum_(p>y) sum_(k>=1, pk<=N) w_(N,pk)(pk)^(-a).

The difference from A_N is bounded by 3h_N, because only terms with
Omega_y>=2 can differ and each has at most three distinct large primes.
The C3 Gaussian replacement is valid also in this sum: for n<=N the
multiplicity is at most three. For n>N the extra Gaussian tail, even
multiplied by log n/log y, is exponentially small. Consequently

    A'_N=sum_(p>y)sum_(k>=1)(pk)^(-a)exp(-2(pk/L)^2)
          +o(L^(1-a)).                              (C7)

For p<=L, monotone sum-integral comparison at the integrable origin gives

    sum_(k>=1)(pk)^(-a)exp(-2(pk/L)^2)
       = C_a L^(1-a)/p + O_a(p^(-a)).                (C8)

Specifically, for phi(k)=k^(-a)exp(-2(pk/L)^2), the difference between
sum_(k>=1)phi(k) and int_0^infinity phi(t)dt has modulus at most
int_0^1 t^(-a)dt=1/(1-a). This proves the uniform error in C8.

The elementary bound pi_count(x)=O(x/log x), a consequence of the PNT input,
and partial summation give sum_(p<=L)p^(-a)=O_a(L^(1-a)/log L).
For p>L the inner sum is at most C_a' p^(-a)exp(-2(p/L)^2). Summing in
intervals [jL,(j+1)L] with the same prime-count bound gives a total
O_a(L^(1-a)/log L). Thus C7-C8 imply

    A_N=C_a L^(1-a) sum_(y<p<=L)1/p+o(L^(1-a)).        (C9)

Finally partial summation of pi_count(t)~t/log t on [y,L] gives

    sum_(y<p<=L)1/p
     =pi_count(L)/L-pi_count(y)/y+int_y^L pi_count(t)/t^2 dt
     =log(log L/log y)+o(1)=log(7/4)+o(1).            (C10)

The relative PNT error is uniformly o(1) for t>=y; the integral of
1/(t log t) over this interval is the fixed constant log(7/4).
No assertion about primes in short intervals, no RH error estimate,
and no independent phases for composite n enter C10.

Equations C3, C5 and C9-C10 prove the first two assertions in C6.
For the last one, C2 and monotone comparison give

    b_Np<=sum_(k>=1)(pk)^(-a)exp(-(pk/L)^2)
          <=C_a'' L^(1-a)/p.

Therefore max_p b_Np/S_N=O(1/y)->0. All three assertions in C6 are proved.
Also 1/2<alpha<1: for example log(7/4)>6/11>1/2 and log(7/4)<3/4<1.

## C4. Two groups of large prime phases produce an exact torus zero

Partition the finitely many primes p>y into groups U_N,W_N so their
coefficient masses a_N=sum_U b_Np and b_N=sum_W b_Np differ by at most
max_p b_Np. This follows by successively assigning each coefficient to
the group with the smaller current sum. By C6,

    a_N/S_N -> alpha/2, b_N/S_N -> alpha/2.

For p in U_N set z_p=exp(iu); for p in W_N set z_p=exp(iv).
Keep z_p=1 for p<=y. The complete normalized polynomial is

    G_N(u,v)=[R_N+a_N exp(iu)+b_N exp(iv)+H_N(u,v)]/S_N.

C5-C6 show convergence in C^1 on the real (u,v) plane to

    G(u,v)=1-alpha+(alpha/2)[exp(iu)+exp(iv)].          (C11)

Let phi=arccos((1-alpha)/alpha). Since 1/2<alpha<1,
0<phi<pi/2. At u_0=pi+phi and v_0=pi-phi, G=0 and the real
2-by-2 Jacobian of (Re G,Im G) has nonzero determinant, of modulus
(alpha^2/4)|sin(2phi)|. Hence G_N has a zero near (u_0,v_0) for every
sufficiently large N.

One explicit justification of that last stability step: let J=DG(u_0,v_0).
On a sufficiently small closed ball about (u_0,v_0), the derivative of
x -> x-J^(-1)G(x) has norm less than 1/4. C^1 convergence makes the
derivative of x -> x-J^(-1)G_N(x) less than 1/2 there, and its displacement
at the center tends to zero. For large N this map sends the ball into
itself and is a contraction. Its fixed point is an EXACT zero of G_N.
Thus the small nonlinear term H_N is fully included, not merely bounded
and then discarded at a putative zero.

We have constructed prime phases z=z^(N) for EVERY sufficiently large N
such that P_z(sigma_0)=F_N(z)=0. Composite phases retain unique-factorization
relations throughout.

## C5. Consequence for the proposed route, and only that route

Apply C1 to the exact zero from C4, separately for each sufficiently large N.
The resulting D_N zeros approach the vertical line Re s=11/8 at unbounded
positive heights. Small enough circles lie in Re s>5/4. The Gamma and
pi factors have no zeros or poles there, so these are zeros of M_N as well.
Hence no unbounded subsequence of the raw finite M_N is zero-free throughout
Re s>5/4. This disproves EDGE, not merely its all-N strengthening.

The order of quantifiers is essential: fix N, then let the recurrence
heights increase. No uniform height or explicit first failing N is claimed.
The locally uniform limit M_N->2xi(2s-2) on fixed compact sets is perfectly
compatible with these zeros escaping to infinity as N increases. Nothing
here places a zero of xi off its critical line or determines the sign of V.

The working prime properties were unique factorization (phase relations and
density) and the unconditional prime-count law (the mass fraction log(7/4)).
In this raw finite approximation they produce an obstruction to the hoped-for
global stability, rather than the positive reserve sought for the original V.

Independent-review status is required before treating C0-C5 as accepted.
The auxiliary prime-torus note had incorrectly suggested that quantitative
recurrence plus an extra transversality hypothesis were needed for C1; this
proof supplies the missing implication directly and does not rely on that
part of the note. Its valid exact phase identity was useful for discovery.

AUTOPSY: dropped=COUPLING; note=Raw finite-source zero-freeness at every height is stronger than locally uniform convergence to xi; prime phases create high zeros for every sufficiently large finite source while the limiting sign remains open.

## Independent acceptance

Candidate SHA256: `b56d0a2023e3b5c1d0ee730b282eb8c1802436150dd2327fe5651cf5e167aa8a`.
Read-only reviewer `/root/sibling5_check`; review SHA256: `df4dbb1186b486227133b1075ca6402f6c41cf0753b26cd9ba593efb6b1fe69d`.
Parent independently derived and checked C0-C5. Only the status and this receipt were added after review. EDGE is excluded for this raw finite family; original V and RH remain open. No canonical admission or Lean verification.
