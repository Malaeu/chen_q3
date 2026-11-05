# Arithmetic reciprocal assembly inherits high off-axis zeros

STATUS: ACCEPTED_LIMITED_PAPER; ACCEPT_ARITHMETIC_RECIPROCAL_ASSEMBLY_HIGH_ZERO_OBSTRUCTION_ONLY.
Base: ae905d0b8e290f500303f8f141e8ba4cc5e0a238. Isolated research.
Original full V and RH remain OPEN; no original-source negative witness.

## Bounded question and prior scope

The accepted MELLINEDGE result concerns the raw finite Mellin transforms,
and explicitly does not classify zeros of the reciprocal assemblies.
The arithmetic assembly report proves an exact positive even source,
convergence to full Phi, and an exact sum of two reflected Mellin terms;
its zero question is left open. This note checks that exact sum. It does
not reopen generic SUPPORT, Pick, or the geometric gamma family.

Inputs read in full, with byte pins in the adjacent private manifest:

1. REPORT_2026-09-15_ARITHMETIC_RECIPROCITY.md, AR1--AR4.
2. REPORT_2026-09-16_MELLINEDGE_COFINAL_OBSTRUCTION.md, C0--C5.

We inherit their already accepted source bounds, prime-torus construction
and convergence proofs; we do not claim a new independent audit of all
those earlier results. The NEW step is the uniform estimate for the
reflected term in the complete assembled transform, followed by Rouche.

The only additional published analytic input is the vertical-strip gamma
asymptotic, NIST DLMF 5.11.9, https://dlmf.nist.gov/5.11.E9 . It follows
from the sectorial Stirling expansion 5.11.3 and is uniform when the real
part ranges in a fixed bounded interval. The two gamma arguments below
have exactly opposite imaginary parts; their exponential factors cancel
in the ratio. No estimate uniform in N is required or asserted.

## A1. Source and exact assembled transform

Let T_N be the sum of independent Gamma(2,rate pi*n^2), 1<=n<=N,
and let r_N be its density. Put kappa=5/2, c=kappa/2=5/4, and

    a_N(x)=exp(5x/2)r_N(exp(2x)),
    H_N(x)=[a_N(x)+a_N(-x)]/2,
    M_N(s)=E[T_N^(s-1)].

The normalized Fourier transform of H_N, in its defining strip, is

    A_N(z)=[M_N(c-iz/2)+M_N(c+iz/2)]/[2 M_N(c)].       (A1)

The denominator M_N(c) is strictly positive. The ordinary integral for
A_N is holomorphic for |Im z|<4N+1/2. Define

    B_N(w)=M_N(w)+M_N(kappa-w).                       (A2)

At w=c-iz/2 the numerator in A1 is exactly B_N(w). In particular

    z=2i(w-c).                                       (A3)

No replacement by the sign, modulus, or just one of the summands is made.

For 0<Re w<kappa, both Mellin terms admit the accepted exact formula

    M_N(w)=4 pi^(1-w)Gamma(w) D_N(w),
    D_N(w)=sum_(n=1)^N w_Nn n^(2-2w)(w+d_Nn),
    w_Nn=(N!)^4/[(N-n)!^2(N+n)!^2],
    d_Nn=n(H_(N+n)-H_(N-n))-3/2.                     (A4)

H_k in A4 denotes a harmonic number, not the source H_N(x). All finite
harmonic corrections and all composite-prime phase dependencies remain
in D_N. The real log is used for powers of positive pi and n.

## A2. Accepted prime-torus limit, with N fixed first

For every sufficiently large fixed N, the accepted C1--C4 construct unit
phases zeta_p for primes p<=N and real tau_j tending to +infinity such that

    P_N(s)=sum_(n=1)^N w_Nn n^(2-2s)
                     product_(p<=N) zeta_p^v_p(n),
    P_N(11/8)=0,
    D_N(s+i tau_j)/(i tau_j) -> P_N(s)                (A5)

locally uniformly in s. P_N is entire and not identically zero because
P_N(s) tends to w_N1>0 as real s tends to +infinity. In the earlier proof,
unique factorization supplied the allowed phases and the unconditional
prime-count law supplied the requisite mass split. Both are inherited.

Choose a closed disk K centered at sigma_0=11/8 with radius delta<1/32.
It lies strictly inside c<Re s<kappa. The radius can be chosen so that
P_N has no zero on its boundary. Multiple interior zeros are allowed.

## A3. The reflected term vanishes in the same normalization

On a neighborhood of K and for sufficiently large tau>0 define

    F_(N,tau)(s)= B_N(s+i tau)
                  /[4 pi^(1-s-i tau)Gamma(s+i tau) i tau].       (A6)

The normalizing factor is holomorphic, finite and nonzero there. Direct
substitution of BOTH terms of A4 gives the exact identity

    F_(N,tau)(s)=D_N(s+i tau)/(i tau)
                  +G_tau(s) D_N(kappa-s-i tau)/(i tau),
    G_tau(s)=pi^(2s+2i tau-kappa)
                  Gamma(kappa-s-i tau)/Gamma(s+i tau).         (A7)

For s=sigma+iv in K, put y=tau+v>0. The real parts of the two gamma
arguments are kappa-sigma and sigma; the imaginary parts are -y and y.
The uniform vertical-strip gamma asymptotic therefore gives

    |G_tau(s)|=pi^(2sigma-kappa)
                    y^(kappa-2sigma)[1+o(1)],                 (A8)

uniformly on K. Since sigma>=11/8-delta, kappa-2sigma<=-1/4+2delta
<-3/16. Thus sup_K |G_tau|=O_K(tau^(-3/16)).

Also, for fixed N, the finite formula A4 gives directly

    sup_(s in K) |D_N(kappa-s-i tau)| <= C_(N,K)(1+tau).        (A9)

Indeed every n^(2-2(kappa-s-i tau)) has modulus bounded on K independently
of tau, and every linear factor is bounded by tau plus a fixed constant.
No independent choice of the reflected prime phases is made or needed.

Combining A7--A9 and the actual sequence from A5 proves

    F_(N,tau_j)(s) -> P_N(s), locally uniformly on K.            (A10)

This establishes a strict perturbation estimate on the boundary of K.
It does NOT say B_N vanishes at the old raw M_N zeros, nor compare a
perturbation to a vanishing leading term at a single point.

## A4. Zeros of the full assembled transform

The minimum of |P_N| on the chosen boundary is positive. For all sufficiently
large j, A10 and Rouche give a zero s_j of F_(N,tau_j) in K. The nonzero
normalizing factor implies B_N(s_j+i tau_j)=0. A1--A3 then give

    z_j=2i(s_j+i tau_j-c),       A_N(z_j)=0.                    (A11)

Their real parts tend to -infinity and

    |Im z_j-1/4| < 2delta < 1/16.

In particular these zeros lie strictly inside 0<Im z<1/2, and also inside
the defining Fourier strip for every N>=1. This is not a conclusion from
meromorphic continuation beyond the integral's domain.

Using successively shrinking zero-free circles about sigma_0 and a diagonal
subsequence of arbitrarily large recurrence times strengthens this to

    Re z_j -> -infinity,       Im z_j -> 1/4.                   (A12)

Evenness and reality of H_N imply A_N(-z)=A_N(z) and
A_N(conjugate(z))=conjugate(A_N(z)). Consequently there are corresponding
zeros at unbounded positive real parts and near both Im z=+1/4 and -1/4.
These symmetries do not need an additional independent phase selection.

Therefore, for EVERY sufficiently large N, the actual arithmetic reciprocal
transform A_N has infinitely many off-real zeros within |Im z|<1/2. No
unbounded subsequence of this particular finite family can be zero-free
throughout the punctured critical strip at every horizontal height.

## A5. Exact boundary of the conclusion

The raw MELLINEDGE report alone did not classify the zeros of H_N's
transform. A3--A4 now pay the missing reflected-term estimate. Positive
evenness obtained by arithmetic reciprocal assembly does not remove those
high zeros. This is a new corollary for that already specified approximation,
not a new proof of the original sign and not a newly discovered prime theorem.

The quantifier order remains: first fix a sufficiently large N, then let
the recurrence heights tend to infinity. The proof gives no uniform-in-N
height, no fixed compact containing such zeros for infinitely many N, and
no first failing numerical N. The accepted convergence A_N -> normalized
xi on each fixed horizontal strip is compatible with zeros escaping to
infinity: it is absolute convergence, with no positive lower bound on the
tiny limiting transform at all large horizontal heights.

In particular the weaker compact-by-compact eventual zero-exclusion
condition (for each fixed R and epsilon) is not refuted by A12. That
condition for this family would still require proof; no new generic request
to prove it is opened here. The geometric square-root assembly is distinct
and its previously proved central slab remains unchanged.

This does not alter the full density r, original f, interval I, full V,
boundary terms, or any complex-family quantifier. No negative row of the
original V is obtained. Actual RH, full V, Pick and global VAR remain open.
The bounded decision is to reject global finite-level zero exclusion for
the arithmetic assembly too; preserve its convergence and exact formulas.
No source-sign counter reset, canonical admission, or production mutation.

AUTOPSY: dropped=COUPLING; note=Exact arithmetic reciprocal assembly retains high finite-level zeros because the reflected Mellin term is uniformly smaller in the prime-torus normalization; compact limiting zero exclusion and original full-source sign remain open.

## Independent acceptance

Candidate SHA256: a3d0baea3825b966d3ae9a115f862286618e001c51d424f64b0bbcef50c74532.
Complete independent review SHA256: 531db4103acc613e0b65d2e8e5ceb2b59ca37858aab67e36839ea0345b73845d.
Parent check SHA256: 04b04362fa89297fab70d28c25349b3ee48a062d075981627995522d74ac3353.
Reviewer: /root/pairzero_geometry_review. Both source reports were read and pinned; DLMF 5.11.9 including its uniformity clause was checked directly. No correction was required. Only the bounded arithmetic-assembly obstruction is accepted. No Lean verification, canonical admission or original-source sign conclusion is asserted.
