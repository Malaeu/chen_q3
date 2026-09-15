# Finite-gamma approximants: the critical-strip interface

Status: PAPER analytic candidate; exact independent review required before
delivery. Source base: 5aba82c8108c19006c03d0fe207c38234ac0bbae.
No canonical admission, change to the paused native goal, or RH claim.

## 1. Return to the actual target

The user renewed the request to prove RH using the existing results.
Neither a self-adjoint realization nor real zeros of every auxiliary function
throughout the whole plane is necessary as a general requirement for RH.
The existing finite-gamma family already has a proved analytic limit. Its
full-plane real-zero preserver was disproved; a weaker local condition was
not settled by that result. This report states the weaker condition exactly
and proves what the branch obstruction does say about horizontal bands.

Source documents at the pinned base, read in full:
`docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md`, G1-G3, G6;
`docs/Codex/REPORT_2026-09-14_GAMMA_COFINAL_BRANCH_OBSTRUCTION.md`, B1-B8.
Their previous independent PAPER reviews remain scoped to their actual claims.

For independent Gamma(2,1) variables define

    T_N=sum_(n=1)^N Gamma_(2,n)/(pi*n^2), density r_N,
    G_N(x)=sqrt(r_N(exp(2x))*r_N(exp(-2x))) >0 on R,
    Z_N=integral_R G_N(x)dx,
    M_N(z)=integral_R G_N(x)exp(-izx)dx/Z_N.

All square roots here are positive real roots. Let r be the full density.
Already proved: r_N(u-v) is TN infinity,
||r_N-r||_infinity<=2pi/N, r(1/t)=t^(5/2)r(t), and

    G_N(x)<=2pi exp(1/7) exp[-(pi/2)cosh(2x)]

uniformly in N. With Phi(x)=exp(5x/2)r(exp(2x)), the resulting entire
functions satisfy, locally uniformly in the whole complex plane,

    M_N(z) -> F_*(z)=xi(1/2-iz)/xi(1/2),  F_*(0)=1.     (C1)

Raw r_N loses exact inversion B. G_N restores real reflection symmetry;
it is not thereby proved to retain additive TN infinity or the exact
holomorphic divisor structure of the full source. These are distinct claims.

## 2. What the old obstruction proves in every fixed band

Fix N>=13. B5 gives a>0, alpha>=1/2 and a nonzero finite exponential sum

    P(z)=sum_l C_l exp(-i b_l z),  b_l distinct real,
    U(z)=exp(a*z)z^(alpha+1)M_N(z)=P(z)+O(1/Re z)       (C2)

as Re z tends to infinity in each fixed horizontal band. Constants may
depend on N and on the band. U is holomorphic on Re z>0; its prefactor has
no zeros there. Distinct frequencies give constants L,c>0 such that every
real interval [A,A+L] contains s with |P(s)|>=c. Indeed, the integral of
|P|^2 over that interval is L sum|C_l|^2 plus bounded cross terms, uniformly
in A; choose L so the diagonal dominates those terms. Then |U(s)|>=c/2
for all sufficiently large A.

Fix B>0 and choose d>L+B+2. The disk of radius d about s covers
[A,A+1]+i[-B,B]. On the disk of radius 2d, (C2) bounds |U| above by a
constant independent of large A. Jensen's formula therefore bounds the
number of zeros in the inner disk by a constant independent of A.
Evenness covers negative real parts; the remaining compact rectangle has
finitely many zeros, since M_N is entire and M_N(0)=1. Thus, with
multiplicities,

    #{z: M_N(z)=0, |Re z|<=R, |Im z|<=B}
        = O_(N,B)(1+R).                                (C3)

In addition B7 proves

    log max_(|z|<=R)|M_N(z)|=O_N(R log(R+2)),
    log M_N(iT)>=(T/2)log T-O_N(T+log(T+2)).           (C4)

Suppose only finitely many zeros lay outside some fixed horizontal band.
Then (C3), together with those finite exceptions, gives total radial zero
count n(R)=O(1+R). The even entire function M_N has order at most one and
has no zero at zero. Pairing opposite zeros in Hadamard's product removes
the linear exponential factor by evenness. Consequently

    log|M_N(iT)| <= C + sum_j log(1+T^2/|z_j|^2)=O(T).

Here z_j is one root from each opposite pair, with multiplicities. The final
estimate follows by Stieltjes integration from n(R)=O(1+R), starting below
the first positive root modulus. Finite polynomial factors add O(log T).
This contradicts (C4). Therefore

    for every fixed N>=13 and every B>0,
    infinitely many zeros of M_N satisfy |Im z|>B.     (C5)

This is a fixed-N statement about arbitrarily high zeros. It does NOT prove
that all nonreal zeros escape as N tends to infinity; the two limits must
not be exchanged. It also neither excludes nor exhibits a nonreal zero in
the critical band |Im z|<=1/2.

## 3. The exact weaker condition and its complete sufficiency

For R>0 and 0<epsilon<1/2 set

    K_(R,epsilon)={z: |Re z|<=R,
                       epsilon<=|Im z|<=1/2}.

The following condition on the fixed sequence M_N is equivalent to RH:

    for every R>0 and 0<epsilon<1/2 there is N0
    such that for every N>=N0, M_N has no zero in K_(R,epsilon).   (C6)

Proof of sufficiency: if F_* had a nonreal zero z0 in |Im z|<1/2,
choose R,epsilon so z0 lies inside K_(R,epsilon), and a closed disk around
z0 inside K whose boundary has no zeros of F_*. By (C1), Rouche's theorem
gives a zero of every sufficiently large M_N inside the disk, contradicting
(C6). The classical location of xi zeros and zero-freeness on Re s=0,1
exclude the boundary and exterior. Thus all zeros of F_* are real and RH
follows. No simplicity assumption is used.

Proof of necessity: under RH, F_* is nonzero on K_(R,epsilon). Its modulus
there has positive minimum. Uniform convergence (C1) then excludes zeros
of M_N on K for all sufficiently large N.

The necessity argument is NOT a source proof of (C6): using that unknown
positive minimum before proving RH would be circular. (C6) is an exact
consumer interface, not new source-sign progress or a new solved theorem
about the zeros of xi.

All-real auxiliary functions were stronger than needed. For a transparent
logical example, (1+z^2/N^2)cos z converges locally uniformly to cos z,
although every member has nonreal roots at +iN and -iN. This is not claimed
to be a gamma-family example. It only separates the quantifiers.

## 4. One specific next proof task

An explicit error budget is available, without assuming anything about zeros.
Let C=2pi exp(1/7), c=pi/4, delta_N=2pi/sqrt(eN), and, for N>=3,

    L_N=(1/2)log(4 log(N)/pi),
    D_N(R)=integral_R exp(R|x|)|G_N(x)-Phi(x)|dx.

The uniform sup bound and the common double-exponential envelope give

    D_N(R) <= E_N(R)
      :=2 delta_N L_N exp(R L_N)
           +2 C c^(-R/2) Gamma(R/2,log N),              (C7)

for every R>=0, where Gamma(a,b)=integral_b^infinity t^(a-1)exp(-t)dt.
Indeed the central interval contributes at most the first term. On its
complement use |G_N-Phi|<=2C exp[-c exp(2|x|)], add the two tails and set
t=c exp(2x). This yields exactly the second term. Both terms tend to zero
for fixed R. The same envelope also yields the finite upper bound

    integral_R exp(R|x|)Phi(x)dx
       <= B_R:=C c^(-R/2)Gamma(R/2,c).

Writing Z=integral_R Phi>0, whenever E_N(0)<=Z/2 the normalization is paid:

    sup_(|Im z|<=R)|M_N(z)-F_*(z)|
      <= 2 E_N(R)/Z + 2 B_R E_N(0)/Z^2.               (C8)

The estimate is uniform even in Re z, but it is an absolute approximation
bound. It is not a lower bound on either transform away from the real axis.
In particular it does not prove C6 where transforms can be very small.

Try to prove (C6) directly from the full fixed rate product and the coupled
reciprocal construction. A useful result would supply, for each R,epsilon,
an N0 from source estimates that exclude zeros of M_N on K. A zero-location
bound on compact critical rectangles with distance to the real axis tending
to zero is another way to supply the same interface.

Do not replace the target by full-plane real zeros, simplicity, another
Gaussian multiplier, or positivity of V. Do not infer it from (C3)-(C5):
their constants depend on N and their large-Re limit is a different limit.
Do not infer zero exclusion from an approximation error alone without a
proved nonzero comparison function and its required lower bound.

A fixed-N nonreal zero only refutes an all-N strengthening. To disprove C6
for this actual convergent family one needs zeros in one fixed off-axis
critical compact for an unbounded sequence of N; that would itself refute
RH by (C1). No such witness is known here. Failure of a proposed estimate
must be reported in its narrower scope.

## 5. Bounded semantic return already performed

Three new shelf dictionaries (Meixner-Pollaczek expansion; continuous Hahn
Mellin reciprocity; orthogonal polynomial hyperbolicity preservers) returned
INCOMPLETE because of index freshness, not no hits. Their exact outputs are
retained in the source-polynomial-preserver-20260915 evidence directory.
The old source-query receipts were reused rather than repeated.

Romik's primary paper was inspected as a possible alternative. Theorem 3.1,
printed p.27, gives an expansion of the full Xi with local uniform convergence;
it does not supply the all-order zero-preserving estimate sought here. The
source's literal phrase is "converges uniformly on compacts". Source:
https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi-acta-online-first.pdf
PDF SHA256 a28edcf341776bf801e9d0c2de4631639b2c46c579a67a38cc2788d255e2ae87,
721444 bytes. Only introduction and relevant expansion statements were read;
no full-paper or proof-of-RH claim. This alternative was not selected. The
present continuation uses the already proved gamma limit (C1).

Decision: retain the old global obstruction, reopen only the weaker compact
critical-strip proof question under the user's renewed instruction. This is
one interface correction and an analytic attempt to supply it, not a reset
of source-sign counters or another claim that a renamed unknown is progress.
