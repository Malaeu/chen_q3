# Post-Q13 own attempt: original-P projection of exponential residue probes

2026-10-23. Mechanism tested: after Q13 paid the full analytic frequency return,
can the original three constraints suppress prospective September remainder
exponential components before bounding their signed sum? No actual residue
expansion or actual off-line pole is assumed here.

## Shelf crosswalk
September PROSHKA_VERDICT_GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY_2026-09-06.md
§4 gives exact L++ and L+- transforms of D=K_N-K_A in terms of
r_p=Omega_p-1/(1-kappa_p), h_pq=J_pq+Omega_p-Omega_q.
Both signs and all mixed terms are indispensable. Bounds(26) alone are not a
small compressed quadratic form. Lemma7's full Poisson identity remains OPEN;
§5 explicitly identifies the missing half-plane continuation contribution.
OPENSGN_INDEPENDENT_CHECK confirms the reduction, not its missing value.
Q08_ANNIHILATOR_PREFLIGHT already proves B=D²-1/4 only changes an exponential
amplitude away from ±1/2; do not relabel this old fact as a new gain.
The following calculation quantifies the ORIGINAL-P norm, rather than only
applying a differential filter to an isolated mode.

## Exact source coordinates
L=log m,T=L/2,omega_j=2pi j/L,M=floor(m^epsilon), fixed0<epsilon<1/32.
psi(r)=sum c_j(-1)^j exp(i omega_j r)/sqrt L on[-T,T], zero outside.
P is the original endpoint plus two exponential-moment projector.
For any complex z off the finite mode poles:

 Lpsi(z)=int psi(r)exp(zr)dr
        =2sinh(zT)/sqrt L * sum c_j/(z+i omega_j).

Let D_M(z)=prod_(|j|<=M)(z+i omega_j). Its numerator N_c has degree<=2M−1
because sum c_j=0. The two moment constraints give
N_c(z)=(z²-1/4)R_c(z), degree R_c<=2M−3.
This is an injective, hence onto, parametrization of a (2M−2)-dimensional
space for M>=2. No change of allowed source vectors is made.
At z=i omega_k with |k|<=M the removable limit is sqrt L(-1)^k c_(-k),
not a universal zero. Outside that band the same lattice points are common
zeros. The only other common zeros are ±1/2. This algebra alone is not a
quantitative bound on a sum of residue contributions.

## Quantitative projection lemma
Fix z=a+ib with a>0. Let V_z be the Riesz representer on the original finite
band of psi -> int exp(zr)psi(r)dr (conjugating the exponential in the
representer only changes harmless conjugation conventions). Then

 ||P V_z||²/m^a -> C_z
 C_z = 1/(2a)-1/|z+1/2|²
     = |z-1/2|²/[2a |z+1/2|²].                         (1)

In particular C_z>0 for z!=1/2. This is a statement about a fixed hypothetical
probe, not the existence of any pole or any positive source defect.

Proof. In the full interval space, ||exp(zr)||²/m^a ->1/(2a).
Its Fourier tail beyond M has squared norm/m^a=O_z(L/M): the exact
coefficients have denominator z−i omega_j and endpoint numerator of
absolute size O_z(m^(a/2)). For M/L->infinity, summing j^-2 proves the tail
bound. The same holds for each exponential contact ±1/2. Normalize the
three constraint vectors: their Gram tends to I by the original sparse
receiver estimates, or directly by the same coefficient formulas.
The overlap of exp(zr)/m^(a/2) with the normalized growing contact tends
in squared absolute value to 1/|z+1/2|²: integrate exp((z+1/2)r) exactly.
Its overlap with the normalized decaying contact tends to zero: the largest
possible exponential factor after normalization decays like m^-min(a,1/2),
with an L factor in the coincident denominator case.
The endpoint vector is the normalized all-ones vector in source coordinates.
Pairing j and −j in sum1/(z−i omega_j) makes that sum O_z(L) once L is large
and a>0 fixed (the corresponding convergent full sum is (L/2)coth(zL/2)).
Thus the endpoint overlap divided by m^(a/2) is O_z(sqrt(L/M)) and vanishes.
The exact finite projection is v* v−(C* v)* (C* C)^−1(C* v), retaining all
constraint cross terms. Passing to its Gram limit gives(1). This proof works
on the original integer m schedule and fixes z,epsilon before taking limits.

Independent bounded read-only q14_shelf PAPER PASS of exact rational map and
quantitative projection lemma, with fixed-z/fixed-epsilon scope; no actual
residue expansion or aggregate sign inferred.

## Consequence and boundary
The rank-one positive probe quadratic |Lpsi(z)|² has exact compressed norm
||P V_z||², hence a fixed power m^a for z!=1/2. Thus original-P projection
alone does not turn a generic fixed exponential probe into m^eta with eta->0.
This does NOT estimate a genuine signed residue aggregate: its coefficients,
reflected partners, continuous component and all cross terms must first be
derived from the actual xi remainder and kept together. The result does not
prove a CCM lower bound, RH obstruction, or failure of a joint signed method.

q14_projection_checks/check.py supplies four noninterval QR diagnostics with
z=1/4+3i/4 and epsilon1/40. L is sampled continuously for numerical stability;
these are projection-only diagnostics, not original integer-m CCM evaluations.
Scaled values approach C_z=10/9. No large prime sums, Lean or new dependency.

## Concrete rollback / question
Stop the proposal that finite codimension P automatically suppresses unknown
continuation terms. Keep Q13 paid return. The actual missing supplier is a
one-sided compression of the September remainder with its true coefficients
and mixed sectors; individual exponential norms cannot supply it for free.
Ask for one concrete source-specific signed contribution formula/inequality
on original P, with complete cost; do not assume the global Poisson identity
or delete residues merely because the known poles ±1/2 are annihilated.
