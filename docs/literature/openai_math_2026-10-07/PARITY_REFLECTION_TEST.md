# Parity restriction and the reflection contour

2026-10-07. Continuation of MASKED_LOW_INTERFACE.md. Exact object: the completed row with c squarefree, d|c and v_p(n) even for all p|d. We need a bound uniform in moving squarefree d, together with its coupled additive row. This is an algebraic test of that interface, not an improved low estimate.

## Exact rewrite on the initial half-plane

For every n and squarefree d,

product_{p|d} 1_{v_p(n) even}
 = sum_{r|n, rad(r)|d} (-1)^Omega(r).

The proof is local: sum_{k=0}^v (-1)^k is 1 for even v and 0 for odd v. This identity requires neither cancellation estimates nor coprimality of c and n.

Use s for the completed Dirichlet-series variable, and t=s-1/2 for the original Mellin variable. The source defines T(s,Psi)=D(s,Psi)L0(s,Psi), with

L0(s,Psi)=sum_n conjugate(alpha(n))^3 Psi(n)^3 q_n^(-3s+1/2).

Let D_d be the same squarefree c series with d|c. Since the c,n restrictions are separate and the source allows shared primes, absolute convergence for Re s>1 gives the exact restricted row

T_d^even(s,Psi)=D_d(s,Psi)L0(s,Psi) E_d(s,Psi),
E_d=product_{p|d}(1+z_p)^(-1),
z_p=conjugate(alpha(p))^3 Psi(p)^3 q_p^(-3s+1/2).

Indeed the unrestricted n local series is (1-z_p)^(-1), the even series is (1-z_p^2)^(-1), and their ratio is (1+z_p)^(-1). If Psi(p)=0, z_p=0 and both local series are 1. In the actual character row this includes the zero mask when p divides m.

Source: pinned paper.tex, proposition completed-reflection, 1677–1738; unmarked-central-completion and Mellin identity, 2818–2840. The source SHA256 is 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.

## The contour obstruction

For a unit character value, the geometric expansion of E_d converges absolutely precisely for Re s>1/6, equivalently Re t>-1/3. Its absolute local cost is (1-q_p^(-3Re s+1/2))^(-1). On every fixed line strictly to the right of 1/6, the product is at most C_(epsilon,s) q_d^epsilon: outside a fixed finite prime set, each factor is at most q_p^epsilon, and the remaining finite factors are absorbed into C. This is only the scalar multiplier cost on that line, not a moment estimate.

The denominator 1+z_p has candidate zeros on Re s=1/6. For z_p's unit coefficient b_p=exp(i theta_p), they satisfy

s=1/6 + i(theta_p-(2k+1)pi)/(3 log q_p), k in Z.

These are poles of the isolated rational multiplier. They are NOT asserted to survive in the full product: cancellation against D_d L0 requires a separate proof.

The source reflection proof shifts s from a>1 to 1/2-sigma<0, sigma>1/2 (2385–2403). This crosses the candidate-pole line. Thus the small absolute multiplier cost on the original half-plane does not justify carrying the old reflection and row moment across unchanged. One must establish cancellation, or compute and bound the extra residues, as well as continue the c-restricted factor uniformly. If several local denominator zeros coincide, their multiplicities must also be retained.

Negative control: an arbitrary holomorphic factor equal to 1 does not cancel these denominator zeros. Hence holomorphy of the original unmodified completion alone supplies no cancellation for the new restricted product. This diagnostic does not assert that the actual arithmetic product has such poles.

## Extracting the squarefree restriction as a moving character

There is a more useful exact reduction of D_d. The source proves for coprime squarefree primary a,b that

gamma_2(ab)=gamma_2(a)gamma_2(b)chi_b(a)^4

(paper.tex 10208–10213). Put Psi'(a)=Psi(a)chi_a(d)^4, retaining its zero on every a sharing a prime with d, and C_d=gamma_2(d) conjugate(alpha(d)) Psi(d). Substitution c=d*c' gives

D_d(s,Psi)=C_d q_d^(-s) D(s,Psi').

Since chi_n(d)^12 is exactly the coprimality indicator, L0(s,Psi') equals L0(s,Psi) with every n divisible by a prime of d removed. Therefore the stronger identity is

T_d^even(s,Psi)
 = C_d q_d^(-s) T(s,Psi') product_{p|d}(1-z_p^2)^(-1).            (3)

This holds first for Re s>1. If Psi(d)=0, the original restricted row is identically zero; treat this branch directly rather than dividing by character values. Otherwise the fourth-power reciprocity twist belongs to the moving good-prime data in the source reflection, while the fixed bad set S stays fixed. Its n cube acts only as a puncture; the finite Euler factor in (3) restores precisely the even valuations at the punctured primes.

Thus D_d need not be left as an unexplained new series. Equation (3) reduces it to the original completed family with explicit modified local exponents and a finite correction. The latter has candidate poles at both z_p=1 and z_p=-1, all on Re s=1/6. The earlier negative-sign poles describe E_d relative to D_d L0; (3) also accounts for restoring the punctured positive-sign factor. Noncancellation and residue estimates remain unproved. Source reflection can be invoked on T(s,Psi'), but its finite correction cannot simply be omitted during the contour shift.

For a single d=p with Psi(p) nonzero, let s_k be a zero of 1-z_p(s)^2. Its derivative is 6 log q_p, so the residue of the completed Mellin integrand is exactly

C_p q_p^(-s_k) Vhat(s_k-1/2) X^(s_k-1/2) T(s_k,Psi') / (6 log q_p).

If T vanishes there this expression is zero. Before bounding T or summing k, the absolute scale of the explicit powers is q_p^(-1/6) X^(-1/3). This is not a residue bound: the conductor-dependent T value and Mellin-height sum remain. For general d retain the other local denominators and treat coincident zeros with their actual multiplicities. This gives a concrete next input instead of an unnamed contour correction.

For each fixed p and fixed character row, this already yields a legitimate contour identity: the original integral on Re s=a>1 equals its integral on any fixed b<0 plus the sum of the displayed residues. The source proves polynomial height growth of T on fixed strips (2369–2382), and Vhat decreases faster than every power there. The pole heights form one equally spaced progression for 1-z_p^2, so the residue sum converges absolutely for fixed data; choose horizontal contours a fixed positive distance from that progression. The left-line denominator is also bounded away from zero since |z_p|>1 there. None of these fixed-data statements controls the dependence on p or the moving row. In particular they do not permit summing the coupled d operator using the original moment bound.

Independent bounded check: mobius_source_audit verified (3), zero masks, fourth-power reciprocity, contour variables and the single-prime residue. The source's fixed-data reflection constants explicitly depend on the moving local data (1750–1752). A constant independent of all d for the absolute divisor product requires beta=3Re s-1/2>1; the weaker q_d^epsilon bound above holds for each fixed beta>0. These are different uniformity claims. The source reflected-kernel variable is 1/2-s, not the original t=s-1/2, so its positive contour does not rescue the old geometric expansion.

Status: exact initial-half-plane rewrites and fixed-prime residue formula checked. No bound for the residue sum uniform in the moving data or for the aggregate coupled d operator is claimed. The useful next calculation is the restricted completed reflection using (3), with these potential residues explicit, rather than treating the parity condition as a harmless bounded coefficient.
