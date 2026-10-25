# Direct all-P contour budget after Q27

2026-10-26. BOUNDED PAPER PASS: read-only all_p_contour_extension audited
the complete payload, original-domain transfer, fees and converse; no
material defect. Q27 classical/source dependencies remain inherited.
No Lean, interval arithmetic or numerical spectral run was performed.
Baseline a9a40a5b. This extends the paid analytic representation to the
actual requested space; it does not establish its missing arithmetic sign.

## Original domain, no subspace promotion

Fix 0<epsilon<1/32. Keep N=m,L=log m,M=R=floor(m^epsilon) and exactly
the original three-contact projector P=P_(m,epsilon). Work for all sufficiently
large m, with onset allowed to depend on epsilon. Define omega_j=2pi j/L,
Omega=2pi M/L and V2=sum_(|j|<=M)omega_j²/L.
All operators below act on ran P and retain their original coefficient
carrier by zero padding. There is no H0/H1 decomposition and no omitted
off-diagonal block: repeat Q27's calculation DIRECTLY with P in place of Pi0.

The span of original contacts is invariant under conjugation, so P is real
symmetric, and P1=0. Define v_±(z)_j=(z±i omega_j)^(-1) and

 S_P(z)=P[v_+(z)v_+(z)^T+v_-(z)v_-(z)^T]P/L.

The transpose, both orientations and all mixed entries are retained. The
causal inverse is still the literal Q_M(log n), since exp(i omega_j L)=1.
Q27's (2.3)--(2.5) follow for every vector of this full original space,
including all Lambda(p^k), the atom n=m, and the right-line n>m return.
Subtracting the growing continuum gives exactly one -H_P, 0<=H_P<=4P.

## Estimates independent of the polylog specialization

Q27's proofs of (3.2)--(3.4) use only contraction, P1=0 and the frequency
lattice: ||S_P(x+it)||<=8V2/|t|^4 for x>=0,|t|>=2Omega, and
||S_P(u+it)||<=3L for u>=1/L. Also V2<=Omega³. None requires M=ceil(8L²).
The pole-integrability/Markov construction therefore supplies one u in
[1/L,2/L] for the whole space, and one common H in [Y,Y+1], avoiding zeros,
with the same bounds as Q27(4.6),(6.4):

 B=2^20 Cstar L(1+Omega)log(12L)log(20+Omega),
 e=V2[32sqrt(m)L/Y³+2^20 Cstar log(12L)log(Y+10)/Y³
       +2^10 Cstar²sqrt(m)log²(Y+10)/(L Y⁴)].                 (1)

The zeta inputs are precisely Q27's fixed classical local factorization and
zero-count bounds, not ZF78 or RH. Every crossed actual zero remains in

 Rsign=He sum_(Re rho-1/2>u, |Im rho|<H)
           mult(rho) m^(rho-1/2) S_P(rho-1/2).               (2)

No contour is selected separately for individual vectors or positive W.
All finite-height inversion leakage, two vertical tails and both horizontal
sides are included in (1). Use the fixed choice nu=1/12 and

 Y=max(4Omega+10,16,m^(1/4+epsilon)).                        (3)

Eventually the last term dominates. With V2=O(m^(3epsilon)/L³), the three
fees in e are respectively

 O_epsilon(m^(-1/4)/L²),
 O_epsilon(m^(-3/4)log L/L²),
 O_epsilon(m^(-1/2-epsilon)/L²).

Thus e=O_epsilon(m^(-1/4)/L²)=o(1). Meanwhile

 B=O_epsilon(m^epsilon L log L).                            (4)

All constants are independent of m and vectors, after fixing epsilon.
There is no requirement of a uniform onset as epsilon tends to zero.

## Exact original goal interface and complete budget

Writing A=P A_prime P, Q27's SAME contour orientation yields

 A=-H_P+V-Rsign+E,  ||V||<=B, ||E||<=e.                    (5)

The original short sector satisfies the inherited two-sided norm bound

 b=(56+32Omega)sqrt(R)+12(1+log R)^2
   =O_epsilon(m^(3epsilon/2)/L+m^(epsilon/2)+L²).            (6)

Consequently, with every actual Mobius coefficient in the exact split,

 T_>R <= -Rsign-H_P+(B+e+b)P,                              (7)
 P K_m P >= Rsign+H_P-(B+e+50L+8)P.                        (8)

The second line does not pay the short sector again: it concerns the full
prime matrix. Proper powers are already in A, so no additional fee is added.
For every fixed epsilon>0, all analytic/short/archimedean scalar fees in
(7)--(8) are bounded eventually by C_epsilon m^(2epsilon).

An independently supplied bound

 Rsign >= -D_epsilon m^(theta(epsilon)) P,
 theta(epsilon)>=0, theta(epsilon)->0,                     (9 OPEN)

would therefore give the actual requested T_>R bound with
eta(epsilon)=max(theta(epsilon),2epsilon)->0. This statement covers the
entire original P; there is no unpaid H0 complement in this derivation.
Condition (9) refers to the SAME common admissible contours u,H in (5).
The conditional sparse witness and its previously paid return would then
apply, but (9) has NOT been proved.

Conversely, if the requested T_>R upper with exponent eta(epsilon)->0 were
supplied, (5), A=T_>R+T_<=R, ||T_<=R||<=b, and H_P<=4P imply

 Rsign >= -[B+e+4+b+C_epsilon m^(eta(epsilon))]P.           (10)

Thus the existence of the desired vanishing-exponent upper family is
equivalent, up to vanishing-exponent analytic fees, to a lower family for
the WHOLE signed residue matrix. This is not an independent supplier, nor
evidence that the new sign problem is easier. It identifies precisely the
remaining debt after paying the original-space return.

## Stopping boundary

Q27's H0-only comparison needed unpaid complement/cross blocks for an
all-P promotion. We have avoided that promotion by repeating its algebra
and estimates on P itself. The larger Omega,V2 costs were explicitly paid.
No favorable arithmetic exponent has been obtained, and the target remains
open. Bounding (2) by the sum of individual norms again loses its signs;
changing Y only reduces an already negligible analytic error. Do not count
this extension as three new attempts, a new prime law, or an RH result.
No Q28 has been sent.
