# Zero-density completion of the original-P residue sum

2026-10-26. Bounded independent PAPER PASS by residue_density_supplier: partial
summation, full high tail, exponent and scope checked; no material defect.
Upstream Q27 kernel and contour dependencies remain inherited.
Baseline f3c16ecf. No new arithmetic exponent or RH claim.

## Exact receiver and supplier

Keep the original P, N=m, L=log m, M=R=floor(m^epsilon), fixed
0<epsilon<1/32. Use the SAME common u,H from
CCM_POST_Q27_ORIGINAL_P_CONTOUR.md (1)--(5). Its whole residue is

 Rsign=He sum_(beta-1/2>u, |gamma|<H)
       mult(rho) m^(rho-1/2) S_P(rho-1/2).

Both time orientations and every mixed entry remain inside S_P. The
required lower bound is -C_epsilon m^theta(epsilon)P with theta->0.
Already paid analytic, short and archimedean costs are O_epsilon(m^(2epsilon)).
Here we test only the completion Rsign >= -sum ||individual terms|| P.
This is the information-loss step; the following costs are certificates,
not lower bounds for the actual residue, prime operator or CCM.

Supplier: Guth--Maynard, arXiv:2405.20552v2, Theorem 1.2 and (1.4).
https://arxiv.org/html/2405.20552v2
Shelf PDF: docs/routeB_bus/litreview/pdfs/2405.20552.pdf
SHA256 915392cf7d0ecd108479814a9a1481e23423ef63415776471cec3975ae482cae.
Exact formula (1.4): N(sigma,T) <= T^{30(1-sigma)/13+o(1)}.
N counts zeros with Re rho>=sigma and |Im rho|<=T, with multiplicity.
This combines Theorem 1.2 with Ingham; it is not a zero-free assertion.
For the budget below use the usual fixed-loss version with T^a for any
fixed a>0. A finite sigma mesh gives the same exponent calculation if
uniformity of the displayed o(1) is not invoked; allow an arbitrarily
small additional m-power loss for the mesh.

Shelf queries signed residue matrix zero density; weighted zero counting
partial summation; reflection positivity analytic transpose all returned
ASK_STATUS INCOMPLETE (semantic freshness), not evidence of absence.
The source itself was read at Theorem 1.2 and (1.4).

## Full low/high return

Choose G=m^kappa with epsilon<kappa<1/4+epsilon; thus eventually
2Omega<G<H. The inherited local count O(log(t+2)) per unit interval and
||S_P(x+it)||<=8V2/|t|^4 give

 high norm <= C sqrt(m) V2 log(G+2)/G^3
           = O_epsilon(m^(1/2+3epsilon-3kappa)/L^2).

This retains every zero above G up to H and bounds them by an infinite
tail. Taking kappa>1/6+epsilon makes this certificate o(1). For example
kappa=5/24+epsilon is admissible and gives exponent -1/8 exactly.
Root rational arithmetic checked these inequalities, including the uniform
endpoint 9/32<13/30; this is algebra, not a spectral experiment.

For the low part, ||S_P(x+it)||<=3L when x>=u>=1/L. Put sigma0=1/2+u.
Writing each weight as m^u+L integral_(sigma0)^beta m^(sigma-1/2)d sigma
gives, without discarding any low zeros,

 low norm <= 3L [m^u N(sigma0,G)
          + L integral_(sigma0)^1 m^(sigma-1/2) N(sigma,G)d sigma].

Using (1.4), the integral power envelope is

 F_kappa(sigma)=sigma-1/2+(30kappa/13)(1-sigma).

On our allowed kappa interval, kappa<1/4+1/32=9/32<13/30.
Thus F is increasing and its supremum as sigma approaches 1 is 1/2.
The initial term has power 15kappa/13, strictly less than 1/2.
Consequently this completion supplies only m^(1/2+arbitrarily small loss),
up to logarithms, even when the high tail is o(1). It supplies no theta->0.
The already available 12sqrt(m) fallback is better and is retained.
No optimization of G within this calculation repairs the low residue sign.

## Negative control and stopping boundary

A fixed hypothetical off-critical conjugate pair beta0 +/- i gamma0,
beta0>1/2, is compatible with such counting upper bounds: eventually
u<beta0-1/2 and H>|gamma0|, so it remains in this residue sum. This is
not a claim that this pair exists, that its actual compressed contribution
has a specified size or sign, or that other residues cannot cancel it.
It tests the missing hypothesis: a counting theorem does not exclude all
low exceptional zeros or control the joint real quadratic form.

Even the hypothetical density law N(sigma,T)<=T^{2(1-sigma)+o(1)} would
give F=sigma-1/2+2kappa(1-sigma), still with supremum 1/2 for kappa<1/2.
This is a diagnostic of this particular absolute completion, not a claim
that density theory or signed methods can never help the original goal.

Rollback: retain the exact signed Rsign before the norm sum. The next
supplier must control its actual matrix correlation, or give an independent
source inequality with a full map back. Lowering the already-paid contour
error and merely improving a zero count are not that supplier. No Q28 sent.
