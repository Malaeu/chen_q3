# Lowering z after angular extraction: exact principal local test

2026-10-07. Pinned source and phases as in ANGULAR_FACTOR_NEIGHBORHOOD.md. This is a test of reusing the existing selected-slot error estimate after moving z toward 1/6, not a bound for the full signed physical sum.

At u=1, real x=a in (1/2,3/5), real w=1-a and z=1/6, write P=q_p, q=P^-1, W=P^(a-1), D=eta(p)P^-a and R=kappa(p)P^(3-6a), where |eta|=|kappa|=1. Substitution in the source local identity (4015–4039), with V=q and J_0=-D+WR, gives exactly

Pstar=(1+W)(R-D)/(1-R),
Pfull=1/(1-q)+W/(1-W)+Pstar,
B=bar(eta)P^a Pstar/Pfull-W.

As P tends to infinity all q,W,D,R tend uniformly in phase to zero; Pfull=1+o(1). Since D/R has modulus P^(5a-3) -> 0, we get

B+1 = bar(eta) kappa P^(3-5a) (1+o(1)),
|B+1| / P^(3-5a) -> 1.

This is uniform in the unit phases for a in any compact subinterval of (1/2,3/5). In particular a=51/100 gives local growth P^(9/20). The error is not pointwise O(P^-1/2). The principal row is not covered by the source nonprincipal reflected-L proposition in the first place; this calculation must NOT be presented as a counterexample to that proposition. It shows that angular extraction alone does not preserve the principal local approximation B~-1 on the proposed lower contour.

The source high central line is w=1-a-6e, x=a+16e, not w=1. Thus the previously proved nonzero principal slice at w=1 does not directly establish a central-contour slot bound. At z=1/6 the scalar zeta_F(6z) also has a pole: an actual contour must stay to the right or explicitly pay its residue. The formula above is a local boundary discriminator, not authorization to move an integral through that pole.

For a nearby real z=1/6+t, t>0, the raw R/D magnitude is P^(3-5a-6t). The leading R contribution in the unramified local error remains of that order when it dominates the other terms. A pointwise P^-1/2 payment for this term requires 5a+6z >= 9/2, hence at a=51/100 requires z >= 13/40 = .325. This is only a termwise necessary budget for that proof method, not a global impossibility theorem; collective signed cancellation could change the payment. The exact boundary asymptotic above is the established statement. No high or low exponent gain, no RH closure.

## Independent check and unramified extension

causal_algebra_audit checked the source substitutions and exponent budget: PASS. The local asymptotic extends to every p not dividing u, with v=chi_p(u), W=vP^(a-1), D=eta v^-1 P^-a. Still DW=eta q, so the identical Pstar and Pfull formulas hold and

B+v^-1 = bar(eta) kappa P^(3-5a)(1+o(1)),

uniformly in v and the other unit phases on compact a ranges in (1/2,3/5). Thus even unramified nonprincipal rows do not retain the desired local main/error approximation by angular extraction alone. This does not contradict the source proposition, which fixes z=17/50. The proposed shortcut (reuse its slot-error estimate unchanged on z=1/6) is rejected; collective cancellation of the explicit leading term is a separate open task.
