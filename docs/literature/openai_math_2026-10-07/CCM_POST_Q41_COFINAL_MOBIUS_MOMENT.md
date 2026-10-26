# Post-Q41: cofinal small short-Mobius moment, full return still open

2026-10-26. Independent q32_annulus_audit qualified PASS: primary statement, cofinal
schedule, Laurent coefficients and auxiliary norm allowance checked. Third own bounded preflight after
Q41; same original P and consumer. No source exponent improvement.

## Source and exact scope

Gallardo-Gutierrez and Seco, Zero-Free Regions of the Riemann Zeta Function
and Approximation in Weighted Dirichlet Spaces (2025), DOI10.1007/s11785-025-01661-2.
Primary https://link.springer.com/article/10.1007/s11785-025-01661-2 .
Saved sources/gallardo_seco_weighted_dirichlet_2025.html,
413632bytes SHA256247a11335a252e1f0b92283d3548aa73a8befc10547a1ead944038e624682cf2.
Locator Remark3.2(e), proof of Theorem3.1 equation(16). Quote:
“there are infinitely many values”. They use Selberg's sign-change theorem
for sum_{d<=U}mu(d)/d to obtain infinitely many U with U|a_U|<=1/2.
This is a partial arithmetic input, not their conditional Theorem3.1 bound(14).
The latter assumes the needed estimate on G(n,U); it is not proved there
unconditionally. The cited Selberg proof is not independently recertified.

## Own map to the exact Q41 channels

Fix epsilon,K=ceil(1/epsilon), and choose the indicated unbounded sequence U.
For each sufficiently large U choose an integer m in
[U^{1/epsilon},(U+1)^{1/epsilon}); this interval has length>1 eventually.
Then floor(m^epsilon)=U, with the original schedule unchanged, and
|a_U|<=1/(2U)=O_epsilon(m^{-epsilon}). This is cofinal, not all-m.
It is compatible with the receiver's cofinal option; no upper is yet supplied.

From the preceding joint-pole preflight the highest artificial Laurent
coefficient of B_UK at s=1 is (-1)^{K+1}a_U^K.
Its formal causal kernel is proportional to exp(t/2)t^K/K!.
Its full physical norm on [0,L] is at most C_K sqrt(m)L^K |a_U|^K
=O_epsilon(m^{1/2-epsilon*K}L^K), hence o(1).
This pays ONE artificial pole term, not the full prime matrix.

The remaining higher poles have not acquired the same a_U^K factor.
For each fixed r<=K, |M_U^{(r)}(1)|<=sum_{d<=U}(log d)^r/d
<=C_r(1+log U)^{r+1}. Write Y=-a_U/(s-1)+Y_reg.
Every negative Laurent coefficient of Y^K contains at least one a_U,
but need not contain K copies. Multiplying by -zeta'/zeta shows every
coefficient of B_UK of pole order>=2 is bounded by
C_K |a_U|(1+log U)^{C_K}, using |a_U|<=1 and fixed-K Taylor coefficients.
A finite sum of the corresponding causal kernels therefore has price
O_epsilon(sqrt(m)|a_U|L^{C_K})
=O_epsilon(m^{1/2-epsilon}L^{C_K}).
This is an available allowance, NOT a lower bound or necessary price.
Its exponent does not tend to zero as epsilon tends to zero.
The simple pole and finite-window contour remainder must remain joint;
we do not assume their sign, discard them, or attach an unproved small cost.

## What this does and does not decide

The source supplies an actual cofinal small coefficient that was absent in
the fixed-U test. Thus the old test cannot be promoted to a moving-U no-go.
However small a_U alone does not bound all derivative moments or the
signed finite-window return. Finite short inversion still equals Lambda
through m exactly. Using the complete remainder returns the prior source.
Full usable consumer bound remains A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
T_gtR<=(s_keep+b_div)P, PK_mP>=-(s_keep+50L+8)P.
No all-P favorable bound, RH claim, Lean/Arb or production numerical run.

The next concrete question may use this cofinal input only if it treats
the lower Laurent hierarchy AND the finite-window remainder jointly, with
actual short mu, both orientations and every mixed term. Merely bounding
the top pole again or assuming G(n,U) bound(14) is forbidden.
