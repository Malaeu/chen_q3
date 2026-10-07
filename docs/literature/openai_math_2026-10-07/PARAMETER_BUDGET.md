# Compensated-probe parameter budget — 2026-10-07

Scope: conditional bookkeeping for the existing proof skeleton, NOT a theorem extending the paper to arbitrary geometry. The paper proves its compensated low estimate at fixed geometry. Its general high-representation definition does not establish that such a representation exists for every choice of its parameters.

Sources: pinned qrh78 paper.tex, 5560–5610 (high data and Euler regions), 6857–6875 (geometry), 8340–8362 (Gram estimate), 8564–8647 (low estimate and rescaled ranges). URL/hash in sources.json.

## Normalize the quantity being optimized

Write b=l_y-l_x, ell=total prime-slot length and impose the SAME balance l_x+l_y+ell=1. Then

l_x=(1-ell-b)/2, l_y=(1-ell+b)/2, h=1+ell-l_x=(1+3ell+b)/2.

The high Mellin exponent is C(s)=s+c, c=l_x/2-1+h/6. If the same low-side bound L=l_x/2+b/12 were available, its formal zero-free threshold would be

sigma_budget=L-c=1-h/6+b/12=11/12-ell/4.                 (1)

Thus changing the asymmetry b alone leaves this particular threshold unchanged. The source's ell=1/6 gives exactly 7/8. Approaching 1/2 in (1) requires ell approaching 5/3, which is incompatible even with positive l_x,l_y and the retained balance (these force ell<1). Already this restricted, hypothetical bound cannot reach 1/2 by geometry alone. This is an obstruction to this formula with these balances, not a general limit of metaplectic methods.

## Where the current proof's uniform substitution stops

The actual Gram proposition assumes Q,Y'>=1 and P_a=Y'^2/Q>=1. For a rescaled subset of total slot length d,

Q ~ Z^(l_x+l_y-2d), Y' ~ Z^(l_y-d), P_a ~ Z^b.

To reuse this proposition literally for EVERY subset, including d=ell, requires

1-3ell>=0, l_y-ell>=0, b>=0,

with fixed constants handled separately at equalities. In particular ell<=1/3, hence (1)>=5/6. This 5/6 number is only a barrier for the uniform-every-subset reuse strategy. One might handle small-Q subsets by a different argument, exploit their coefficients, or preserve cancellation between subsets. None of those possibilities is excluded or proved here.

The paper further absorbs P_a^2/Y' into P_a^(1/6). Uniform positive power margin requires

l_y-ell-11b/6 = 1/2-3ell/2-4b/3 > 0,

so ell<1/3-8b/9, yielding sigma_budget>5/6+2b/9. At the actual b=1/8, ell=1/6, the absorption margin is 1/12, matching the source. It is NOT legitimate to assume this stronger absorption is necessary for every possible argument; the unabsorbed Gram bound is also available.

## Keep the unabsorbed term and the subset coefficient together

The full Gram estimate has 1+P_a^(1/6)+P_a^2/Y'. In the current row-norm/Cauchy calculation, the net tuple/scaling factor contributes -d in the exponent. Conditional on the other component estimates remaining valid, the three exponents for a subset are

L_0(d)=l_x/2-d,
L_1(d)=l_x/2+b/12-d,
L_2(d)=l_x/2+b-l_y/2-d/2.

For b>=0, their maximum over d>=0 is attained at d=0 and has formal threshold

max(11/12-ell/4, 2/3+2b/3).                            (2)

This avoids the false inference that the worst Gram term at d=ell is also the worst final weighted contribution: the rescaling penalty matters. Formula (2) still presupposes the component estimates on all relevant scales; it does not extend them through Q<1. Under the literal every-subset applicability constraint ell<=1/3 it is at least 5/6. With only ell<1 it is still at least 2/3, so this unchanged algebraic budget cannot approach 1/2 even if small-Q terms were separately settled.

## Additional high-side obstruction

The cited high-data Euler domains themselves include a region with Re(s)>=7/8; the other region starts at 51/100 and has coupled Re(s+w)>1+epsilon. The general notation C(s) is therefore not a theorem of holomorphic control throughout Re(s)>1/2. Any improved endpoint needs the actual contour path, local convergence estimates and nonvanishing correction rechecked. The published high-side endpoint certificate alone does not do that.

## Next mathematical target

A successful improvement must alter an estimate or the detector geometry, not only optimize b. The immediate source object is the additive Gram bound's three terms and the reflected row-energy estimate: find a signed joint estimate for the SAME probe that improves their Cauchy product, or a new balance preserving the reciprocal-L signal. A request to Proshka should contain this exact budget and ask for one source-supported replacement inequality, with a stop condition if it assumes the desired cancellation. No RH/SP or source-observability gate is closed by this bookkeeping.

Independent bounded check: growth_symbol_attempt confirmed (1), the Q scale constraint and the 5/6 uniform-reuse implication, including the fixed-prefactor caveat at ell=1/3. Formula (2) is root bookkeeping from the displayed full Gram bound; no generalized analytic estimate is claimed.
