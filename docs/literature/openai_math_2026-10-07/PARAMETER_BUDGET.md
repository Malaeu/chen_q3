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


## 2026-10-09 candidate: perturb a strict endpoint margin (independent P3 PASS)

Read-only long_positive_alias checked P3, the Gram/capacity arithmetic and
source-domain mapping. Acceptance is conditional bookkeeping only; all
parameter-perturbed analytic hypotheses below remain OPEN.

This is a conditional feasibility calculation, NOT an improved zero-free
region. Source paper hash rechecked:42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.
The source's balanced-endpoint lemma at15995-16080 gives -E_*>=49/440640
for 0<=delta<=5/6,0<=x<=1/2. Its proof exhibits a positive polynomial
certificate. This strict ideal margin suggests checking a small geometry
perturbation instead of declaring 7/8 an algebraically rigid endpoint.

Let t>0 be FIXED before Z and set

    ell_t=1/6+t, b=1/8,
    lx_t=17/48-t/2, ly_t=23/48-t/2, h_t=13/16+3t/2,
    sigma_t=7/8-t/4.

The original balance is retained. Exactly C_t(s)=s-11/16, while the
hypothetical low exponent lx_t/2+b/12=3/16-t/4=C_t(sigma_t).
The all-subset Gram conditions remain strict at t=1/100000:
1-3ell_t=1/2-3t>0; ly_t-ell_t=5/16-3t/2>0;
ly_t-ell_t-11b/6=1/12-3t/2>0. These inequalities do not themselves
prove that every other low-side hypothesis survives.

Use source stage-high-exponent (paper6090) with g=q ell_t, a=(1+delta)/2,
z0=17/50 and hold its ideal row pair (R,q) fixed. At d=h_t,

    E_t(h_t;R,q)-E_0(h_0;R,q)
       =t[delta+q+(3/2)R-1/4].                      (P3)

If 0<=R<=1,0<=q<=delta/2,0<=delta<=5/6, its increase is at most(5/2)t.
Thus the SAME hypothetical ideal row bound R=R_*(delta,x), q=x delta,
would retain endpoint saving at least49/440640-1/40000>0 at t=1/100000.
The source formula R_*=1-delta+(5/6-delta)delta P_x/(2J) has R_*<=1
because D_x>=P_x and J=(5/6-delta)D_x+delta P_x>=(5/6)P_x;
the added fraction is at most delta/2. The first draft cited only
J>=delta P_x, which was insufficient; the independent pass corrected
that justification without changing P3 or its bound.
The available endpoint slot capacity ell_t/h_t increases with t:
its derivative is (9/16)/h_t²>0. This is a capacity comparison only,
not a new selected row-count theorem.

Crucial outstanding premise: the literal high-data, buffered contours,
principal detector, every intermediate-d row estimate and the full low
estimate must hold for this perturbed physical probe. The published retained
integral lemma assumes sigma0>=7/8; substituting sigma_t into it is invalid.
D1 also requires Re z>=17/50 and cannot reach the residue z=1/6.
Existing ANGULAR_FACTOR_NEIGHBORHOOD.md gives a local correction-factor
continuation near that residue (and angular absolute nonvanishing above2/3),
not all the required global bounds or the new high representation.

Hence sigma_t=7/8-1/400000 is only a CANDIDATE threshold. No new strip,
CCM floor or RH gain is claimed. Next bounded test is the exact high-side
hypothesis transport for this single rational t, not a broad optimization
or another request to assume the missing signed CCM estimate.


Source-domain return checked in the same pass: on the nonprincipal central
contours s=a+16e,w=1-a-6e,z=17/50, D1 uses s+w=1+10e and fixed floor
a>=51/100. On the candidate principal rectangle the angular argument
6 Re s+6 Re z-4 is greater than2.2399 for Re s>=sigma_t and
Re z>=33/200. This local Euler margin does not prove full principal
contour control. Source fixed-bin5808-5834, principal-residue6174-6222,
high-bin15699-15757 and fixed-geometry low8564-8647 must be returned
on the same perturbed physical probe. In particular do not retain the
old identity kappa=3/4+2Delta with Delta now measured from sigma_t:
actual kappa=2beta_*-1=3/4-t/2+2(beta_*-sigma_t). The source's row
capacity comparison must be rechecked with that value, along with every
intermediate d, all height costs, normalizers and proper subsets.

Decision: one bounded follow-up on analytic transport at this fixed rational
t may change the available polynomial exponent; repeating P3 or asserting
continuity of the final theorem may not. No question has yet been sent and
no external family theorem, Hecke uniformity or improved zeta claim is admitted.


### All physical row ranges: conditional perturbation audit

2026-10-09. Independent read-only long_positive_alias source audit of
paper12531-12579,15100-15446,15699-15757,15843-15917,16112-16217;
root checked the moment hypothesis and frequency-range proof directly.
This extends the exponent bookkeeping, not the analytic high theorem.
For FIXED d,R,q the exact change is

    E_t(d)-E_0(d)=t(13/50+delta/4+q)<=177t/200.       (P4)

At d=h_t the additional displacement is (3t/2)(R+delta/2-17/50).
The moment parameter must be separated from the bin ceiling:

    Delta_old=beta_*-7/8, Delta_plus=max(Delta_old,0),
    kappa_bin=2beta_*-1,
    kappa_m=max(3/4,kappa_bin)=3/4+2Delta_plus.

The plain moment lemma permits kappa_m in[3/4,1] and requires
beta_*<=(1+kappa_m)/2 when kappa_m<1. This holds in BOTH branches.
Its baseline capacity therefore remains available when Delta_old<0;
the capacity comparison uses Delta_plus/4, never a negative Delta_old.
The source Part II setup does not make this split, so detector-counts
still needs restatement with kappa_bin<=kappa_m. This is an identified
transport obligation, not permission to substitute into the old theorem.

Under the source prior beta_*<=11/12, Delta_plus<=1/24. For the
capacity-inflated R=R_*+Delta_plus/4, the endpoint perturbation is at
most161t/64 (apart from adjustable small losses). Thus its strict
ideal saving49/440640 exceeds the perturbation at t=1/100000.
The adaptive slopes stay positive and below2. Also ell_t/h_t increases
and5ell_t-h_t=1/48+7t/2, so the original fixed0<zeta<1/48 remains
within slot supply and the extension to h_t+zeta costs at most2zeta.

For d_min<=d<=1/2 the unchanged no-selected-prime count
R=76/75-2delta/3 has positive slope101/150-delta/6. At its endpoint
the saving is at least49/14400-177t/200>0. The floor delta=1/50
cost is at most1.28t against7/1200; the delta=5/6 endpoint costs
at most1.25t against7/96. These are ideal margins before small losses.
For d<d_min the source saving becomes63/800-51t/100>0.
For d>h_t+zeta the exponent is

    B0_t+(h_t+zeta)(1+epsilon)-zeta*z_infinity+epsilon,
    B0_t=53/32-3t/4.

A sufficiently large fixed z_infinity still makes this negative, if the
corresponding raw analytic tail estimate transfers. All physical slots
remain in the high correction even in the no-selected-prime row count.

CLOSES: arithmetic feasibility across all d ranges and a valid clipped
moment-parameter choice at the level of its stated hypothesis.
OPEN: actual perturbed detector counts, all high contour hypotheses,
full low estimate and target-independent order of losses. No new strip,
CCM exponent or family nonvanishing result is established here.


### Full low-side proof return, with the row-norm loss retained

2026-10-09. long_positive_alias independently traced separation3397-3475,
8073-8109, reflected-energy7747-7804, row-norm8111-8330 and low8564-8649;
root checked the underlying energy branches and subset accounting. This
is a proof adaptation conditional on the source component lemmas, not
an independent verification of the entire source manuscript.

For the same perturbed physical probe, put M_t=1-ell_t. In each rescaled
subset J, d=sum_(i in J)ell_i, M'_t=M_t-2d and ell'_t=ell_t-d.
The completed scale, original masks and all marked slots stay intact.
Exactly M'_t+ell'_t-1=-3d. In the reflected-energy proof the second
branch before specializing the geometry is

 M'_t+(1+3ell'_t-2M'_t-2Delta_H+theta_N)/4
 =M'_t+(d+5ell_t-1-2Delta_H+theta_N)/4.

The first branch is M'_t-Delta_H up to the allocated small losses.
Their maximum, after the same dyadic smoothing/tail allowances, gives

 sum_(0<q_m<<Q)|B^J_(m,sigma)(Z)|²
       << Z^(M'_t+rho_t(d)+epsilon),
 rho_t(d)=max((d+5ell_t-1)/4,0).                    (P5)

The original row-norm statement cannot be quoted unchanged: rho_t
can reach3t/2. The general reflected-energy input allows fixed bounded
lengths, and its proof's bound T_d<=H-3d+small losses is unchanged by
the exact balance. Original dual ideals, shared-prime permissions and
zero masks are retained; no new coprimality condition is introduced.

For the actual tuple ratio r_J=q_(p_J)/Z^d bounded above and below,
X'=Z^(lx_t-d)/r_J,Y'=Z^(ly_t-d)/r_J and
Q=q_(b_*)Z^(M'_t)/r_J². Therefore

 P_a=Y'^2/Q=q_(b_*)^(-1)Z^(1/8).

Uniformly over subsets, M'_t>=1/2-3t>0,
lx_t-d>=3/16-3t/2>0, ly_t-d>=5/16-3t/2>0,
and ly_t-d-11b/6>=1/12-3t/2>0. Thus the same fixed-data threshold
makes Q,Y',P_a>=1, and the full Gram bound reduces to
(Q/Y')P_a^(1/6) times its height and small-power factors.
Cauchy with P5 now gives the old tuple bound multiplied by Z^(rho_t(d)/2).
The actual tuple count Z^(d+epsilon), rescaling coefficient Z^(-3d/2)
and X' square root Z^(-d/2) give net additional exponent

    -d+rho_t(d)/2<=0                               (P6)

for every0<=d<=ell_t, because ell_t<1/5. If rho_t=0 this is immediate;
otherwise it equals(-7d+5ell_t-1)/8<0. In particular the hidden loss
is paid by the same subset's rescaling; it is not dropped or charged
against a different summand. Summing all finitely many subsets yields

 |I_(eta,modified,t)(Z)|<<Z^(3/16-t/4+epsilon).      (P7)

Constants may depend on the fixed target arithmetic data, chosen disjoint
positive slot system and smooth tests. The exponent does not. Division by
the original principal slot-mass normalizer costs only the source's
arbitrarily small power. No analysis-height cutoff enters the physical
probe or this normalizer. This closes the conditional low proof transfer;
nonprincipal high transport, the clipped detector-count restatement and
common target-independent parameter order remain OPEN. In particular P7
alone gives no zero-free assertion or improvement for CCM.
