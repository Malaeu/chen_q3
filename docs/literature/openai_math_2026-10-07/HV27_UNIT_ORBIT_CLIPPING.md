# HV.27: invariant selection by unit-orbit energy

2026-10-09. Independent read-only q05_moment_audit O1–O4 PASS; explicit b-mask notation fixed. RH/SP/HV22/HV27 OPEN.
This is an exact finite-group rewrite, not an arithmetic saving.
Same Q3 parameters, full sixthfree u family, rho, b masks and w(b).

## O1. Average before selecting

For fixed b and common profile set J(u)=J_C,u^[b](L), and let E be
the six units of the source field. Set

 Q_b(u)=(1/6)sum_(zeta in E)|J(zeta*u)|².

Unit multiplication permutes the full original u family, leaves its norm,
sixthfree property, fixed-S valuations and all coprimality masks unchanged.
Thus Q_b is unit-invariant and sum_u rho Q_b=sum_u rho |J(u)|².
For V>=0 write T_J(V)=sum_b w(b)sum_u rho (|J(u)|²-V)+
and T_Q(V)=sum_b w(b)sum_u rho (Q_b(u)-V)+. Then

 T_Q(V)<=T_J(V)<=6T_Q(V/6).                         O1

Left: Jensen on the six nonnegative squared magnitudes, then orbit
permutation in the sum. Right: |J(u)|²<=6Q_b(u), pointwise.
This preserves the full row/mask weights and only changes the level
by a fixed constant, never its U exponent. For Q3 V*=V0/4,
T_Q(V0/24)<<H U^-eta*loss suffices for actual HV22.
Small-value cost at any such fixed level is still O(H U^-3/500).
No claim that the two excesses at an IDENTICAL level are equal.

## O2. Exact restored unit projector

Let a_(n,b)=L^-1/2 j_C(n)nu(n)1_(n,b)=1 W(qn/L),
retaining all prime powers and the fixed b-mask.
The restricted unit character alpha_n(zeta)=chi_n(zeta)^epschi
is one of six characters of E. Character zeros at u remain zero.
Set J_alpha(u)=sum_(n:alpha_n=alpha) a_(n,b)chi_n(u)^epschi.
Then J=sum_alpha J_alpha. Orthogonality gives

 Q_b(u)=sum_alpha |J_alpha(u)|².                    O2

The selector theta_bar(u,b)=1_(Q_b(u)>V0/24) is unit-invariant.
Its selected kernel retains only pairs with alpha_n=alpha_m.
In the original n,m expansion this is an exact finite projector,
not an assumed invariance of the old |J(u)|² selector. Set
Z_bar=sum_b w(b)sum_u rho theta_bar. Exactly

 T_Q(V0/24)=G_bar_off+D_bar-(V0/24)Z_bar.            O3

D_bar has the same paid bound O(PU U^epsilon*height) as HV26.
G_bar_off keeps ALL n!=m pairs with equal unit character, original
coefficients, common profile, masks and literal weighted u sum.
The sufficient new inequality is

 G_bar_off-(V0/24)Z_bar <= H U^-1/200*loss.          O4 OPEN

## Scope and next test

O1 removes the particular arbitrary-unit-selector obstruction at a
constant threshold cost. It does not remove same-character correlations,
prove O4, or improve the old full energy bound. In fact the full
orbit-averaged energy equals the original energy exactly. Any prospective
use must give a quantitative estimate on O4 or actual HV22; recovering
this projector alone is not progress in the inverse exponent.
The b=1 test and j_C(n)=mu(n)-1 on C-rough columns still apply.
