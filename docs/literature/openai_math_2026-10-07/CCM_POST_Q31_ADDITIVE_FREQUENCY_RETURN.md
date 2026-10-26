# Post-Q31: pay distant additive frequencies before separating the near phase

2026-10-26. Bounded own derivation; independent q30_square_budget_check bounded PAPER PASS conditional on
the inherited Q02/Q04/Q31 model inputs; smooth base made explicit below.
Goal/RH OPEN. This is a partial source-preserving reduction, not a new bound
for the complete source. No Q32 sent.

## Exact contract and source shelf

Retain original P, m=N,L=log m,M=R=floor(m^epsilon),fixed0<epsilon<1/32.
Set h(x)=x^-1/2 P Q_M(log x)P and Omega=2pi M/L.
Q31 §§1,3 proves finite model return with all three contacts, possible Siegel
character, atom1 and prime powers; its §4.3 loses phase at Holder.
Q04 CCM_Q04_CENTERED_SECOND_PRIMITIVE.md supplies
||h''(x)||<=C(1+Omega)^2 x^-5/2 for L>=1.
CCM_Q02_LOW_RECIPROCAL_RANGE.md proves h(m)=h'(m)=0 on original P.
The latter uses P1=0, not merely Q(L)=0. These are inherited PAPER inputs.
We use h,h' bounds from Q31. No new boundary constraints are imposed.

The exact object is sum_{n<=m} b(n)h(n), b=Lambda-Lambda_tilde_w with
the SAME full model as Q31. The unverified search hint was: a smooth
additive-frequency cutoff might pay far frequencies without discarding
near-frequency phase. Negative control: arbitrary complex b of the same
size has no guaranteed favorable near-frequency sign. Nothing below
assumes such a sign or uses E1's quantitative uniformity theorem.

## Exact smooth partition, including the top

Take B=max(4,ceil(m^(2epsilon))) and eventually 2B<m. Fix a C² function
chi equal1 on(-infinity,1], equal0 on[2,infinity), with values in[0,1].
For concreteness on1<x<2 use1-10u³+15u⁴-6u⁵, u=x-1.
Let X_j=2^j B, j=0,...,J, with J the smallest nonnegative integer such
that2X_J>=m. Define chi_j(x)=chi(x/(2X_j))-chi(x/X_j).
Then chi_j is supported in[X_j,4X_j], nonnegative, has derivative bounds
C_r X_j^-r for r<=2, and exactly

chi(x/B)+sum_{j=0}^J chi_j(x)=1 for1<=x<=m.

No source weight is changed; all overlaps are summed before bounding.
Define a_j(x)=chi_j(x)h(x) for1<=x<=m and zero otherwise.
At m both value and derivative vanish; at the lower support the cutoff
has zero value/derivative. Thus its zero extension has no delta terms
in the second weak derivative, and

integral_R ||a_j''(x)||dx <=C(1+Omega)^2 X_j^-3/2.

The constant is absolute and independent of m,M,vector and dimension.
The unchanged finite matrix includes every mixed Fourier entry and both times.

## Exact arithmetic pairing and paid far part

Let I_j=[X_j,4X_j] intersection[1,m] intersection Z, b_j=b 1_Ij.
With e(t)=exp(2pi i t), define bhat_j(t)=sum_n b_j(n)e(-nt),
ahat_j(t)=sum_n a_j(n)e(-nt), t in[-1/2,1/2]. Exact reconstruction:

sum_n b(n)chi_j(n)h(n)=integral bhat_j(t) ahat_j(-t)dt.

Every prime power, exceptional-character term, complex phase and mixed
matrix coefficient remains. Frequencies here are dual to integer n, not
the physical log-frequency grid. Take tau_j=X_j^-1/2<=1/2.
Call the integrals over |t|<tau_j and its complement N_j and F_j.
Both are Hermitian: b and h(n) are real-scalar/Hermitian and the regions
are symmetric. Their sum is the exact original shell.

The discrete identity (1-e(t))² ahat_j(t)=Fourier(Delta² a_j)(t)
has no omitted endpoints. Two fundamental-theorem integrations yield
sum_n ||Delta² a_j(n)|| <=integral_R ||a_j''(x)||dx:
the translates of the unit triangular integration kernel sum to1.
Since |1-e(t)|>=4|t| on this torus,

||ahat_j(t)||<=C(1+Omega)^2 X_j^-3/2 |t|^-2.

Trivially |b_j(n)|<=L+2w because the complete model lies in[0,2w].
Thus ||bhat_j||infinity<=5X_j(L+2w). Only for the FAR part take norms:

||F_j|| <= C(1+Omega)^2 (L+w)/(sqrt(X_j)tau_j)
         = C(1+Omega)^2(L+w).

This bound does not assert cancellation of arithmetic coefficients.
Summing O(L) complete shells gives
||sum_j F_j||<=C(1+Omega)^2(L+w)L.
There is no separately discarded transition region or terminal shell.

## Full price and still-open signed near part

Use Q31 w=(epsilon L/4)² eventually; the finite model construction does
not require the U2 theorem's interval conditions. The model price is
O_epsilon(m^(3epsilon/2)L³). Define the exact smooth base E_base=sum_{n<=m} b(n)chi(n/B)h(n),
supported on n<=2B (including B<n<2B). The full identity is
A_prime=A_model+E_base+sum_j(N_j+F_j). The smooth base has norm
<=(12+8w)sqrt(2B)=O_epsilon(m^epsilon L²).
The far price is O_epsilon(m^(2epsilon)L+L³), hence all three prices
are <=C_epsilon m^(3epsilon) eventually. Therefore with N=sum_j N_j,

||A_prime-N||<=C_epsilon m^(3epsilon).

This is an operator norm on the SAME original P. The signed N is retained
without modulus. Original divisor short fee b_div has exponent3epsilon/2
up to logs, so any supplied N<=D_epsilon m^theta(epsilon)P would give

T_>R <=[D_epsilon m^theta+C_epsilon m^(3epsilon)]P,
PK_mP >=-[D_epsilon m^theta+C_epsilon m^(3epsilon)+50L+8]P.

Conversely an A_prime upper transfers to N up to the same norm fee.
No b_div is charged twice and no extra H_decay4 is attached to K.
Theta->0 is OPEN; this reduction does not prove it. Q31's full bound
still implies only N<=C[sqrt(m)/L^(1/8)+m^(3epsilon)]P, conditional on E1.
The near arcs contain t=0 and frequencies of order Omega/X; they are
not automatically minor arcs and must not receive a generic minor-arc bound.

## Decision and limits

The far-frequency bill is paid with a vanishing exponent without invoking
new prime cancellation. The sole remaining arithmetic task is the joint
signed pairing on the retained near arcs. This is a faithful localization,
not an independent supplier of its sign. Do not count the coordinate change
or its tests as an improvement of the complete CCM exponent. Stop if the
next proposed near estimate merely reproduces Q31 Holder or scalar-prefix
completion. No actual source no-go or RH claim follows.

## Bounded shelf check

post_q26_operator_rollback checked Q31 matrix Fourier-Abel, Q10 mean-square
and high-order return, transport/Ramanujan quadrature, Q02/Q04 endpoint
formulas. No exact near/far additive split in those inspected sources; this
is not global novelty or absence. ask.sh --defer-external returned INCOMPLETE
for stale semantic indexes. Only second derivatives are used at the top seam.
The arithmetic side b_j is restricted by an INDICATOR, not chi_j: only
a_j carries chi_j, so reconstruction contains chi_j once, not chi_j².
