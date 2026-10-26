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

## Follow-up: constant model and central-arc preflight

2026-10-26. Own refinement; q30_square_budget_check bounded independent PAPER PASS
for this section, including primary DLMF map and all endpoints.
The previous Cramer-Siegel statement is retained as valid. For THIS purely
elementary localization choose instead b0(n)=Lambda(n)-1, including b0(1)=-1.
Do not apply E1 to b0. Q31's d=1 Euler/contact lemma gives directly
||A_one||=||sum_{n<=m}h(n)||<=8+4Omega.
Use exactly the same smooth partition and arithmetic indicators, with b0 in
place of b. The smooth base costs <=16sqrt(2B), while the far frequencies
cost C(1+Omega)^2(L+1)L. With B=ceil(m^(2epsilon)), these and A_one
are bounded by C_epsilon m^(2epsilon) eventually. Therefore, for the
complete signed near-frequency matrix
N0=sum_j integral_{|t|<X_j^-1/2} bhat0_j(t) ahat_j(-t)dt,

||A_prime-N0||<=C_epsilon m^(2epsilon).

No model-character term has been dropped from Q31's E1 application: E1 is
not used at all, and A_prime=A_one+sum b0 h is an exact independent split.
All prime powers and atom1 cancellation remain. The original T/K returns
above hold with 2epsilon instead of3epsilon, and no repeated short/arch fees.

### Test the classical central-arc completion, not a new prime theorem

The inherited Q09_AUTOCORRELATION_PREFLIGHT.md §Explicit centered PNT
already supplies the classical scalar-prefix mechanism and identifies its
failed full exponent. Test it against the new near arcs to detect duplication.
Let X=X_j, Y=min(4X,m), and E_X(v)=sum_{X<=n<=v} b0(n).
Classical PNT plus the floor error gives, uniformly X<=v<=Y,
|E_X(v)|<=C X exp(-c sqrt(log X))=:Ebound(X),
after enlarging constants; including n=X costs O(log X) and is absorbed.
Root primary check: https://dlmf.nist.gov/27.12#E5 states the error for pi.
Partial summation with log weights gives theta error of the same form after
reducing c; proper prime powers cost O(sqrt(x)log²x), also absorbed.
Subtracting floor(x) instead of x adds only O(1). No RH-size error is used.
For the actual finite Fourier polynomial, exact Stieltjes Abel yields

bhat0_j(t)=E_X(Y)e(-tY)+2pi i t integral_X^Y E_X(v)e(-tv)dv,

with the lower atom included in E_X. Thus
|bhat0_j(t)|<=C Ebound(X)(1+X|t|).
This is the q=1 central-arc approximation AFTER subtracting the discrete
constant model. It is not a favorable sign claim.

Put K=1+Omega and tau=X^-1/2. The unchanged matrix test satisfies
||ahat_j(t)||<=C min(sqrt(X),K²X^-3/2 |t|^-2).
For X>=B=m^(2epsilon), eventually K<=sqrt(X). Splitting its near integral
at K/X (or at tau if necessary) gives

||N0_j|| <= C Ebound(X) K²/sqrt(X) [1+log X]
         <= C K² sqrt(X)(1+log X)exp(-c sqrt(log X)).

Summing geometric sqrt(X) over all shells, and using log X>=log B,
returns C_epsilon K² sqrt(m)(1+L)exp(-c_epsilon sqrt(L)).
Its displayed upper-certificate power is1/2+2epsilon-o(1), worse than
Q31's half-power/log cap. The pre-existing direct Q09 Abel transfer has
only one K and is already stronger than this central-arc completion.

Decision: do not count this duplicate PNT input as a new arithmetic attempt
or optimize the logarithmic cutoff to claim a power gain. Keep the cheaper
exact N0 reduction, reject THIS scalar-prefix completion, and retain the
near signed phase as OPEN. These upper-certificate costs are not lower
bounds on N0, actual prime error or CCM.
