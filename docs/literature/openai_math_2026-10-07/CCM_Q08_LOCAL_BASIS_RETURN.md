# Post-Q07 attempt 2: full return from four-mode blocks

2026-10-21. Source and constraints as in CCM_Q08_ANNIHILATOR_PREFLIGHT.md.
This is a conditional supplier budget, not an arithmetic estimate.
Independent read-only q08_difference_budget bounded PAPER audit PASS. Keep M>=2 and n=2M-2.

## Explicit basis of the entire constrained band

Let G(z)=sum_(k=0)^(n-1)g_k z^k and
h(t)=L^(-1/2)z^(-M)(z-1)^3G(z), z=exp(2pi*i*t/L).
Its coefficient vector d has n+3=2M+1 entries, index k meaning mode j=k-M.
The last three entries obey sum k^r*d_k=0 for r=0,1,2, not free edge data. Let D3 be convolution by
(-1,3,-3,1), with zero padding, so d=D3g. With

    a_j=1/4+(2pi*j/L)^2, A=diag(a_j), E=-A D3,

the original f=(D²-1/4)h has c=Eg. This E maps bijectively onto the
original three-constraint subspace. It is not an orthonormal basis.
Each column uses FOUR consecutive original modes, but a general vector
contains ALL column cross terms. No original mode or prime atom is omitted.

The inverse of (z-1)^3 gives, for 0<=k<n,

    g_k=-sum_(i=0)^k binom(k-i+2,2)d_i.

Zero-padded discrete Young and a_j>=1/4 imply

    ||g||_2<=C_n ||d||_2<=4 C_n ||c||_2,
    C_n=sum_(r=0)^(n-1)binom(r+2,2)=binom(n+2,3).            (1)

Thus E*E >= (16 C_n²)^(-1) I. It is essential to pay this metric; using
||g||=||c|| would create an artificial saving.

## A concrete sufficient local supplier, still OPEN

Use the original full Aprime=sum_(2<=q<=m) Lambda(q)/sqrt(q)Q(log q),
and K=E*Aprime E. This retains all prime powers, all cross modes and both
ends. If B_m>=0 and

    K_kk + sum_(ell!=k)|K_kell| <= B_m for every k,            (2 OPEN)

Hermitian row comparison gives K<=B_m I, hence

    c*Aprime c <=16 C_n² B_m ||c||².                        (3)

A stronger sufficient input is K_kk<=b_m and |K_kell|<=b_m for k!=ell,
with b_m>=0. Then B_m=n b_m and the full return costs O(M^7 b_m).
No lower bound for K_kk is needed. Negative diagonal credit can remain in(2).
Diagonal estimates alone do NOT suffice: mixed entries must be paid jointly
or by the absolute row sums explicitly displayed in(2).

For every fixed small epsilon, a proved b_m<=C_epsilon m^kappa(epsilon)
times fixed logarithms, kappa(epsilon)->0, would give the required source
power 7epsilon+kappa(epsilon) (up to any separately chosen positive allowance
for logs). T_{>R} also pays the existing m^(3epsilon/2) short return;
direct K_m pays arch50L+8. Epsilon is fixed before m. None of (2) or the
hypothetical b_m estimate is proved here. This is sufficient, not necessary;
using absolute mixed entries can lose a true joint one-sided cancellation.

## What existing bounds actually supply

The source bound ||Aprime||<=12sqrt(m) follows from the already accepted
Chebyshev estimate and ||Q||<=2. Each E column has squared norm<=20 a_max²,
a_max=1/4+(2pi*M/L)^2. Therefore

    |K_kell|<=240 a_max² sqrt(m).

With(3) this only gives O(M^7 a_max² sqrt(m)), at most power
1/2+11epsilon up to logs. It is worse than using the original direct
12sqrt(m) bound. The local basis itself supplies NO arithmetic saving.
The accepted actual raw-shell lower bound in
CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md still forbids obtaining (2) by
independently paying each raw prime shell at subpower. Centering and all
cross-shell signed effects must remain in the local supplier.

Decision: reconstruction cost is a power of M and therefore compatible with
the target eta(epsilon)->0 IF a suitable full-source local bound is found.
The obstruction is not exponential conditioning; it is the still-unproved
signed arithmetic in the entries/rows. Do not label a four-mode diagonal
experiment a proof for all vectors. No full gain, SP, RH or Lean claim.
