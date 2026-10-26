# Post-Q39: residual-free prime partition and its absolute price

2026-10-26. Own second bounded attempt after Q39; independent read-only qualified PAPER check PASS.
The first was MANY_PRIME_VARIANCE. This attempt removes that incidence residual
exactly and tests the resulting full source budget. No Q40 sent.
Original N=m,L=log m,M=R=floor(m^epsilon), fixed epsilon>0 as in Q39.
D_n=1_(R<n<=m)B_n is the SAME full Hermitian matrix; beta(n)=c*D_n c,
unit c=Pc. Full inner k sums, both times, all complex cross terms retained.

## Exact construction

For every squarefree n>1 select theta_p(n)>=0 on primes p|n,
sum_(p|n)theta_p(n)=1. The choice may depend on m or the test vector.
Example: theta_p(n)=log(p)/log(n) on squarefree n. Define the weights as
zero or arbitrary on non-squarefree n, which are killed by mu(n).

For c-independent weights this is an operator identity. For adaptive weights,
fix c and its weights first; the contracted identity and certificate below
apply to that c, with no common adaptive linear operator asserted.

 T = -sum_p sum_(k:p not dividing k, R<pk<=m)
               mu(k) theta_p(pk) D_(pk).

Reason: mu(pk)=-mu(k) for p not dividing k, including zero when k is not
squarefree; summing the weights on every surviving squarefree n gives one.
No prime-power term of D_n has been deleted: squarefree support refers to
the OUTER divisor n, not the original product n*j inside B_n.
There is no incidence residual in this formula and no changed projector.
The identity is bookkeeping, not the claimed gain.

## Complete price of separate full-block moduli

For the above formula the literal termwise absolute certificate is exactly

 C_theta(m,c)=sum_(p,k:p not dividing k) |mu(k)|theta_p(pk)|beta(pk)|
            =sum_(R<n<=m)mu(n)^2 |beta(n)|.

This remains true for every adaptive nonnegative partition. Hence optimizing
such weights cannot improve THIS certificate at all. Keeping sums within
channels before taking absolute values is a different certificate, not ruled out.
Likewise allowing negative weights is outside this nonnegative statement.

The Q39 bound ||B_n||<=b_m/sqrt(n), b_m=40+16Omega, gives
 C_theta<=2 b_m sqrt(m), T<=2 b_m sqrt(m)P,
 P K_m P>=-[2b_m sqrt(m)+2b_m sqrt(R)+50L+8]P.
Short and arch terms are paid once; no extra near-source or prime-power fee.
This is worse than the inherited full A cap 6sqrt(m)+6m^(1/4), which stays.

## Actual-source lower price on the original P

Use the already independently checked Q39 §§3–6 original-P family c_m.
Uniformly for n>R, sqrt(n) beta_m(n)=phi(n/m)+error, |error|<=zeta_m=o(1).
The full-k phi is continuous and nonzero at x0=(2exp(1/10))^(-1)<1/2,
where phi(x0)=log(2)/sqrt(2). Choose constants 0<a<b<1/2 and v>0
with x0 in(a,b) and |phi(x)|>=v throughout [a,b].
For all sufficiently large m, R<a*m and zeta_m<=v/2, hence on this interval
 |beta_m(n)|>=v/(2sqrt(n))>=v/(2sqrt(m)).

Elementary squarefree counting gives
 sum_(n<=x)mu(n)^2=x/zeta(2)+O(sqrt(x)),
by mu(n)^2=sum_(d²|n)mu(d), the floor error and the convergent d^-2 tail.
Thus the number of squarefree n in [am,bm] is >=(b-a)m/[2zeta(2)]
for all sufficiently large m. Consequently, for EVERY partition above,

 C_theta(m,c_m)>=[v(b-a)/(4zeta(2))]sqrt(m).

The entire inner k sum is present in phi; all projection/contact errors
are the Q39 uniform zeta, not an assumption of post-projection compact support.
This is a lower bound on the literal sum of block moduli, NOT on T, J,
any signed residual, or any CCM eigenvalue. It permits actual cancellation.

## Decision

Residual-free incidence does not fix separate-payment loss. The lower price
is uniform over all nonnegative divisor partitions, including moving weights.
Stop optimizing that certificate. Roll back before block moduli; a next
supplier must retain cancellation between the signed full blocks, rather
than merely select a partition of unity. No new arithmetic exponent or RH claim.

Independent q39_joint_supplier checked the exact leading minus, squarefree
exceptions, adaptive scalar scope, inherited original-P return and density
lower. Root finite Fraction checks:1022 coefficient/absolute-price cases
(n=2..512, equal and p-proportional rational partitions), all PASS. These
are algebra diagnostics, not new CCM numerical evaluations.
