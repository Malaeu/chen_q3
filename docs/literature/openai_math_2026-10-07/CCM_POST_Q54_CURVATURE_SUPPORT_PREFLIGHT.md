# Post-Q54: exact prime support of the endpoint curvature

2026-10-27. Root derivation; bounded independent investigation pending.
Source: Q54 original normalized V_tau=U Q_tau U^T, original linked image
x_n(t)=f(t+log n)/sqrt n, f=I c, c=Pc. No change of m,L,M or contacts.
This is a preflight, not a new accepted consumer estimate.

## Exact local cancellation before absolute values

Let t_p=p^(-tau/2), a=v_p(n), b=v_p(k). Finite divisor inversion factors
V_tau(n,k) as the product over primes dividing nk of the following factors:

- a=b=0: 1;
- a=0<b (or symmetric): -(1-t_p)t_p^(b-1);
- a=b>0: 2(1-t_p);
- a,b>0 unequal: -(1-t_p)^2 t_p^(|a-b|-1).

This follows by taking the two finite backward differences of t_p^|a-b|.
No infinite Euler product or extension of either cutoff is involved.
At tau=0 every nontrivial prime contributes at least one zero. Thus V''_0
vanishes whenever nk contains more than two distinct primes. For one prime,
V''_0(p^a,1)=(2a-1)(log p)^2/4 and
V''_0(p^a,p^b)=-(log p)^2/2 for all a,b>=1.
For exactly two primes the entry is twice the product of their first
slopes: -log(p)/2 for one exponent zero, log(p) for equal positive
exponents, and zero for unequal positive exponents.

These formulas retain all prime powers, complex quadratic cross terms and
both n,k<=m boundaries. They apply to the original linked image without
projector replacement. Root exact formal-log comparison checked 760 entries
at m=2,6,12,24 against direct U[d(n,k)^2]U^T; no floating logarithms.
The check does not prove any infinite-scale bound or evaluate full CCM.

For n=p^a and k=q^b with p!=q the surviving entry is
+(log p)(log q)/2. It contributes a genuine joint prime-power
correlation of the original translated f. Negative same-prime entries and
row-1 semiprime terms are retained, so this observation is not a lower bound
for the complete curvature. Sparsity by prime support is not smallness.
The executable check is q54_replay/check_endpoint_curvature_support.py.

## Why endpoint sparsity alone cannot pay the Taylor return

The Q54 identity needs curvature throughout 0<=s<=tau, not just s=0.
At positive s entries with more than two primes generally return. They must
not be discarded. With d_de<=L and sum_d ||r_d||<=2sqrt(m)(1+L)||f||,

 |Phi'''_s| <= 4m L^3(1+L)^2 ||f||^2 = C3 ||f||^2.

Consequently the exact Taylor remainder satisfies

 R_tau <= tau^2 Phi''_0/2 + C3 tau^3 ||f||^2/6,
 A[f] <= (2h_m+2/tau+C3 tau^2/3)||f||^2 + tau Phi''_0.

This drops only the already proved nonnegative Phi_tau with its negative
coefficient; it does not drop mixed curvature. The displayed allowance,
even if Phi''_0 could be bounded above by zero for free, optimizes at
 tau=(3/C3)^(1/3), with positive fee 3^(2/3) C3^(1/3).
It therefore retains exponent1/3 (and logs) under this completion. This is
a price of this particular third-derivative bound, not a source lower bound.
No favorable endpoint sign has been proved on original P, so even that
hypothetical exponent improvement is NOT a usable CCM result.

Decision: exact endpoint support identifies real arithmetic cancellation,
but cannot replace a joint bound over the whole deformation interval.
Next discriminator: control the linked prime-pair curvature and its higher
prime-support return together, rather than declare higher support absent.
Goal OPEN; no new full exponent; independent review pending; no Q55 sent.
