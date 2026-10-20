# Q04 own attempt 2: scalar balancing cannot repair the shift-square family

2026-10-20. Independent bounded PAPER review ccm_q01_return_review: PASS (exact cross coefficient, uniform AM-GM, constants, original constraints and scope).
Original N=m,L=log m,M=floor(m^epsilon), original ran(P), all prime powers.
This extends the first shift-square test to arbitrary positive balancing
parameters, allowed to depend on m and n. It does not exclude other J.

For a_n=Lambda(n)/sqrt(n), V_n=V_(log n), choose ANY r_n>0 and define

 (J_r c)_n=sqrt(a_n)(sqrt(r_n)Ic-r_n^(-1/2)V_n Ic).
 G_r=sum_n a_n I*(r_n I_H+r_n^(-1)V_n*V_n)I.
 E_r=G_r-D, D=P(A_arch-c_A I)P.

Then J_r*J_r=G_r-P A_prime P and P K_m P=J_r*J_r-E_r exactly.
All cross coefficients remain one; no source change or cyclic shift occurs.

Use the SAME unit vector from CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md:
 f(t)=-3/4+(1+4w^2)cos(wt)-(1/4+4w^2)cos(2wt), w=2pi/L,
 F=f/||f||_2, with exact original three constraints and modes0,+/-1,+/-2.
For L>=2pi and 0<=t<=1/2, the previously proved inequalities give

 f(t)>=(10/3)w^4 t^2,        ||f||_2^2<=23L.

Set alpha=exp(-1/2), beta=exp(-1/4). For alpha*m<n<=beta*m,
h=log(m/n) lies in [1/4,1/2), and therefore

 b_n=||V_n F||_2^2=int_0^h |F(t)|^2 dt
     >= (20/207)(2pi)^8 h^5/L^9 >= kappa_v/L^9,
 kappa_v=20(2pi)^8/(207*4^5)>0.

For every r_n>0, the elementary square
(sqrt(r_n)-sqrt(b_n/r_n))^2>=0 gives

 r_n+b_n/r_n>=2 sqrt(b_n)>=2 sqrt(kappa_v)/L^(9/2).

This is uniform over ALL balancing choices; they may even be optimized
using this vector, although the actual map must work for every vector.
All other terms of G_r are positive. The same unconditional PNT calculation
as in the cited block note gives sum_(alpha*m<p<=beta*m) log p/sqrt(p)
>= (beta-alpha)sqrt(m)/4 eventually. Consequently

 <c,E_r c> >= c0 sqrt(m)/L^(9/2) - 50L - 8,
 c0=(beta-alpha)sqrt(kappa_v)/2>0.

Thus, uniformly in the arbitrary cellwise family r_n, the largest eigenvalue
of E_r on the ORIGINAL sparse band is at least this quantity. No upper
E_r<=C_epsilon m^eta P with fixed eta<1/2 holds on an unbounded subsequence.
Original space is nonzero for M>=2; for every fixed epsilon>0 this is eventual.

This rules out optimizing scalar weights in this factorization and then
DISCARDING J_r*J_r to obtain subpower error. It is NOT a lower bound on
negative eigenvalues of K_m, not a bound for T_gtR, and not a prohibition
against joint cancellation between J_r*J_r and E_r or non-scalar constructions.
The complete source is retained; the restriction to primes is used only in
a legitimate lower bound of the positive G_r on a specified source vector.

Decision: scalar balance parameters cannot fix the large return. Any useful
next construction needs a genuinely joint source comparison, not merely
coefficient tuning inside this independent positive-square family.
No new full exponent. No numerical, Lean or Arb run used.
