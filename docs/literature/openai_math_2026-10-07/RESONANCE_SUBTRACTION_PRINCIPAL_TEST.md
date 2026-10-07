# Removing the shared-prime resonance: principal-factor test

2026-10-07. Own algebra independently checked by causal_algebra_audit: exact sector sum and principal Euler-product preservation PASS. Physical-mask initial-contour identity and local selected-slot algebra separately checked: PASS within the stated scope. This constructs a bounded coefficient mask on the original absolutely convergent physical expression and computes its principal local factors. No improved low estimate or full moved-contour theorem is proved.

Source: pinned qrh78 paper.tex 3856–4050, local-scalar-values and local-P; definitions V,R,W,D and H=P(1-V)(1-W)/(1-D). Principal residue w=1,z=1/6, u=1. SHA/URL in sources.json.

## Sum the resonant sector exactly

For a good prime of norm Q, use the source symbols eta(p), a_p, omega_p and normalized Gauss factors gamma_j. In local-P restrict to

e0=1, l=2r (r>=0), k=1; t=e0+3l=1+6r, j=0.

The local scalar is nonzero for m>=r+1. Since 6m cannot equal t, only the upper Ramanujan branch survives:

C_p(t,1,6m)=omega_p^(-1)G_1*(Q^t-Q^(t-1)).

The phases simplify using gamma_3^2=omega_p (quadratic Gauss sum), gamma_1=G_1/sqrt(Q), and omega_p^2=1. Summing m>=r+1 and then r>=0 in absolute convergence gives

S_p = -eta(p)(Q-1) Q^(-x-w) V / [(1-V)(1-R)],
V=Q^(-6z), R=a_p^2 Q^(4-6x-6z).                         (1)

This matches exactly one displayed term in the paper's complete local identity. It is the whole k=1, t=1 mod6 sector at u=1, including the higher completed prime powers in this sector. It is not every shared-prime term.

At the principal residue w=1,z=1/6,

S_p=-eta(p)Q^(-x-1)/(1-R), R=a_p^2 Q^(3-6x).            (2)

The factor 1/Q gained here is important: the order-one local average by itself did NOT describe the full weighted Euler contribution.

## Candidate removal and retained principal signal

Set P_p^new=P_p-S_p only as an algebraic candidate. With the SAME scalar factorization convention,

H_p^new=H_p+Delta_p,
Delta_p=eta(p)Q^(-x-1)(1-Q^(-1))^2 / [(1-R)(1-D)],
D=eta(p)Q^(-x).                                         (3)

For Re x>=7/8, |R|<=Q^(-9/4) and |D|<=Q^(-7/8). Thus Delta_p is holomorphic and O(Q^(-15/8)), uniformly in imaginary parts and unit phases. The prime-ideal sum of these absolute bounds converges. The original H_p already has a uniformly absolutely summable defect from 1 in its stated second Euler region. After a sufficiently large FIXED exclusion cutoff, the product of H_p^new therefore converges normally and stays arbitrarily close to 1 on the published principal domain (in particular nonzero).

This is a positive partial test: deleting this specific local resonant sector need not erase the reciprocal-L principal signal. It does NOT prove any extension below 7/8, despite (3) alone making sense farther left; the original H_p bounds and high contour conditions must also hold.

## What remains before this can be used

1. Specify a single finite physical operation implementing precisely the deletion, not a post hoc change in the high Euler series.
2. Derive its complete high representation for every u, including ramified selected primes and all zero masks; retain a common fixed exclusion set.
3. Prove a better low estimate for that same physical operation. The deletion depends jointly on v_p(A) and v_p(s); it destroys the separation that allowed independent A-row and B-row norms. This is the exact new joint-correlation obligation.
4. Normalize the principal signal and prove new contour/remainder bounds. (3) supplies only a principal-residue nonvanishing check.

No new zero-free region, Q3 map, SP, Schur sign, or RH conclusion follows. This is a candidate lemma for interpreting the pending Pro Q1; do not send a second question while Q1 runs.

## Physical-mask addendum (initial-contour identity independently checked)

Define d(A,s) as the product over good primes p of

1 - 1_{v_p(s)=1 and v_p(A)=1 mod6}.

For each pair A,s this is a finite 0/1 product. Insert it into the A=c*n^3 coefficient of T_{m,s,eta} in the original general-probe, before summing m. This is an explicitly specified physical operation; it depends on both A and s, but not m. On the original absolute convergence lines, bounded insertion permits the same finite m-Poisson calculation and multiplicative coefficient collection. On u=1 its local factor is exactly P_p-S_p from (1). This does not give bounds after contour movement.

Since all deleted terms have positive A valuation, the marked local factor also changes by P_p^star,new=P_p^star-S_p. For the original selected-prime operation, the change in its holomorphic correction is

G_p^new-G_p=(bar(eta(p))*Q^x-Q^(-w))*Delta_p.

At w=1,z=1/6 this is

Q^(-1)(1-eta(p)Q^(-x-1))(1-Q^(-1))^2/[(1-R)(1-D)].

It is O(Q^(-1)) uniformly for Re x>=7/8. Since H_p^new-H_p=O(Q^(-15/8)) and H_p^new stays away from zero, the principal slot quotient remains

G_p^new/H_p^new = -1+O(Q^(-7/8)).

Thus the original fixed finite disjoint slot normalization retains a nonzero principal residue in the published domain, by the following finite-slot estimate. This claim uses only the principal residue and the explicit physical mask; the main outstanding estimate is low-side cancellation with the joint A,s mask, plus offprincipal/dynamic-region contour bounds. In particular it is NOT permissible to reuse the old separated A_m B_m norm estimates without checking that the new joint mask satisfies their coefficient hypotheses.

For precision, the O(Q^-1) selected correction is NOT multiplied over every good prime. Only the unselected H^new product uses an infinite prime product, and its added defect is summable O(Q^-15/8). For each of the fixed K selected annular slots, nonnegative weights give

sum_p W_i(Q/P_i) Q^-5/6 (G_p^new/H_p^new)
 = -S_i(Z)*(1+O(P_i^-7/8)).

This follows by bounding the weighted error by C*P_i^-7/8*S_i. The original fixed-ray prime theorem gives S_i>0 at sufficiently large Z. A fixed finite product therefore differs relatively from (-1)^K product_i S_i by o(1). There is no use of convergence of sum_p 1/Q. This preserves only the principal residue normalization; all modified offprincipal estimates remain open.

## All-valuation formula (independent bounded check PASS)

For a general sixth-power-free row let j=v_p(u) in {0,...,5}. The same deleted sector k=1,t=1 mod6 has rho^{k-t}=1. At j=1 there is additionally the negative Ramanujan boundary j+6m=t, m=r. Therefore its exact sum is

S_{p,j}=eta(p)Q^(-x-w)/(1-R)
  * [1_{j=1} -(Q-1)V^{1_{j<=1}}/(1-V)].

The change in unselected correction is -S_{p,j}(1-V)(1-W)/(1-D). For j=0, the extra V makes this normally summable in both source Euler regions, including when u is not the principal row. For j>=1 only primes dividing u occur. On the source dynamic contour x_r=a+16e,w_r=1-a-6e,z_r=17/50, the j>=2 correction is O(Q^-10e); with fixed e>0 and a sufficiently large fixed cutoff it is uniformly small. The j=1 correction is O(Q^(-1-10e)). These estimates give a q_u^epsilon majorant by the usual fixed-cutoff/product-over-divisors argument, not a uniform constant independent of u.

The source at lines 8965–8975 identifies its sole large ramified slot monomial as (e0,l,k,m)=(1,0,1,0), j>=2. This belongs to the deleted sector. The remaining monomial table is individually smaller than the Q^(z_r-1/2) slot scale. The checked monomial bounds therefore preserve that existing LOCAL dynamic error scale without spending the conductor deficit at the removed monomial. This does not improve the original global exponent by itself: the published proof already paid that term with the conductor deficit, and the main-slot/row and low estimates remain unchanged or unproved for the mask.

Independent all-j check: causal_algebra_audit confirmed the sector sum, nonvanishing local denominator after a fixed cutoff, and preservation of the existing dynamic local slot scale. For j=0, retain an extra Q^(6e) from |1-W| when w_r<0: the largest changed error exponent is at most a-2.04+12e<=-1.028, still smaller than -51/100. Do not use the sharper bound without w_r>=0. For j>=2 the mask removes the source's sole strict ramified term; all remaining monomials and the rescaling term stay within the source's existing local scale. The global row count, reflected L-factor allocation and low-side estimate have NOT been established for the mask.
