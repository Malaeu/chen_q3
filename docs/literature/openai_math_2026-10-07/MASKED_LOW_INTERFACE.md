# Masked low-side interface — 2026-10-07

The local high-side mask checks do not license reusing the original low moment. This note isolates the needed uniform statement rather than treating a coefficient cutoff as a norm contraction.

## Exact divisor expansion

Let rad_1(s) be the squarefree product of good primes occurring in s to exponent exactly one. For A=c*n^3, c squarefree,

d(A,s) = sum_{d | rad_1(s)} mu(d) 1_{d|c} product_{p|d} 1_{v_p(n) even}.       (1)

This follows by finite expansion of the product defining the mask: v_p(A)=1 mod6 iff v_p(c)=1 and v_p(n) is even. It is an identity at every coefficient, including shared primes, not an asymptotic sieve estimate. The d in (1) is a divisor variable and is distinct from the rescaled slot-length d used in the source's low proof.

For each s, define the completed row B_{m,s}^{mask} by inserting (1) into its c,n sum. The actual low expression before estimates has the shape

Q^(-1/2)/(2pi) * integral W0hat(iv)
  sum_{m!=0} Omega(q_m/Q) xi(m)(q_m/Q)^(-iv)
  sum_s a_{m,s,v}(Y) B_{m,s}^{mask}(Z) dv.                (2)

Here a_{m,s,v} is the individual s summand in the source's A_{m,sigma,v}; the finite ray-class correction and coefficients remain inside B. Formula (2) is obtained by the same Mellin separation but now B depends on the actual s, not merely its fixed ray class. For compensated slots, repeat this for each original signed/rescaled term with its exact coefficient and support. Taking separate norms before collecting these terms is not assumed to save anything.

## The missing source hypothesis

The unmarked completed-row moment, paper.tex 3138–3170, permits a FIXED finite family of finite-ray characters, with conductor support inside fixed S. Its constants and lower thresholds depend on those fixed data. The compensated completed-row norm at 8111ff has prescribed marked slots and a fixed rescaled subset. Neither displayed statement asserts arbitrary moving coefficient masks depending jointly on s and A.

Putting every prime of s or d into the excluded set does not prove a uniform estimate: those primes vary with Z, and the source explicitly allows dependence of constants on the excluded data. Nor is the parity restriction on v_p(n) simply a fixed finite-ray character. The additive Gram proposition at 8340ff estimates A for a prescribed fixed ray coefficient; it says no arbitrary row-dependent arithmetic coefficient is asserted.

Required new input: a bound for the actual double-indexed pairing in (2), or a completed-row estimate uniform under the exact moving divisor/parity restrictions in (1), with sufficiently controlled d costs to sum (1). Only then may the new exponent be compared with C(s). This is still unproved.

## Why bounded masks cannot justify the estimate by themselves

The 0/1 coefficient mask preserves absolute convergence on the initial contour. It need not contract a signed transform's operator norm. Exact abstract diagnostic: the matrix [[1,1],[1,-1]] has norm sqrt(2); deleting its bottom-right entry produces [[1,1],[1,0]], with norm (1+sqrt(5))/2 > sqrt(2). The negative control does not model the actual arithmetic coefficients; it rules out only the generic inference from |mask|<=1 to an oscillatory operator-norm improvement.

Even a proof that the old low bound survives would only recover its old exponent. A route toward RH needs an actual improved estimate and compatible high-side contours, not just successful construction of a masked probe. No global status changes.

## Independent source-fit audit

2026-10-07: mobius_source_audit independently verified (1) and the missing uniformity. Root checked the source statements at 3138–3170 and 8340–8361. The exact alternative to (2) is a sum over moving squarefree d of mu(d) A_m^(d) B_m^(d): A^(d) restricts the source s sum to v_p(s)=1 for every p|d; B^(d) restricts c to d|c and n to even v_p(n) for every p|d. All fixed ray factors remain. Here d||s means these valuation-one conditions, not merely that d is a unitary divisor.

For example, the restricted completed Dirichlet row is

T_d(t+1/2,psi) = sum_{c squarefree,n} gamma_2(c) conjugate(alpha(c*n^3)) psi(c*n^3) 1_{d|c} product_{p|d}1_{v_p(n) even} q_c^(-1/2-t) q_n^(-1-3t).

The joint d sum is finite at fixed Z but its range grows with the annular s scale. The source Gram proof's own Mobius variable arises from a shared divisor of two Gram columns (8393–8448); it does not supply uniformity for this different coupling. The audit establishes no nontrivial aggregate low bound. The next mathematical input must control this coupled divisor sum, including its d costs, or bypass separate norms by a direct joint estimate.
