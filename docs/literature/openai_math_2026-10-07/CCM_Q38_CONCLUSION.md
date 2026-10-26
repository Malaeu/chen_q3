# Q38: coupled parity cancellation and the full signed return

2026-10-26. Root mathematical check and executable replay complete;
independent read-only q32_annulus_audit qualified PAPER PASS on §§3–7,
no material findings. Inherited Q34 source return and S10 consumer remain
accepted inputs, not newly recertified. No new CCM exponent admitted.
Original: PROSHKA_CCM_SQUAREFREE_SIGNED_RETURN_Q38_VERDICT_2026-10-26.md,
87290 bytes/1393 LF, SHA256
39dc21f87cafe26e372bdef4f14e29a49ef78b7e6ee35748b7cdd48e68b978ef.
Six hash-verified assets in q38_replay. Both generated JSON files byte-identical:
45 exact algebra groups,10 planted errors,12 source bodies. Finite algebra
panels are not production sparse-band spectral cells or interval certificates.

## Exact source and auxiliary cancellation

On the original physical L2(0,L), before compression, put
E_plus=sum mu(n)^2 a_Z(n) n^(-sigma) V_log(n),
E_minus=sum mu(n) a_Z(n) n^(-sigma) V_log(n).
The actual nonmultiplicative a_Z retains every g_Z(ell)g_Z(k) channel.
For d=gcd(ell,k), the local product is
mu(k) X_(ell*k) product_(p not dividing ell*k)(1-X_(p*p))
 times product_(p dividing k/d)(1+X_p)
 times product_(p dividing ell/d)(1-X_p).
Thus K=E_plus E_minus has no coefficient with an odd exponent of a prime>Z.
With Q=-partial_sigma K, G=sum |g(ell)|tau(ell)/sqrt(ell),
 ||Q||<=d_budget=L(1+L/2)G^2=O_epsilon(m^(epsilon/2)L^14).
This is a genuine auxiliary upper, not an upper on the original CCM source.

## Complete restoration

D_plus/minus=-partial_sigma E_plus/minus; retain both mixed terms
N=D_plus(E_minus-I)+(E_plus-I)D_minus.
Writing D_even for squarefree composites with even prime count and D_odd
for odd count>=3 gives Q=2D_even+N. Consequently the full causal target is
 C_sf_forward=Q/2+R_forward,
 R_forward=D_odd-D_composite_small-N/2.
After adding the adjoint and compressing only at the ends,
 C_sf=Q_compressed+R_compressed, ||Q_compressed||<=d_budget.
The restored coefficient is r(n)=(gamma(n)-k(n)/2)log n.
On every rough squarefree composite it is exactly log n; on rough primes
it is zero. At p^2, k=-1 and r=log p, cancelling Q/2 as required for C_sf.
Original prime powers remain in the inherited U_sf return, not deleted.
At n=m the physical shift vanishes; its formal coefficient is retained.
No intermediate operator is assumed to preserve P or the three contacts.

## Scope of the failed completion

The displayed coefficient-modulus allowance is
 r_budget=2 sum_(2<=n<m)|r(n)|/sqrt(n),
 s_trial=u_sf+d_budget+r_budget.
Elementary binomial/Chebyshev counting supplies >=m/(256L^2) distinct
rough pq in (m^(2/3),m); each costs >=2L/(3sqrt(m)) before the two-time
factor. Hence r_budget>=sqrt(m)/(192L) eventually.
The complete squarefree count also gives s_trial=O_epsilon(sqrt(m)).
Therefore this allowance has exponent1/2, even on cofinal subsequences.
This is NOT a lower bound for the signed operator or its spectrum.

The full original return is
 T_>R<=(s_trial+b_div)P,
 P K_m P>=-(s_trial+50L+8)P.
The u_sf fee already includes non-squarefree and proper-power returns;
no extra short fee appears in the direct K inequality. Small expenses
u_sf+d_budget+b_div+50L+8 fit C_epsilon m^(2epsilon) eventually.
Retain the cheaper inherited cap s_keep<=6sqrt(m)+6m^(1/4).
No eta(epsilon)->0, new pair margin, RH claim, Lean or Arb run.

## Rollback

Return before multiplication to the complete first derivative with literal
prime deletion, or equivalently centered C0=-C_sf+U_sf+Hd.
Further shrinking Q cannot pay the restored rough composite coefficients.
An arbitrary lower on R is equivalent up to the small d_budget to the
original lower on C_sf, so naming it is not a new arithmetic supplier.
The unweighted squarefree inverse is Liouville, not Mobius; its logarithmic
derivative differs from the true Mangoldt source on even prime powers.
That exact rewrite alone does not supply the sign either.

Next: rollback before the parity product to the retained full first source
form; test a genuinely source-preserving signed comparison. No Q39 sent. Full goal remains OPEN.
