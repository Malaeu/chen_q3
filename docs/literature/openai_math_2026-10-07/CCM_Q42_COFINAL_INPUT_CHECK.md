# Q42 wait: independent cofinal-input check

2026-10-26. Root derivation, read-only q32_annulus_audit qualified PASS.
Prepared after Q42 dispatch; NOT sent as an extra message. Frozen S5 unchanged.
This checks an input only, not a CCM upper or an arithmetic exponent gain.

Let a(x)=sum_{n<=x}mu(n)/n. Absolute convergence for Re s>0 gives
 integral_1^infinity a(x)x^{-s-1}dx=1/[s zeta(s+1)].
Suppose a(x) is eventually nonnegative or eventually nonpositive. Remove
the finite initial integral (an entire function), and change overall sign
if needed. The remaining transform has a nonnegative locally integrable
integrand. Its real abscissa of convergence sigma_c is at most0, because
|a(x)|<=1+log x. Landau's positivity theorem makes a finite sigma_c a
singularity on the real axis.

Classical existence of a nontrivial zeta zero rho=beta+i gamma, reflected
if needed so beta>=1/2, forces sigma_c>=beta-1>=-1/2: otherwise the pole
at rho-1 would lie in the holomorphic half-plane of that tail transform.
Equality of the transform and the meromorphic expression continues from
Re s>0 by uniqueness; the removed entire term cannot cancel that pole.
Yet 1/[s zeta(s+1)] is analytic at every real s in[-1/2,0]. For -1/2<=s<0,
zeta(1+s) has no real zero; this follows directly from the positive
alternating eta series and zeta(t)=eta(t)/(1-2^{1-t}),0<t<1.
At s=0 the apparent singularity is removable since zeta(1+s)~1/s.
This contradicts Landau. Hence both signs recur arbitrarily far out.

If zero values recur, they already give the desired subsequence. Otherwise
there are arbitrarily late adjacent opposite-sign values at n-1,n.
Their absolute values sum to |mu(n)|/n=1/n. One endpoint U∈{n-1,n}
has |a(U)|<=1/(2n), hence U|a(U)|<=1/2. Zero plateaux cause no exception.

Declared classical inputs: existence of a nontrivial zero; meromorphic
continuation/functional equation of zeta; Landau positivity theorem.
No RH or zero-free strip premise. The audit checks their application,
not a fresh foundational proof of those classical results. This gives an
independent justification of the cofinal input cited through Gallardo/Seco,
without claiming that their stronger conditional inequality(14) is proved.
All lower moments and the full finite signed return in Q42 remain open.
