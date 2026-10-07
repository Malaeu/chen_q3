# Fixed-profile cofactor bound from the signed Mellin representation

This is a bounded estimate for B_H,m, not for the full Q3 consumer. It uses the source sextic sieve already audited in SEXTIC_SIEVE_BOUNDED_AUDIT.md and standard nonprincipal finite-order Hecke L-function continuation, functional equation and convexity. It does not assume GRH. Q4 is pending; no second message is sent.

## Statement

Fix eta,S and F in C_c^infinity((0,infinity)), with support away from zero. Let N be sufficiently large that F(1/N)=0, and let Q,T>=1 with Q>=T^2. Fix m before summing H. Sum over squarefree primary good H>1 with Q<q_H<=2Q and (H,m)=1. With B_H,m(N) exactly as in FREE_COFACTOR_COMPLETION_ATTEMPT.md,

sum_H |B_H,m(N)|^2 <<_(F,eta,S,epsilon) (q_m QNT)^epsilon Q^(3/2) N^-1 log(2T).  (A)

Uniformity is only for the displayed parameters with fixed F, or a family with the required common seminorm bounds/separation proved. The short-polynomial bound is SHORT_MOBIUS_MEAN_SQUARE.md.

## Contour and conductor

Use SIGNED_DUAL_MELLIN_ATTEMPT.md(2). For f|rad(m), A_f(j) is a function modulo fixed ell, with finitely many possibilities as f,H vary modulo ell. Partition j by its ideal gcd with ell. Within each stratum expand the fixed finite-group function into multiplicative characters. The sum over all six associates projects onto products whose total unit character is trivial. The fixed component need not itself be a Hecke character: only its product with the moving character must descend to ideals. The resulting Hecke characters have primitive moving conductor H, coprime to their fixed conductor part. They are nonprincipal because H>1. Fixed local factors at ell are bounded and holomorphic on Re s>=1/2; finite gcd-stratum norm factors also cost only fixed constants.

Consequently D_f(s) is holomorphic on Re s>0 with polynomial vertical growth, and on the critical line satisfies
|D_f(1/2+it)| <<_(eta,S,epsilon) Q^(1/4+epsilon)(1+|t|)^C.
This is the ordinary conductor convexity bound, obtained by applying the nonprincipal Hecke functional equation between absolute-convergence lines and Phragmen–Lindelof; the field and fixed conductor factors are fixed. The standard analytic-conductor convention is norm conductor times (1+|t|)^2 here. Reference for the general convexity principle: Gergely Harcos, Subconvex Bounds for Automorphic L-functions and Applications, introduction, https://www.renyi.hu/~gharcos/ertekezes.pdf . No stronger subconvex estimate is used. Root fetched and read PDF page10 (printed page2), lines on the convexity principle; fetched file SHA25635f942d1fc5fee1e2d53bcfdb169c1863f95c432f030992a8f0ab06ded6c797d,1165106 bytes. The standard bound quoted there is C(pi,s)^(1/4+epsilon).

What(s), the Mellin transform of the radial Fourier transform of W=F/t, is holomorphic for Re s>0 and rapidly decreasing vertically uniformly on the closed strip [1/2,c]. M_T is finite. Thus the line in (2) can be moved from c>1 to1/2 with no crossed pole and vanishing horizontal integrals. This is specific to nonprincipal H>1; it is not an assertion about the excluded principal rows.

## Mean-square calculation

On Re s=1/2, the absolute factor outside D_f M_T simplifies exactly:
|tau_H|/(q_ell q_H q_f) * (N/(q_f q_ell q_H))^(-1/2)
=constant_(ell) N^(-1/2) q_f^(-1/2).

Minkowski in the H l2 norm and the t integral, the uniform convexity estimate, and the checked short-polynomial sieve give
||B||_(l2 H) << N^(-1/2) sum_f|rad(m)q_f^(-1/2)
 * integral |What(1/2+it)|(1+|t|)^C Q^(1/4+epsilon)
            [(QT)^epsilon Q log(2T)]^(1/2) dt.
Since sum_f q_f^(-1/2)<=2^omega(m)<<epsilon q_m^epsilon, squaring proves (A), after renaming epsilon. Finite residue-class row restrictions in the D_f decomposition are allowed by the same sieve and cost only a fixed number of terms.

At Q=Z^(13/16), N=Z^(1/2), T=Z^(1/4), (A) has exponent23/32+epsilon, hence the l2 norm divided by sqrt(Q) is Z^(-3/64+epsilon), absorbing logarithms. This is a genuine fixed-profile mean-square improvement over bounding every B by O(log Z), but not a new physical low exponent.

## Exact remaining gap

The original profile depends jointly on H,d and nu. It must be separated with uniform Mellin/seminorm control before invoking (A). The outside v,d sums, selected coefficients, shared primes, nonsquarefree H, principal moving characters, Type I, and the unchanged physical complement are not estimated here. Taking their absolute values can erase this gain; no full bound follows merely by writing (A).

Independent squarefree_conductor_check checked the stated proof, critical-line shift, conductor and exponents. Root records the corrected unit-character formulation above. No Lean formalization or global manuscript certification is claimed.

## Original balanced-box profile extension (independently checked)

For fixed d,v,tuple and dyadic box take F_h(t)=rho(t)V(c t)W0tilde(b h/t), h=q_H/Q in[1,2], c=q_aPg d N/(ZqP), b=XQ/(q_aPg d N), with c,b in fixed compact positive intervals. Insert a smooth h-cutoff equal1 on[1,2]. Fourier inversion in log h gives F_h(t)=integral h^(i tau)F_tau(t) d tau. Every required t-seminorm of F_tau is O_A((1+|tau|)^(-A)) uniformly in c,b, by integration by parts in log h. Linearity and Minkowski extend (A) to this actual profile without a Z-power loss. Independent squarefree_conductor_check PASS; the source transform is smooth by paper3762–3777.

For orientation only, in the allowed fibre aP=P,bP=1,g=1, H squarefree and coprime to Pv, one can triangle-sum the remaining d,v and tuples. Cauchy in H costs sqrt(Q), so the H-sum is O(Z^epsilon Q^(5/4)/sqrt(N)). The d harmonic mass is O(1) on its dyad; v has B=Z^(23/48) terms; tuple countZ^(1/6) cancels1/qP. Multiplying sqrtX/Y=Z^(-29/96) gives physical exponent181/192. This is an insufficient upper bound for that restricted fibre, not a lower bound and not a bound for omitted sectors. In particular the partial cofactor gain does not close the desired3/16-delta bound.
