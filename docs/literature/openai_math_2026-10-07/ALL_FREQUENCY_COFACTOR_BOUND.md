# Cofactor mean square with all good frequency valuations

Extension of FIXED_PROFILE_COFACTOR_BOUND.md. Root derivation and independent squarefree_conductor_check bounded PASS. This pays a cofactor subproblem, not the full Type-II or physical probe.

For eta,S fixed, m fixed before summing H, Q,T>=1,Q>=T²,N>=T, and fixed annular F excluding the unit contribution, define B_H,m(N) exactly as before. Sum over all primary good H with Q<q_H<=2Q; no squarefree restriction and no (H,m)=1 restriction. Then

sum_H |B_H,m(N)|² <<epsilon (q_m QNT)^epsilon
 [Q^(3/2)/N *log(2T) + Q^(1/6)*log(2T)^2].                  (A)

The balanced original H-dependent profile is also permitted by the uniform log-H separation proved in the preceding note. If frequencies are elements rather than primary ideal representatives, split the six unit classes; each changes only fixed finite phases and constants.

## All-row short-polynomial estimate

Uniquely write H=s k², s squarefree and k arbitrary primary good. No (s,k)=1 condition belongs here. Zero-extended multiplicativity gives bar chi_e(H)=bar chi_e(s)bar chi_e(k)^2. For fixed k, the coefficient of the squarefree-row sieve is mu(e)eta(e)1_(e,m)=1 q_e^(-1/2-it)bar chi_e(k)^2, independent of s; its squared mass is O(log(2T)). Sum the source full-ball sieve with K=2Q/q_k²,D=T over q_k<=sqrt(2Q). Ideal counting and convergent norm zeta sums at2 and4/3 yield

sum_H |M_H(t)|² <<epsilon (QT)^epsilon log(2T)
 [Q sum_k q_k^-2 + T sqrt(Q) + (QT)^(2/3)sum_k q_k^-4/3]
 <<epsilon (QT)^epsilon Q log(2T),                           (B)

because Q>=T². Dyadic H restrictions are permitted by the source lemma. This is uniform in t and m. The source is paper.tex4707–4725, with ideal counting618–623.

## Moving conductor and canceled-prime masks

Write v_p(H)=6a_p+r_p,0<=r_p<6. Let R_H=product_(r_p>0)p and E_H=product_(v_p(H)>0,r_p=0)p. After reciprocity the moving character is product_(p|R_H)chi_p(.)^(-r_p), primitive modulo squarefree R_H; each r_p in1..5 is nontrivial locally. Canceled exponents leave the zero mask E_H. Fixed unit/ray factors remain in the same S-supported period ell.

For R_H>1 the moving character is nonprincipal. Open only the masks on good primes in rad(mH)/R_H: primes dividing R_H already have character value zero. The new divisors f need not be coprime to the short e; no such restriction is introduced. The dual series has finite local corrections from the fixed ell part and a primitive moving conductor of norm q_R<=2Q. The same fixed-period character expansion and unit projection used in FIXED_PROFILE_COFACTOR_BOUND.md gives holomorphic nonprincipal Hecke L-components on Re s>0, with critical-line convexity O(Q^(1/4+epsilon)(1+|t|)^C).

At the critical line, the primitive Gauss norm sqrt(q_R) cancels the q_R^(1/2) from the Mellin scale, leaving N^-1/2 q_f^-1/2. The f-set now depends on H, so do NOT use Minkowski over a falsely common divisor list. Instead use the pointwise bound sum_f q_f^-1/2<=2^omega(mH)<<(q_mQ)^epsilon and the uniform supremum of the dual-series bounds. The same M_H(t) is retained independently of f. Cauchy in the weighted t integral followed by (B) proves the first term of (A).

## Full sixth powers are retained and paid

R_H=1 precisely when the primary ideal H=k^6. There are O(Q^(1/6)) such dyadic rows. No claim of vanishing fixed principal character is made. Directly expanding beta=delta−mu_le*1, the annular harmonic count at L=N/q_e>=1 bounds |B_H,m(N)|<<log(2T), uniformly in the fixed profile and puncture. This gives the second term of (A), including any surviving principal zero mode. It also covers nonprincipal fixed twists on those rows without needing a separate sharper estimate.

At Q=Z^(13/16),N=Z^(1/2),T=Z^(1/4), the two powers are23/32 and13/96. Thus all good frequency valuations have the same ambient-normalized cofactor RMS saving Z^(-3/64+epsilon) as the squarefree subfamily. This is not an average normalized by the count of any further sparse row subset.

## General dyadic range and its boundary

The unsimplified argument also gives, for Q,T>=1 and N>=T,

sum_H |B_H,m(N)|² <<epsilon (q_mQNT)^epsilon
 {Q^(1/2)/N [Q+T sqrt(Q)+(QT)^(2/3)]log(2T)
  +Q^(1/6)log(2T)^2}.

One may take the minimum with Q log(2T)^2, after the same epsilon factor. In the square decomposition every contributing k has q_k<=sqrt(2Q), so K=2Q/q_k²>=1 as required by the source sieve. No additional small-K case is hidden. The only use of Q>=T² above was simplifying the bracket to O(Q).

Put Q=Z^q,N=Z^n,T=Z^(1/4). The four ambient-normalized RMS exponents are q/4-n/2, 1/8-n/2, q/12+1/12-n/2, and -5q/12. For q>0 this estimate yields a strict power gain exactly when n>max(q/2,1/4). At n=1/4 the second term gives exponent zero, so the sharp cofactor boundary is not paid by this argument. This is a limitation of the displayed estimate, not a lower bound or impossibility result. Independent mobius_source_audit checked the extension and these inequalities.

## Scope still unpaid (full consumer)

No H row has been discarded in (A), but the estimate is for B alone. Outer selected factors Delta_P(H), shared-prime L_g(H), v,d and tuple contractions can carry further size and signs; their full weighted joint action is not bounded here. Type I, the original physical n>1 and other complement sectors, detector residue, and high-side continuation remain open. Do not promote (A) to a full low exponent. Q4 is still pending in the same chat; compare its terminal calculation before selecting the next question.
