# Free cofactor completion before the next inequality

Own attempt following audited Q3, baseline 0f066a12. Status: bounded independent mobius_source_audit PASS, including support, conductor, harmonic normalization and exponents; no full consumer estimate.

## Exact object

Freeze d,g,v,P,H in Q3(9), retain their coefficients outside, and localize nu smoothly at N. Put m=gPv and chi_H^*(nu)=eta(nu) conjugate(chi_nu(H)), with zero values at common primes. The original d-dependent radial profile is included in smooth annular F; constants below depend on its controlled seminorms. The tested inner sum is

B_H,m(N)=sum_(nu,m)=1 beta_T(nu) chi_H^*(nu)/q_nu F(q_nu/N).

Assume the annulus excludes norm1 (as on the balanced large-Z fibre). From beta=delta_1-mu_le*1, exactly

B_H,m(N)=-sum_qe<=T,(e,m)=1 mu(e)chi_H^*(e)/q_e
               sum_(k,m)=1 chi_H^*(k)/q_k F(q_k/(N/q_e)).       (A)

There is NO (k,e)=1 condition and no squarefree restriction on k. The entire product nu=e*k enters every original profile. The same substitution can be made inside both factors of the Q3 energy before inequalities; it retains all e,e',H,H',v,v' cross terms. This note tests only the individual completion after that exact substitution, not the full energy.

## Actual squarefree-frequency fibre

For squarefree good H>1 coprime m and fixed finite-order eta, reciprocity resolves chi_H^* into a primitive moving character of conductor H times a fixed ray character. Fixed-modulus splitting costs a constant depending on eta and S. Write Q=q_H and L=N/q_e. With W(t)=F(t)/t, the inner harmonic sum is L^-1 sum chi_H^*(k) W(q_k/L)1_(k,m)=1. Insert sum_f|(k,m) mu(f); the nontrivial primitive moving factor makes zero dual frequency vanish.

The Q3 CRT/Poisson normalization gives dual norm length K_f asymptotic Q*q_f/L and harmonic prefactor of magnitude O(1/(q_f*sqrt(Q))). Before any absolute summation, all Gauss, fixed-ray and dual character phases remain. Annular counting and Schwartz decay then give the individual bound

|inner| <<_eta,S,F,epsilon (mQ)^epsilon min(1,sqrt(Q)/L).         (B)

This is an upper-bound method, not a lower bound for the actual signed sum. The divisors f account for the mask on m; no coprimality with e is inserted. Repeated-prime H and the principal moving conductor require the general Q3 conductor/mask formula and its zero mode, not (B).

## Budget exposed by the actual cofactor cutoff

At Q=Z^(13/16), N=Z^(1/2), T=Z^(1/4), write E0=N/sqrt(Q)=Z^(3/32). Taking absolute values only after (A),(B) gives

sum_qe<=T 1/q_e min(1,q_e/E0)
 << 1+log(T/E0) when T>=E0.                                  (C)

The e<=E0 portion costs O(1); the range E0<q_e<=T costs at most O(log Z), with no power saving from this estimate. Thus even though small divisors have individual cancellation, the full truncated cofactor range is not paid by termwise completion. This does not prove the range is large or refute a signed aggregate estimate.

For f=1 the exact dual length is Q*q_e/N=Z^(5/16)*q_e, ranging up to Z^(9/16). It is shorter than the original nu length N only for q_e<Z^(3/16), and shorter than the actual free-k length L only for q_e<E0=Z^(3/32). These are different comparisons; the latter is the relevant individual square-root threshold. Moving mask divisors lengthen it further.

Negative control: replacing mu(e)chi_H^*(e) by arbitrary unit phases is allowed by the triangle estimate (C), so it cannot detect the actual signed cancellation of the truncated divisor sum. Also H with all valuations divisible by six has trivial moving conductor and can retain a principal mean; treating every H as primitive nonprincipal would be false.

## Semantic return

Obstruction retained: the same short divisor both weights the Mobius sum and expands the dual scale, while the full energy couples all frequencies and cofactors. Dictionaries: (i) bilinear dispersion with complementary divisor switching, (ii) metaplectic Gauss sums and conductor-lowering reciprocity, (iii) parity-sensitive truncated inverse Dirichlet series. UNVERIFIED rewrite: keep signed e and the new dual variable together, rather than apply (B) to each e. Another UNVERIFIED option is cancellation with the Type-I piece before taking energy. Both must retain the physical complement and the detector residue.

No new Q4 sent. This is one explicit failed termwise budget, not a replacement objective or proof of RH.

Shelf query on truncated Mobius convolution returned ASK_STATUS: INCOMPLETE (semantic freshness), not absence. The other two dictionary queries (complementary divisor switching; metaplectic conductor lowering) also returned INCOMPLETE. No estimate is imported from search snippets.
