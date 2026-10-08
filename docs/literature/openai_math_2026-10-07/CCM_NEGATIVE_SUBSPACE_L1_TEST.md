# Actual negative-subspace l1 constraint from the flat-phase estimate

2026-10-08. Own followup while Q5 is pending; not sent to Pro. Same original K=K_m, d=2m+1,L=log m. Put B=100L^(7/2), so the independently checked flat-phase result is ||Kz||_2<=B sqrt(d) for every vector |z_j|=1. No zero-free input is used below.

Let E_s=1_(-infinity,-s](K), s>0. For any unit v in range(E_s), the spectral inverse u=(K restricted to range(E_s))^(-1)v exists, has ||u||_2<=1/s, and Ku=v. Select z_j=v_j/|v_j| when v_j is nonzero, arbitrarily otherwise. Hermitian symmetry gives

 ||v||_1=|v*z|=|u*Kz| <= B sqrt(d)/s.                    (1)

This holds for every vector in the ACTUAL deep negative subspace, not merely for individual eigenvectors. An empty subspace makes the statement vacuous. It does not bound its physical endpoint trace by zero or assert uniform support.

For S the indices of the k largest |v_j| and w=v_(S complement), decreasing rearrangement gives

 ||w||_2² <= ||v||_1²/k <= B²d/(s²k).                    (2)

Proof: every omitted coordinate is <=||v||_1/k, and multiply this maximum by the omitted l1 sum. Each vector has its own S; no common k-dimensional coordinate subspace is obtained.

For an actual unit eigenvector Kv=lambda v with lambda<=-s, put tau=||w||_2<1 and x=(v-w)/sqrt(1-tau²). Exact eigenvector cancellation, retaining all mixed terms, gives

 x*Kx=lambda+[w*Kw-lambda tau²]/(1-tau²).                 (3)

Indeed v*Kw=lambda tau², since v*w=tau². If M=||K||, the upward return is <=(M+|lambda|)tau²/(1-tau²)<=2M tau²/(1-tau²). For tau²<=1/2 it is <=4M B²d/(s²k). The available unconditional M<=B sqrt(d) therefore costs <=4B³d^(3/2)/(s²k). To certify x*Kx<=lambda+s/2 by this budget one requires k>=8B³d^(3/2)/s³, in addition to k>=2B²d/s².

For s=m^delta with fixed0<delta<1/6, this sufficient k exceeds d eventually. Thus this particular truncation-return estimate does not give useful sparse reduction for the arbitrarily small exponents needed by SP. It does not prove that sparsification itself is impossible. A known LOWER spectral bound cannot substitute for the UPPER bound on w*Kw in (3).

What is new here is (1) for the actual negative spectral subspace. What remains missing is arithmetic control on its concentrated coefficient vectors, or a sharper signed Rayleigh return. No new full-floor exponent, moment gain, or RH result is claimed. Independent ccm_window_transport audit PASS for actual-subspace inverse, phase choice, tail, exact signed return, constants and scope. The same budget also fails at delta=1/6 due to its logarithmic factor.
