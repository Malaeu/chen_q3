# Short Mobius polynomial mean square

The exact signed-dual Mellin identity retains M_T(1-s). Here is one bounded estimate for that actual polynomial, conditional only on the previously audited source sextic-sieve lemma; it is not a bound for its product with D_f.

Let eta be fixed finite order, S its fixed bad set, m any ideal fixed before the H sum, and Q,T>=1 with Q>=T^2. For squarefree primary good H with Q<q_H<=2Q and real t set
M_H(t)=sum_qe<=T,(e,m)=1 mu(e)eta(e)conjugate(chi_e(H))q_e^(-1/2-it).
Then
sum_H |M_H(t)|^2 <<_(S,epsilon) (QT)^epsilon Q log(2T),
uniformly in t and m. Restricting the H rows further, for example (H,m)=1, is allowed.

Proof: source paper.tex4707–4725, the full-ball sextic large sieve, accepts c_e=mu(e)eta(e)1_(e,m)=1 q_e^(-1/2-it), independent of H, and sign−1 with original zero values. Its l2 mass is at most sum_qe<=T 1/q_e << log(2T). Taking K=2Q,D=T gives K+D+(KD)^(2/3)<<Q because T^2<=Q. All constants are independent of the puncture since it only removes coefficients. No dyadic split or extra logarithm is required.

At Q=Z^(13/16),T=Z^(1/4), the condition is satisfied. This does not authorize shifting the previous Mellin contour to Re s=1/2 and does not control D_f(s)M_T(1-s), H-dependent test profiles, the outer d,v sums, nonsquarefree H, principal rows, or physical complement. Those must be handled separately.

Root reread the exact lemma and checked coefficient independence; independent squarefree_conductor_check PASS. Source normalization and full theorem scope remain pinned in SEXTIC_SIEVE_BOUNDED_AUDIT.md. The entire OpenAI manuscript is not certified by this use.
