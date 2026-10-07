# ZF78 pays the higher logarithmic moments

Own continuation while Direct Shift Q1 is running. Not separately sent. Independent squarefree_conductor_check audit PASS for the tail, signed remainder, exact moment identity and quantifiers; external ZF78 remains conditional. Source variables are exactly SHIFTED_ARITHMETIC_RESERVE.md: 0<=eta<=3/8, b=1/2+eta, a=1/2-eta, w_r=Lambda(r)r^-b, u_r=a(A_eta,r_previous-c_eta)/r^a-1, with ALL prior prime powers.

ZF78 gives |u_r|<=C_(eta,epsilon) r^(-1/8+epsilon). Choose a prime-power anchor Q large enough that |u_r|<=1/2 for every event r>Q. The existence of this eventual anchor follows from the conditional bound; no explicit numerical anchor is certified here.

For K>=1 and |u|<=1/2,
log(1+u)=P_K(u)+rho_(K+1)(u),
P_K(u)=sum_(k=1..K)(-1)^(k+1)u^k/k,
|rho_(K+1)(u)|<=2|u|^(K+1)/(K+1).
The integral identity rho_(K+1)(u)=(-1)^K int_0^u t^K/(1+t)dt proves the formula and bound for either sign of u.

Put delta=eta+(K-3)/8-(K+1)epsilon. When delta>0, summing over ALL integers rather than only prime powers yields
sum_(r>Q)w_r |rho_(K+1)(u_r)| <<_(eta,epsilon,K) Q^(-delta)log(2Q).
Indeed the summand is bounded by a constant times log(r)r^(-1-delta). This pays the entire omitted logarithmic tail uniformly in the final event q>=Q.

In particular:
- eta=0: K=4, 0<epsilon<1/40, delta=1/8-5epsilon>0.
- eta>0: K=3, 0<epsilon<min(1/8,eta/4), delta=eta-4epsilon>0.
- eta>1/8: K=2 with epsilon<(eta-1/8)/3.
- eta>1/4: K=1 with epsilon<(eta-1/4)/2.
Threshold endpoints require the next degree unless a stronger input is proved. Constants and Q can depend on the fixed eta and epsilon; no uniform passage eta->0 is asserted.

## Exact retained consumer

Let M_k(Q,q)=sum_(Q<r<=q, r prime power) w_r u_r^k, and L(Q,q)=sum ell_r. Then
E_eta,q=E_eta,Q-(1/a)sum_(k=1..K)(-1)^(k+1)M_k(Q,q)/k-L(Q,q)+error(Q,q),
|error(Q,q)| <<_(eta,epsilon,K) Q^(-delta)log(2Q), uniformly q>=Q.
The independently checked L-tail is O_eta(Q^-b log²Q). A sufficient lower bound for the finite signed moment combination, including the fixed anchor and d_eta,q, is still OPEN.

For eta=0 the retained combination is M1-M2/2+M3/3-M4/4. It includes up to five interacting prime-power events when the four prefix factors are expanded. No independence, factorization, random signs, or deletion of early history is permitted. This is finite degree, not finite height or a finite computation.

For K=3, rho4(u)=-int_0^u t³/(1+t)dt<=0 even for negative u>-1. Therefore its contribution to E is nonnegative. Dropping that favorable term gives a one-sided lower bound; for eta>0 it also has the vanishing absolute tail above. This favorable sign alone does not control M1-M2/2+M3/3. At eta=0 the cubic truncation is still a valid stronger sufficient lower bound, but its discarded term is not paid by this magnitude argument; K=4 gives the two-sided vanishing-error reduction.

Status: conditional finite-degree reduction only, no new sign, no smaller zero-free strip, no RH. The older SELBERG_SCALAR_AUDIT keeps the exact nonlinear correction u-log(1+u); this calculation pays its high-degree tail using the new power saving and does not supersede the old exact identity. It is available to test the pending Pro response, not authorization for a second concurrent question.


## Exact entropy return: do not separate the moments blindly

Root derivation; independent squarefree_conductor_check audit PASS, including jump factors, pre/post-event endpoints and bounds. This generalizes the EXISTING eta=0 entropy return in JOINT_LATTICE_AUDIT lines20–30; it is not a new positivity mechanism.
For continuous logarithmic time set y(t)=A_eta(exp t)-c_eta and u(t)=a*y(t)exp(-at)-1, using the right-continuous full prime-power prefix. Between events u'=-a(1+u); at event r the jump is a*w_r*exp(-at). Define F(u)=(1+u)log(1+u)-u>=0 for u>-1.
For post-event endpoints T=log Q and t=log q, the exact jump chain rule gives
S(Q,q):=sum_(Q<r<=q)w_r log(1+u_r_pre)
 =[exp(at)F(u(t))-exp(aT)F(u(T))]/a
  +int_T^t exp(as)u(s)ds-a L(Q,q).
Each jump correction is exact: exp(at)[Delta F-F'(u_pre)Delta u]=a² ell_r. No early jump or anchor is discarded.
Substitution into the exact E increment cancels the loss completely:
E_eta,q=E_eta,Q-[exp(at)F(u(t))-exp(aT)F(u(T))]/a²
 -(1/a)int_T^t exp(as)u(s)ds.
At an event endpoint the original source satisfies exactly
Psi_eta(log q)=E_eta,q+q^a F(u(log q))/a²-R_eta(log q).
Thus the finite moment combination encodes the same integrated source discrepancy and a nonnegative endpoint entropy; it is not four independent reserves.

Under ZF78, F(u)=O(u²) near0 gives the conditional entropy bound
q^a F(u(log q))/a² <<_(eta,epsilon) q^(1/4-eta+epsilon).
It tends to0 for each fixed eta>1/4 after choosing epsilon<eta-1/4. At eta=0 it need not be small in absolute size under this bound. The integrated discrepancy is still only O(q^(3/8-eta+epsilon)) in magnitude (constants/anchor absorbed). Neither term has the needed combined sign. The Q1 response should be tested against this exact return before claiming progress from a moment reformulation.
