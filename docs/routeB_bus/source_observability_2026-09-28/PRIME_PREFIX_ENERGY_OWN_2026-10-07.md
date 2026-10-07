# Prime-prefix drift: ordered Stieltjes energy test and alias return

Previous goal turn: PROGRESS, Q9 component audited and pushed. This attempt keeps the same scalar target and complete arithmetic source. No Q10 has been sent.

## Exact obstruction and dictionaries

We need E_q>=d_q on every late prime-power cell (sufficient for eventual complete Suzuki Psi>=0, hence RH). Q9 reduced its unpaid part to C_Q-J_Q, an ordered prime-prefix discrepancy with all earlier powers retained; see SELBERG_SCALAR_AUDIT_2026-10-07.md. Losses and proper-power EVENT drift have vanishing whole-tail budgets. Their existence gives no sign for the prime contribution.

Dictionaries: Stieltjes integration by parts / ordered triangular kernel; entropy balance with jump quadratic variation; Selberg remainder recursion / multiplicative renewal. Search hints were UNVERIFIED until the explicit calculations below. Negative control is a sublinear oscillatory perturbation of the approximate remainder equation, not another von Mangoldt function.

Shelf queries `Selberg symmetry formula`, `iterated Chebyshev integral`, `prime prefix correlation` completed with ASK_STATUS INCOMPLETE (semantic-index freshness failure); no absence claim. Existing scalar source files were read. The primary Selberg paper was then fetched to test what its actual recursion pays.

## Own exact energy calculation (independently checked)

Let A(x)=sum_(n<=x) Lambda(n)/sqrt n, delta(x)=A(x)-c-2sqrt x, and a_n=Lambda(n)/sqrt n. All integrals below are finite on [Q,q], 1<Q<=q, and anchors use post-jump values. At each event n, delta(n)-delta(n-)=a_n; between events delta'(x)=-1/sqrt x.

Define C_all=sum_(Q<n<=q) a_n delta(n-)/sqrt n and J_all=2 sum_(Q<n<=q) a_n [eta_n-log(1+eta_n)], eta_n=delta(n-)/(2sqrt n). Then

C_all = integral_Q^q delta(x)/x dx
 + [delta(x)^2/(2sqrt x)]_Q^q
 + (1/4) integral_Q^q delta(x)^2/x^(3/2) dx
 - (1/2) sum_(Q<n<=q) a_n^2/sqrt n.                 (A)

Proof: d(delta^2)=2 delta_- ddelta+sum a_n^2 atoms, ddelta=dA-dx/sqrt x, and d(x^-1/2)=-(1/2)x^-3/2 dx. Finite Stieltjes integration by parts gives (A), including both endpoints. The positive bulk square appears with a positive sign in C, hence an adverse sign in the drift -C+J. It is not free favorable reserve.

Let y=A-c>0 and D(x)=2y log(y/(2sqrt x))-2y+4sqrt x, the Q8 entropy. Between events D'=-delta/x. At n, its jump is 2a_n log(y(n-)/(2sqrt n))+ell_n. Therefore

C_all-J_all = D(q)-D(Q)+integral_Q^q delta(x)/x dx-L_Q(q).  (B)

Combined with E_q-E_Q=-C_all+J_all-L_Q, (B) is exactly the existing Q8 identity E_q-E_Q=-[D(q)-D(Q)]-integral delta/x. Restoring the proper-power event sum recovers Q9 with its P(Q) budget. No new arithmetic estimate has appeared. Symmetrizing the ordered kernel without retaining boundary, nonlinear correction and jumps would change the target.

## Primary source candidate: exact hypothesis mapping

Selberg, An Elementary Proof of the Prime-Number Theorem, Annals 50 (1949), 305-313. DOI 10.2307/1969455. Fetched PDF: ../../literature/selberg_drift_2026-10-07/selberg1949.pdf; SHA256 47de9d3c50d48e57fde27058d37a487b9414a67c8aace831c02ffba29ef8e6e6.
URL: https://www.math.lsu.edu/~mahlburg/teaching/handouts/2014-7230/Selberg-ElemPNT1949.pdf

Printed p310 equation (2.12), with R(x)=theta(x)-x:
R(x)log x + sum_(p<=x) log p R(x/p)=O(x).
Printed p313, final remark, exact excerpt: “o(x log x) instead of O(x).” This refers to the weakened permissible remainder in (2.8). Sections 3-4 prove R(x)/x->0 using near-small subintervals and an iterative absolute-value bound. This is a source-verified PARTIAL ANALOGUE, not a signed critical-scale estimate. The paper's R is the unweighted prime-count discrepancy, NOT our archimedean correction R(t) and NOT our weighted delta.

The project map is partial summation from theta (plus all proper powers) to A. PNT-scale asymptotics map to magnitude control; they do not supply the ordered signed C_Q-J_Q upper bound. The actual prime support hypothesis is retained in the source, but no theorem quoted here controls the required integrated sign.

## Own error-tolerant recursion test (independently checked)

Fix 1/2<sigma<1, gamma>0, f(x)=x^sigma cos(gamma log x). Keep the ACTUAL prime weights in the linear operator
T f(x)=f(x)log x+sum_(p<=x) log p f(x/p).

From theta(t)<=3t and partial summation,
sum_(p<=x) log p/p^sigma <= 3 x^(1-sigma)/(1-sigma).
Also x^sigma log x <= x/[e(1-sigma)] for x>=1. Thus
|T f(x)| <= [3+1/e]x/(1-sigma).

Consequently adding epsilon*f to any solution of the approximate R equation still satisfies an O(x) remainder equation. Further, integral_1^infinity |f(x)|/x^2 dx <=1/(1-sigma), and f'=O_(sigma,gamma)(x^(sigma-1)). These coarse integral/continuity properties do not exclude the oscillation either.

This is a test of the INFORMATION supplied by that approximate equation. R+epsilon*f is not asserted to equal theta-x, be prime-supported, or satisfy the exact Mobius identity. It is not a counterexample to the actual arithmetic target. It says that spending only the O(x) remainder recurrence cannot discriminate a critical-scale oscillatory component. A sharper signed source remainder, or another exact arithmetic constraint not absorbed into O(x), is still required.

## Decision

No new supplier, no RH claim, no replacement target. Ordered-energy symmetrization returns exactly to the already open discrepancy/entropy balance. The approximate Selberg recursion offers no imported estimate at the needed scale. Next action must retain exact arithmetic information beyond that approximation; do not send Q10 as an integration-by-parts or PNT request. Independent checks: growth_symbol_attempt PASS (A), (B), all jumps/endpoints and exact Q8 return; causal_algebra_audit PASS the error-tolerant recurrence test, constants and narrow scope. Root verified the primary-source mapping. This bounded attempt is checked and STALLED as an independent sign supplier.
