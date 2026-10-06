# Full CCM negative-bottom growth: same-phase rollover, question1/10

This is a continuation, not a fresh route. The previous Proof of CCM Growth
chat exhausted10/10. Use the attached source pack as mathematical context.
Do not repeat the earlier ten questions or treat historical questions in the
appendices as new requests. The active request is the last section here.

route_id: ROUTE_B
front_id: FULL_CCM_NEGATIVE_BOTTOM_GROWTH
source_object_family_id: CCM_FULL_N_EQ_M_ORIGINAL_COFINAL
terminal_consumer_id: FULL_WEIL_CRITERION_VIA_SUBPOLYNOMIAL_NEGATIVE_BOTTOM
honesty_state: CHALLENGER_NOT_RH
convention_lock_id: W02_MINUS_WR_MINUS_ALL_PRIME_POWERS_PHASED_LOG_WINDOW

## Fixed source and terminal

m=N, L=log m, full complex carrier e_j(x)=L^-1/2 exp(2pi i j x/L)
on[0,L], |j|<=m, zero extension, P_m orthogonal projection.
These are the original eventual cells m_j=preAnchorTailStart(P)+j+2.
Centered coordinates t=x-L/2 give psi_j=(-1)^j L^-1/2 exp(2pi i jt/L).
K_m is the complete CCM Weil-form compression; no parity restriction.
S_s f(x)=f(x-s) with zero extension, S_L=0.
C[sigma]=P_m int(S_logx+S_logx*)d sigma(x)P_m.
The complete joint source is
 dmu=sum_(2<=n<=m)Lambda(n)/sqrt(n)delta_n
       -(x^-1/2-x^-3/2)dx on[1,m].
All prime powers and both pole pieces are retained.
H_m(r)=diag(a(omega_j))+rI-C[mu],
 a(omega)=2int_0^infty e^-s/2/(1-e^-2s)(1-cos(omega s))ds,
K_m=H_m(0)+E_m, ||E_m||<=C0=cA+28,
cA=EulerGamma+log(8pi)+pi/2.

Already proved with cutoff and Fourier error paid: ANY hypothetical actual
off-critical zero .5+delta+i gamma, delta>0, forces
 lambda_min(K_m)<=-c m^delta/(log m)^(2delta)
on EVERY sufficiently late original cell. This does not assert such a zero.
Sufficient OPEN target SP: for every eta>0, lambda_min(K_m)>=-C_eta m^eta
eventually; an unbounded original good-cell set for each eta also suffices.
This would exclude every off-critical zero. SP and RH remain OPEN.

## What is retained / not to repeat

Full-source floor is only -cA-C sqrt(m)L³ exp[-.001(L/log L)^(1/3)].
Full signed zero Gram reduction has a polylog floor outside codim O(m/L^5).
Repaired high-zero cutoff T=mL² has full norm tail<=3e6/sqrtL.
The positive low Gram G_low contains all critical rows and all pair-sum rows;
B contains pair-difference rows for delta>8logL/L, |gamma|<=T.
R=ker B, E=R^perp. For epsilon=O(L^10 logL), actual regular block
A_r=P_R H_m(r)|R >=(r-epsilon)I. For r>epsilon and v in E,
 f=J_r v=v+y, y=-A_r^-1 B_r v, B_r=P_R H_m(r)|E.
Schur=H_EE-B_r* A_r^-1 B_r; no bound ||J_r|| assumed.
The attached high-zero answer defines these exact objects and constants.

Killed only in recorded scopes: uniform causal undressing on whole carrier;
removal of I-R pole cancellation; old endpoint jet majorant;
fixed shifted-xi observation lift and gamma-neutralized positive kernel;
sign-blind Cotlar / independently positive arithmetic-packet envelopes.
Fixed-inner exceptional norm transfer is RH-strength and STALLED.
Actual arithmetic packets DO have large negative distant correlations on
middle modes, but these are not actual exceptional Schur witnesses.
Do not replace the signed source by independent positive envelopes.

Type-I was paid; centered long-alpha a>=A0=ceil sqrt(m) was paid at
O(m^5/12 L^3/2 log(2L)) on the whole carrier. These are COMPONENT errors,
not improved full bottom floors. Q10 paid wheel return and powers of two;
parity-centered differencing STALLED at weighted EVEN-shift aggregate.
The final Q10 source and its precise audit/own attempt are attached in full.
Minor Q10 proof clarification: floor(K*)>=2K*/3 for K*>=2 establishes
its intermediate constant214; replacing214by218 also leaves1024 unchanged.

## Active request: execute the linear finite-convolution attempt

The exact remaining pairing is Q10(14): R_*(v,J_r v), with weight F defined
by Q10(13) and exact compensator Dtilde in Q10(4). All restrictions remain.
H=rI-C_*+F10, ||F10||<=Delta10=O(m^5/12 L^3/2 log(2L)).
Schur=r||v||²-Re R_*(v,J_r v)+Re<v,F10 J_r v>.
This is the unresolved PAPER_CHAIN/SP consumer, not a proved floor.

Own attempt is in PARITY_PRIME_AUDIT: exact Heath-Brown k=3 identity with
z=ceil((m/U)^(1/3)), valid for every required b<=m/U without remainder,
inserted LINEARLY into R_* before any prime-pair differencing.
It gives j=1,2,3 sums with coefficients3,-3,1; products of j truncated
Möbius factors and j free factors (one logarithmic), every factor odd.
Subtract the exact -2 odd sum and keep Dcal; do not recenter for free.
A long product does NOT ensure a long free factor: di=p nearz/3,
n1=n2=1,u=3 gives a nonzero j3 representation with all free factors<=3.
This individual tuple is not a lower bound for the aggregated source.

Please EXECUTE this source-specific multilinear test. Separate sectors by
an explicit free-factor scale, pay the free integer/log-factor quadrature
with the exact product cutoffs and signed coefficients, and retain every
sector whose long variables have Möbius weights. Seek a JOINT signed bound
which advances the actual Schur pairing, using the actual regular equation
if useful. Keep the whole original carrier or prove the faithful transfer
from scalar primitives; no omitted cross modes, endpoint traces, compensator,
prime powers, or ||J_r v||. Optimize a real parameter/range and show its cost.
A smaller error for yet another piece is secondary: identify and attack the
remaining signed coefficient-weighted sector at the same time.

If this attempted supplier stalls, give the exact source-specific residual
and a proved narrow reason its concrete estimate stalls, then the next
mathematical supplier worth testing. Do not merely rename SP, request an
unproved prime-pair asymptotic, quote a mean-value theorem as a uniform
bound, or declare an abstract arbitrary-coefficient counterexample to be
an obstruction for the actual Möbius source. No plan-only answer.
Use primary literature only with exact hypotheses mapped to these sums.
All-eta SP, original G1/G3 and RH are OPEN; paper first, Lean later.
