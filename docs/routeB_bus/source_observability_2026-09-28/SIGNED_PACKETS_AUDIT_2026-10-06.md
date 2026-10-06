# Growth answer7: signed packets, audit and own continuation

Source: PROSHKA_SIGNED_PACKETS_INLINE_2026-10-06.md. Same phase and full
complex CCM carrier; no changed schedule, even restriction or RH assumption.
Question7 exact text is in SHIFTED_XI_KERNEL_AUDIT_2026-10-06.md.

## Accepted PAPER conclusions and scope

For X=floor(m/L^8), H=ceil(L^4), the actual joint prime-minus-pole packet
matrices satisfy sum C_l² <=64 L^5 I, while their sign-invariant Cotlar
constant is >=Gamma=sqrt(m)log(L)/(1000 L^9) on every sufficiently late cell.
Independent positive packet upper envelopes likewise cannot certify the
actual shifted form for r=A m^eta, eta<1/2. These are certificate kills,
not negative witnesses for the actual CCM form or exceptional space.
The actual +/- labelled sums (minus labels NOT negated) obey
 Re<C_+ e_j,C_- e_j> <= -Gamma²/8
for a source-selected middle carrier mode. Pairs beyond every fixed
polylogarithmic arithmetic-packet distance still contribute <=-Gamma²/16.
All output modes, prime powers, both continuous pole terms and P_m remain.
This is a genuine signed source correlation, but no improved bottom floor.
The remaining upper correlation bound is OPEN and is only sufficient for
this one arithmetic range, not all of SP.

## One bounded independent pass per disjoint proof block

growth_symbol_attempt checked sections1–3: packet primitive bound, square
function, prime mass, both cosine aliases, pole integration by parts and
constants. causal_algebra_audit checked sections4–6: sign-invariant Cotlar,
positive-envelope witness, archimedean series bound, far-pair counting,
exact finite kernel and actual Schur correction. Both passed.
Use separately R_m=o(sqrt X) and R_m=o(Gamma). A quotient relation mentioned
in a root review prompt was not a paper premise and is not asserted.
Write the corrected vector with embeddings explicitly:
 J_r v = i_E v - i_R A_r^{-1} B_r v.
No uniform bound on J_r has been proved.

Primary Cotlar theorem checked in the author's proof:
https://terrytao.wordpress.com/2011/05/25/the-cotlar-stein-lemma/
Its two row sums use ||T_i T_j*||^(1/2) and ||T_i* T_j||^(1/2).
They coincide here because C_l are self-adjoint; packet signs leave both
unchanged. This exactly supports the certificate obstruction, not SP.

## Own attempt before question8: retain the endpoint geometry

Work in H=L²[0,L], S_s f(t)=f(t-s)1_{t>=s}, P=P_m.
Let a=log X, b=L-a, so a>L/2 eventually. For the SAME signed measure
mu restricted to [X,2X), put V=int S_log(x) dmu(x), T=V+V*.
With E_h=1_[0,b], E_t=1_[a,L], V=E_t V E_h and E_h E_t=0.
Consequently V²=0 and, for every f in ran P,
 ||(sum C_l)f||²
 = ||V E_h f||²+||V* E_t f||²-||(I-P)Tf||².
Thus the exact cross-packet functional in answer7 is
 Xcross(f)=||V E_h f||²+||V* E_t f||²
           -||(I-P)Tf||²-sum ||C_l f||².
This preserves a beneficial projection-loss term. It is an identity, not
an estimate or new progress toward the sign. causal_algebra_audit checked
this exact root derivation once and passed.
The same-direction nilpotence cannot be used after compression:
 P S_s P S_t P = -P S_s(I-P)S_t P, s,t>=a.
In fact the finite Fourier compression of S_s is an invertible interval
Gram matrix times a diagonal phase for s<L, so these products do not vanish.

For a concrete analytic representation, reflect the output t=L-u and
push mu forward by h=L-log x. Then
 (V f)(L-u)=int f(h-u) dnu(h),
with f extended by zero, h in (b-log2,b], and
 dnu = sum_{X<=n<2X} Lambda(n)/sqrt(n) delta_{L-log n}
       -(sqrt(m)e^{-h/2}-m^{-1/2}e^{h/2})dh
on that same half-open support. This is a finite-window Hankel operator
between the two endpoint strips of width b~8log L. It keeps the exact
logarithms and both pole pieces. No Hankel boundedness theorem is invoked.
In the one-sided form the compression disappears only because f is already
in ran P: <f,Cf>=2 Re<f,Vf>. Projection effects persist in f and its Schur
correction. General L² trace choices cannot replace actual J_r v.

Decision: blind packet gluing KILLED in its precise shapes; signed endpoint
Hankel estimate remains OPEN. Keep the signed arithmetic mechanism and ask
for an actual estimate on corrected vectors, not another positive envelope.
SP, G1/G3 and RH remain OPEN; no Lean run.

## Exact question8 sent in the same living chat

Continuation 8/10, SAME full CCM negative-bottom-growth phase. Answer7 is independently audited and accepted with its exact limited scope: sum C_l²<=64L^5I; sign-blind Cotlar constant>=Gamma and independent positive packet envelopes fail for eta<1/2; actual negative far-packet compensation on the selected middle mode. SP and actual exceptional Schur sign remain OPEN. The witness is not known exceptional. Root checked the primary finite Cotlar theorem. R=o(sqrt X) and R=o(Gamma) are the separate relations used.

We need a SIGNED ESTIMATE now, not another kill of blind norms or an identity renamed a supplier. Own attempt, independently checked:
On H=L²[0,L], causal S_s f(t)=f(t-s)1_{t>=s}, P=P_m, keep your exact joint signed measure mu on [X,2X), X=floor(m/L^8). Put a=log X>L/2, b=L-a~8log L, E_h=1_[0,b], E_t=1_[a,L], V=int S_log(x) dmu(x), T=V+V*. Exactly V=E_t V E_h, V²=0. For f in ran P,
||sum C_l f||²=||V E_h f||²+||V*E_t f||²-||(I-P)Tf||²,
and your Xcross(f) is this expression minus sum||C_l f||².
Compressed same-direction products are NOT zero: P S_s P S_t P=-P S_s(I-P)S_t P.
Reflect output t=L-u and push mu by h=L-log x:
(Vf)(L-u)=int f(h-u)dnu(h),
nu=sum_{X<=n<2X} Lambda(n)/sqrt n delta_{L-log n} -(sqrt m exp(-h/2)-m^(-1/2)exp(h/2))dh on (b-log2,b], with f zero extended.
This is an exact short-strip Hankel form; not a bound. The one-sided source form is exactly 2Re<f,Vf> for f in ran P. Endpoint restrictions of f are coupled by original finite Fourier synthesis.

Consumer remains actual Schur with A_r positive regular block, B_r regular-exceptional block, J_r v=i_E v-i_R A_r^{-1}B_r v and r=C_eta m^eta. Evaluate the signed arithmetic expression on THESE corrected vectors, preserving ||J_r v|| and the full B_r* A_r^{-1}B_r correction. Do not replace them by independent endpoint traces or the answer7 middle witness.

Try to prove a genuinely stronger source-specific one-sided relative bound using this Hankel/endpoint geometry, the prime-minus-continuous combination, and the regular equation defining J_r. A direct form bound is preferable to imposing subpolynomial norm of each dyadic block. If working with Xcross, keep the negative projection-loss term and prime-prime plus both prime-continuous cross terms coherently. Account for other arithmetic ranges before claiming a full floor; no intersections of separately chosen good cells.

Deliver the strongest new estimate you can PROVE with explicit original-norm error and exact quantifiers, even if it is not SP. An unconditional improved fixed exponent would already be major and must be justified, not inferred from zero density. If this exact corrected-vector endpoint approach stalls, isolate the first unestimated signed scalar/bilinear term after exploiting the regular equation, and test a specific source lemma for it; do not spend this answer rediscovering blind Cotlar failure, generic Pick positivity, fixed positive-space transfer, or RH-equivalent restatements. Use verified primary literature only where hypotheses map exactly. Same K_m, m=N,L=log m, all complex modes, all prime powers and both pole terms. G1/G3/RH remain open until actual estimates close them.
