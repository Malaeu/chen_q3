# Q9: exact multiplicative cancellation and proper-power drift tail

Status: PAPER component accepted; prime-prefix sign OPEN. RH/SP/G1/G3/actual Schur/scalar reserve OPEN.

Provenance: living chat `6ac58a1c-1568-83ed-95d0-857526e2b6cb`, user `b6ac7803-bd73-4e1e-90d1-75709b4d8beb`, answer `ce9e2ab4-bbe4-4b6f-85dc-182cdb898057`. Exact request: GROWTH_ROLLOVER_QUESTION9_2026-10-07.md; own attempt: SELBERG_SCALAR_OWN_2026-10-07.md; native answer: PROSHKA_SELBERG_SCALAR_INLINE_2026-10-07.md. Root read the complete expanded PAPER verdict as well as native answer. Equation numbering below refers to the full preview, whose numbering differs from inline.

## Accepted arithmetic and its limited consequence

For actual integers, P_n(z)=n^z product_{p|n}(1-p^-z) gives Lambda_2(n)=(mu*log^2)(n): (2k-1)log^2 p for p^k; 2 log p log r for p^a r^b; zero on three or more distinct primes. The ordered Lambda*Lambda has coefficients (k-1)log^2 p, 2 log p log r, and zero respectively. Thus the mixed-prime product sector cancels exactly under every product-only ramp or weight. At an actual prime the convolution slope jump is zero, while the forcing jump is log^2(p)/sqrt(p).

This stops the attempt to spend the positive convolution as an independent local restoring term. It does not kill nonlocal consequences of the identity, multiplicative methods generally, or the terminal target. Failure type NO_DERIVATION; no theorem-family kill.

## New quantitative tail, complete history retained

Use the audited Q8 pre-jump estimate |Delta(v)| <= C_delta sqrt(v) exp(-beta sqrt(log v)), beta=alpha/2>0, for v>=Q0 and |Delta/(2sqrt(v))|<=1/2. Set

s(v)=Lambda(v)/sqrt(v) log(4v/(A(v-)-c)^2).

Then |s(p^k)| <= 2 C_delta log(p)/p^(k/2) exp(-beta sqrt(k log p)). For every real Q>=Q0,

P(Q)=6 C_delta exp(-beta sqrt(log Q)) [sqrt(log Q)/beta+1/beta^2+1+16 Q^(-1/6)]

bounds the entire sum of |s(p^k)| over p^k>Q, k>=2. Squares use partial summation with theta(x)<=3x and z=sqrt(2log x); cubes and higher have weighted tail <=48 Q^(-1/6). The lower partial-summation boundary is nonpositive. Strict p^k>Q is preserved. P(Q) tends to zero faster than every negative power of log Q. Constants exist from the accepted unconditional Suzuki/Q8 input; this is not a numerical certificate.

Only event contributions at proper powers are bounded away. Every A(p-) below still contains ALL previous prime powers.

## Exact surviving quantity and return

eta_p=(A(p-)-c-2sqrt(p))/(2sqrt(p)),
C_Q(q)=sum_{Q<p<=q} log(p)/p [A(p-)-c-2sqrt(p)],
J_Q(q)=2 sum_{Q<p<=q} log(p)/sqrt(p) [eta_p-log(1+eta_p)] >=0.

The prime drift is exactly -C_Q+J_Q. Its ordered pair kernel is log(p)log(r)/(p r^(j/2)), r^j<p, together with the -c and -2sqrt(p) reference subtractions. It is not the product-only kernel annihilated above. Neither an individual positive pair nor J_Q>=0 estimates the net C_Q-J_Q sufficiently.

For prime-power anchor Q>=Q0, define M_Q(q)=E_Q-C_Q(q)+J_Q(q)-L_Q(q)-d_q. Then, for every prime-power q>=Q,

M_Q(q)-P(Q) <= E_q-d_q <= M_Q(q)+P(Q),
0<=L_Q(q)<=(18log Q+24)/sqrt Q.

The right unresolved supplier is an upper bound for C_Q-J_Q, with its exact subtractions and anchor E_Q, sufficient to pay loss, P(Q), and d_q. No such bound is supplied. A negative E_q-d_q alone does not refute cell positivity; the stronger E_q<=0 discriminator has not been triggered.

The complete Volterra substitution is valid: L Psi+2B'*Psi'-Psi'*Psi'=L B+B'*B'-R_mu. B(0)=F(0)=Psi(0)=0 and B'(t)=O(1+|log t|) near zero, so the derivatives are locally integrable with no omitted impulse. The reflected convolution is not an L2 norm.

## Independent checks and decision

- causal_algebra_audit: PASS proper-power tail constants, strict boundaries, Q0 dependence and complete two-sided return; full prehistory retained.
- growth_symbol_attempt: PASS support formulas, both ordered factors, product-only cancellation, exact correlation and nonlinear correction, Volterra endpoint integrability. No sign or RH conclusion.
- Root: read full preview; verified tail factor 6*16=96, prime-drift sign and narrowing of the stopping verdict. Proshka's reported 4095 finite formal checks are auxiliary reported controls, not independently reproduced evidence; unrestricted identities use the finite-product proof.

Q9 is answered and checked. Q10 is NOT selected or sent. Next bounded work: source/alias return for the ordered prime-prefix net drift and an own quantitative attempt; no repeat of loss-only or magnitude-only envelopes. No Lean needed for this PAPER component.
