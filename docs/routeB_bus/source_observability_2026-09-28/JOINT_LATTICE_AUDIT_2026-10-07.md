# Q10 exact joint lattice return: checked, signed estimate unchanged

Status: PAPER identities checked; this bounded floor-pairing attempt STALLED. No new one-sided estimate, component bound or terminal margin. RH/SP/G1/G3/actual Schur/scalar reserve OPEN. No counterexample to the target or impossibility claim about other arithmetic methods.

Provenance: chat `6ac58a1c-1568-83ed-95d0-857526e2b6cb`; user `2454f011-d320-43f1-a9e1-7d125b40568d`; answer `29afc971-faa8-4da1-aa80-8923eedce5d2`. Request/own new divisor-pairing calculation: GROWTH_ROLLOVER_QUESTION10_2026-10-07.md. Exact native answer: PROSHKA_JOINT_LATTICE_INLINE_2026-10-07.md. Root read the entire expanded PAPER preview as well; it adds no independent signed estimate. Previous own quadrature and energy attempts are committed separately.

## What the joint operation actually does

For x=e^t, define G_d(v)=v^-1/2(t-log v)log(v/d) on d<=v<=x. Its derivative is v^-3/2[P0(v,t)+log(d)P1(v,t)], with precisely the coefficients in the request. Both G_d(d) and G_d(x) vanish, for real integer or noninteger x.

Finite Fubini and the actual floor identities imply:
1. The combined unweighted half-sums integrate to zero, divisor by divisor. Neither individual integral is claimed zero.
2. The constant -1 floor term integrates to zero by d=1.
3. The harmonic Mobius part integrates to minus the ENTIRE continuous main term, including H0(s)=4e^(s/2)(s-4)+4s+16.

After recombination F=M-T_K, the exact survivor is
F(log x)=integral_1^x v^-3/2[1+(1/2)log(x/v)] psi_Ch(v)dv.
This is the original complete prime-power ramp by Stieltjes integration, with coefficient ONE. No residual independent favorable correction survives. The derivative here is with respect to logarithmic time t (x=e^t); it is A(x), with complete jump Lambda(q)/sqrt q. It must not be read as an x-derivative.

## Complete source and reserve return

Let W(x)=integral_1^x v^-3/2[1+(1/2)log(x/v)] [psi_Ch(v)-v]dv. The exact baseline integral is 4sqrt x-log x-4. Thus
Psi(log x)=(c+1)log x+(b+4)-R(log x)-W(x),
E_q-d_q=(c+1)log q+(b+4)-W(q)-D_entropy(q)-d_q.

At x=1, W(1)=0 and R(0)=b+4, preserving Psi(0)=0. All prime powers remain in D_entropy through A(q); R is canceled only in the reserve definition, never omitted from Psi.

The exact drift return is
S_Q(q)=(c+1)log(q/Q)-[W(q)-W(Q)]-[D_entropy(q)-D_entropy(Q)]+L_Q(q).
This supplies no signed estimate of W+D_entropy. Q8/Q9 loss and proper-power drift tails, thresholds and constants are unchanged. In particular,
E_q-d_q >= E_Q+S_Q^prime(q)-L_bound(Q)-P(Q)-d_q,
with S_Q^prime=-C_Q+J_Q, retains exactly the previously unpaid sign. The clipped full-cell minimum is unchanged; sparse good cells do not supply eventual nonnegativity.

## Independent bounded checks and decision

- causal_algebra_audit PASS native equations1-10: polynomial change, Jacobian, floor signs, complete H0, primitive endpoints, all three cancellations, coefficient-one source return for real x.
- growth_symbol_attempt PASS native equations11-16: baseline, c+1/b+4, R(0), reserve/entropy and drift signs, inherited tails with original thresholds, all-event requirement. Root notes the displayed derivative is d/dt, not d/dx.
- Root checked the complete preview and exact return. Proshka's reported 2048 rational-cutoff and symbolic controls were not independently reproduced and are not used in place of the unrestricted finite-Fubini proof.

The only newly closed issue is correctness of the submitted joint calculation. The terminal signed estimate made NO PROGRESS. Counting a canceled Mobius term as extra reserve after the complete prime sum returns would double count it. Do not repeat this pairing or open a higher convolution hierarchy on the strength of this identity.

The living chat is now 10/10 answered and checked, exhausted. No new chat or follow-up question has been created. Next selection requires a source-verified inequality genuinely estimating the remaining one-sided arithmetic quantity, following alias return; an equivalent rewrite is not a supplier. Lean is deferred because no paper proof of RH is complete.
