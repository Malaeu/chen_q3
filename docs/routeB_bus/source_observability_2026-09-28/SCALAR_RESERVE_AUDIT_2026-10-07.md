# Q8 scalar arithmetic reserve: checked component, signed lower barrier open

Native answer: `PROSHKA_SCALAR_RESERVE_INLINE_2026-10-07.md`; exact question: `GROWTH_ROLLOVER_QUESTION8_2026-10-07.md`; root attempts and tighter clipped-minimum estimate: `SCALAR_RESERVE_OWN_2026-10-07.md`.
Chat 6ac58a1c-1568-83ed-95d0-857526e2b6cb; answer 3c583de5-f233-4474-9025-965d15cc8865. Native completed/idle and UI regenerate/voice controls observed. Root read the entire linked PAPER document in its rendered preview; its mathematical claims agree with the native inline answer. No new question sent.

## Source and exact definitions

Primary: Suzuki arXiv:2206.03682v4, existing local `docs/routeB_bus/litreview/pdfs/2206.03682.pdf`, SHA256 eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41. Root and independent checker inspected Theorem1.1(3); Theorems1.7 and11.1 fix the all-eventual consumer.
R(t)=(1/4)sum_(k>=1) exp(-(2k+1/2)t)/(k+1/4)^2; d_q=4/[25q^(5/2)(1-q^-2)]. These definitions are in the question and full supplement; supplied here to make the inline bounds reproducible.
All actual prime powers, poles, archimedean terms, negative jumps and zero multiplicities are retained. No RH assumption is used in the new estimates.

## Independent bounded checks

- causal_algebra_audit: PASS on central-binomial lower/upper Chebyshev bounds, pre-jump y>=sqrtq/2 for q>=64, complete loss tail, partial-summation boundary signs, linear-error cancellation, quadratic remainder, and global affine finite discriminator.
- growth_symbol_attempt: PASS on Suzuki magnitude input, distributional upper curvature, both one-sided secant bounds across negative jumps, derivative-to-A identities, constants and threshold, nonlinear exponent propagation, and critical-pair/off-line-quartet signs. Constants inherited from Suzuki are existential, not numerical.
- Root checked algebra against the source and the full PAPER preview. The extra lower bound a²/(y+a)<=ell in that supplement follows directly from the same integral formula. Own global-minimum equivalence and clipped-minimum sandwich each received one prior independent bounded check.

## Accepted results and practical limit

For every integer Q>=64, sum_(q>Q) ell_q <=(18logQ+24)/sqrtQ. This improves the earlier root bound 300log²(2Q)/sqrtQ and pays the entire infinite loss.
Writing delta(x)=A(x)-c-2sqrtx and u=(A-c)/(2sqrtx), the exact reserve is
E_x=4+b-integral_1^x delta(v)/v dv-4sqrtx[u logu-u+1].
The instantaneous linear discrepancy cancels. Under |u-1|<=1/2, the last nonnegative penalty lies between delta²/(3sqrtx) and delta²/sqrtx.
Suzuki's unconditional magnitude estimate and the exact upper curvature imply, at every sufficiently late event,
-(C_Psi+C_delta²)sqrtq exp(-alpha sqrt(logq)) <= E_q <= C_Psi sqrtq exp(-alpha sqrt(logq))+d_q.
The envelope straddles zero and grows in absolute size; it gives no required positive reserve and no negative event.
E_q=Psi(t*_q)+R(t*_q)+K_q(t*_q), with K_q>=0 and t*_q>0. Therefore a certified E_q<=0 would force actual Psi<0 and contradict RH. This corrects the question's overly broad finite-negative warning: a mere failure E_q<d_q remains inconclusive. No such nonpositive E event is established.
Root's clipped value V_q obeys V_q-epsilon_q<=min_cell Psi<=V_q, epsilon_q=12/[125q^(11/2)(1-q^-2)^2]; it likewise supplies no arithmetic sign.

## Decision and next exact obligation

The bounded magnitude/convexity mechanism is STALLED as a supplier of the terminal sign, not KILLED. The loss component is closed on paper. No further loss-only estimate or representation change counts as addressing the missing step.
For an actual prime-power anchor Q, S_Q(q)=sum_(Q<v<=q) Lambda(v)/sqrtv log(4v/y_(v-)²) must satisfy S_Q(q)>=-E_Q+L_Q(q)+d_q at every late event for the tested sufficient reserve. L_Q is paid; the lower signed barrier is not.
Next bounded work must attempt an arithmetic lower estimate for this signed drift (or a proved weaker all-cell minimum condition), after checking existing suppliers. No Q9 has been selected or sent. Do not redo Q8.
RH, SP, G1/G3 and actual Schur sign remain OPEN. No Lean run is needed to establish this paper closeout. No claim of terminal sign progress.
AUTOPSY: dropped=SIGN; note=absolute source magnitude and summable losses do not control the lower signed drift excursions.
