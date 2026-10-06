# Growth answer9: centered long-factor control, remaining prime correlation

Exact answer: PROSHKA_ADDITIVE_CRT_INLINE_2026-10-06.md.
Exact question9: SMALL_DIVISOR_AUDIT_2026-10-06.md.
Same full carrier and original eventual family. No RH assumption.

## Proof result and consumer

The root additive-shift/CRT lemma is spent on actual compatible progression
sums before taking variation. With A>=A0=ceil sqrt m and t<=Omega,
the chosen K=floor(max(K1,K2)) pays all four terms of the vdC envelope.
The centered signed measure d rho_U = sum alpha_U(n)delta_n + A_U da
has PLUS continuous mean. This cannot be replaced by an uncentered sum.
After low/high frequency estimates and summing all prime-power b weights,
 ||C_long|| <=40000 m^(5/12)L^(3/2)log(2L) eventually on EVERY original cell.
The lower-frequency primitive, |t|<=A0/U, is <=128UL.
The exact joint d,h matrix reconstruction pays ALL complex carrier modes
and their cross terms, with no dimension factor or separate good cells.

The exact source is H(r)=rI-C_rem+F9, ||F9||<=Delta8+4 M_m.
C_rem is the centered short-alpha flux U<a<A0 PLUS the full D_U compensator.
The actual regular equation controls P_R C_rem J_r v-r(J_r v-v) only.
Schur differs from r||v||²-Re<v,C_rem J_r v> by at most
 (Delta8+4 M_m)||v|| ||J_r v||.
The source pairing and ||J_r v|| remain OPEN. This is not a 5/12 floor.
On x in [m/L^8,2m/L^8), the remaining prime-power variable obeys
b>x/A0>>sqrt m/L^8. Additive differencing the short alpha variable has
no useful shift range at top frequencies; this is an estimate limitation,
not a counterexample to the actual form.

## Independent checks and endpoint qualification

growth_symbol_attempt checked §§2–4 once: compatible CRT progression
constants5/31, zero-shift count, full vdC envelope, K1/K2 floor and eventual
uniform range, constants24/372, high-frequency partial summation and exact
low-frequency mean cancellation. Pass; all stated constants have slack.
causal_algebra_audit checked §§1,5–7 once, conditional on §§2–4:
centered split and continuous signs, geometric sums/constants, low-frequency
128UL, complete joint matrix reconstruction, actual Schur and W formula,
short-factor scale stall. Pass with explicit excluded-upper-end convention:
for [A,2A), Stieltjes endpoint values are rho_U(2A^-)-rho_U(A^-).
At an inclusive product cutoff y use rho_U(y); at an excluded cutoff use
the left limit. This preserves all atoms. The answer capture is unchanged.
The phrase positive terms in the W bound is not needed: 2(R+R*) is retained
with its exact sign; no positivity assumption about that form is imported.
Arias de Reyna Lemma5 and source conventions were read and verified in the
previous audit; no new external analytic theorem is used here.

## Own attempt before question10: prime-power parity and finite wheel

For integers B>=2 and odd 1<=k<=B, and arbitrary complex weights F(n),
 |sum_(B<=n<2B) Lambda(n)Lambda(n+k)F(n)|
 <=2 log²(3B) max|F|.
Proof: a nonzero pair has exactly one even member, which must be 2^r.
There are at most 2 floor(log_2(3B)) candidates and each product is at most
log2*log(3B). All higher powers remain accounted for.
Consequently the unconditional PNT, on endpoints in [B,3B], gives uniformly
for these ODD shifts
 sum_(B<=n<2B)(Lambda(n)-1)(Lambda(n+k)-1)=-B+o(B).
This last consequence is UNWEIGHTED. It supplies no bound on the two
oscillatory prime-continuous mixed terms in the CCM consumer.

For squarefree Q set w_Q(n)=Q/phi(Q) 1_(gcd(n,Q)=1).
Over a complete Q-period its mean is1 and its pair mean is exactly
 S_Q(k)=prod_(p|Q) p(p-nu_p(k))/(p-1)²,
 nu_p(k)=1 if p divides k, otherwise2.
CRT proves this by excluding one or two residue classes at each prime.
The centered wheel autocorrelation is S_Q(k)-1. For Q=2 this is -1 on
odd shifts and +1 on even shifts. Thus subtracting the constant density1
does not make the arithmetic correlation featureless; its local residue
structure must be kept if additive shifts of the prime variable are used.
Finite-wheel centering is a decomposition only: no smallness of Lambda-w_Q
and no Hardy–Littlewood asymptotic are asserted. A wheel cannot silently
replace the original continuous compensator or the full prime-power source.

causal_algebra_audit independently checked this bounded root lemma once:
parity count/constants, uniform unweighted PNT consequence, CRT wheel formula.
Pass. This is a discriminator for the next estimate, not an RH supplier.
SP/G1/G3/RH remain OPEN. No Lean run.

## Exact question10 sent in the same living chat

Continuation 10/10 (last new question in this chat), SAME full CCM negative-bottom-growth phase. Answer9 is audited in one disjoint bounded pass per proof block. Accepted: centered long-alpha component a>=A0=ceil sqrt m paid at ||C_long||<=40000 m^(5/12)L^(3/2)log(2L), low-frequency primitive<=128UL, all original carrier/cross terms retained. K1/K2 and constants checked. Delta9 is a remainder budget only, NOT a 5/12 floor. Exact short-alpha flux plus D_U in (21), actual J_r and Schur sign remain OPEN. Endpoint clarification: an excluded dyadic upper2A uses rho_U(2A^-); inclusive product cutoff y uses rho_U(y). No positivity of R+R* was used.

Own attempt before switching the additive shift to the long PRIME-POWER variable:
For B>=2 integer, odd integer1<=k<=B and ARBITRARY complex F(n),
|sum_{B<=n<2B} Lambda(n)Lambda(n+k)F(n)|<=2log²(3B) max|F|.
A nonzero pair has an even member2^r, at most2floor(log2(3B)) candidates, each product<=log2*log3B. Thus unconditionally by PNT, uniformly over those odd k,
sum_{B<=n<2B}(Lambda(n)-1)(Lambda(n+k)-1)=-B+o(B).
The last consequence is UNWEIGHTED; it does not pay oscillatory mixed prime-continuous terms.
For squarefree Q, w_Q(n)=Q/phi(Q)1_(n,Q)=1 has period mean1 and exact pair mean
S_Q(k)=prod_{p|Q}p(p-nu_p(k))/(p-1)², nu=1 if p|k else2.
Centered wheel pair mean=S_Q(k)-1; Q2 yields -1 on odd shifts,+1 on even shifts. Both elementary facts independently checked. No smallness of Lambda-w_Q and no prime-pair asymptotic assumed.

This exposes mandatory local residue structure in the proposed prime-variable differencing. Please EXECUTE the signed remaining-prime test on your exact (21), using odd/even or an explicitly chosen finite wheel where useful, with all corrections back to the ORIGINAL continuous D_U paid. Preserve both mixed continuous terms, all prime powers, exact product cutoffs, actual (v,J_r v) and regular equation(18). Do not import a Hardy-Littlewood prime-pair conjecture or replace Lambda by a sieve majorant/truncated surrogate without a proved signed error in the consumer norm. An upper bound for positive prime pairs alone does not estimate the centered signed correlation.

The main requested outcome is a proved one-sided bound for this remaining source pairing that can actually improve the full Schur/bottom bound; give the full original-norm error and quantifiers and identify precisely what it spends. If your actual test cannot supply it, give its exact residual aggregate (including the residue-class baseline and mixed continuous terms), prove the narrow reason the attempted bound fails or quantitatively stalls, and identify a materially different source-specific mathematical supplier worth testing next. Do not spend the answer only re-proving the parity/wheel identities supplied above or renaming the open RH-strength sign.

This is the last slot: close with a compact truthful same-phase handoff stating what is proved, the surviving exact inequality, which attempts are killed vs merely stalled, and the next OWN mathematical attempt. Do not claim RH, SP or a fixed improved full bottom exponent from component estimates. We retain the original complex CCM K_m,m=N,L=log m,eventual cells. G1/G3 and RH OPEN. If literature is used, verify hypotheses against the actual signed consumer, not just a similarly named kernel.
