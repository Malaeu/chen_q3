# Scalar drift: checked partial source, finite-height limitation

Chirre–Helfgott, *Optimal bounds for sums of non-negative arithmetic functions*, https://arxiv.org/pdf/2512.15709 . Local `chirre_helfgott.pdf`, SHA256 558f33421d8cbd31c969434c065375836dace5fa7248358542d7691c03138e31.
Proposition9.1, printed p34: “Assume the Riemann hypothesis holds up to height T”. Its precise domain is T>=10^7, x>max(T,10^9), -1.999<=sigma<=100. Root reread statement and opening proof; growth_symbol_attempt checked sigma=1/2 specialization independently.
At sigma=1/2 it supplies A(x)<=U_T(x)=(c_T+e_T)sqrtx-alpha+d_T, alpha=zeta'/zeta(1/2)=-c,
c_T=(pi/T)coth(pi/(2T)), e_T=pi/(T-1), d_T=log²(T/(2pi))/(2pi)-log(T/(2pi))/(6pi).
This is a CONDITIONAL PARTIAL supplier with a finite verified zero-height premise, not an unconditional arbitrary-T estimate. No zero-verification certificate is imported or checked here; any application must establish its finite premise.

Mittermeier, *The Remaining Riemann-Hypothesis Tail*, Part3 v3, https://zenodo.org/records/22076071 . Local `mittermeier_part3_v3.pdf`, SHA256 74ee615e634490f8431bd6731411ef2e177025d1a00bcf2f35008506d77c6e26.
Abstract, p1: “That all-event inequality remains open. RH is not proved.” Root read Theorems4.3,4.6,5.6 and proofs, pp9-10,15-16. They give a positive local timing cost J, exact capacity C, and the upper bound integral min{Ppre,U_T(u)-A(x)}du/u. C>=that upper bound is still unpaid for all events.
Mapping: this paper's smooth A is our B; its weighted prefix W is our A; its frozen active reserve V differs from our clipped V_q. The scalar formulas preserve the source but do not discharge Q8's signed margin.
Correction to its equation75: R_T,a(u)-M_a(logu)=delta_T*sqrtu+d_T-Y(logu)+R'(logu), delta_T=c_T+e_T-2. The omitted R' is negative, leading term -(2/5)u^-5/2. Root checked this directly from B'=2sqrtu+c-R'; the independent checker found the same correction. It does not affect the asymptotic limitation below but must not be called exact without it.

## Checked bounded consequence

For fixed finite H and every admissible T<=H, delta_T>=pi/(H-1)>0. The Q8 unconditional asymptotic A(x)=2sqrtx+o(sqrtx) therefore implies U_T(x)-A(x)>=pi*sqrtx/[2(H-1)] uniformly eventually.
For any sequence q/x->1, Ppre=A(q-)-A(x)=o(sqrtx). Since U_T(u)-A(x) increases in u, its minimum with Ppre equals Ppre on all of [x,q], uniformly over T in [10^7,H], eventually. The pinned finite-height estimate is then EXACTLY the front-loading cap Ppre*log(q/x).
Root proof independently checked by growth_symbol_attempt: PASS. This rules out an asymptotic extra gain from fixed-height clipping on shrinking relative windows. It does not rule out front-loading itself, larger windows, or the original RH target. Increasing H without fresh finite-height verification is not licensed by Proposition9.1.
The abstract positive-arrival negative control and alias searches are in `docs/routeB_bus/source_observability_2026-09-28/SCALAR_DRIFT_ALIAS_RETURN_2026-10-07.md`. Multiplicative von Mangoldt structure is missing from that control; it is not a counterexample to the actual source.
