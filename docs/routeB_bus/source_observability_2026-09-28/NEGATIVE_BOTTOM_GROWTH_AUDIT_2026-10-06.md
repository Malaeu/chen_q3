# Negative bottom growth: answer10 audit and next mathematical attempt

Source: `PROSHKA_NEGATIVE_BOTTOM_NORMING_INLINE_2026-10-06.md`.
Same literal full K_m, carrier |n|<=m, L=log m, original eventual sequence.
All statements involving w=delta+i gamma with delta>0 are CONDITIONAL on
such an off-critical zero of xi(.5+w). No such zero is asserted.

## Answer10: source pair and original-carrier projection

The old source-pair separator is in
`../proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md`, D25-D28.
The current source G=-4 Phi does not change its normalized functions:
J_w v(t)=exp(-wt) integral_(-infinity)^t exp(wu)v(u)du,
M_(J_w v)(z)=M_v(z)/(w-z),
d_w=(-1)^r M_G^(r)(w)/r!, H_w=J_w^r G/d_w.
At w the normalized transform equals1; at every other distinct zeta zero
it is0. The reflected partner is wdagger=-conj(w). For
u_b=exp(-ib gamma)tau_b H_w-exp(ib gamma)tau_(-b)H_wdagger,
the FULL signed zero formula gives W(u_b,u_b)=-2r exp(2 delta b).
The L2 bound D=2(||H_w||2^2+||H_wdagger||2^2) is independent of b.

Proshka's new part uses a=L/2, b=(a-1)/4, f_a=chi_a u_b, where chi has
fixed-width transitions and fixed derivative bounds. Its complete-form
compactification error is <=3000 B exp(-(a-1)/4). Uniform fixed third
L1 derivative of f_a gives an E-norm projection error

 E3=C3[(m+16)/(5 pi) Omega^-5+2/(3 pi) Omega^-3
         +2/(pi^2) Omega^-4]^(1/2), Omega=2 pi m/L.

E is the weighted integrated-translation norm of the Sept12 audit, not the
Sept26 Holder-translation norm. Both zero-extension jump strips are paid.
The Fourier-form error is O(m^(-11/8)L^(3/2)). Consequently the proposed
new statement is lambda_min(K_m)<=-c_* m^(delta/4) on every late original
cell, and rho_m<=epsilon_m/(c_* m^(delta/4)). Projection audit accepted by the bounded independent pass below.

The pair auditor accepted normalization, multiplicities, translation phases,
tails and the L2-density cross-check: any negative compact test forces
lambda_min(K_m)->-infinity. The latter uses approximation by radical
translates in L2 followed SEPARATELY by compactification in the form norm.
It does not conflate the topologies or prove a negative test exists.

## Root refinement, independently checked: use more of the window

The following is not in answer10. If |v(t)|<=C exp(-c exp(2|t|)) and
M_v(w)=0, use the left integral for t<=0 and the right integral for t>=0.
For s>=0 and either sign of t,
exp(2(|t|+s))>=exp(2|t|)+exp(2s)-1. Hence

 |J_w v(t)|<=C exp(-c exp(2|t|))
             integral_0^infinity exp(|w|s-c(exp(2s)-1))ds.

The integral is finite and independent of t. Repeated J_w therefore retains
fixed double-exponential tails; the ODE (partial+w)J_w v=v gives derivative
tails as well. Constants depend on the fixed zero and its multiplicity.
There is no uniform conditioning assumption on zeros.

Now set h=log L, b=a-h, for sufficiently large L. On the cutoff transition
and exterior, each translated source has |t-(+/-b)|>=h-1. Weighted tail
integration (y=exp(2|x|)) and the paid cutoff derivative give

 ||(1-chi_a)u_b||_E<=C exp(b) exp(-c' L^2),
 ||u_b||_E<=C exp(b),
 |W(chi_a u_b)-W(u_b)|<=C m exp(-c' L^2).

Here and below W(v) abbreviates W(v,v); constants may change but are fixed
in m. Uniform fixed-order unweighted derivative norms of chi_a u_b remain
valid, so the SAME E3 above is O(m^-3/2 L^3/2). Since ||f_a||_E<=C sqrt(m),
the Fourier-form error is O(m^-1 L^3/2). Both errors vanish, while exactly

 W(u_b)=-2r m^delta L^(-2delta).

Orthogonal projection still gives ||P_m f_a||2^2<=D. Thus the candidate
strengthening is lambda_min(K_m)<=-c m^delta/(log m)^(2delta), hence
<=-c_eta m^(delta-eta) for any fixed 0<eta<delta on every late original
cell. This is a conditional adverse alternative, NOT a lower bound and
NOT a counterexample to RH. The pair and projection passes accepted the required tails and budget.

## Next source estimate and own attempt, not a supplied theorem

The checked adverse alternative shows it is enough to prove that
(-lambda_min(K_m))_+ grows subpolynomially: for EACH eta>0 it is at most
C_eta m^eta eventually. A uniform constant lower bound would also suffice.
This would be a NEW terminal consumer on the same K, not retroactive
closure of the old G1/G3 ground-transform constructors. The bound is OPEN.

Existing semiboundedness is only fixed-window. The Sept4 sign-free Ritz
verdict explicitly gives a deteriorating O(sqrt(m)log m) envelope;
`D0PstarSourceWeilSesquilinearForm.lean` also has a cutoff-dependent lower
bound constant. Neither provides the needed uniform/subpolynomial bound.

Our coarse direct calculation agrees. With cA=gamma+log(8 pi)+pi/2,
W=D_arch-cA||f||2^2+W02-Prime. The pole form equals
2(|integral cosh(t/2)f|^2-|integral sinh(t/2)f|^2), so

 W02>=-[sqrt(m)-m^(-1/2)-L]||f||2^2,
 Prime<=2 sum_(n<=m) Lambda(n)/sqrt(n) ||f||2^2.

Dropping nonnegative D_arch gives lambda_min>=-cA-(1+4L)sqrt(m).
This is exponent1/2, not subpolynomial; no new source bound is claimed.

The exact joint pole/prime rewrite retains their cancellation. Define
Q_f(s)=2 Re integral conj(f(t))f(t+s)dt, E(x)=psi(x)-x+1,
A(x)=x^(-1/2)Q_f(log x), where psi includes all prime powers. E(1)=0 and
A(m)=0, so Stieltjes integration by parts gives

 W(f)=D_arch(f)-cA||f||2^2+integral_0^L exp(-s/2)Q_f(s)ds
       +integral_1^m E(x) A'(x)dx.

The remaining continuous correlation term is nonnegative, with Fourier
multiplier 1/(1/4+omega^2). The final signed arithmetic correction has NO
proved subpolynomial lower form bound. This is the known Chebyshev-primitive
representation, not a new sign or a reason to replay the old selected-plane
primitive loop. Any next question must attack an actual estimate of joint
pole/prime action, not rename this missing inequality.

## Independent dispositions and phase decision

Read-only Luna researcher answer10_pair_audit accepted the source-pair signs,
multiplicities, -4 normalization, full zero formula, ordinary-L2 translate
density and its separate form-norm compactification. It also gave an explicit
safe tail exponent c=pi/2^(r+1) for H,H' after repeated J and division by d_w.
The root estimate above preserves c via another elementary bound; only
existence of a fixed c>0 is used. Fixed higher derivative integrability is
inherited from the smooth source construction/ODE and checked for C3.

Read-only Luna researcher answer10_projection_audit accepted (1)-(3), the
fixed-width cutoff constants, uniform C3, E3, original diagonal projection,
negative Rayleigh quotient direction, and norming consequences. It also
checked the root improvement conditional on those H,H' tails, now supplied
by the independent pair pass. Both distinct inputs hold simultaneously.
The same pass checked the coarse lower bound and exact Stieltjes identity;
no lower bound on the arithmetic correction was obtained.

Opaque Suzuki citation tokens in the source answer were not used as a new
unconditional input. The already checked full complex-test Weil criterion
and exact CCM restriction supply the consumer. No Lean build or RH claim.

The old Missing T7 Lemma chat is complete at10/10 and closed to new sends.
Direct overlap is STALLED: no lower rho, no OS, no G1/G3 closure. The bounded
norming-weight alias search found a representation and an inapplicable PDE
analogue, not a supplier; see `WEAK_OVERLAP_SPECTRAL_MEASURE_2026-10-06.md`.

Select one next mathematical phase: control negative-bottom growth on the
SAME full CCM family, exploiting joint pole/prime cancellation before norms.
This is an explicit terminal-consumer change after the recorded stalls, not
a silent substitution of a different trial/ground family. It does not mark
any old G1/G3 constructor proved. Owner authorized route/consumer choices;
only PX_RH_CLAIM remains owner-only.

phase_key:
  route_id: ROUTE_B
  front_id: FULL_CCM_NEGATIVE_BOTTOM_GROWTH
  source_object_family_id: CCM_FULL_N_EQ_M_ORIGINAL_COFINAL
  terminal_consumer_id: FULL_WEIL_CRITERION_VIA_SUBPOLYNOMIAL_NEGATIVE_BOTTOM
  honesty_state: CHALLENGER_NOT_RH
  convention_lock_id: W02_MINUS_WR_MINUS_ALL_PRIME_POWERS_PHASED_LOG_WINDOW

New missing assertion: for every eta>0 there is C_eta such that on every
sufficiently late original cell, lambda_min(K_m)>=-C_eta m^eta. This is OPEN,
not a literature theorem and not an inference from fixed-window lower
semiboundedness. RH would make it true trivially; no RH premise is allowed.
The signed Chebyshev expression above is inherited, not progress by renaming.
One next proof attack must estimate the actual full joint term, or identify
a proved source-specific obstruction. No continuation11 in the old chat.
