# Shifted xi positive kernel: audited obstruction and own next test

Same full CCM growth phase; exact question6 is in HIGH_ZERO_TAIL_AUDIT.
Exact answer6: PROSHKA_SHIFTED_XI_KERNEL_INLINE_2026-10-06.md.
No RH/SP claim, no Lean run.

## Accepted scope after one bounded independent pass per part

growth_symbol_attempt checked sections1–4: E=xi(2-iz) kernel decay,
actual positive-row witness with height in [Omega/2,Omega], finite
observation-preserving lift cost, approximate-observation variant,
raw-transform nonmembership and truncated norm. No material finding.
Clarification: C,P mean ALL finite low rows through T=mL². If the
comparison norm also includes higher positive rows, add tau_m from
answer5; the superpolynomial-cost conclusion is unchanged.

causal_algebra_audit checked sections5–7: entire gamma-neutralized
generator, reciprocal Euler-product boundary bound, canonical diagonal,
tail and Lipschitz/grid budgets, zero-free entire gauge obstruction,
Hardy isometry and compression. No mathematical finding in those claims,
conditional on the rational enclosure and primary HB/model facts.
The adjoint identity is D=U*(I-Pi_Theta)U exactly; no inverse substitution.
Root read Lagarias Lemmas2.1(1),6.1(i), BBB section2.1 kernel/model
identification, DLMF5.4.3. Sources and hashes are in
docs/literature/shifted_xi_kernel_2026-10-06/README.md.

Root independently implemented and executed
 shifted_xi_diagonal_certificate_2026-10-06.py
using only Fraction arithmetic, positive atanh log series with a geometric
tail and cosine Taylor through degree200 with degree202 remainder.
It does NOT execute Proshka code. Result PASS: all35 prime powers,
stated head and log100 enclosures, v(10)<-3/100; exact upper
 -3980476992010243/131300000000000000.
This is reproducible rational PAPER evidence, not Lean/Arb validation.

## What is killed, and what is not

For the FIXED canonical E=xi(2-iz), every proposed all-source observation
lift has a carrier witness with norm cost / (||Cf||²+||Pf||²+s||f||²)
at least exponential exp(pi²m/(2L)) divided by a fixed polynomial
when s=Cm^eta. Thus no polynomial uniform comparison exists; the
finite source witness is not claimed to lie in ran B* or be a bottom mode.
Gamma-neutralizing Etilde=.5(2-iz)(1-iz)zeta(2-iz) gives a bounded
weighted boundary norm, but its proposed canonical kernel has diagonal
<-2 at a source frequency near10 on every cell L>=500pi.
This is NOT a negative CCM direction.

Every zero-free entire multiplier fails to repair Etilde's HB property:
its trivial zeros force upper-half-plane zeros of E0#/E0 with
Blaschke product at i bounded by3/(2N+3), contradicting a nonzero value.
Only this auxiliary class is killed; meromorphic completion and other
source maps are not excluded.

## Root own attempt on the proposed next test

The answer's model-space compression Pfrak=U*PiTheta U is independently
positive, but its proposed all-source-row defect on E=ran B* is not a
weaker supplier. Full proof: HARDY_DEFECT_OWN_ATTEMPT_2026-10-06.md.
For any fixed actual off-line zero delta+i gamma, delta>0, the exact
carrier Riesz vector b_m of its B row satisfies
 ||b_m||² ~ r m^delta/(2delta),
 liminf <b_m,(I-Pfrak)b_m>/||b_m||² >=1/2.
The right endpoint profile is translated to +infinity; multiplication
by the fixed unimodular Theta and P_+ preserves its limiting norm.
The cross term with the fixed left profile tends to zero; Fourier
projection error squared is O_w(m^delta L/m), explicitly paid.
Therefore ||(C op P op B)(I-Pfrak)Pi_E||²>=c_w m^delta on every late cell.
Under RH, B is empty and the defect is exactly zero. The all-eta
unbounded-good-cell defect target is thus RH-equivalent.
growth_symbol_attempt independently checked this new deduction once.
It is conditional on a hypothetical off-line zero, not an observed zero
and not an unconditional impossibility of the estimate.

The norm-transfer route has stalled on precisely this RH-strength
defect; a useful next mechanism must estimate the SIGNED source form
directly and pay its real remainder, rather than call a positive
auxiliary norm the Weil form.

## Bounded alias return and decision

polar_commutator_alias ran shelf-first ask.sh (INCOMPLETE freshness result,
not absence) and read Suzuki arXiv:2606.09096v3 (23 Sep2026), Theorem1.1
and (2.9)-(2.10). Root read those primary HTML passages and the existing
SUZUKI_SCREW_USAGE_CARDS. They give a LOCAL signed-form realization, not
fixed-PiTheta transfer or a positive sign; screw positivity is iff RH.
Do not infer global temperedness from continuity of g. The current
endpoint-jumping carrier also cannot simply be assigned an H1_0 domain.
Decision: fixed-positive-space norm transfer is STALLED. Keep the same
source/final consumer and attack the actual joint d,h arithmetic signed
matrix, paying its coherent cross-band/Schur interaction directly.

## Exact question7

Continuation 7/10, SAME full CCM negative-bottom-growth phase. Answer6 is audited. Fixed E=xi(2-iz) observation-preserving lift has superpolynomial cost; gamma-neutralized canonical kernel has negative late-grid diagonal; zero-free entire gauge repair fails. Root read Lagarias Lemmas2.1(1),6.1(i), BBB section2.1 and DLMF5.4.3. Root independently reproduced the 35-prime-power certificate with Fraction arithmetic (different code: no range reduction, log atanh series, cosine Taylor degree200): v(10)<=-3980476992010243/131300000000000000<-3/100. Clarification: C,P in the source norm are all finite LOW rows; including the high positive Gram adds only the accepted tau_m. No actual CCM negative direction or SP closure.

Own attempt on your proposed next test is now proved and independently checked. It exposes an RH-strength obstruction even AFTER restriction to ran B*, not just on unrelated top modes.
Fix a hypothetical actual off-line zero w=delta+i gamma, delta>0, multiplicity r. Its negative-row Riesz vector is h_L(t)=sqrt(2r)sinh(delta t)e^{-i gamma t}1_I, and the exact carrier vector is b_m=P_m h_L. Then ||b_m||²~r m^delta/(2delta), and ||h_L-b_m||²=O_w(r m^delta L/m), so the scaled projection error vanishes.
After shifting I to[0,L], m^{-delta/2}h_L is, up to a unit phase, sqrt(r/2)(a_L-ell_L), where a_L=e^{delta(x-L)}e^{-i gamma x}1_[0,L] tends to a right translate by L of a fixed negative-halfline exponential, while ell_L=e^{-(delta+i gamma)x}1_[0,L] tends to a fixed positive-halfline exponential. For ANY FIXED inner Theta, P_+(barTheta times Fourier(a_L)) has limiting squared norm1/(2delta): right translation moves all its L2 mass into positive time. Its cross term with the fixed left profile tends to zero by weak translation. Thus with D_m=I-U_m*PiTheta U_m,
liminf <b_m,D_m b_m>/||b_m||²>=1/2.
Eventually this row belongs to B, so b_m/||b_m|| is in ran B*. Selecting that output row yields
||(C op P op B) D_m Pi_{ran B*}||²>=c_w m^delta
on EVERY late original cell. Under RH, B is empty and the defect is zero. Therefore your proposed all-eta subpolynomial defect bound is ITSELF RH-equivalent. This is not an observed off-line zero or an unconditional kill; it records a stall of the fixed-positive-map norm-transfer strategy. Do not re-prove the same conditional separator, relax back to all-carrier norm transfer, or propose another fixed inner Theta: the argument covers every fixed inner function.

A bounded alias-hunt also found no sign supplier. Suzuki arXiv:2606.09096v3, Theorem1.1 and (2.9), gives the direct LOCAL signed identity Q_W^a(v)=int int g(x-y)v'(y)conj(v'(x))dxdy and Friedrichs realization. Root read it and the existing SUZUKI_SCREW_USAGE_CARDS; kernel positivity is explicitly iff RH. This is already-known source representation, not new compensation. Do not import global temperedness merely from continuity of g, or an H1_0 premise for our endpoint-jumping carrier.

DECISION: stop seeking an auxiliary positive norm as the supplier. Return to the ACTUAL signed arithmetic matrix from answer3, retaining the regular/exceptional reduction and repaired high-zero budget from answers4–5:
C_m=diag(d)+(1/pi)[diag(h),H_discrete],
d_j=(2/L)Re int_0^L Phi(omega_j;e^u)du, h_j=Im Phi(omega_j;m),
K_m=diag(a(omega_j))-C_m+E_m with the accepted bounded remainder.
Here Phi is the SAME joint prime-minus-pole primitive from answer3; all prime powers and I-R/pole pieces remain.

NEXT concrete test: execute a SIGNED relative-form / coherent-block cancellation estimate for this joint d,h source, restricted through the actual exceptional Schur if useful. Exploit the fact that d and h come from the SAME Phi; do not bound them separately by R_m or assume generic divided-difference positivity. The target is to pay the surviving neighbor/cross-band contribution against the actual diagonal slack and regular Schur correction, at a scale that improves the outstanding negative-bottom exponent. A weighted Hilbert/Cotlar or integration-by-parts identity is useful only if you actually estimate its remaining signed arithmetic term.

Keep the current full carrier, original schedule and all couplings. We already have a full floor m^(1/2-o(1)), a polylog floor outside codim O(m/L5), and a small full high-zero tail. Another density/rank/tail improvement, a necessary two-mode test alone, an abstract matrix counterexample, or a reformulation of SP as positivity will not change the plan. Return a proved source-specific signed estimate, or a proved obstruction to the specific estimate you actually attempted and the exact remaining arithmetic correlation. No plan-only response, no RH claim.

Question7 sent and browser-confirmed by 2026-10-06 21:58 UTC in the same
living Pro chat: full new message, Pro, ChatGPT antwortet, Stoppen, empty
composer. No resend. Next useful observation around 22:18 UTC.
