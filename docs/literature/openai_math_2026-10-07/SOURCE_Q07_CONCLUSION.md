# Source Q7 — conditional parameter frontier; inverse-moment gain open

2026-10-09. Q7 terminal observed around 00:14–00:15 UTC in the same
Execute Joint Probe Calculation chat. All 971 lines of the downloaded original
were read. This is source question 7/10, not the exhausted CCM moment chat.

## Evidence and exact scope

Chat: https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd .
Request `PROSHKA_PERTURBED_SOURCE_Q07.txt`, sent 2026-10-08 23:34 UTC:
824191 bytes, 17542 LF, final newline,
SHA256 `a8f7efc908445fd8e8feb50b3f87297acb199195d1aac788c5d8715e6d7368c6`.
Source-work baseline `4bf1d047959d49e32f5b7c3883502d98b210a887`.
Original `PROSHKA_VERDICT_PERTURBED_SOURCE_Q07.md`:
88710 bytes, 971 LF,
SHA256 `55d909e213f484bb2b43e14d69f114e1fa68377bcde73f0fe77070514e806f58`.
Pinned source paper SHA256
`42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.
Original answer is preserved unchanged. No resend or Answer now.

The Q7 response accepts the own H1–H7 assembly at
sigma=349999/400000 **conditional on the source component lemmas**.
It explicitly does not independently certify all analytic proofs of the
source manuscript, its Hecke family ceiling, or a new unconditional zero-free
theorem. Linux zeta Comparator remains report-only; no Hecke import or Mac rerun.

## Conditional moment adaptation independently checked

Read-only `q05_moment_audit` checked Q7(35)–(37) against source lines
12531–14965, including the induction and parameter order: conditional PASS.
The printed lemma only allows kappa in [3/4,1]. Its proof can instead be
adapted to [2/3,1], with beta_* <= (1+kappa)/2 for kappa<1.
This is a proof adaptation, never a verbatim invocation outside the stated range.

The terminal width estimate uses z<=M/4 in place of 2M/9, while kappa*z<=M/6
preserves the loss rho/6. The comparison regime has z<M/18 and bounds
7M/9+xi and 17M/18+xi, each with margin M/18. Taking xi<=rho/36 before
the slot count preserves the comparison because M>rho there.
The prime contour starts at (1+kappa)/2>=5/6; its exponent stays kappa*z.
Slot deletion uses kappa<=1, and 3<=6kappa-1<=5 keeps the same uniform
affine defect bounds. Mesh is chosen before K; fixed-count constants and
the later height order may depend on K. No arbitrary row-dependent prime
coefficients or target-dependent mesh is admitted.

## Root exact arithmetic

`venv_djo/bin/python docs/literature/openai_math_2026-10-07/Q07_FRONTIER_EXACT_CHECK.py`
passes with SymPy 1.14.0. It verifies Q7(30),(38), both discriminants,
all four positive Bernstein minima, exact root isolation and uniqueness
throughout [1/6,167/1000], and the positive rational failed-iteration control.
This is exact algebra, not a numerical sampling argument or proof of the
analytic premises. Independent domain/transport audit is recorded below.

Read-only `long_positive_alias` independently PASS for the full low formula,
global Bernstein/monotonicity certificate, actual delta ceiling, fixed/free-b
frontiers and (44)→(45) localization. That audit treated the kappa extension
as conditional; the separate source-induction audit above supplies exactly
that adaptation, still conditional on the source's internal analytic inputs.
Far-left witness lengths have the existing (alpha-delta)(v-r) margin;
near-critical lengths fit in a fixed neighborhood after a small shift.

The fixed-b=1/8 budget frontier with the printed moment is
11/12-(1693+7sqrt(465053))/(4*38760) = 0.874957200615373761... .
With the adapted moment it is 11/12-ell_1/4 = 0.87495715035054...,
where ell_1 is the isolated quartic root in Q7(39)–(40).
Allowing b to vary gives the relaxed frontier 0.874957019420098946...,
with the cubic root in Q7(42). These are bounds of the specified sufficient
estimate, not lower bounds for the actual physical probe and not impossibility
theorems for an improved arithmetic estimate.

In particular ell=1/6+1/5000 already gives a positive high budget
189481/4936500000 at delta=29/75,x=1/2 with the old moment. The old margin
cannot be spent afresh in each iteration. The full low budget retains
rho(d)=(d+5ell-1)_+/4; its first-branch minimum is 13/15, so deleting this
cost and quoting the older relaxed 5/6 barrier would misstate the full problem.

## Next mathematical input

Q7(44) requests a power improvement for the ACTUAL inverse polynomials on
sixth-power-free source rows q_u~U, lengths D=U^r in a fixed neighborhood
of the critical r~1.1234:

    sum_u |M_u(U^r; W_{sigma_u,t_u})|^2
       << U^((1+5r)/6-theta+epsilon) (1+T1)^A, theta>0.

The source coefficients, zero masks, common orientation, fixed arithmetic
data and allowed rowwise profile parameters remain literal. Theta and the
neighborhood precede the target. This estimate is OPEN.
The proposed row-count gain is nu=(delta*P_kappa/J_kappa)*theta, about
0.247*theta near the critical bin, giving high-budget gain h*nu.

The next own attempt retains the sparse image {u*a^6} before source
positive extension to all rows q_v<=CH. The diagonal fits the requested
budget for small theta; its density alone does not control the energy.
Q7(47) is only the fixed-scale, common-profile off-diagonal. An estimate
there must also pay the scale supremum, D/q_d returns and profile derivatives
from the EXACT source identity (46), with no new coprimality restrictions.
No additional exponent is established by Q7.

Parameter tuning alone is STALLED. The chosen next mechanism is this
source inverse-moment improvement, within the same compensated-probe phase.
Do not multiply unrelated earlier partial gains together. No Q8 sent.
RH/SP and all unconditional source-premise obligations remain OPEN.

AUTOPSY: dropped=THEOREM_SHAPE; note=repeated geometric shifts exhaust the sufficient high budget near .874957; a new source-specific inverse-moment gain is still unproved.
