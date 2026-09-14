# ODDCURV intake — accepted fixed-compact tail, full sign open

Status: ACCEPT_SCOPED_INTEGRATED_CURVATURE_TAIL_ONLY.
Request: REQ-2026-09-12-ODDCURV.
Boundary: GOAL058_ACTUAL_THETA_INTEGRATED_ODD_KERNEL_LOG_CURVATURE.
Source base: 7653a3503d20be4dba91a333ff96e5eea30c738c.
Parent and sole independent checker have completed the PAPER audit.
No Lean certification, canonical writer admission or RH claim is made.

## Exact receipt

The ODDCURV response in the same mathematical chat
https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13-rh-marz-2026/c/6aa52001-4094-83eb-9520-01a09f54eff2
completed naturally and displays `20m 1s nachgedacht`.
The first scheduled completion observation was near 2026-09-12T11:27Z.
The exact generation-completion timestamp was not continuously measured.
The downloaded file was copied unchanged to
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODDCURV_2026-09-12.md`.
Parent read all 831 lines. Its 52645 bytes, 831 LF, final LF and SHA256
`3309c6fb3f5c3a0e20979c14b9a36471e753feed18a42017b4f211fafe6ea840`
match the producer receipt. Request, boundary and six provenance fields match.

The browser subsequently showed a new manually entered follow-up asking for
the complete IC/ODD2 result, followed by natural Pro reasoning and Stop control.
That is a separate pending continuation of this same mathematical question.
It does not invalidate the completed response or supply its missing sign.
No duplicate Codex request was sent into that busy conversation.

## Parent decisive checks

1. For `z_n=pi n^2 exp(2x)`, the full source is
   `f^(j)(x)=exp(x/2)/A sum P_j(z_n)exp(-z_n)` with
   `P_0=4z^2-6z` and `P_(j+1)=(1/2-2z)P_j+2zP_j'`.
   The degree is at most j+2. Bounding exp(x/2) by z_n^(1/4), then
   maximizing `z^(j+9/4)exp(-z/2)`, gives precisely the stated D_j.
   Summing the remaining exponentials using n^2-1>=3(n-1) proves (8).
   Evenness extends it to negative x. These are full-series bounds, including
   every fixed derivative needed by the later differentiations.

2. The V derivatives in (9) follow the product rule, with both derivatives of
   the linear factor included in V_st. Differentiating the reflected second
   argument changes the subtraction to addition in K_t and K_st, as in (10).
   For v>=R, every shifted absolute argument is >=v-R. The four kernel
   integrands are bounded by `4(1+R+v)(D0+D1)^2 exp(-pi exp(2(v-R)))`.
   With w=v-R, `1+2R+w<=(1+2R)exp(2w)` gives the explicit integrated tail (11).
   Smoothness on finite intervals and these local uniform tails justify
   differentiation and the double-integral Fubini identity (35).

3. In the full reflected formula (17), `z=exp(2v)-1` gives
   `dv=dz/(2(1+z))`. The ratio f(s+v)/f(s) contributes
   `(1+z)^(9/4)exp(-alpha z)H(alpha(1+z))/H(alpha)`.
   Their product is exactly the `(1+z)^(5/4)/2` in U and W.
   The coefficient of s is the difference f(t+v)-f(t-v); the rest is
   `(t+log(1+z))f(t+v)+(t-log(1+z))f(t-v)`.
   Thus (19) retains the full reflection and separates only nonzero factors
   depending on s or on t. They contribute zero mixed logarithmic derivative.

4. On a fixed B=[a,b] with a>0, min_B f>0. The definition of L_B controls
   U,W, their second z derivatives, the first z derivatives of U/(1+z) and
   W/(1+z), and the same expressions after one t derivative.
   For large z, all f arguments have absolute value >=v(z)-b, so (8) gives
   an exponential in -(1+z), uniformly in t. Polynomial/logarithmic prefactors
   and their z derivatives preserve decay. The required f derivatives have
   order at most three. Hence L_B is finite independently of the sign claim.

5. At z=0, `U=0`, `U_z=p/2`, `W=t`, `W_z=5t/4`.
   Taylor's integral remainder bounds P minus its affine part by
   `L_B(s+1)z^2/2`, and Q-t by `L_B(s+1)z`.
   The exact moments of exp(-alpha z) yield the first column of (24).
   The derivative `D=partial_s+2alpha partial_alpha` adds, respectively,
   coefficients 6+1 for R1 and 4+1 for R2. In R_E the E' contribution is
   at most `2L_B(s+1)alpha^-4`; the exponential and explicit-s derivatives
   add at most `3L_B(s+1)alpha^-5`.
   Differentiating the factor -3/(2alpha) in the combined R contributes too:
   its combined coefficient is 21/2, not 15/2.
   The total `7+21/2+2/alpha+3/alpha^2<20` proves (26) for
   R,R_t,D R,D R_t. The full E,E' estimates are inherited from accepted ODD2.

6. The exact affine terms give
   `I=t/alpha+(s p(t)/2-t/4)/alpha^2+R`.
   In particular -t/4 retains the source correction -3/(2q).
   With e=alpha R/t, differentiating alpha and 1/t is bounded by
   `60L_B(a^-1+a^-2)(s+1)/alpha^2`, as built into H_B.
   Thus q,q_s,q_t are at most `2H_B(s+1)/alpha` in absolute value and
   `q_st=(1/2-s)rho'(t)/alpha+e_st` has the stated controlled remainder.
   Under alpha>=4H_B(s+1), |q|<=1/2. The exact logarithmic formula
   `C=q_st/(1+q)-q_s q_t/(1+q)^2` gives error at most
   `[2H_B(s+1)+20H_B^2(s+1)^2]/alpha^2`, bounded by (14)'s constant24.
   The nonlinear cross term is retained; no unbounded remainder is
   differentiated formally and no score-integrability assertion is borrowed.

7. The accepted SLACK source explicitly supplies
   `J_f=t(f'^2-ff'')+ff'>0`; this is stronger than an abstract strict-concavity
   phrase. Direct algebra gives `rho'=(t p'-p)/t^2=-J_f/(t^2 f^2)<0`.
   Its continuous negative has positive minimum eta_B on the fixed compact.
   Since `(s+1)^2/(s-1/2)<=4(s+1)` for s>=1, the factor192 in (33) makes
   the constant24 error at most half the leading positive term. This proves
   `C(s,t)>=eta_B(s-1/2)/(2pi exp(2s))>0` for s>=S_B,t in B.
   Existence of S_B follows from exponential growth. It depends on B.

## Independent verdict and mathematical scope

The sole read-only checker `/root/sibling5_check` returned
`ACCEPT_SCOPED_INTEGRATED_CURVATURE_TAIL_ONLY` for the exact response SHA.
It independently checked (8), reflected signs, (19)'s Jacobian, L_B finiteness,
all four remainder budgets and the logarithmic/threshold constants24 and192.
It explicitly inherited the accepted E/E' tail input and the strict Csordas
J_f inequality. Parent also checked the accepted source's explicit J_f formula;
the historic source theorem was not re-audited instead of this new proof.

Accepted quantifiers:
`for each compact B subset (0,infinity), there exists S_B such that
 C(s,t)>0 for all s>=S_B and t in B`, and the symmetric strip.
There is no bound on the dependence of S_B on B sufficient to cover the whole
quadrant. The joint large-node, near-diagonal, near-axis and remaining finite
regions are not thereby covered. The ODD2 identity requires the entire square
[x,y]^2, so this result does not yet close a family of full ODD2 forms.

IC and ODD2 remain unproved and unrefuted. The owner counter changes 1 to 2,
without treating this partial theorem or the older transfer audit as a reset.
The producer's single 10-term, v<=1 diagnostic is uncertified and is unused
by both audits; it supplies no finite-cell sign certificate. It was not rerun.

The existing manually started full-sign continuation is pending. Receive and
audit its actual result before any new dispatch. A repeated absence of a full
ODD2 supplier counts as the third no-delta cycle; then the standing owner
instruction requires returning for the joint brainstorming discussion.
Transport waiting and receipt/review steps are not additional cycles.

PX_RH_CLAIM: NOT_MADE.
