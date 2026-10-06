# Full joint Hilbert estimate: answer3 audit and own block preflight

Exact answer: PROSHKA_JOINT_HILBERT_INLINE_2026-10-06.md.
Exact question3: ENDPOINT_FACTOR_AUDIT_2026-10-06.md.
Same full complex V_m, m=N, L=log m, original consecutive tail schedule.
SP/RH remain OPEN; no Lean run or RH claim.

## Accepted after bounded independent checks

causal_algebra_audit checked (2)-(7),(14)-(22): exact shift matrix, joint
signed measure, Hilbert commutator sign, norm<=pi independent of dimension,
archimedean boundary norm<=20 (including L=1: bound<19.19), all endpoints,
full complex carrier, separated blocks and consumer quantifiers.

growth_symbol_attempt checked (8)-(13): half-integer sharp Perron cutoff,
uniform twist error, zero-free contour, near/far zero sums including zeros
beyond U, residue and lower endpoint, all y and all frequencies, and c=.001.
An initial sign-typo report was withdrawn after rereading the denominator:
Lambda(n)/n^(s+1/2+i omega) is already the correct coefficient.
Root independently fetched/read MTY Thm1.1 p2 and HSW Cor1.2 p2; URLs,
hashes and exact mapping are in docs/literature/joint_hilbert_2026-10-06.

The actual signed measure is
 dnu=sum_(n<=m) Lambda(n)/sqrt(n) delta_log(n) -(exp(s/2)-exp(-s/2)) ds.
Let Phi(omega;y)=integral_[0,log y]exp(-i omega s)dnu(s),
 R_m=sup_(|omega|<=2pi m/L,1<=y<=m)|Phi(omega;y)|.
For omega_j=2pi j/L, h_j=Im Phi(omega_j;m),
 d_j=(2/L)Re integral_0^L Phi(omega_j;exp u)du,
 C=diag(d)+(1/pi)[diag(h),Hdiscrete], ||C||<=4R_m.
This pays all dimensions and cross terms at once.

With t(L)=(L/log L)^(1/3), c=.001, eventually
 R_m<=C sqrt(m)L³ exp(-c t(L)),
 lambda_min(K_m)>=-cA-4R_m,
 <f,D_F f><=(4R_m+2L)||f||².
The arithmetic input is the unconditional shrinking zero-free region;
its width tends to zero. Thus the exponent remains 1/2-o(1), not o(1).
Every fixed inverse logarithmic power is gained, but SP is still OPEN.

The archimedean matrix differs from diag(a(omega_j)) by norm<=20.
For low |j|<=q and top Q<=|k|<=m, Q>=q+2,
 ||P_low K P_top|| <=2(R_m+8)/pi sqrt(2(2q+1)/(Q-q-1)).
This tends to zero for q=floor(L^A), Q=ceil(m/2), every fixed A.
No middle or neighboring-frequency term is discarded or paid at SP scale.

## Own attempt: block centering and the actual scale limit

For any index block I, restrict the discrete Hilbert matrix to I.
Since constants commute, for any real b,
 ||T_II|| <=2 max_(j in I)|h_j-b|.
Taking b=(max_I h+min_I h)/2 yields the exact sufficient bound
 ||T_II||<=osc_I h.
Thus if q_j=a(omega_j)-d_j+r and min_I q_j>=osc_I h,
 diag(q)_II-T_II is PSD. This does not establish the inequality for
our source: neither this diagonal slack nor local oscillation is controlled
at subpolynomial scale. Blockwise constants cannot be subtracted from
cross-block entries: their differences produce additional off-diagonal
terms which must remain. This is the precise failed own attempt, not a
new supplier or a theorem-shape kill for the source.

For the already proved low/top estimate, set E(L)=exp(c t(L)).
Its envelope is O(L³ sqrt((q+1)/E(L)²)) when Q=ceil(m/2), q=o(m).
So it pays low/top coupling for q=o(E(L)²/L^6); for example
q=floor(E(L)/L^8) gives O(E(L)^(-1/2)/L)=o(1).
The first displayed q is sufficient for the envelope, not a necessary
condition on the actual source. For q=m^theta, theta>0, this upper envelope
diverges; divergence does not prove actual coupling large. It identifies
why the same absolute-value estimate cannot eliminate macroscopic bands.

## Remaining target

T=(1/pi)[diag(h),Hdiscrete], S(r)=diag(a(omega_j)-d_j+r).
For every eta>0 need unbounded original good cells with
 S(C_eta m^eta)-T>=0 on the WHOLE carrier on the same cell.
Equivalence to SP costs only cA+28; it is not counted as progress.
Pair determinants are necessary only. Next attack retains signed divided
differences and actual diagonal slack across contiguous/neighboring bands.

## Alias return and exact question4

Boundary Pick source read and algebra checked by root after researcher report:
docs/literature/polar_boundary_pick_2026-10-06/README.md. It is equivalent
to the missing PSD, not a supplier; derivative upper caps, not equality.
Shelf status INCOMPLETE; no absence claim. No new mechanism selected from
the alias alone. Continue the signed joint matrix on neighboring bands.

Continuation 4/10, SAME full CCM negative-bottom-growth phase. Answer3 is processed: independent matrix audit accepted (2)-(7),(14)-(22); independent arithmetic audit accepted (8)-(13), including zeros beyond U, all cutoffs/frequencies, endpoints and constants. Root fetched/read MTY arXiv2212.06867 Theorem1.1 p2 and HSW arXiv2107.06506 Cor1.2 p2; hypotheses map correctly. No sign correction is needed in Perron: n^(s+1/2+i omega) is in the denominator. The exact full-carrier bound sqrt(m)L³ exp(-.001(L/logL)^(1/3)), arch remainder20, and low/top coupling are accepted PAPER progress. SP/RH remain OPEN.

Own attempt before this question:
For any contiguous block I, constants commute with the compressed discrete Hilbert matrix, hence
||T_II|| <= 2 inf_b max_(j in I)|h_j-b| = osc_I h.
Thus min_I[a(omega_j)-d_j+r] >= osc_I h is sufficient for the diagonal block. Neither side is controlled at the required scale for our source. Centering separately on blocks does NOT remove cross-block constants: their differences remain in (h_j-h_k)/(pi(j-k)).
Writing E(L)=exp(c(L/logL)^(1/3)), your low/top envelope for Q=ceil(m/2) is O(L³sqrt(q+1)/E). It works even for q=floor(E/L^8), but not as an estimate for q=m^theta, theta>0: the ENVELOPE diverges (not a lower bound on actual coupling). It therefore cannot remove the bulk by repeated use of the same R_m norm estimate.

Bounded alias-hunt return: the exact matrix S(r)-T is a boundary Pick matrix. Put u_j=-h_j/pi, t_j=(j-i)/(j+i), w_j=(u_j-i)/(u_j+i), c_j=(j+i)/(u_j+i), gamma_j=|c_j|²q_j, q_j=a(omega_j)-d_j+r. Then P=diag(c)(S-T)diag(c)*. Bolotnikov–Kheifets, Boundary Nevanlinna–Pick interpolation problems for generalized Schur functions, author PDF https://www.math.wm.edu/~vladi/ot165.pdf, section1 pp2-3 (1.5)-(1.7), gives equivalence to a Schur interpolant with those boundary values and derivative UPPER CAPS. It constructs the interpolant from PSD, so it supplies no independent arithmetic positivity. Equality derivative interpolation has stricter conditions; do not substitute it. Generic negative control h_j=j and q_j=q gives S-T=(q+1/pi)I-11*/pi and eigenvalue q-(2m)/pi, so generic positive slack or divided-difference structure is insufficient. Shelf search was INCOMPLETE, not absence.

NEXT task: advance the remaining signed matrix comparison using the actual relation between h_j and d_j, not their separate maxima. Work on contiguous and neighboring frequency bands that include the unresolved middle, keep their cross terms, and return an actual source-specific one-sided inequality against q_j=a(omega_j)-d_j+r. The decisive requested result remains: for every eta>0 there are arbitrarily large ORIGINAL m with S(C_eta m^eta)-T>=0 on the whole complex carrier of that ONE cell.

Choose and execute a concrete weighted block/Schur or analytic positive-kernel attempt; any Pick/Herglotz construction must be produced independently from the prime/pole data and prove the derivative caps, not assume the target PSD. Pay block-gluing and zero diagonal pivots. It is useful to close a genuine intermediate estimate if it controls a remaining neighboring/bulk interaction at a better scale with a precise path to the consumer. Another replacement of R_m by an absolute maximum, a 2-mode necessary test alone, improved constants in the shrinking zero-free region, or a circular Pick interpolation criterion will not change the plan. If the proposed signed mechanism fails, give its exact source-specific obstruction or exact unsupplied hypothesis and one distinct mathematically justified next step. Preserve full W, I-R, all prime powers, endpoints, m=N, and original schedule. No RH claim.

Question4 sent around 2026-10-06 20:20 UTC to the same living Pro chat.
Browser readback: complete question4, model Pro, ChatGPT antwortet,
Stoppen, empty composer. Next observation around 20:40 UTC or completion.
Do not resend. Answer3 supplement download was not established; all accepted
claims above refer to the complete inline answer and independently read PDFs.
