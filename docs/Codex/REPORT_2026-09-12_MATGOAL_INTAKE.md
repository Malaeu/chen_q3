# MATGOAL response intake — 2026-09-12

Status: ACCEPTED_PARTIAL_PAPER; parent and independent response checks complete.
Scope: isolated mathematical candidate, PAPER only. No Lean certification,
canonical writer admission, runtime takeover, phase change, or RH claim.

## Exact receipt

Request REQ-2026-09-12-MATGOAL, boundary
GOAL058_SOURCE_SPECIFIC_RH_PROGRAM_AFTER_SIBLING5, source base
7653a3503d20be4dba91a333ff96e5eea30c738c.
The response retains all six provenance phase fields of the request and states
that these do not admit a new mathematical phase.

Browser conversation: https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13-rh-marz-2026/c/6aa52001-4094-83eb-9520-01a09f54eff2
Natural completion displayed `25m 40s nachgedacht`, a full response and no Stop
control. The exact Markdown was downloaded through its visible download
button. Its 45178 bytes, 764 LF, final LF, and SHA256
`710c587ea317df581ba235aa17d3f248c096bdfd54a9af1fd122defd206a0706`
match the producer receipt. The downloaded bytes were copied unchanged to
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_MATGOAL_2026-09-12.md`.
Parent read all 764 lines. The producer file is immutable in this intake.

## Parent decisive checks

1. **G3 and the final criterion.** Read Suzuki's introduction and (3.3),
https://arxiv.org/html/2301.00421 , on 2026-09-12. With
`phi(t)=C_g(t)=integral g(x)conj(g(x-t)) dx`, `phi(-t)=conj(phi(t))`.
The pole integrals are `m_+ conj(m_-) + m_- conj(m_+)` and the two prime sums
combine to `-2 sum Lambda(n)/sqrt(n) Re C_g(log n)`.
The archimedean integrand is exactly
`||g-g(.-t)||_2^2 - 2(1-exp(-t/2))||g||_2^2` after reversing the original minus
sign. The second integral equals `log 2 + pi/2`: substitute `u=exp(-t/2)` and
use `1/((1+u)(1+u^2)) = 1/(2(1+u)) + (1-u)/(2(1+u^2))`.
Thus `c_A=gamma+log(8*pi)+pi/2` is correct. The source explicitly gives the
criterion on all complex compact smooth tests. This verifies G1-to-G2 with the
stated formula. It does not independently re-audit the inherited SLACK
V-to-Q transfer. At t=0 the **squared** translation norm is O(t^2).

2. **Physical normalization.** `t=exp(2x)` gives
`exp(5x) dx = (1/2)t^(3/2) dt`, so the unitary map and A are correct.
For `g_a=a^(5/4)r(at)`, substitute `y=as` in `(at)r(at)=(k*r)(at)`;
its scaled Volterra equation has no extra factor a, as in MV13.
In MV12 `x_i+x_j=(log a_i+log a_j)/2`; summing with complex coefficients
really gives `Re(conj(H)L)` with coefficient one, not two or one half.

3. **Ground-state correction.** The upper/lower triangle symmetrization
produces `j(s,t)=w(max(s,t))k(|t-s|)/2`. Its marginal at fixed t is
`(w(t)t r(t) + integral_t^infty w(s)k(s-t)r(s) ds)/2`.
This proves the MV4 sign and every factor of MV5. Tonelli and `Kr=tr` give
`integral integral j r r = integral t r^2 domega`. The absolute correction is
bounded by the same mass. Near zero, `2wr ~4*pi^2*t^-2 exp(-pi/t)`;
this yields the stated MV6 prefactor. At infinity the integral ratio tends
to `b_infty`; the given exponential majorant is integrable.

4. **Infinite negative index.** For the decreasing Gaussian, the right
Riemann sum of spacing sqrt(ell) is between the integral and the integral
minus sqrt(ell). Multiplication by two gives precisely MV7. The kernel
`|u-v|^-1/2` is bounded by Schur (norm at most4) and strictly positive by its
Laplace mixture of positive Fourier multipliers. Compactness of a unit
sphere in each finite-dimensional E gives alpha_E>0 without a uniform
infinite-dimensional spectral gap.
After the exact unitary rescaling, the weight ratio error is at most
`3 ell/(4a)`. The constant-kernel error has norm at most ell; the other error
is at most `(sqrt(ell)/2)*4*3ell/(4a)`. This is MV9.
With a=eps^2, ell=eps^3, all positive errors sum to
`eps^2 + 2eps^3 + (3/2)eps^(5/2) <= (9/2)eps^2 < 5eps^2`.
For eps=(alpha_E/20)^2, the positive term is
`(alpha_E/4)eps^(3/2)`, leaving the stated negative quarter.
Every dimension d is permitted with its own eps. A form of rank r has a
radical of codimension at most r; intersecting it with a negative space of
dimension r+1 proves the finite-rank obstruction.

5. **Scope.** MV proves an obstruction for the defined auxiliary q_V on
C_c^infinity(0,infinity). The negative spaces approach t=0. The exact V
consumer in MV12 integrates t>=1 and its different scale columns solve
different Volterra equations. No identity q_V=V and no sign conclusion for
original Q, V or the Connes-Consani operator is available. B1-B4 ratify only
the explicitly constructed F9 character, with the named analytic source
dependencies inherited from the earlier exact-character audit.

The proof is accepted by the parent at this limited PAPER scope pending the
separate reviewer. One wording correction: response line118 says the norm
is O(t^2); it is the squared norm appearing in G3 that is O(t^2).
The displayed mathematical formula and convergence claim are correct.

## Goal and remaining exact consumer

The target remains Q(g)>=0 for every complex compact smooth g, then the
classical Weil criterion. The selected intermediate input is the complete
SL20/DN20 form V_f for all finite real nodes and complex coefficients.
The inherited V-to-Q transfer remains an explicit dependency requiring a
full audit before any complete RH candidate can be accepted.
A new positive auxiliary energy without a verified map into this same V is
not a supplier. MV12 is the unchanged consumer, not positive progress.

The current mathematical no-progress repetition count remains0: this
response proves a new strict obstruction. This does not reset historical
killed classes or authorize rerunning them. The finite-field family result
is a separate PAPER theorem and supplies no archimedean comparison.

PX_RH_CLAIM: NOT_MADE.

## Independent response receipt

The sole read-only checker `/root/sibling5_check` returned ACCEPT for the
exact response SHA710c587ea317df581ba235aa17d3f248c096bdfd54a9af1fd122defd206a0706.
It independently rederived MV1–MV13, including every factor in MV5, the
weighted rescaling/MV9 constants, arbitrary finite negative dimensions and
the finite-rank intersection, and matched B1–B4 to its earlier character
audit. It explicitly inherited the source MV2/DN2 law and the SLACK transfer;
Suzuki/G3 was assigned to and checked separately by the parent above.
Thus ACCEPTED_PARTIAL_PAPER is limited to the exact MV theorem and identities
under those dependencies. No kernel or Lean verification was performed.
