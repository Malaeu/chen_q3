# Independent PAPER audit: infinite-window CCM

STATUS: LISTED_CLAIMS_PAPER_CONFIRMED_POHOZAEV_IMPORT_WITHDRAWN_AND_APPLICATION_GAP
VERIFIER: PAPER
RH_PROVED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false

## Pinned source and scope

Source: `PROSHKA_VERDICT_CCM_INFINITE_WINDOW_2026-11-02.md`, inbox ref
`da3459f`, Git blob `e8bd22411090230102b353c7c22ea25c314dde51`.
SHA-256 verified before import:
`91e1928f76d192083263cc6d83a8e2bcafbd5a23881ac37a69f4050b1f63b600`.
The 47,664-byte source has 566 lines. Canon and mirror were imported unchanged
in `b101cb9b15f0c42d113d3de24c96a984848387ff`, parent
`5d42ac5cc90d27d7ef94099f99922af6fd8dc982`.

The owner's requested equation numbers (2)--(14) do not occur under those
labels in this pinned file. This audit follows the explicitly listed claims,
using the actual equation labels and one-based source line numbers below.
The listed boundary, atom-birth, and Lipschitz claims occur in source sections
4--5, beyond its literal sections 1--3. Source sections 6--9 are not audited.
No source formulas, route status, or numerical diagnostics were changed.

## Item-by-item verdicts

| Requested claim | Actual source location | Verdict |
|---|---|---|
| (2): symbol bounds | (2.2), lines 115--127 | CONFIRMED |
| (3): closedness and lower bound | (2.3), lines 129--133 | CONFIRMED |
| (4): compact embedding, attainment, compact resolvent | (2.4)--(2.5), lines 138--158 | CONFIRMED |
| (5): lambda_N decreases to lambda_infinity | (2.6), lines 162--169 | CONFIRMED |
| (6): support monotonicity | (3.1), lines 175--184 | CONFIRMED |
| (7): eigenfunction L-infinity estimate, constant 1/2 | (4.1)--(4.3), lines 190--231 | CONFIRMED |
| (8): half log-Laplacian plus bounded remainder | (4.6), lines 259--270 | CONFIRMED |
| Boundary theorem applicability with all shifts and pole | (4.7), lines 272--280 | CONFIRMED |
| Requested (9), (11), (12): boundary estimate, zero trace, collar/correlation consequences | (0.1)--(0.2), (4.4)--(4.5-new), (4.8), lines 235--301 | CONFIRMED |
| (13): new-atom contribution o(epsilon) | (5.2-new), lines 349--359 | CONFIRMED |
| (14): local Lipschitz continuity | (5.1-new), lines 314--345 | CONFIRMED |

No ERROR was found in these listed source claims. This confirmation does not
provide a Pohozaev identity, a normalized trace limit, or a full eigenfunction
Hadamard formula.

### Symbol, form, compactness, and Galerkin limit

The kernel inequalities in line 125 are correct. The principal integral gives
one half log(1+4t^2), and the remaining contribution is at most
2 integral exp(-s/2)(1-cos(ts)) ds <= 4. Fourier normalization is consistent.

The ambient Hilbert space is the even L2 space on the fixed interval.
Support and parity are closed constraints; the nonnegative Fourier multiplier
gives a closed form. Each compressed shift is an L2 contraction, with
|Q_f(a)|<=2||f||_2^2. The pole is bounded positive rank one. Thus the displayed
lower bound holds. Completeness is in the form norm, not closure of the
domain in the unweighted L2 norm.

The high-frequency bound (2.4), fixed support, and low-frequency translation
estimate establish Kolmogorov--Riesz compactness. Strong L2 convergence of a
minimizing subsequence preserves norm, parity, and support. Lower
semicontinuity of A and continuity of the bounded perturbations give
attainment and compact resolvent.

The Fourier form core is verified in Connes--Consani--Moscovici,
*Zeta Spectral Triples*, Proposition 3.4. Proposition 3.2 identifies the
logarithmic coordinate/window normalization L=2 log(lambda). Reflection
preserves the form, so even projection preserves this core. Nested finite
sections therefore converge downward to the full bottom. This is a fixed-L
limit, not an interchange with a varying-L diagonal.

For L1<L2, zero extension embeds the full smaller form domain in the larger
one without changing the global form value. Newly available atoms have zero
correlation on an old support. This proves (3.1), without positivity or RH.

### Semigroup estimate

The correct positive operator is J_L, not the signed full K_L. The killed
jump semigroup is sub-Markov and dominated by its whole-line counterpart.
Its time-one kernel satisfies

    ||p_1||_2^2 <= (1/(2*pi))*integral_R (1+4t^2)^(-1) dt = 1/4.

Hence its L2-to-L-infinity norm is at most 1/2. The Duhamel identity (4.3),
L-infinity contraction, and the rank-one pole bound give exactly U_L(lambda).
The pole norm squared is L+2 sinh(L/2). No positivity of the eigenfunction
or the semigroup of K_L is assumed.

### Boundary reduction and consequences

In one dimension c_1=1 and rho_1=-2 gamma. The remainder in (4.6) is explicitly

    R_L f(x) = integral_0^infinity r_0(s)[2f(x)-f(x+s)-f(x-s)] ds
             + (1/2) integral_1^infinity [f(x+s)+f(x-s)] ds/s + gamma*f(x),

with zero extensions. Its L-infinity norm costs at most
4R_0+log_+(L)+gamma. The symmetric-kernel Schur estimate also gives L2
boundedness and equality of the form domains.

The finite sum of shifted functions costs at most 2S_L U_L. The pole costs
P_L and the remainder costs R_L U_L, giving the displayed V_L. The even weak
equation holds for general tests as well: odd-test pairings vanish by parity.

Hernandez-Santamaria--Lopez Rios--Saldana, Theorem 1.1, applies in N>=1 to a
bounded open set with uniform exterior sphere condition, a bounded forcing,
and a bounded weak solution in H(Omega), zero outside. An interval and the
reduced CCM equation satisfy these hypotheses. The theorem needs neither a
local nonlinearity nor positivity of this solution or of the full operator.
It gives global continuity and the logarithmic boundary upper bound. Scaling
to the unit interval and the supplied closed-graph argument justify the
fixed linear graph-norm constant in D_L. Zero exterior values then force
the ordinary endpoint trace to vanish.

The overlap at displacement L-delta has length delta. The two boundary
factors and the correlation normalization yield exactly (4.8), including its
factor 2. Thus the endpoint difference quotient tends to zero; no claim
about convergence of interior correlation derivatives is needed. Constants
are locally uniform in L and in bounded eigenvalue ranges.

For the omit-one-atom comparator, the same estimates hold. Applying each
minimizer in the other Rayleigh quotient proves the o(epsilon) atom-birth
bound without simplicity.

For Lipschitz continuity, boundedness and finite energy permit the indicator
cuts. Stationarity gives line 324. The singular near-cut rectangle integrates
to 2 delta log(2); boundary decay controls it. The remaining singular region
is O(delta) by lines 339--343. Prime and pole cross-terms are smaller, and
the retained mass stays bounded away from zero. This proves the stated
locally uniform Lipschitz estimate.

## Literature check: arXiv:2411.15985, Theorem 2.3

Correction (2026-11-02): the earlier audit read v1 but missed the current
arXiv withdrawal notice. Version 2, dated 26 April 2025, withdraws the paper
because of a crucial error in the Pohozaev proof. Verified at
https://arxiv.org/abs/2411.15985 . Theorem 2.3 v1 is therefore NOT an accepted
theorem supplier, even if its stated hypotheses were established. The
hypothesis comparison below describes the withdrawn statement only. The
independent form and boundary-theorem checks above are unaffected.

Verdict: INVALID_IMPORT (withdrawn) and GAP -- the v1 statement does not apply
to the current CCM package solely
from bounded shifts/pole and the boundary upper estimate.

Theorem 2.3 of Arora--Giacomoni--Vaishnavi is stated for N>=1, a bounded
C^{1,1} domain, and u in H(Omega) intersect L-infinity, with zero exterior
values encoded in H(Omega). Its additional hypotheses are:

1. At each boundary point the interior limit of u(y)^2 log(delta(y)^(-2))
   exists; the resulting weighted boundary integral against x dot nu is finite.
2. L_Delta u is pointwise bounded in Omega.
3. The weak equation is L_Delta u=f(x,u), where f(.,t) is Lipschitz on the
   closed domain for almost every t, and f(x,.) is continuous locally on R
   for almost every x.

No positivity or star-shapedness assumption is imposed in Theorem 2.3 itself.
An interval satisfies its geometric condition. H-membership, boundedness,
and zero exterior data are confirmed here. The other checks are:

| Hypothesis | Status for the audited CCM equation |
|---|---|
| Existing logarithmically weighted boundary limit | GAP: source lines 303--308 explicitly establish only a bound, not existence of the limit. Ordinary zero trace does not supply this limit. |
| Pointwise bounded logarithmic Laplacian | GAP: (4.7) supplies bounded weak forcing. A classical pointwise realization is not established. The boundary paper itself distinguishes these notions. |
| Local RHS with Lipschitz x-dependence | GAP: shifts and R_L are bounded operators but are not local multiplication nonlinearities. Freezing a particular solution produces a forcing function whose Lipschitz regularity has not been proved. |

The rank-one pole, once its scalar coefficient is fixed, is smooth in x on
the interval and is not itself the regularity obstruction. The shifted terms
and the bounded remainder still require the missing regularity checks.
These are unverified hypotheses, not a claim that every CCM eigenfunction
necessarily violates them. An abstract extension covering arbitrary bounded
nonlocal perturbations is not supplied by the cited theorem.

In dimension one the boundary integral is an endpoint sum, with x dot nu=L/2
at both endpoints of the centered interval. It uses the weighted limiting
trace, not the ordinary value u=0. Consequently the boundary decay result
cannot be used to declare the Pohozaev boundary term zero.

## Primary references

1. Connes--Consani--Moscovici, *Zeta Spectral Triples*, Propositions 3.2--3.4:
   https://arxiv.org/html/2511.22755v1
2. Hernandez-Santamaria--Lopez Rios--Saldana, *Optimal boundary regularity and
   a Hopf-type lemma for Dirichlet problems involving the logarithmic
   Laplacian*, Theorem 1.1, section 4 and Appendix A:
   https://arxiv.org/html/2401.18033v2
   Published DOI: https://doi.org/10.3934/dcds.2024084
3. Arora--Giacomoni--Vaishnavi, *Nonlocal elliptic equations involving
   logarithmic Laplacian: Existence, non-existence and uniqueness results*,
   Theorem 2.3:
   https://arxiv.org/html/2411.15985v1

This is an independent PAPER review of the listed source arguments and
published/preprint theorem hypotheses. It supplies no RH bound, normalized
trace limit, or additional support-variation theorem.
