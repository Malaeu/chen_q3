---
TASK_ID: LINUX_SELF_CORRECTION_9
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
CORRECTS: 5a02a6fd, section 6 (two framing claims)
RH_CLAIM: false
---

# Correction 9 — the measure does not annihilate anything; the diagnosis was premature

## 1. Withdrawn: "mu_beta annihilates smooth test functions"

Report `5a02a6fd`, section 6, wrote that `mu_beta` "is by construction the finite
explicit formula, so it annihilates smooth test functions". Too fat, and wrong as
stated. `mu_beta` is assembled from **positive** densities and **positive**
von-Mangoldt atoms. For any smooth non-negative `G`,

    integral G d mu_beta > 0.

No annihilation occurs. The cancellation the route depends on comes from a
different place entirely: the **antisymmetry of the test function** under the
reflection `R(t) = 2 pi - t`. Since the modes are integers,

    sin(n(2 pi - t)) = - sin(n t)   =>   G(R(t)) = - G(t),

and therefore, exactly,

    integral G d mu = (1/2) integral G d( mu - R_* mu ).

The right object is the **signed reflection discrepancy** `mu - R_* mu`, not the
measure itself. Its total mass is zero, which is what makes cancellation
possible; `mu_beta` alone has mass of order `sqrt m` and cancels nothing.

## 2. Withdrawn: "the load-bearing gap needs mode-index control of x"

Same report, sections 6-7, concluded that the missing supplier is the behaviour of
`x_k(z) = C_k^{-1} kappa_k(z)` as a function of the mode index, on the grounds
that the catalogue bounds `x` only in norm. The conclusion does not follow, and
the reason is the rank-one structure of the Hilbert commutator, which I had in
hand and did not use:

    [N, H] = eta eta^T - I,   N = diag(n_i),   eta = (1,...,1).

Off the diagonal `(n_i - n_j) H_ij = 1`; on the diagonal both sides vanish.
Duhamel for `U_t = exp(i t N)` then gives, exactly,

    [U_t, H] = i integral_0^t U_s (eta eta^T - I) U_{t-s} ds,

so that

    hat omega(t) = <x, [U_t,H] q>
                 = i integral_0^t <x, U_s eta> <eta, U_{t-s} q> ds - i t <x, U_t q>.

Both factors are trigonometric polynomials. Their `L^2` norms in `t` are
`sqrt(2 pi) ||x||_2` and `sqrt(2 pi) ||q||_2`; differentiating the second brings
down `n_i`, giving `||N q||_2`. So a regularity budget for `hat omega` is bought by

    ||x||_2      — already available, it is the normalization,
    ||N q||_2    — the mode energy of the *trial*, an object we construct.

No pointwise control of `x` by mode index is required. The diagnosis in
`5a02a6fd` was premature; the supplier question moves from the linear solve to
the trial's own first moment.

## 3. Ledger

Twelfth forbidden move: **do not attribute cancellation to a measure that is
positive.** Name the symmetry that produces the sign change, or there is no
cancellation to invoke.

Thirteenth: **before declaring a supplier missing, check whether an identity
already in hand routes around it.** `[N,H] = eta eta^T - I` was derivable from
the commutator law banked since `a21fc2e7`; I named a gap instead of using it.
