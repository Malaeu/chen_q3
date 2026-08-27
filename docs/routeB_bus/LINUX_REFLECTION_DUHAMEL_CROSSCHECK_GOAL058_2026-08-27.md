---
TASK_ID: LINUX_CROSSCHECK_OF_THE_PARALLEL_REFLECTION_DUHAMEL_VERDICT
MODE: PAPER_PLUS_DECLARED_NUMERIC_CHECK
BODY: Linux-Claude
DATE: 2026-08-27
CHECKS: parallel-chat verdict pinned at head 5a02a6fd (relayed by the owner, not in the repository)
DISCRIMINATOR: PASS
RESULT_CODE: TWO_INDEPENDENT_DERIVATIONS_ARE_ONE_IDENTITY
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
RH_CLAIM: false
CLOSES:
  - DUHAMEL_AND_VOLTERRA_AS_TWO_SEPARATE_CANDIDATES
  - CANCELLATION_MECHANISM_UNLOCATED
OPENS:
  - TRIAL_MODE_ENERGY_BOUND_ALONG_THE_SCHEDULE
---

# Cross-check: the reflection/Duhamel line and the Volterra line are one object

## 0. Provenance, stated first

The owner relayed a verdict from the **parallel** judge chat. It pins head
`5a02a6fd` and is therefore written **before** `b9e7c589` (Volterra/Hilbert
identification), `d9802775` (its ratification), `d2c044f7`, `82778859`,
`f8ac6384` and `880cf3a0`. It does not know that line exists. Nothing in it is a
repository verdict; it is treated here as a mathematical proposal to be checked,
per the relay rule elevated in `880cf3a0`.

Three of its claims are checkable in minutes. All three hold. A fourth
observation, not in either line, follows from putting them together.

## 1. Reflection identity — holds

Modes are integers, so `sin(n(2 pi - t)) = -sin(n t)` and the polarized test
function is antisymmetric: `G(R(t)) = -G(t)` for `R(t) = 2 pi - t`. Hence

    integral G d mu = (1/2) integral G d nu,   nu = mu - R_* mu,

and `nu` has total mass zero. Elementary and exact.

## 2. Rank-one commutator — holds exactly

    [N, H] = eta eta^T - I,   N = diag(n_i), eta = (1,...,1).

Checked symbolically (off-diagonal `(n_i - n_j) H_ij = 1`, diagonal zero) and
numerically at `N = 3, 7`: max deviation `0` and `2.2e-16`.

## 3. Duhamel factorization — holds exactly

    [U_t, H] = i integral_0^t U_s (eta eta^T - I) U_{t-s} ds,   U_t = exp(i t N).

Derived by `B(t) = U_t H - H U_t`, `B(0) = 0`, `B'(t) = i U_t [N,H] + i B(t) N`.
Checked numerically at `t = 0.4, 1.3, 2.7` on a `9 x 9` carrier: deviations
`5e-10`, `5e-9`, `2e-8`, quadrature-limited.

## 4. The main-term matching — holds, and it is exact

This is the substantive find of the parallel line, and it is stronger than a
heuristic. Replacing `d psi(x)` by `dx` in the prime measure and substituting
`t = 2 pi log x / L` gives the reference density

    d mu_{P,main}(t) = ( L / (2 pi^2) ) e^{ L t/(4 pi) } dt,

whose reflection under `R` is

    d (R_* mu_{P,main})(u) = ( L sqrt m / (2 pi^2) ) e^{ - L u/(4 pi) } du.

The literal `W02` density, from the kernel-green node `2aaff3e7`, is

    d mu_{W02}(u) = ( 2 L sinh^2(L/4) / pi^2 ) e^{ - L u/(4 pi) } du,

and since `2 sinh^2(L/4) = (e^{L/2} - 2 + e^{-L/2})/2`,

    d mu_{W02}(u) = ( L / (2 pi^2) ) ( sqrt m - 2 + 1/sqrt m ) e^{ - L u/(4 pi) } du.

**The `sqrt m` leading parts are identical.** The difference is exactly

    ( L / (2 pi^2) ) ( -2 + 1/sqrt m ) e^{ - L u/(4 pi) } du,

of order `log m`, not `sqrt m log m`. Verified numerically: at `m = 10^16` the two
coefficients are `1.8664051391e8` and `1.8664051765e8`, and their difference is
`-3.73`, matching `(-2 + 1/sqrt m) L/(2 pi^2)` to nine digits at every size
tested (`m = 10^2, 10^4, 10^8, 10^16`).

This is the mechanism the corridor lacked. The pole ledger **is** the reflection
of the prime main term, up to an explicitly computable `O(log m)` remainder. Nine
preflights died on absolute majorants because every such bound severs a pair
whose leading asymptotics are tuned to each other by construction.

## 5. The observation neither line has: the two are the same identity

The parallel line factorizes `hat omega`; our ratified line gives the Volterra
kernel in closed form. They are not two candidates. Writing
`conv(t) = integral_0^t <x, U_s eta> <eta, U_{t-s} q> ds`, the parallel line gives

    hat omega(t) = i conv(t) - i t <x, U_t q>,

while `b9e7c589` gives, with `alpha_k = omega_k/(pi i)` and `beta_k = 2 conj(x_k) q_k`,

    K_{x,q}(w) = sum_k (alpha_k + beta_k w) e^{2 pi i k w}.

Substituting `t = 2 pi w`, the `alpha`-part is `hat omega(t)/(pi i)` and the
`beta`-part is `2 w <x, U_t q>`. The two diagonal terms **cancel identically**, and

    K_{x,q}(w) = (1/pi) * conv(2 pi w).

Verified at five points to `9e-8`, quadrature-limited. So the Volterra kernel is
*exactly* the Duhamel convolution, and the diagonal channel is precisely the term
that converts one presentation into the other. Two derivations, three weeks and
two chats apart, produce one identity.

Practical consequence: the diagonal channel is not an inconvenience to be carried
alongside. It is the bookkeeping difference between two ways of writing the same
object, which is why every attempt to drop it has failed.

## 6. Consequence for the supplier question

From the Duhamel form, both factors are trigonometric polynomials. Their `L^2`
norms in `t` are `sqrt(2 pi)` times the `l^2` norms of the coefficient vectors,
and differentiating brings down a factor `n_i`. So a regularity budget for
`hat omega` is bought by

    ||x||_2   — free, it is the normalization,
    ||N q||_2 — the mode energy of the trial.

Two things follow. First, the diagnosis of `5a02a6fd` sections 6-7 was premature
and is withdrawn in correction 9. Second, the dimension-growth objection — that
`eta` has norm `sqrt(2N+1)` — does not bite: `<eta, U_t q>` is never estimated by
`||eta|| ||q||`, it is a trigonometric polynomial whose `L^2` norm in `t` is
`sqrt(2 pi) ||q||_2`. No carrier-dimension factor appears.

## 7. What is now the load-bearing object

    TRIAL_MODE_ENERGY_BOUND_ALONG_THE_SCHEDULE:
    control  ||N q_k||_2 = ( sum_n n^2 |q_{k,n}|^2 )^{1/2}  along the selected
    schedule, together with the cumulative reflection discrepancy
    F_m(t) = nu_m([0,t]) at consumer strength.

Both are properties of objects we construct, not of the arithmetic. That is the
first time in this corridor that is true of the whole open list.

## 8. Numeric declaration

No live verdict authorizes numerics. All checks above were run under the owner's
direct instruction to verify the relayed verdict, are labelled
DIAGNOSTIC_NEVER_A_PROOF, and none of them enters an argument: sections 1-3 and 5
are finite algebra, section 4 is an identity between two closed forms.
