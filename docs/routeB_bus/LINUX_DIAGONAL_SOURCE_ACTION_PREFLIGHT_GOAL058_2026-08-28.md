---
TASK_ID: GOAL058_LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric profiling
BODY: Linux-Claude
DATE: 2026-08-28
AUTHORITY: owner instruction this session ("го"), no live judge directive; VOI hold lifted by the owner
DISCRIMINATOR: HOLD
RESULT_CODE: DIAGONAL_OBJECT_IDENTIFIED_SUP_NORM_REJECTED_WEIGHTED_NORM_OPEN
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared, with an explicit reliability caveat
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - DIAGONAL_PRICED_BY_SUP_NORM
OPENS:
  - DIAGONAL_TRIAL_WEIGHTED_L2_NORM
---

# The diagonal channel: literal form, and the wrong tool identified

## 0. Result

The diagonal channel has a literal form that differs structurally from the
off-diagonal one in a way that must be carried: **the Euler-Mascheroni head does
not vanish on the diagonal.** The same `sqrt m` pairing between the pole and
prime ledgers is present, so the diagonal is subject to the same
no-component-split rule as everything else.

The main negative result is about tooling: pricing the diagonal by
`sup_n |M_nn - a|` is the wrong bound, because the diagonal is **smallest where
the trial has most of its mass** and largest at the lattice edge where the trial
is concentrated least. Discriminator: HOLD, on the correctly-weighted object.

## 1. Literal form, and the structural difference

From `CCMFiniteWeilSourceMatrixN1.lean`, the diagonal branch of the kernel is

    ccmQKernel L n n x = 2 (L - x)/L * cos(2 pi n x / L),

so, ledger by ledger at `j = n`:

    W02_nn   = 32 L sinh^2(L/4) (L^2 - 16 pi^2 n^2) / (L^2 + 16 pi^2 n^2)^2,
    Prime_nn = sum_{2<=k<=m} (Lambda(k)/sqrt k) * 2 (L - log k)/L * cos(2 pi n log k/L),
    WR_nn    = (gamma + log(4 pi tanh(L/2)))
               + integral_{(0,L]} [ e^{x/2} * 2(L-x)/L * cos(2 pi n x/L) - 2 ] / (e^x - e^{-x}) dx,
    M_nn     = W02_nn - WR_nn - Prime_nn.

**The difference that matters.** On the center column the head vanished because
`ccmQKernel L n 0 0 = 0` for `n != 0`. On the diagonal
`ccmQKernel L n n 0 = 2(L-0)/L * cos 0 = 2`, so the head is
`gamma + log(4 pi tanh(L/2)) = log(4 pi) + gamma + o(1)`, of size `O(1)` and
**present**. Every identity derived for the off-diagonal channel by exploiting the
vanishing head is therefore unavailable here. The subtraction inside the integrand
is likewise no longer vacuous; it is what keeps the integral convergent at `x = 0`,
since the numerator vanishes there.

## 2. The same `sqrt m` cancellation, again

Profiled at `n = 0` (declared numeric, section 5):

    m = 10^2:   W02 = 14.071   arch = 3.679   prime = 10.367   M_00 = +0.0251
    m = 10^3:   W02 = 34.343   arch = 4.164   prime = 30.163   M_00 = +0.0162
    m = 10^4:   W02 = 85.130   arch = 4.447   prime = 80.673   M_00 = +0.0102

Four orders of magnitude of cancellation at `m = 10^4`, between two ledgers of
size `8 sqrt m / L` each. Algebraically, `W02_00 = 8(sqrt m - 2 + 1/sqrt m)/L`
exactly, and the prime diagonal at `n = 0` is
`2 sum Lambda(k)/sqrt k - (2/L) sum Lambda(k) log k/sqrt k`, whose leading term is
also `8 sqrt m / L` by partial summation against `d psi`. So the diagonal carries
the same paired structure as the off-diagonal, and the rule stands: it must never
be estimated ledger by ledger.

## 3. The wrong tool, and the right object

The channel is

    D_k(z) = sum_i ( (M_k)_ii - a_k ) * conj(x_k(z)_i) * q_{k,i}.

The reflex bound is `|D| <= sup_i |M_ii - a| * ||x||_2 ||q||_2`. That is a
component split in disguise: it prices the diagonal at its **worst** lattice site
irrespective of how much trial mass sits there.

The profile says this is exactly backwards. At `m = 10^3` the diagonal is

    n:      0      1      2      5     10     25     50    100
    M_nn: 0.016  0.016  0.017  0.019  0.036  0.166  0.190  0.340

monotone increasing away from the center, while the selected trial is a
projected prolate/Hermite packet whose coefficient mass is concentrated at small
`|n|`. The diagonal is small precisely where `q` lives, and large precisely where
`q` does not.

The correct pairing, by Cauchy-Schwarz applied to `x` against the vector
`((M_ii - a) q_i)_i` rather than to `x` against `q`, is

    | D_k(z) | <= ||x_k(z)||_2 * ( sum_i | (M_k)_ii - a_k |^2 |q_{k,i}|^2 )^{1/2}.   (*)

The second factor is a **trial-weighted `l^2` norm of the diagonal**, and it is the
object that must be bounded. It is never larger than the sup bound and, on the
profile above, is far smaller. Named:

    DIAGONAL_TRIAL_WEIGHTED_L2_NORM.

With the envelope of report `7cd5f9a5`, `(*)` reads

    | D_k(z) | <= sqrt( L/(2 sigma) ) * m^{sigma/2} / min(beta_k, 1)
                  * || diag-weighted trial ||,

so the diagonal channel now has exactly one unsupplied factor of its own, the same
count as the off-diagonal channel.

## 4. What is not claimed

I profiled the outer lattice as well and obtained values of order `1` to `7` at
`m = 10^3`, non-monotone in `n`, with the maximum wandering between `n/m = 0.25`
and `n/m = 0.99` across sizes. **I do not claim a sup bound from those numbers.**
The integrand `[e^{x/2} 2(L-x)/L cos(2 pi n x/L) - 2]/(e^x - e^{-x})` oscillates
`n` times across the window, and at large `n` my quadrature is not trustworthy
even split by period; the non-monotone jumps look like quadrature error rather
than structure. Recorded as an open observation with both readings named: either
the diagonal genuinely has erratic large values at the lattice edge, or the
outer profile is a numerical artefact. The outcome that separates them is an
analytic estimate of that oscillatory integral, not a finer grid.

This does not affect section 3, which needs the *central* profile — reliable,
smooth and consistent across three sizes — and the concentration of `q`, not the
outer values.

## 5. Declaration

No live verdict authorizes numerics; this profiling was run on the owner's
direct instruction to proceed, is labelled DIAGNOSTIC_NEVER_A_PROOF, and enters
no argument. Sections 1 and 3 are source reading and Cauchy-Schwarz; section 2's
algebraic identity `W02_00 = 8(sqrt m - 2 + 1/sqrt m)/L` is closed form.

## 6. Next load-bearing gap

    DIAGONAL_TRIAL_WEIGHTED_L2_NORM

that is, a bound on `( sum_i |(M_k)_ii - a_k|^2 |q_{k,i}|^2 )^{1/2}` along the
selected schedule. Its two natural inputs both already exist in named form: the
central diagonal profile of section 1, and the mode profile of the trial, which
is the same object as `SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER`. The diagonal
channel is therefore no longer isolated from the rest of the ledger — it consumes
the same trial-profile supplier the regularity side needs.
