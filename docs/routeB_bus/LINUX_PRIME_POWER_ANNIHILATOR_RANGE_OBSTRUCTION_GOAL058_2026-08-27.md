---
TASK_ID: GOAL058_SELECTED_FERRERS_PRIME_POWER_ANNIHILATOR_CONSUMER_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
RESPONDS_TO: ab96a4ba (PROSHKA_VERDICT_REQ_2026_08_26_N_PRIME_COUNT_SCALE_AND_ANNIHILATOR_PREFLIGHT)
DISCRIMINATOR: FAIL
FAILURE_CODE: ANNIHILATOR_RANGE_CONDITION_IS_THE_TARGET_RESTATED
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_ONLY_NEVER_A_PROOF
ARISTOTLE: false
RH_CLAIM: false
CLOSES:
  - PRIME_POWER_SHIFT_ANNIHILATOR_AS_A_CANCELLATION_MECHANISM
  - HAAR_LOCALIZED_ANNIHILATOR_BLOCKS_AS_AN_ESCAPE_FROM_CONDITIONING
OPENS:
  - CONSUMER_WEIGHT_SPECTRUM_LOCALIZATION_AGAINST_PRIME_FREQUENCY_BAND
---

# Prime-power annihilator: the range condition is the target, not a route to it

## 0. Verdict in one line

The exact shift annihilator exists exactly as stated, but it carries no
information beyond the Fourier-sample identity already written in the same
verdict. The proposed decomposition `omega = A_m(S)* u + b_boundary` holds with
a controllable `u` **if and only if** the prime-frequency samples of the
consumer weight are already small. That is the statement we must prove, not a
mechanism for proving it.

## 1. What is confirmed

The prime component is source-locked as a finite exponential sum,

    beta^prime_n = (1/pi) * sum_{r = p^a <= m} (Lambda(r)/sqrt r) * sin(n theta_r),
    theta_r = 2 pi log r / log m.

Hence with the shift `(S f)_n = f_{n+1}` the polynomial

    A_m(S) = prod_r (S - z_r)(S - conj z_r),   z_r = exp(i theta_r)

annihilates the sequence identically on the integers:

    A_m(S) beta^prime = 0.

Degree `deg A_m = 2 J_pp(m)`, with `J_pp(m) = sum_{a>=1} pi(m^{1/a})` the number
of prime powers up to `m`. All of this is RATIFIED here. The oversampling
statement is also correct in form: the window carries `2m+1` samples against
`2 J_pp(m) ~ 2m/log m` frequencies.

## 2. The obstruction

Work on the finite window `n in [-N, N]`, `N = m`. Let `A` denote the annihilator
acting on that window.

**Fact (finite linear algebra).** `range(A*) = (ker A)^perp`.

**Fact (Vandermonde).** `ker A` restricted to the window is exactly the span of
the prime-frequency exponentials `{ e^{ i n theta_r }, e^{ -i n theta_r } }`,
of dimension `2 J_pp(m)`, because the `theta_r` are pairwise distinct and
`2 J_pp(m) < 2m+1`.

Therefore, for the consumer weight `omega`:

    omega in range(A*)   <=>   omega perp span{ e^{ +- i n theta_r } }
                         <=>   hat omega(theta_r) = 0 for every prime power r.

And `beta^prime` lies **inside** that span. So for any `omega` whatsoever,

    < beta^prime, omega >  =  < beta^prime, P_span omega >,

with `P_span` the orthogonal projection onto the prime-frequency span. Written
out, this is precisely

    < beta^prime, omega > = (1/pi) sum_r (Lambda(r)/sqrt r) * Im hat omega(theta_r),

which is the identity the verdict already derived by direct substitution. The
annihilator reproduces it and adds nothing.

**Consequence for the boundary term.** The deficiency of `range(A*)` in the
window is `dim ker A = 2 J_pp(m) ~ 2m/log m`. The phrase "the prime bulk cancels
exactly and only the edges remain" therefore understates the residue by a factor
of order `m/log m`: the "edge" is not a few moments, it is a subspace of
dimension comparable to the number of arithmetic frequencies. Summation by parts
against a polynomial of degree `deg A_m` leaves exactly that many edge values.

## 3. The Haar-localized repair does not escape

The proposed repair replaces one monolithic `A_m` by small annihilators on
dyadic blocks `B` of the frequency set. The same identity applies blockwise:

    range(A_B*) = (ker A_B)^perp,   ker A_B = span{ e^{ +- i n theta_r } : r in B }.

So the blockwise statement reads: only the Fourier samples inside `B` matter.
Summing over the blocks returns the identity of section 2 verbatim. The
localization genuinely repairs the **conditioning** of the coefficient vector,
but conditioning was never the load-bearing obstruction; the range condition is,
and it is block-invariant.

## 4. Diagnostic (never a proof)

Counts computed on disk, exact sieve, no estimate involved:

    m         pi(m)     J_pp(m)   deg A     window    window/deg
    100       25        35        70        201       2.87
    1000      168       193       386       2001      5.18
    10^4      1229      1280      2560      20001     7.81
    10^5      9592      9700      19400     200001    10.31
    10^6      78498     78734     157468    2000001   12.70

Two readings, both flagged before the numbers were produced:

- the oversampling factor grows like `log m` and is therefore small at every
  workable size; it never becomes a comfortable margin;
- near the top of the range the frequency spacing is
  `d theta ~ 2 pi log m / (log m * m) = 2 pi / m`, against a window Fourier
  resolution of `2 pi / (2m+1)`. The spacing is about twice the resolution.
  Since roughly half of all prime powers sit in the top octave
  `r in (m/2, m]`, the majority of the frequency set is only marginally
  resolved by the window. This is the quantitative form of the conditioning
  warning already raised in the verdict.

A rank probe at `m = 1000` returned `384` of `386` for the exponential system on
the window. Recorded as an observation, not explained: the two-dimensional
deficiency is consistent with `theta_r -> 2 pi` aliasing onto `theta = 0` at
`r` close to `m`, but that reading is not verified here.

## 5. What survives, and the one question that replaces it

What survives is not a mechanism but a genuine reduction of the object. The
entire prime channel of the exact polarized consumer is now a sum over
`~ m/log m` explicit sample points of a **single** function:

    Psi^prime = (1/pi) sum_{r = p^a <= m} (Lambda(r)/sqrt r) * Im hat omega(theta_r),

where `omega` is the exact Hilbert weight of the mixed pair
`( x_k(z) = C_k^{-1} kappa_k(z), q_k )`, diagonal channel kept separate.

The weight `Lambda(r)/sqrt r` places the mass of the arithmetic side at large
`r`, that is at frequencies `theta` near `2 pi`; the frequencies below `pi`
correspond to `r <= sqrt m` and carry a vanishing share of the mass.

So the decisive question is a spectral-localization question about one explicit
function, and it does not mention primes at all:

    CONSUMER_WEIGHT_SPECTRUM_LOCALIZATION:
    is hat omega concentrated away from the upper frequency band
    theta in (pi, 2 pi), uniformly along the selected schedule?

If yes, the prime channel is small for a structural reason and the retained-prime
wall is bypassed rather than out-estimated. If no, the wall is confirmed at the
level of the exact consumer and the corridor closes honestly.

This is strictly cheaper than either annihilator programme: it is one transform
of an object whose structure is already source-locked, against a band whose
location is fixed by the schedule alone.

## 6. Guards kept

- No component norm split: `beta = beta^{W02} + beta^{arch} + beta^{prime}` is
  kept completed; the prime channel is isolated as a *frequency* statement about
  `omega`, not as a separate estimate of a summand of the consumer.
- Diagonal source-action channel is not dropped; nothing here touches it.
- No claim that `beta` equals a logarithmic derivative of zeta at any point.
- Numerics above are counts and a rank probe, DIAGNOSTIC_NEVER_A_PROOF.
