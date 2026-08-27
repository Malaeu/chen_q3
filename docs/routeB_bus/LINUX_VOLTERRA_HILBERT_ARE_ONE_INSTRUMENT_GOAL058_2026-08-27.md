---
TASK_ID: GOAL058_POLARIZED_VOLTERRA_KERNEL_IDENTIFICATION
MODE: PAPER_PLUS_NUMERIC_CORROBORATION
BODY: Linux-Claude
DATE: 2026-08-27
AUTHORITY: owner instruction, this session, to check whether the spectral instrument we already built is the same object
DISCRIMINATOR: PASS
RESULT_CODE: HILBERT_CURRENT_IS_THE_VOLTERRA_COEFFICIENT
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
RH_CLAIM: false
CLOSES:
  - POLARIZATION_OF_THE_VOLTERRA_KERNEL_TO_A_MIXED_PAIR
  - COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY_AS_AN_OPEN_SHAPE
OPENS:
  - WEIGHTED_L1_BOUND_ON_THE_POLARIZED_HILBERT_CURRENT_COEFFICIENTS
---

# The Hilbert current and the Volterra kernel are one instrument

## 0. Result

Our cut-flux object and Groskin's Volterra sine-chord kernel are not two tools to
be combined. They are the same tool seen from two sides. Precisely: **our test
function is the odd part of his kernel, and our Hilbert-current weight is his
kernel's coefficient.**

The consequence is immediate. The kernel has an exact closed form as a finite
exponential polynomial with linear coefficients, so our open regularity gap stops
being a question about an unknown function and becomes an explicit weighted
`l^1` bound on coefficients we already compute.

## 1. The closed form

For a coefficient vector `u` on the mode lattice, Groskin's kernel is
`K_u(omega) = 2 int_0^omega T_u(t) T_u(omega - t) dt`, `T_u(t) = sum_m u_m e^{2 pi i m t}`.
Expanding the double sum and integrating termwise:

    K_u(omega) = sum_k ( a_k + b_k * omega ) e^{2 pi i k omega},
    a_k = (2/(pi i)) * u_k * sum_{n != k} u_n/(k - n),
    b_k = 2 u_k^2.

The inner sum in `a_k` is `(H u)_k` for the discrete Hilbert operator
`H_{kn} = 1/(n_k - n_n)`. Therefore

    a_k = (2/(pi i)) * u_k (H u)_k = (2/(pi i)) * w_k,

with `w_k` the current-divergence weight of the cut-flux work, and `b_k` the
diagonal weight. The kernel's two coefficient families are exactly the two
channels the judge has insisted on keeping separate since verdict `eeb18777`.

## 2. Polarization — the step that was open is closed

Verdict `3f4c23eb` fixed the mixed weight
`omega_i(x,q) = conj(x_i)(H q)_i + conj((H x)_i) q_i`, star-first. Report
`9c1a5a9b` flagged the polarization of Groskin's kernel as an unproved step,
because his derivation uses the real-even symmetry `u_{-k} = u_k` to cancel
imaginary parts. That worry is unfounded. Define

    K_{x,q}(omega) = int_0^omega [ T_{conj x}(t) T_q(omega - t)
                                 + T_q(t) T_{conj x}(omega - t) ] dt.

Then, for **arbitrary complex** `x` and `q`, with no evenness and no reality:

    K_{x,q}(omega) = sum_k ( alpha_k + beta_k * omega ) e^{2 pi i k omega},
    alpha_k = omega_k(x,q) / (pi i),
    beta_k  = 2 conj(x_k) q_k.

So the polarized Volterra coefficient **is** the judge's polarized weight,
divided by `pi i`, and the polarized diagonal coefficient is the literal diagonal
channel. Nothing had to be assumed about the coefficient class.

## 3. The dictionary between the two views

Our test function is `G(t) = sum_k omega_k sin(n_k t)`. Writing `t = 2 pi omega`
and `K_alpha(omega) = sum_k alpha_k e^{2 pi i k omega}`:

    G(t) = (pi/2) [ K_alpha(omega) - K_alpha(-omega) ].

`G` is the odd part of `pi K_alpha`. In the real even quadratic case the even part
cancels identically and the relation collapses to `G = pi K_alpha`; that special
case is the one Groskin works in. The general polarized statement is the odd-part
form above.

Two consistency checks fall out and were not imposed: `K_{x,q}(0) = 0` reproduces
the zero-mass identity `sum_k omega_k = 0`, and `G(pi) = 0` reproduces the
vanishing at the band edge that report `5a02a6fd` derived from `S_{2 pi} = 0`.

## 4. What this does to the open gap

`5a02a6fd` named the load-bearing gap as the modulus of continuity of
`t -> <x_k(z), [S_t, H] q_k>` on `(0, 2 pi]`. That function is now known in closed
form, and it is entire. Differentiating the closed form termwise gives an explicit
bound with no analysis in it:

    sup_omega | K'_{x,q}(omega) | <= sum_k [ |beta_k| + 2 pi |k| ( |alpha_k| + |beta_k| ) ].

So the gap changes shape. It is no longer "is this unknown function smooth"; it is

    WEIGHTED_L1_BOUND_ON_THE_POLARIZED_HILBERT_CURRENT_COEFFICIENTS:
    bound  sum_k (1 + |k|) | omega_k(x_k(z), q_k) |  along the selected schedule.

That is a finite sum over the mode lattice of an object built from `x`, `q` and
`H` — all three already source-locked. It is the first time in this corridor that
the open quantity is a norm of something we can write down entrywise.

Two warnings, stated so they are not skipped. The bound above is an absolute
majorant over the coefficients, and this route has repeatedly been killed by
absolute majorants. It is a *regularity* budget, not the consumer itself, so the
signed cancellation in the consumer is untouched by it. Second, a weighted `l^1`
bound on `omega_k` still needs the mode-index behaviour of `x_k(z)`, which the
asset bank does not supply — the hole of section 7 of `5a02a6fd` is not filled,
only relocated to a place where it is one explicit sum.

## 5. Corroboration, declared

The closed form of section 1 was checked against direct numerical quadrature of
the Volterra integral at four points (agreement `<= 3.5e-9`, quadrature-limited);
the polarized closed form of section 2 likewise for random complex `x, q`
(`<= 1.5e-9`); the dictionary of section 3 to `<= 2.2e-14`; the zero-mass
consequence to `1.6e-15`; and the derivative bound of section 4 was checked to
hold (numerical `sup |K'| = 577.0` against the bound `1286.1`) on a random
instance. All DIAGNOSTIC_NEVER_A_PROOF; the algebra of sections 1-3 is a
termwise integration of a finite double sum and stands on its own.

## 6. We already built this, on 2026-08-07, and forgot it

This is the part that matters for process rather than mathematics.

`docs/routeB_bus/phase0_scripts/arch_block.py` implements the exact chain
`v -> K_v -> g_v` in closed form. Its `TestFn.__init__` computes, verbatim,

    self.alpha[k] = 2 * self.u[k] * off_diagonal_sum / (mp.pi * 1j)
    self.beta[k]  = 2 * self.u[k] ** 2

which is section 1 of this report. The script was run on 2026-08-07 and PASSED
against Groskin's published three-route reference for `c = 13, N = 4` to
`8.5e-20`, with the source lock recorded in
`docs/routeB_bus/phase0_scripts/threeroute_c13N4_reference.json`
(Zenodo record 21146461, package md5 `71e7890a609c6db38f1324ce8225b840`).
`phase0_ccm_crosswalk.py` had already locked `lambda^2 = m`, `L = log m`,
`c = m`, `beta = L/(4 pi)` and the pole block by two independent closed forms.

So the instrument was built, validated against the author's own reference, and
its README written — three weeks before the corridor was declared FATAL. In the
nine preflights since, nobody connected `alpha_k = 2 u_k (H u)_k/(pi i)` in that
file with the Hilbert current we were deriving by hand.

Recorded as the eighth forbidden move: **a validated script in
`phase0_scripts/` is a supplier, and `ask.sh` does not index Python.** Before
naming a new object, grep the phase-0 and probe scripts for its formula, not only
the Lean catalogue and the prose.

## 7. Requests

Two, both cheap:

1. adjudication of the polarized identification of sections 2 and 3, which if
   accepted retires `COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY` in its current
   phrasing and replaces it with the weighted `l^1` gap of section 4;
2. authorization to formalize sections 1-3 in Lean. They are finite algebra over
   a finite index set — a termwise integration and a coefficient identification —
   and they would bank the bridge between the Hilbert-pairing file
   `G6N1SelectedFerrersHilbertPairing.lean` and the spectral normal form
   `CCMFiniteWeilCenterSpectralNormalForm.lean`, which currently sit unconnected.
