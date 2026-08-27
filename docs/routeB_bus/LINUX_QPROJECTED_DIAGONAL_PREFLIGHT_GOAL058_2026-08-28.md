---
TASK_ID: GOAL058_SELECTED_FERRERS_QPROJECTED_DIAGONAL_SOURCE_ACTION_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric test
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 87e5ea2f
DISCRIMINATOR: HOLD
RESULT_CODE: QPROJECTED_DIAGONAL_IDENTITY_WITHOUT_SOURCE_RATE
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - UNIFORM_COSINE_TRANSFORM_OF_THE_DIAGONAL
OPENS: []
---

# The Q-projected diagonal: zero-mass weight, second-order endpoint vanishing, split weights

## 0. Result

Three things close and one hoped-for unification dies.

The `Q`-projected weight has **zero total mass**, so the diagonal channel is a
zero-mass pairing exactly like the off-diagonal one. Its cosine test vanishes to
**second order at both endpoints**, which is where both `sqrt m` masses sit — one
order better than the sine test. And the two channels are precisely the
reflection-even and reflection-odd halves of one decomposition, which makes the
`C13` shadow exact rather than metaphorical.

What dies is the hope of writing the diagonal as one cosine transform of the
completed measure: the pole and prime ledgers carry **different weights in the
same variable**. Tested and refuted, correction 12 section 3.

## 1. The Q-projected object

From the verdict, with `y = Q x = C^{-1} Q kappa` and `b_n = conj(y_n) q_n`,

    Psi = <y, M q> = D_perp + (1/2) Phi(G_y),
    D_perp = sum_n M_nn b_n,
    sum_n b_n = <y, q> = 0.                                             (1)

The vanishing of `sum b_n` is not an extra hypothesis; it is `y = Qx` by
construction. It is the diagonal analogue of the zero-mass identity
`sum_i omega_i = 0` that the off-diagonal weight satisfies.

## 2. The diagonal test function, and its endpoints

Since `M_nn` is built from `cos(2 pi n x/L)` in every ledger, the pairing
factorizes through

    B(theta) = sum_n b_n cos(n theta),

evaluated at `theta = 2 pi x / L` and at the prime angles
`theta_k = 2 pi log k / L`. By (1),

    B(0) = sum_n b_n = 0,
    B(2 pi) = sum_n b_n cos(2 pi n) = sum_n b_n = 0,

the second because the modes are integers. Expanding at the origin,

    B(theta) = sum_n b_n (1 - n^2 theta^2/2 + O(theta^4))
             = - (theta^2/2) sum_n n^2 b_n + O(theta^4),

so `B` vanishes to **second** order at both ends, and by periodicity the same
holds at `2 pi`. Two consequences:

- the archimedean endpoint singularity `d mu_arch ~ dt/(2 pi t)` is not merely
  compensated but over-compensated: the integrand is `O(t)` there, absolutely
  integrable with room to spare, and no compensated primitive is needed for this
  channel;
- both `sqrt m` masses — the folded pole density concentrated at `t -> 0` and the
  prime atoms concentrated at `t -> 2 pi` — are met by a test vanishing
  quadratically. The diagonal channel meets the large masses at its own zeros.

`B` is reflection-**even**, since `cos(n(2 pi - theta)) = cos(n theta)`, while the
off-diagonal test `G` is reflection-**odd**. The two channels are therefore the
even and odd halves of one reflection decomposition. That is the `C13` shadow,
now exact: the shadow is not an artefact to be carried, it is the even channel.

## 3. What does not unify

The natural next step — write `D_perp` as one cosine transform of the completed
measure `mu` — fails. From closed form, ledger by ledger,

    W02_nn   = integral t * cos(n t) d mu_{W02}(t),
    Prime_nn = integral (2 pi - t) * cos(n t) d mu_prime(t),

so the weights are reflections of each other, matching the fact that the
densities themselves are reflections of each other (verdict `979feca5`). A single
weight does not exist in the raw variable. Refuted numerically before being
reported: at `m = 10^3, n = 0` the literal diagonal is `0.0162` while the uniform
`t`-weighted transform gives `126.38`.

The constructive reading is that any unification must be attempted **after the
fold**, in the reflected variable, where both densities already coincide to
leading order. That is a well-posed next step and is not attempted here.

## 4. What the terms that survive are

Under the `Q`-projection all `n`-independent diagonal terms pair to zero
(correction 12 section 1): the archimedean Euler-Mascheroni head, the Rayleigh
shift `-a I`, and the constant subtraction `ccmQKernel L n n 0 = 2` inside the
`WR` integrand. What remains in each ledger is exactly its `n`-dependent part:

    W02:   32 L sinh^2(L/4) (L^2 - 16 pi^2 n^2)/(L^2 + 16 pi^2 n^2)^2,
    Prime: sum_k (Lambda(k)/sqrt k) * 2 (L - log k)/L * cos(n theta_k),
    Arch:  integral_{(0,L]} e^{x/2} * 2(L-x)/L * cos(2 pi n x/L) / (e^x - e^{-x}) dx,

the last with its constant subtraction already discharged by `B(0) = 0`.

## 5. The bound, and what it needs

    | D_perp | <= || y ||_2 * ( sum_n |M_nn|^2 |q_n|^2 )^{1/2},

with `|| y ||_2 = || Q C^{-1} kappa ||_2 <= || Q kappa ||_2 / beta` from the
verdict's minimal coercivity — note `/beta`, not `/min(beta,1)`, because on the
`Q` block `C` acts as `Q(M - eps I)Q`. Two inputs:

- `QPROJECTED_P59_KERNEL_COMPACT_RATE` — `|| Q kappa(z) ||_2^2 = || kappa(z) ||_2^2
  - |<q, kappa(z)>|^2`, so the closed form of report `7cd5f9a5` is an upper bound
  and the exact object subtracts the trial's overlap with the kernel row. That
  overlap is not estimated here;
- `SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR` — unchanged, and still unsupplied.

The second factor of the display is the trial-weighted diagonal norm of report
`15bc50f6`, whose central profile is small and whose outer profile I explicitly
declined to bound.

## 6. Next load-bearing gap

    FOLDED_VARIABLE_DIAGONAL_UNIFICATION

that is: after the periodic fold that already aligns the pole and prime
densities, does a single weight represent both diagonal ledgers? Section 3 shows
the raw variable does not admit one and says exactly why; the folded variable is
untested. It is cheap, it is decisive for whether the diagonal joins the
off-diagonal in one functional, and it is the only step here that could reduce
the ledger rather than describe it.
