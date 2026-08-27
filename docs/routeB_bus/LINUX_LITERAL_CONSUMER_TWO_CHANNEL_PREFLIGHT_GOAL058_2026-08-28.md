---
TASK_ID: GOAL058_SELECTED_FERRERS_REFLECTION_DUHAMEL_LITERAL_CONSUMER_REPAIR_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: cc0effc7
DISCRIMINATOR: HOLD
RESULT_CODE: DIAGONAL_OR_NORMALIZED_FINITE_ROW_ADAPTER_STILL_OPEN
LEAN_EDIT: false
NUMERICS: none
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - ONE_FUNCTIONAL_SHORTCUT_FOR_THE_LITERAL_CONSUMER
OPENS: []
---

# The literal consumer is two channels, permanently

## 0. Result

The exact two-channel identity closes, and the one-functional shortcut is killed
by a witness rather than by preference: the full Volterra kernel **cannot** be
reflection-odd, because it is not periodic. `R1` is therefore not a stylistic
choice over `R2` — `R2`'s shadow is exactly the diagonal channel, so the two
candidates are the same split written twice. Discriminator: HOLD, on the two
adapters. Matches `P_LITERAL_REPAIR_1`.

## 1. The literal consumer, with its constant

    Psi_k(z) = <x_k(z), (M_k - a_k I) q_k>
             = D_k(z) + (1/2) * Phi_k(G_{k,z}),                          (1)

    D_k(z)   = sum_i ((M_k)_ii - a_k) * conj(x_k(z)_i) * q_{k,i},
    G_{k,z}(t) = <x_k(z), [S_t, H] q_k>,   S_t = diag(sin(n_i t)),
    Phi_k(G) = integral_{(0,2pi)} G d nu_k,   nu_k = mu_k - R_* mu_k,
    R(t)     = 2 pi - t.

The `1/2` is the reflection constant, restored per correction 11. The diagonal
channel is **not** absorbed and, by section 2, cannot be.

## 2. Why the shortcut is impossible

`G_{k,z}(t) = sum_i omega_i sin(n_i t)` is `2 pi`-periodic, because the `n_i` are
integers, and odd. Hence `G(2 pi - t) = G(-t) = -G(t)`, which is the antisymmetry
the reflection identity consumes.

The full polarized Volterra kernel is

    K(w) = sum_k ( alpha_k + beta_k w ) e^{2 pi i k w},
    alpha_k = omega_k/(pi i),   beta_k = 2 conj(x_k) q_k.

Its second family carries the prefactor `w`, which is **not periodic**. Concretely
`K(w+1) - K(w) = sum_k beta_k e^{2 pi i k w}`, which vanishes identically only if
every `beta_k = 0`, i.e. only if `conj(x_i) q_i = 0` for all `i`. Since
`||q_k||_2 = 1`, that forces `x_k(z)` to be supported off the support of `q_k`,
which the graph identity `C_k x = kappa_k(z)` does not permit for generic `z`.
So `K` is aperiodic, the reflection map does not act on it, and no rewriting can
place the diagonal inside `Phi`.

This also settles the relation between the two candidates. Splitting `K` into its
reflection-odd part and an explicit shadow, as `R2` proposes, gives exactly

    K_odd(w) = (1/(pi i)) sum_k omega_k e^{2 pi i k w},
    K_shadow(w) = w * sum_k beta_k e^{2 pi i k w},

and the shadow is the diagonal family. `R2` recovers `R1`. The `C13` card is
satisfied — the symmetry is restored by naming the shadow — but it buys no new
object.

## 3. What each channel needs, separately

**Off-diagonal channel `(1/2) Phi_k(G)`.** Requires:

- `COMPENSATED_ENDPOINT_REMAINDER_PRIMITIVE` — integrability of the remainder
  after subtracting the two endpoint logarithms with residue `1/(2 pi)`
  (correction 11 section 3);
- `COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND` — the arithmetic input: the
  Stieltjes remainder `d psi - dx`, the `1..2` lower-endpoint correction, and the
  archimedean endpoint functional, none covered by the continuous main model;
- a regularity norm of `G`, which by the ratified Duhamel/Volterra crosswalk uses
  only `||x_k(z)||_2`, `||q_k||_2 = 1` and `||Mode * q_k||_2`.

For the last of these, two inputs and their exact relation, per verdict
`cc0effc7` and correction 10:

    ||Mode * q_k||_2^2 = s_k^2 * sum_{n in modeSet} n^2 |<V_n, g_k>|^2,
    physicalFourierEnergy(i_k, g_k) = (4 pi^2/L_k^2) * sum_{n in Z} n^2 |<V_n,g_k>|^2,
    ||Mode * q_k||_2^2 <= s_k^2 * (L_k^2/(4 pi^2)) * physicalFourierEnergy(i_k, g_k),

with `s_k = ||P_N g_k||^{-1}`. The inequality is the adapter
`SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER`; the normalizer side has the
Lean-proved supplier `selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger`
under frozen W5 inputs, the energy side has the undischarged contract
`SelectedPhysicalFourierEnergyControl`.

And `||x_k(z)||_2` now has an explicit envelope from report `7cd5f9a5`:

    ||x_k(z)||_2 <= ||kappa_k(z)||_2 / min(beta_k, 1),
    ||kappa_k(z)||_2^2 = L_k^2 * sinh(L_k Im z)/(L_k Im z)  (upper bound on our carrier),

so the kernel half is closed in exact form and only the complement floor
`beta_k` remains on that line.

**Diagonal channel `D_k(z)`.** Requires `LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND`:
a compact budget for `sum_i ((M_k)_ii - a_k) conj(x_k(z)_i) q_{k,i}`. Nothing in
the reflection machinery touches it, and by section 2 nothing can. Its own
structure is the diagonal branch of `ccmQKernel`, `2(L-x)/L * cos(2 pi n x/L)`,
which is a separate source object from the off-diagonal branch used everywhere
above.

## 4. Ledger of the whole open list

    off-diagonal, analytic:   COMPENSATED_ENDPOINT_REMAINDER_PRIMITIVE
    off-diagonal, arithmetic: COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND
    regularity, ours:         SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
                              SelectedPhysicalFourierEnergyControl (undischarged)
                              SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
    diagonal:                 LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND

Six items, one of which is arithmetic. I do not repeat the claim that any single
one is binding; correction 11 withdrew that.

## 5. Next load-bearing gap

    LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND

selected because section 2 proves it can never be absorbed, so it must be paid
directly and no representation shift will remove it. Every other open item has at
least one route that might retire it; this one has none.
