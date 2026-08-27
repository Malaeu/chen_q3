---
TASK_ID: GOAL058_SELECTED_FERRERS_ZERO_TRANSFER_COMPACT_OBSERVABILITY_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 60df219b
DISCRIMINATOR: HOLD
RESULT_CODE: ZERO_TRANSFER_EXACT_WITHOUT_QUANTITATIVE_COMPACT_OBSERVABILITY
LEAN_EDIT: false
NUMERICS: none
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - FINITE_CELL_OBSERVABILITY_POSITIVITY
OPENS: []
---

# Compact observability: positive at every cell, and the window sees only `log m` of `m` modes

## 0. Result

`Obs_{m,K} > 0` is proved for every finite cell, by analyticity rather than by
span at the poles, so the compact quantifier is respected. The observation
operator then reduces to an explicit object: a scalar times a **discrete Cauchy
transform evaluated on a window**.

That reduction exposes the difficulty quantitatively and in the direction
opposite to my previous report: the window covers `O(log m)` of the `2m+1` lattice
sites, so observability is structurally weak for directions localized away from
it. No cofinal envelope is established in either direction. Discriminator: HOLD.

## 1. Finite-cell positivity, proved without the pole trick

Let `K` be a fixed compact with nonempty interior in the tracking strip and let
`v` range over the unit sphere of `q_m^perp`. Define
`O_{m,K}(v) = sup_{z in K} |<C_m^{-1} Q_m kappa_m(z), v>|`.

Each `kappa_{m,k}` is entire in `z`, so `z -> <C^{-1} Q kappa(z), v>` is entire.
If it vanished on `K`, which has an interior point and hence a limit point, it
would vanish identically; the coefficient vector `Q C^{-1} v` would then be zero
by linear independence of the `kappa_k`, forcing `v = 0` since `C^{-1}` is
injective and `v in q^perp`. So `O_{m,K}(v) > 0` for every unit `v`. The map
`v -> O_{m,K}(v)` is continuous and the unit sphere of the finite-dimensional
space `q^perp` is compact, so the infimum is attained and

    Obs_{m,K} > 0   for every fixed finite m.

The pole evaluation of report `0acfef97` is not used; it proves span on the whole
plane, which is a different quantifier, per correction 13 section 4.

## 2. The observation operator in closed form

`C` and `Q` are Hermitian, so with `u = Q C^{-1} v in q^perp`,

    <C^{-1} Q kappa(z), v> = <kappa(z), u>.

Substituting the closed form `kappa_k(z) = L sin(w)/(w - k pi)`, `w = z L/2`,

    O_{m,K}(v) = sup_{w in K'} | L sin(w) * sum_k conj(u_k)/(w - k pi) |,
    K' = (L/2) K.                                                        (1)

So observability of a direction is the supremum, over a rescaled window, of a
**discrete Cauchy transform** of that direction, damped by `L sin(w)`. This is the
same transform the consumer error already runs on; the front now uses one object
in three places.

## 2a. The window covers a vanishing fraction of the lattice

`K` is fixed, so `K'` has diameter `~ (L/2) diam(K)`, i.e. it spans

    N_window ~ L diam(K)/(2 pi)  =  O(log m)

lattice sites out of `2m+1`. The observation window therefore sees a fraction
`O(log m / m)` of the carrier. For a direction localized at modes `|k| ~ m`, every
denominator in (1) is of size `~ m pi`, so

    O_{m,K}(e_j) <~ L * sup_{K'}|sin w| / (m pi)  <~  (L/pi) m^{sigma_K/2 - 1},

with `sigma_K = max_{z in K} |Im z|`, using `|sin w| <= e^{|Im w|} = m^{|Im z|/2}`.
Hence the **worst** direction is observed only at scale `m^{sigma_K/2 - 1}`, which
tends to zero for any compact with `sigma_K < 2`. Consequently

    Obs_{m,K} <~ (L/pi) m^{sigma_K/2 - 1} -> 0,

and no lower envelope for `Obs_{m,K}` exists. Any usable statement must therefore
be about the **specific** direction `Q Phi(a_rho)`, never about the infimum.

## 3. The specific direction, and why its localization matters

`Phi(a) = [S_a, H] q + C_a q`. Both terms are built from `q`, which is the
projected prolate packet: by construction its coefficient mass is concentrated at
low `|n|`, and the catalogue's own object measuring the deviation is
`selectedFerrersFiniteCCMOddMass`. `[S_a,H]q` spreads that mass through the
Hilbert kernel, whose tails decay like `1/|n|`. So `Phi` is concentrated near the
centre of the lattice — inside the observation window, not outside it.

This is the favourable configuration for observability and the reason section 2a
does not settle the question: the bound there is for the worst direction, and
`Phi` is not the worst direction. What is missing is a **lower** envelope for

    O_{m,K}( Q Phi(a_rho) )

along the selected schedule, which requires a quantitative statement about how
much of `Phi`'s mass lies inside a window of `O(log m)` sites, and how the damping
`L sin(w)` interacts with it on `K'`. Neither is available, and I will not
substitute the absence of a supplier for a bound, per correction 13 section 7.

## 4. Threshold comparison, stated explicitly

The verdict's necessary object is

    Z_{m,K}(rho) = m^{sigma} (log m)^{3/2} sup_{z in K} |T_{m,z}(a_rho)|,

and `sup_z |T| = O_{m,K}(Q Phi(a_rho))` by (1) and the pairing identity. So the
kill requires

    O_{m,K}( Q Phi(a_rho) )  >~  m^{-sigma} (log m)^{-3/2}

infinitely often. Section 2a shows the generic worst direction sits far below this
at `m^{sigma_K/2 - 1}`, and section 3 shows `Phi` is not that direction. The
comparison is therefore open, with the two sides currently separated by no proved
inequality in either direction.

## 5. The growing quartet, exact vector and criterion

For `rho` with `sigma > 0` the quartet contributes, with `a = a_rho`,

    e^{2 pi a} T(a) + e^{2 pi bar a} T(bar a) = 2 Re( e^{2 pi a} <y, Phi(a)> )

when the source coefficients are real, the two remaining members being damped by
`e^{-2 pi a}`. The exact cancellation criterion for the growing pair is therefore

    Re( e^{2 pi a} < y, Phi(a) > ) = 0   for all z in K,

which by linearity in `y` is a **real-linear** condition on `Phi(a)`, weaker than
the complex condition `Q Phi(a) = 0`. Correction 13 section 5 withdrew my
identification of the two. Whether the real condition can hold for the literal
selected `q` is open; it is one real linear equation per `z`, and `y(z)` spans
`q^perp`, so it is equivalent to `Re(e^{2 pi a} Phi(a)) = 0` as a real vector, i.e.
`e^{2 pi a} Phi(a)` purely imaginary. That is a codimension-`(2N+1)` real
condition, not a symmetry.

## 6. Cancellation among all zeros of maximal real part

Not established, and I record what would decide it rather than guessing. Let
`sigma_max` be the supremum of `Re rho - 1/2`. The zeros attaining it contribute
`sum_j 2 Re( e^{2 pi a_j} <y, Phi(a_j)> )` with `|e^{2 pi a_j}| = m^{sigma_max}`
common to all of them and only the phases `e^{2 pi i gamma_j L/(2 pi)} = m^{i gamma_j}`
differing. Since these phases oscillate in `m` while `Phi(a_j)` varies slowly, the
sum is a trigonometric polynomial in `log m` with frequencies `gamma_j`. Complete
cancellation for all large `m` would force every coefficient to vanish, by
almost-periodicity; partial cancellation on a sparse set of `m` is not excluded.
So a `limsup` statement, not a `lim`, is the right target, and the corridor's
schedule `m = k+2` is cofinal enough to make `limsup` meaningful. This is the
first structural handle on cross-zero cancellation and is offered as such, not as
a theorem.

## 7. Next load-bearing gap

    LOWER_ENVELOPE_FOR_O_M_K_OF_Q_PHI_ALONG_THE_SCHEDULE

with the explicit threshold `m^{-sigma} (log m)^{-3/2}` of section 4. The
observation operator is now closed form, the finite-cell positivity is proved, and
the worst-direction upper bound is explicit; what is absent is any statement about
the one direction that matters.
