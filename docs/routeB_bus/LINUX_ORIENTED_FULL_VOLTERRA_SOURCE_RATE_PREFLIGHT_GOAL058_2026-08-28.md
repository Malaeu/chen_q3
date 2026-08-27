---
TASK_ID: GOAL058_SELECTED_FERRERS_ORIENTED_FULL_VOLTERRA_SOURCE_RATE_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric verification
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 53a99a39
DISCRIMINATOR: HOLD
RESULT_CODE: ORIENTED_FULL_VOLTERRA_IDENTITY_WITHOUT_SOURCE_RATE
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - SQRT_M_MASS_AS_AN_OBSTRUCTION_TO_THE_SMOOTH_PART
OPENS: []
---

# The oriented functional: smooth mass is `6/pi`, and the whole arithmetic is one Stieltjes discrepancy

## 0. Result

The oriented one-functional identity is derived and verified. Its consequence is
the sharpest reduction the corridor has produced: **after the oriented
cancellation the smooth part of the source has total mass exactly `6/pi`,
independent of `m`.** The `sqrt m` obstruction is gone from that part, not
estimated away.

What is left of the arithmetic is a single object: the von-Mangoldt Stieltjes
discrepancy `d(psi(x) - x)`. Discriminator: HOLD, matching
`P_ORIENTED_VOLTERRA_1`.

## 1. Derivation of the oriented identity

Not assumed from the verdict; derived, then checked.

Write the consumer as off-diagonal plus diagonal. The off-diagonal part is
`sum_n beta_n omega_n` with `beta_n = integral sin(n t) d mu(t)`, so it equals
`integral G(t) d mu(t)`. The diagonal part is `sum_n M_nn b_n` and, ledger by
ledger from closed form,

    W02_nn   = integral t (cos n t) d mu_W02(t),
    Arch_nn  = integral (2 pi - t) (cos n t) d mu_arch(t),
    Prime_nn = integral (2 pi - t) (cos n t) d mu_prime(t).

Now use the two symmetries. `B` is reflection-even, so for any measure `nu` on
`(0, 2 pi]`, `integral (2 pi - t) B(t) d nu(t) = integral s B(s) d(R_* nu)(s)`.
`G` is reflection-odd, so `integral G d nu = - integral G d(R_* nu)`. Since
`tau = W02 - W_R - Prime`, the archimedean and prime ledgers both enter with a
minus, and both are reflected; the `W02` ledger is not. Collecting,

    Psi = <y, M q> = integral J d mu_W02^raw - integral J d( R_*(mu_arch + mu_prime) )
        = < sigma_m , J >,                                              (1)

    J(t) = G(t) + t B(t),   sigma_m = mu_W02^raw - R_*(mu_arch + mu_prime),

with `mu_W02^raw` left on `(0, infinity)`. The `n`-independent archimedean scalar
is absent because `<y,q> = 0`, per correction 12.

Endpoint laws: `J(0) = 0` and `J(2 pi) = 0`, both from `sum_n b_n = 0` together
with `G(0) = G(2 pi) = 0`; and `J(t) = O(t)` near each endpoint, since `G(t) =
O(t)` and `t B(t) = O(t)`.

**Verification, declared.** On the literal `m = 13`, `N = 3` cell with a random
`q` normalized and `y = Q y_0`: `<y, M q> = -0.0312905620` computed from the
literal matrix, `<sigma_m, J> = -0.0312905619` computed from (1). Difference
`2.5e-11`, quadrature-limited. Endpoint checks `J(0) = 0`, `J(2 pi) = 4.8e-16`,
`sum b = 4.9e-17`.

`J` is the full polarized Volterra kernel in real form: `G` is its
constant-coefficient family and `t B` its linear family. My earlier witness that
this kernel is aperiodic is exactly why the construction works — the source is
left unfolded to match it.

## 2. The folding falsifier, confirmed

The verdict's obstruction to folding is exact:

    sum_{r>=0} (t + 2 pi r) e^{-a(t + 2 pi r)} = e^{-a t}/(1 - q_m) * ( t + 2 pi q_m/(1 - q_m) ),
    q_m = e^{-2 pi a} = m^{-1/2},   a = L/(4 pi).

Checked to machine zero at `t = 0.3, 1.7, 4.0`. The extra term
`2 pi q_m/(1 - q_m) = 2 pi/(sqrt m - 1)` is the winding shadow: folding the
**zeroth** moment is exact, folding the **first** moment is not, and a folded
single-weight formula that omits the shadow is false. My superseded next-gap
`FOLDED_VARIABLE_DIAGONAL_UNIFICATION` is withdrawn on this ground.

## 3. The mass of the oriented source

Split `sigma_m` into its smooth part and its arithmetic remainder. Model the
prime measure by its continuous reference, replacing `d psi(x)` by `dx`; the
reflected reference density is `[L sqrt m/(2 pi^2)] e^{-a t}` on `(0, 2 pi]`, and
the raw `W02` density is `[L/(2 pi^2)](sqrt m - 2 + 1/sqrt m) e^{-a t}` on
`(0, infinity)`. Two pieces remain:

- **on `(0, 2 pi]`**, the difference of densities is
  `-[L/(2 pi^2)](2 - 1/sqrt m) e^{-a t}`, of total mass
  `(2/pi)(2 - 1/sqrt m)(1 - 1/sqrt m) -> 4/pi`;
- **on `(2 pi, infinity)`**, the `W02` tail survives entire, of mass
  `(2/pi)(1 - 2/sqrt m + 1/m) -> 2/pi`.

Total smooth mass `-> 6/pi = 1.909859...`, with no `m` in it. Computed at
`m = 10^2, 10^4, 10^8, 10^16, 10^32`: `1.6043, 1.8782, 1.9095, 1.90986, 1.909859`.

This is the first time the corridor has a source whose smooth part is bounded
rather than of size `sqrt m`. The two `sqrt m` ledgers do not need to be
estimated against each other; in the oriented representation they have already
subtracted.

## 4. What is left, exactly

    Psi = < sigma_m^smooth , J > + < d(psi - x)/sqrt x , J >,

where the first term is bounded by `(6/pi + o(1)) * ||J||_infinity` and the
second is the von-Mangoldt Stieltjes discrepancy, the sole arithmetic input.

One structural remark, offered as an observation and not carried through. Under
the reflection, the prime index `k = m` maps to `t = 0`, and the angles behave as
`t = 2 pi log(m/k)/L`. So the top of the prime range sits at the endpoint where
`J(t) = O(t)`. Integrating the Stieltjes term by parts, the boundary contribution
at `x = m` — the one that carries the full `(psi(m) - m)/sqrt m` — is multiplied
by `J` at that endpoint, which vanishes. Whether this survives the full
integration by parts, and with which weight, is not established here; it is
recorded because it is the first mechanism suggesting the endpoint vanishing is
not decorative.

## 5. Open list, unchanged in membership

    SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
    QPROJECTED_P59_KERNEL_COMPACT_RATE
    SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
    SelectedPhysicalFourierEnergyControl
    COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND   (now: the Stieltjes term of section 4)
    COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

The `sqrt m` mass is struck from the difficulty of the fifth item; what remains
of it is the discrepancy alone.

## 6. Guards

- No component split: the three ledgers are never estimated separately; section 3
  quotes their densities only to exhibit the exact difference.
- The `6/pi` is the mass of a **model** smooth part; the difference between model
  and literal is precisely the Stieltjes term, which is carried, not dropped.
- `||J||_infinity` is not bounded here. It requires the regularity side, whose
  inputs are the `Q`-projected kernel rate and the complement floor.
- Numerics declared, DIAGNOSTIC_NEVER_A_PROOF: the identity check of section 1,
  the folding check of section 2, and the mass table of section 3. Sections 1-3
  are all closed-form derivations; the numbers confirm, they do not carry.

## 7. Next load-bearing gap

    ORIENTED_STIELTJES_DISCREPANCY_AGAINST_AN_ENDPOINT_VANISHING_TEST

that is, a bound for `integral J(t(x)) d(psi(x) - x)/sqrt x` where `J` vanishes to
first order at both endpoints of the reflected range. This is now the entire
arithmetic content of the front.
