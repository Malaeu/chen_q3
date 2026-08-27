---
TASK_ID: GOAL058_SELECTED_FERRERS_ORIENTED_STIELTJES_ZERO_TRANSFER_CIRCULARITY_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric verification
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: ac8b183b
DISCRIMINATOR: FAIL
RESULT_CODE: SIGNED_ORIENTED_STIELTJES_RATE_IS_ZERO_FREE_REGION_STRENGTH
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - SIGNED_ORIENTED_STIELTJES_ROUTE_AS_AN_UNCONDITIONAL_ROUTE
OPENS: []
---

# Zero transfer: the consumer detects off-line zeros, so its rate cannot be unconditional

## 0. Result

The transfer coefficient has an exact finite form, and it is **not** structurally
zero. The annihilation condition reduces to a single sharp criterion which the
selected trial has no reason to satisfy and generically does not. Consequently a
zero off the critical line is **detected** by the consumer, and proving the
required compact rate unconditionally would prove a zero-free region.

Discriminator: FAIL. This is the second of the two outcomes named in `b11a33e0`,
and it closes the arithmetic gate honestly rather than leaving it open.

## 1. Transfer coefficient, exact finite form

With `J(t) = sum_n omega_n sin(n t) + t sum_n b_n cos(n t)` and `Re a > 0`,

    T(a) = integral_0^{2 pi} J(t) e^{-a t} dt
         = sum_n omega_n S_n(a) + sum_n b_n C_n(a),
    S_n(a) = n (1 - r)/(a^2 + n^2),
    C_n(a) = (a^2 - n^2)(1 - r)/(a^2 + n^2)^2 - 2 pi a r/(a^2 + n^2),
    r = e^{-2 pi a},

the verdict's form, confirmed. Removable denominators are handled by analytic
continuation of the original finite integral. Verified against direct quadrature
at `a = 0.4` and `a = 0.25 + 0.9i` to `7e-16`.

## 2. The transfer is a source pairing of exactly the consumer's shape

Substituting `omega_n = conj(y_n)(Hq)_n + conj((Hy)_n) q_n` and
`b_n = conj(y_n) q_n`, and collecting by `conj(y_j)` using
`sum_{n != j} S_n q_n/(n-j) = -(H S q)_j`,

    T(a) = < y , Phi(a) >,   Phi(a) = [S_a, H] q + C_a q,                (1)

with `S_a = diag(S_n(a))`, `C_a = diag(C_n(a))`. Verified numerically at three
values of `a` to `4e-16`.

`Phi(a)` is the divided-difference matrix of the single-exponential source
`psi_a(x) = integral_0^{2 pi} sin(x t) e^{-a t} dt` applied to `q`: `S_n(a)` is
`psi_a(n)` and `C_n(a)` is `psi_a'(n)`. So the zero transfer has the **same
algebraic shape as the consumer itself**, with the completed source replaced by
one exponential.

## 3. The span gate, settled trivially

`kappa_k(z) = L sin(w)/(w - k pi)`, `w = z L/2`. Evaluate at the pole
`z = p_j = 2 pi j/L`, i.e. `w = j pi`: every entry with `k != j` vanishes and the
`j`-th equals `L cos(j pi) = ± L`. Hence

    kappa(p_j) = ± L e_j,

so the kernel rows contain the standard basis, and `{ kappa(z) }` spans the whole
carrier; `{ Q kappa(z) }` spans `q^perp`; and since `C^{-1}` is invertible and
preserves `q^perp`, `y = C^{-1} Q kappa(z)` ranges over all of `q^perp` as `z`
varies. Verified numerically at `j = -2, 0, 1`.

## 4. Exact annihilation criterion

By section 3, `z -> T_{m,z}(rho)` is identically zero **iff** `Phi(a_rho)` is
orthogonal to `q^perp`, i.e. iff

    Q Phi(a_rho) = 0,   equivalently   q is an eigenvector of [S_a, H] + C_a.   (2)

This is sharp, not sufficient-only. The selected Ferrers row is constructed from
a prolate two-mode combination whose defining conditions — mean zero, `L^2`
normalization, modes `0` and `4`, the anchor relations — make no reference to
`psi_a` for any `a`. There is no source theorem making (2) hold, and the
catalogue supplies none; asked this session, nothing returned.

The verdict's own falsifier settles the generic case: on modes `{0,1}` with
`q = e_0`, `y = e_1`, the test is `J(t) = sin t`, endpoint-vanishing and
`Q`-orthogonal, yet `T(a) = (1 - e^{-2 pi a})/(a^2 + 1) != 0`. Confirmed to
`1e-16`. Endpoint vanishing and `Q`-orthogonality are therefore not sufficient,
exactly as stated.

## 5. Quartet cancellation does not save it

For a zero `rho` the functional equation and conjugation give the quartet
`rho, 1 - rho, bar rho, 1 - bar rho`, whose transfer arguments are
`a, -a, bar a, - bar a` with `a = (rho - 1/2) L/(2 pi)`. Since
`m^{rho - 1/2} = e^{2 pi a}`, two members grow and two decay. For real source
coefficients `T(bar a) = conj(T(a))`, so the two growing members combine to

    2 Re( e^{2 pi a} T(a) ),

which vanishes identically in `z` only if `Re(e^{2 pi a} T(a)) = 0` for all `z` —
again a condition of type (2), not a symmetry. The quartet organizes the terms;
it does not cancel them.

## 6. The circularity, stated with its inequality

Write `sigma = Re rho - 1/2 > 0`. The zero contributes to the consumer at scale

    (L/(2 pi^2)) * m^{sigma} * |T(a)|,   |T(a)| = |<y, Phi(a)>|.

For `|a| ~ sigma L/(2 pi)` and modes `|n| <= m`, the entries obey
`S_n(a) = O(n/|a|^2)` and `C_n(a) = O(1/|a|^2)`, so `||Phi(a)|| = O(1/L^2)` up to
the trial's own norm, and the contribution is of order `(||y||/L) m^{sigma}`. The
front requires `|Psi| = o(1/sqrt L)` on compacts, hence would require

    ||y|| * m^{sigma} = o( sqrt L )

for every off-line zero. Since `||y||` is bounded below by the graph solve and
`m^{sigma} -> infinity` for any fixed `sigma > 0`, the required rate is
incompatible with the existence of any zero off the critical line.

**Therefore an unconditional proof of the required compact rate would prove a
zero-free region of the same strength.** The signed oriented Stieltjes route is
not an unconditional route.

## 7. What this does and does not say

It does **not** say the construction is wrong. The opposite: a finite family that
could not see an off-line zero would be worthless as a certificate, and this
computation shows ours sees one, with an explicit coefficient. The Guinand-Weil
dictionary predicts exactly this — the finite form evaluates a zero sum, so zeros
are visible in it by design.

It does say that the tracking rate, in this representation, is not a lemma on the
way to the theorem; it is the theorem. Any further work on the five constructed
inputs — the complement floor, the kernel rate, the energy adapter, the
normalizer, the regularity budget — would be spent proving a bound whose truth
already implies what it was meant to help prove. The verdict's
`EXECUTION_PRIORITY` freeze was correct, and this preflight discharges it in the
negative.

## 8. What survives untouched

- the oriented one-functional identity `Psi = <sigma_m, J>`, verified to `2.5e-11`;
- the uniform ceiling `6/pi` on the smooth source variation;
- the closed form `||kappa(z)||^2 = L^2 sinh(L Im z)/(L Im z)`;
- the polarized Volterra/Duhamel identification and all Lean nodes;
- the center spectral normal form, kernel-green.

None of these depends on the rate. They are representation assets and remain
available to any future route that does not consume the arithmetic gate.

## 9. Next load-bearing gap

    OWNER_REPRESENTATION_RERANK

The arithmetic gate is closed in the negative for this representation. Reopening
requires either a different consumer that does not detect zeros at this strength,
or an explicit decision to work conditionally. Neither is mine to choose.
