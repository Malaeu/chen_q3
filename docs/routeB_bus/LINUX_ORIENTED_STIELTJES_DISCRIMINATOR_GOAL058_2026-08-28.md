---
TASK_ID: GOAL058_ORIENTED_STIELTJES_DISCREPANCY_AGAINST_AN_ENDPOINT_VANISHING_TEST
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric evaluation
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 5ec3b20c
DISCRIMINATOR: FAIL
RESULT_CODE: ABSOLUTE_MAJORANT_OF_THE_STIELTJES_TERM_REIMPORTS_THE_SUBPOWER_WALL
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - MAJORANT_ROUTE_FOR_THE_ORIENTED_STIELTJES_TERM
OPENS: []
---

# The Stieltjes discriminator: the majorant route dies, and it dies at the old wall

## 0. Result

The precommitted partial-summation identity is derived and its two boundary terms
**both vanish**, exactly as predicted. The endpoint vanishing of `J` is therefore
real and load-bearing, not decorative.

It is also not enough. Bounding the resulting integral by the absolute value of
`E(x) = psi(x) - x` reimports the `exp(L/2)` versus `exp(c L^{3/5})` gap that was
declared FATAL at `a843c458`. Discriminator: FAIL, for the majorant route only.
Section 4 states precisely what is and is not killed.

## 1. Repairs accepted

- **Total variation.** My headline "exactly `6/pi`, independent of `m`" is
  repaired. The exact value is `(2/pi)(1 - r)(3 - 2r)` with `r = m^{-1/2}`,
  strictly below `6/pi` for every finite `m`; `6/pi` is the supremum over the
  cofinal family and the limit. Computed: `1.60428` at `m = 10^2`, `1.87816` at
  `10^4`, `1.90954` at `10^8`, `1.90985929` at `10^16`, agreeing with `6/pi` to
  `2e-16` at `10^32`. The `m`-independent statement is the **uniform upper
  bound**, and that is what the front may use.
- **Category.** The full oriented source is not a finite measure; only the
  `W02`-minus-prime-main smooth part is. "Total mass of `sigma_m`" is withdrawn
  as a forbidden object.
- **Archimedean functional.** The verdict's bound is confirmed and its constant
  evaluated: `C_arch = integral_0^infinity u e^{u/2}/sinh(u) du = 8.5986645773`,
  finite because the integrand tends to `1` at the origin and to `2 u e^{-u/2}`
  at infinity. So `|<R_* mu_arch, J>| <= (8.5987/L) * Lip(J)`, and the complete
  non-arithmetic part is controlled in the mixed norm
  `||J||_infinity + Lip(J)/L`.

## 2. The partial summation, derived

With `t_m(x) = 2 pi log(m/x)/L` and `f(x) = J(t_m(x))/sqrt x`,

    t_m'(x) = -2 pi/(L x),
    f'(x)   = -x^{-3/2} [ (2 pi/L) J'(t_m(x)) + (1/2) J(t_m(x)) ].

Integrating by parts,

    integral_[1,m] f dE = [ f E ]_1^m - integral_1^m E f' dx.

Both boundary terms vanish: at `x = m` because `t_m(m) = 0` and `J(0) = 0`; at
`x = 1` because `t_m(1) = 2 pi` and `J(2 pi) = 0` — note this holds despite
`E(1) = -1 != 0`, so it is the test that kills it, not the source. Hence

    R_m(J) = -(1/pi) integral_1^m E(x) x^{-3/2}
             [ (1/2) J(t_m(x)) + (2 pi/L) J'(t_m(x)) ] dx,

which is the precommitted target verbatim, including sign and endpoint
convention. Nothing was repaired after seeing a rate.

## 3. Why the majorant fails

Unconditionally `|E(x)| <= C x exp(-c (log x)^{3/5} (log log x)^{-1/5})`. Write
`x = e^u`, so `dx = e^u du` and `x^{-3/2} |E| <= C e^{-u/2}`. The endpoint
vanishing gives `J(t_m(x)) = O((L - u)/L)`, so with `v = L - u`,

    integral_1^m |E| x^{-3/2} |J| dx  <~  e^{L/2} * e^{-c L^{3/5}} * (4/L).

The two exponents do not compete: `L/2` against `c L^{3/5}`. Evaluated,

    m = 10^6:    L/2 = 6.91,     c L^{3/5} = 4.83
    m = 10^50:   L/2 = 57.57,    c L^{3/5} = 17.25
    m = 10^1000: L/2 = 1151.29,  c L^{3/5} = 104.07
    m = 10^10000:L/2 = 11512.93, c L^{3/5} = 414.31

The difference grows without bound, so the majorant diverges at every size. The
`1/L` bought by the endpoint vanishing is a polynomial factor against an
exponential gap; it changes nothing. This is the same obstruction recorded as
`GOAL058_COMBINED_GAMMA_RETAINED_PRIME_OSCILLATION_WALL` and ratified FATAL in
`a843c458`: sub-power savings against a power demand.

## 4. What is killed and what is not

**Killed:** any route that bounds `R_m(J)` through `|E|`. That includes every
bound of Korobov-Vinogradov type, and it is the reason the endpoint vanishing,
though genuine, does not by itself close the front.

**Not killed:** the signed evaluation of `R_m(J)`. The integrand oscillates and
nothing above uses that. But the risk must be named rather than left implicit.
Expanding `E` by the explicit formula, `R_m(J)` becomes a sum over zeta zeros in
which a zero with `Re rho = sigma` contributes at scale `m^{sigma - 1/2}`. A
bound at consumer strength, uniform in `m`, would therefore constrain how far
right zeros may lie. That is the shape of the converse recorded at `4651fc18`
(`INGHAM_TURAN_PINTZ_CONVERSE`), and it is the same circularity boundary the
corridor met before. I do **not** claim the converse applies here — our `J` is a
specific damped test and the required strength is `o(1/sqrt(log m))` on compacts,
not a uniform power saving. I claim only that the risk is of that family and must
be adjudicated before the signed route is opened.

## 5. Honest position of the front

Of the six open items, five concern objects we construct and are unaffected by
this result. The sixth, the arithmetic one, has now been narrowed to a single
signed integral whose majorant provably fails. The oriented representation
achieved something real — the smooth source is uniformly bounded by `6/pi` where
it used to be `sqrt m` — and that gain does not extend to the discrepancy.

## 6. Next load-bearing gap

    SIGNED_ORIENTED_STIELTJES_EVALUATION_OR_ITS_CIRCULARITY_VERDICT

that is: either an evaluation of `R_m(J)` that uses the oscillation of `E`, or a
ruling that such an evaluation at the required strength is equivalent to a
zero-free region and therefore inadmissible. The second outcome would close the
front honestly; the first would open it. Both are cheap to decide compared with
attempting either blindly, and I do not select between them.
