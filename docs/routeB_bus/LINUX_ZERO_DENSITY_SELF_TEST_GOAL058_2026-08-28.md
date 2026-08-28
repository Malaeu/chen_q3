---
TASK_ID: LINUX_SELF_TEST_DOES_THE_COUNTEREXAMPLE_APPLY_TO_US
MODE: PAPER_PLUS_DECLARED_NUMERIC_VERIFICATION
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 4bbd4e0b
AUTHORITY: owner standing instruction — verify before reporting
DISCRIMINATOR: alarm, not a transaction
RESULT_CODE: MODEL_FAMILY_SHARES_THE_COUNTEREXAMPLE_MECHANISM
RH_CLAIM: false
---

# I verified the counterexample, then asked whether it applies to us. It may.

## 1. The counterexample is correct

`F_n(z) = cos(n z)`: entire, even, all zeros real at `(k+1/2) pi/n`, exponential
type `n -> infinity`. Zero spacing `pi/n -> 0`. Counted: `1, 2, 6, 25` zeros in
`[0,1]` at `n = 2, 5, 20, 80`, densities `0.64, 1.59, 6.37, 25.46` per unit.

The logic is exact and it is **our own Hurwitz argument run backwards**. If
`g_n F_n` is locally bounded and compact-tight, Montel gives a locally uniform
limit `h`; for any real `x` pick zeros `z_n -> x` of `F_n`, which are zeros of
`g_n F_n` since `g_n` is zero-free; locally uniform convergence gives `h(x) = 0`;
so `h` vanishes on an interval and, the strip being connected, `h ≡ 0`. This
contradicts tightness. So the generic theorem I requested is **false**, and no
choice of zero-free gauge repairs it.

My `R1_A_EXACT` as posed is answered in the negative. Accepted.

## 2. The question that matters more: does the mechanism apply to our family?

Asked immediately, because the kill is not about gauges — it is about **zero
density**. Any family whose real zeros become dense on a fixed interval dies the
same way, gauge or no gauge.

**Structural reason to worry.** Our transform factors as

    T(v)(z) = 2 sin(z L/2) * ( Cauchy transform of v at w = z L/2 ),

and the scalar factor `sin(z L/2)` has zeros at `2 pi k / L`, spacing
`2 pi/L -> 0`. Those zeros are cancelled only where the Cauchy factor has a pole,
i.e. only at lattice points where the coefficient is nonzero. The lattice spacing
is the same `2 pi/L`. So the zero set of `T(v)` interlaces a lattice whose spacing
tends to zero — the same geometry as `cos(n z)`.

**Measured, on the coefficient profile the corridor actually uses** (centred
Gaussian-Hermite, `l^2` normalized), counting real sign changes of `T(xi)` on
`[-1,1]`:

    L =  4  (m ~ 5.5e1) :  0 zeros,  0.0 per unit
    L =  8  (m ~ 3.0e3) :  2 zeros,  1.0 per unit
    L = 16  (m ~ 8.9e6) :  4 zeros,  2.0 per unit
    L = 24  (m ~ 2.7e10):  8 zeros,  4.0 per unit

Roughly linear in `L`. If the literal ground family behaves this way, then by
section 1 **no locally uniform nonzero limit exists on a fixed compact**, and R1
fails for reasons that have nothing to do with the gauge.

## 3. What I am not claiming

Two gaps, both real, and I am not closing either by assumption.

- The coefficient vector above is a **model** of the prolate packet, not the
  literal `selectedFerrersTrackedGroundVector`. The literal one is an eigenvector
  of the CCM matrix and could in principle have far fewer sign changes on a fixed
  interval.
- I have not verified the **variable convention** of `centeredCriticalStrip`
  against the height map `t_n = 2 pi n/L`. If the fixed compact of the roof is
  fixed in a variable that already carries the `L`-rescaling, the density count
  above is the wrong count and the alarm is void.

Either gap, if resolved the favourable way, dissolves the alarm. I raise it
because the unfavourable resolution would be fatal to R1 as a whole, not merely
to a representation, and because it is cheap to settle from the source.

## 4. The decisive question, stated for the source

    LITERAL_GROUND_ZERO_DENSITY_ON_A_FIXED_COMPACT:
    is the number of zeros of the literal selected ground transform inside one
    fixed compact of the centered critical strip bounded uniformly in k?

If yes, our family is separated from `cos(n z)` and R1 survives the kill.
If no, R1 dies by the same counterexample, and the corridor must return to the
owner again.

This is a question about `centeredCriticalStrip`'s convention and about the
literal eigenvector, both of which are on disk. It needs no new mathematics.

## 5. Declaration

Numerics are declared DIAGNOSTIC_NEVER_A_PROOF and are used here only to raise an
alarm, never as an argument. The factorization in section 2 is exact algebra from
the `dslope` definition.
