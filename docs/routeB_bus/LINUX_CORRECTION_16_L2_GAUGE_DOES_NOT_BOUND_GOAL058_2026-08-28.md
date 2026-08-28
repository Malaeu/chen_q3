---
TASK_ID: LINUX_SELF_CORRECTION_16
MODE: PAPER_PLUS_DECLARED_NUMERIC_VERIFICATION
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: e7fc70b0 sections 4-5
AUTHORITY: owner standing instruction this session — verify every finding before reporting it
RH_CLAIM: false
---

# Correction 16 — I checked my own claim and it fails: the `L^2` gauge does not bound the family

## 1. What I withdrew and why I checked it

Report `e7fc70b0` said `R1_A` "reduces to propagation" and that "the real-zero
structure is what a Cartwright-type argument would consume". Both sentences were
written without verification. Checked now, on the owner's standing instruction.

**Check B, real zeros and growth.** For entire functions with only real zeros the
modulus **increases** in the imaginary direction. Tested on `sin z`, on a cubic
with three real roots, and on `prod_{k=-3}^{3}(z-k)`, at two real abscissas and
five heights: monotone increase in every case. So real-zeroness is the **source**
of the off-axis growth, not a tool against it. My sentence had the arrow
backwards.

**The decisive check.** For the `L^2`-gauged **raw** family, normalized on the
disc of radius `0.25` at the origin, the ratio `sup_{K} |hat F| / || hat F ||`
on the disc of radius `0.15` centred at `0.6 i`:

    L =  4 :   3.46
    L =  8 :   9.14
    L = 16 :  90.48
    L = 32 : 7579.60

Growth consistent with `e^{L h/2}`. **So the `L^2`-gauged raw family is not
locally bounded on the strip**, and `R1_A` is not merely "unproved" for that
gauge — it is false. Withdrawn.

The reason is structural and vector-independent: `T(v)(z) = 2 sin(z L/2) *
(Cauchy transform of v)`, and the scalar prefactor alone contributes
`e^{L |Im z|/2}` whatever `v` is. No choice of coefficient normalization removes a
factor that has already been pulled out front.

## 2. What survives

**Check A, the mean-value constant.** `sup_K |f| <= (1/(r sqrt pi)) ||f||_{L^2(K_0)}`
for `K` at distance `r` inside `K_0`: verified over 40 random holomorphic
instances at `r = 0.3, 0.5`, worst observed ratios `0.53` and `0.60`, so the bound
holds with room. Section 4 of `e7fc70b0` is arithmetically correct; what it does
**not** do is reach compacts outside the gauge set, which is exactly where the
growth lives.

**`R1_B` still stands.** The tightness argument uses only that the `L^2` norm on
`K_0` is `1` and that the strip is preconnected. It never uses boundedness, so it
is unaffected.

## 3. What the checks produced instead, and it is better than what I withdrew

**The zero-free type corrector works.** Multiplying by `exp(i z L_k/2)` — the
multiplier already present in the corridor as `bareTransform` — and then gauging
in `L^2` on the same disc gives, at the same test point `0.6 i`:

    L =  4 :  1.0170
    L =  8 :  0.5225
    L = 16 :  0.1310
    L = 32 :  0.0039

decreasing, against `7579.60` for the raw family at `L = 32`. The multiplier has
**no zeros**, so it is admissible as the gauge `gamma` of `SlotS2` and leaves the
zero set untouched.

**The transform of an even coefficient vector is even in `z`.** Verified to
`3e-14` at three complex points and two values of `L`, with a control: an odd
coefficient vector gives a discrepancy of order `2` to `13`. Symbolically,
`kappa_{-n}(-z) = kappa_n(z)`, so `xi` even implies `T(xi)(-z) = T(xi)(z)`. The
ground vector **is** even, by the banked centrosymmetry of the finite CCM matrix.
So for the raw object one half-plane controls the other.

## 4. The gap that is now exact

The corrected object `exp(i z L/2) T(xi)` is bounded in the **upper** half-plane
and doubly amplified in the lower; the raw object `T(xi)` is **even**. Neither
fact alone covers a symmetric compact, and the two do not compose trivially,
because the corrector is not even. So the open statement is:

    R1_A_EXACT: a single holomorphic gauge g_k, zero-free on the centered
    critical strip, such that { g_k * T(xi_k) } is uniformly bounded on every
    compact of the strip, given exponential type L_k/2 -> infinity, all zeros
    real, and even symmetry.

## 5. Ledger

Twenty-fourth forbidden move: **check the direction of a structural property
before citing it as help.** Real zeros force growth off the axis; I cited them as
if they controlled it.

Twenty-fifth: **a bound proved inside a set is not a bound on the set's
neighbourhood.** The mean-value estimate is uniform and correct and reaches only
compacts strictly inside the gauge set; the family's difficulty is entirely
outside it.
