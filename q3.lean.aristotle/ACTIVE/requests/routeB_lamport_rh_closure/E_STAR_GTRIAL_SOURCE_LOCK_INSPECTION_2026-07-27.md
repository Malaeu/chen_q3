# E_star → gTrial_m source-lock inspection

Date: `2026-07-27`
Scope: report only; no theorem claim.

## Exact chain

The multiplicative window data are:

```text
λ_m = √m
L_m = log m
d*u = du/u
I_m = [λ_m⁻¹, λ_m]
H_m = L²(I_m, d*u)
```

Lean source locks:

```text
D0KTrialStage1.lean:19-20   λ_m
D0KTrialStage1.lean:26-27   L_m
D0KTrialStage1.lean:33-34   d*u
D0KTrialStage1.lean:40-41   I_m
D0KTrialStage1.lean:50-51   H_m
```

For the midpoint representative `hTrial_m`, Stage 2 defines

```text
E_star(hTrial_m)(u)
  = √u · ∑'_{n : ℕ+} hTrial_m(nu)

gTrial_m
  = E_star(hTrial_m)|_[λ_m⁻¹,λ_m]
    ∈ L²([λ_m⁻¹,λ_m], du/u)

gTrial_m_N
  = P_m_N(gTrial_m).
```

Lean source locks:

```text
D0KTrialStage2.lean:24-26   E_star
D0KTrialStage2.lean:41-47   gTrial_m
D0KTrialStage2.lean:56-62   gTrial_m_N
```

The underlying D0 locks cited by those declarations are
`D0_5_GROUND_AND_TRIAL_TYPES.md:81-92`,
`PEN_3_3_G04_OBJECT_DICTIONARY.md:112-133,141-160,169-180,195-212`, and
`H8ULBMAL/fulltext.md:1262-1267,1293-1297,1410-1419`.

## (a) Quadratic/autocorrelation check

```text
NO.
```

`E_star` is a starred summation operator linear in `hTrial_m`; restriction to
`I_m` and the orthogonal projection `P_m_N` remain linear.  Neither
`conj hTrial_m`, a convolution `hTrial_m ⋆ hTrial_m̃`, nor
`|hTrial_m|²` occurs in the Stage-1/2 chain.  Therefore these files do not
provide an autocorrelation or exact-square factorization of `gTrial_m`.

## (b) Mellin values

With the paper's convention
`M(k)(s)=∫₀^∞ k(u)u^(s-1)du`
(`H8ULBMAL/fulltext.md:1420-1424`), the Stage-1/2 definitions expose only

```text
M(gTrial_m)(s)
  = ∫_[λ_m⁻¹,λ_m]
      u^(s-1/2) · (∑'_{n : ℕ+} hTrial_m(nu)) du.

M(gTrial_m)(0)
  = ∫_[λ_m⁻¹,λ_m]
      u^(-1/2) · (∑'_{n : ℕ+} hTrial_m(nu)) du.

M(gTrial_m)(±σ)
  = ∫_[λ_m⁻¹,λ_m]
      u^(±σ-1/2) · (∑'_{n : ℕ+} hTrial_m(nu)) du.
```

```text
CLOSED EVALUATED FORMS VISIBLE: NO.
```

Stage 1–2 contain no Mellin-transform declaration and no evaluation of these
three integrals.  The paper passage at `H8ULBMAL/fulltext.md:1420-1467`
supplies critical-strip convergence/error estimates, not closed values at
`0, ±σ`.
