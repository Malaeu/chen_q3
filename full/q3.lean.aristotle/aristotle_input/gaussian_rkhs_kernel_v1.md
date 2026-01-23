# Gaussian RKHS kernel identity (Bochner/Fourier) — v1

## What to prove

Fill in the `sorry` proofs in:

- `full/q3.lean.aristotle/aristotle_input/gaussian_rkhs_kernel_v1.lean`

Target theorem (main deliverable):

- `GaussianRKHS_Sandbox.integral_conj_mul_kFun`

It should prove the **exact** identity

```
∫ ω, conj (kFun t0 x ω) * kFun t0 y ω
  = (Real.exp (-((x - y)^2) / (4*t0)) : ℂ)
```

for `t0 > 0`.

## Dependencies between lemmas

1) `kFun_norm_sq`  
Used to simplify the integrand’s norm and reduce `L2`-type integrability to a Gaussian integral.

2) `integrable_norm_sq_kFun`  
Uses `kFun_norm_sq` + `integrable_exp_neg_mul_sq` (Mathlib) to show integrability.

3) `integral_conj_mul_kFun` (main)  
Algebraically simplify `conj(kFun x ω) * kFun y ω` into a constant factor times
`cexp (I * t * ω) * cexp (-b * ω^2)`, then apply:

- `fourierIntegral_gaussian (hb : 0 < b.re) (t : ℂ)`

with `b = (t0 : ℂ)` and `t = ((y - x) : ℂ)`.

Then cancel the normalization constant (the `normConst` was chosen exactly for this).

## Hints (very important)

- Use `open scoped ComplexConjugate` and `conj` (`starRingEnd`) for conjugation.
- `fourierIntegral_gaussian` is already in Mathlib: don’t re-prove the Gaussian Fourier transform.
- Be careful: `simp` can rewrite `(t0 / 2 : ℝ)` into `t0 / (2 : ℂ)` after coercions; avoid “simp explosion”.
  Prefer controlled rewriting (`dsimp`, `ring_nf`, `simp [*, pow_two]`) on small subexpressions.
- Key identities:
  - `conj (cexp z) = cexp (conj z)` (use `Complex.exp_conj`)
  - `‖cexp z‖ = Real.exp z.re` (use `Complex.norm_exp`)
  - `∫ ω, cexp (I*t*ω) * cexp (-b*ω^2) = (π/b)^(1/2:ℂ) * cexp (-t^2/(4*b))`

## Output expectation

Return hole-free proofs (no `sorry`, no `exact?`) so we can safely port the lemmas into the main Lean project.

