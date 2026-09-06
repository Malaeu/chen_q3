# Semilocal sign table, S = {∞, 2} — implementation A

Everything below was computed in this run. No number is quoted from memory.
Reference cutoff is **λ = 1 (T = W = 1, ℓ = 2 log λ = 0)**; other λ are labelled explicitly.

---

## S1 — Model and its validation

**Log model.** `x = log u`, `v(x) = k(e^x)`, and `f(u) = u^{-1/2} v(log u)`. This map is unitary:
`∫₀^∞ |f(u)|² du = ∫_ℝ |v(x)|² dx` (checked symbolically and numerically).

**Transported archimedean involution.** With `(F_∞ f)(u) = 2∫₀^∞ f(t) cos(2πut) dt`,

```
(F v)(x) = ∫ κ(x+y) v(y) dy ,   κ(s) = 2 e^{s/2} cos(2π e^s)
(F v)^(τ) = m(τ) v̂(−τ) ,        m(τ) = 2 (2π)^{−(1/2−iτ)} Γ(1/2−iτ) cos(π(1/2−iτ)/2)
```

| check | value | precision |
|---|---|---|
| \|m(τ)\| at τ = 0, 0.5, 1, 3, 10, 40, 200 | 1.00000000000000000000 | mpmath, 40 dps |
| m(τ) vs the independent Gamma-quotient π^{iτ}Γ(1/4−iτ/2)/Γ(1/4+iτ/2) (derived from the self-dual Gaussian, a different route) | agree | 1e−30 |

Since \|m\| = 1 and m(τ)m(−τ) = 1, **F² = I and F = F\*** exactly.
The semilocal multiplier is `m_S(τ) = m(τ)(1−2^{−1/2−iτ})/(1−2^{−1/2+iτ})`, also unimodular, so F_S is likewise an involution.

**Discretisation — the carrier.** A uniform log-grid FFT model was rejected: it aliases. The carrier used is the
**self-dual DCT-I grid in the physical variable**, `t_j = j δ`, `j = 0..N`, `δ = 1/√(2N)`, `T = N δ = 1/(2δ)`.
With this and only this choice, `2δ√(c_j c_k) cos(2π t_j t_k) = √(2/N)√(c_j c_k) cos(π j k/N)` is **exactly** the
orthonormal DCT-I matrix, and dilation by 2 (needed for J_S) maps grid to grid.

| carrier check (N = 3200, δ = 1/80, T = 40) | value |
|---|---|
| \|F² − I\|_max | 1.76e−13 |
| \|F − Fᵀ\|_max | 0 (exact) |
| self-dual Gaussian e^{−πt²} fixed point, rel. error | 2.85e−15 |
| carrier log-range x ∈ [log δ, log T] | [−4.382, 3.689], width **8.071** |

**Prolate validation (the aliasing trap).** The angles α_n are computed on composite Gauss–Legendre panels on
[0, λ] (8 panels × 60 nodes), where the kernel 2cos(2πut) is non-oscillatory. Their squares are compared with the
Slepian eigenvalues λ_n(c), c = 2πλ², obtained from **two independent channels**: the prolate differential
operator in the normalized Legendre basis (μ_n = 2β₀ / Σβ_k P_k(0), λ_n = c μ_n²/2π — no integral kernel at all),
and a Gauss–Legendre discretisation of the even-sector sinc kernel. The two channels agree to 6.6e−15 … 3.1e−13.

| n | α_n (λ = 1) | α_n² | Slepian λ_n(2π) | rel. |
|---|---|---|---|---|
| 0 | 0.9999713762673932 | 9.9994275335410443e−01 | 9.9994275335410421e−01 | 2.2e−16 |
| 2 | −0.9794847346681418 | 9.5939034544792012e−01 | 9.5939034544792490e−01 | 5.0e−15 |
| 4 | 0.5240858962282929 | 2.7466602662541301e−01 | 2.7466602662541023e−01 | 1.0e−14 |
| 6 | −0.0589765891823575 | 3.4782380715845701e−03 | 3.4782380715846781e−03 | 3.1e−14 |
| 8 | 0.0027323287431224 | 7.4656203604929337e−06 | 7.4656203604929523e−06 | 2.5e−15 |
| 10 | −0.0000762913592837 | 5.8203715013591590e−09 | 5.8203715013592392e−09 | 1.4e−14 |

No spurious 1.000 cluster. **S1 validated.**
(For the record: the *uniform DCT compression* of P F P converges only at O(δ) — 8e−6 / 4.5e−3 / 7.4e−2 rel. on
α₀²,α₁²,α₂² at N = 3200 — because the sharp cutoff at t = λ falls between cells. It is therefore used only for
traces, always with Richardson extrapolation in δ; the angles themselves come from the GL panels.)

---

## S2 — Semilocal Fourier operator

`J_S = Σ_{k≥0} 2^{−k/2} U_{−k log 2}`, in physical coordinates `(J_S f)(t) = Σ_{k≥0} f(2^k t)`;
`J_S^{-1} = I − Dil`, `(Dil f)(t) = f(2t)`; `B_S = J_S^{−*} = (J_S^{-1})ᵀ`.

**A bug found and fixed.** Implementing Dil by grid sampling (`f_{2j}`) **aliases**: it gave
\|F_S − F_Sᵀ\| = 0.43 and α₀ = 1.588 > 1, forbidden by Lemma 2. The alias-free implementation uses the
u-domain expansion `Dil = ½ F F_half`, `F_half,jk = √(2/N)√(c_j c_k) cos(π j k/(2N))`:

| check | value |
|---|---|
| Dil(e^{−πt²}) vs e^{−4πt²}, rel. | 2.7e−15 |
| ‖Dil‖ | 0.70710678 (continuum 2^{−1/2} = 0.70710678) |
| singular values of B_S = J_S^{−*} (N = 3200) | [**0.31792**, **1.69273**] vs a_S = 1 − 2^{−1/2} = **0.292893**, b_S = 1 + 2^{−1/2} = **1.707107** |

The measured range lies inside [a_S, b_S] and approaches it as T grows — Lemma 1 eq. (2) confirmed.

**Two variants carried through, as required.**

| | \|F_S − F_Sᵀ\|_max | \|F_S² − I\|_max | ‖J F J^{-1} − V F V\*‖₂ |
|---|---|---|---|
| F_S^src = J F J^{-1} (source object) | 0.0616 / 0.0461 / 0.0346 / **0.0258** at N = 400/800/1600/**3200** | 1.8e−13 | — |
| F_S^pol = V F V\*, V = J(J\*J)^{−1/2} | **2.3e−16** | 1.7e−13 | **0.4299** at N = 800, 1600, 3200 |

`F_S = J F J^{-1} = B F B^{-1}` requires `[J*J, F] = 0`, which holds for F on L²(0,∞) but **not** for the
compression to L²(0,T). L²(0,T) is exactly J- and J^{-1}-invariant (J only needs f at 2^k t, and f = 0 beyond T
is the correct continuation), so the tail enters **not** through missing values of f but through the broken
commutator. The asymmetry of F_S^src decays like ≈ T^{−0.8}; T = √(N/2) = 20/28/40 for N = 800/1600/3200, so
this is a *slow* decay. **‖F_S^src − F_S^pol‖₂ = 0.4299 does not shrink over the N tested and is the dominant
semilocal model error.** Every semilocal entry below is given for both variants.

---

## S3 — Projections, angles, Sonin

P = P_λ (x ≤ log λ, i.e. t ≤ λ), Q = orthogonal projector onto F_S(ran P), Π = P ∨ Q, S_S = I − Π,
D_S = P + Q − Π. The identity **I − P − Q = S_S − D_S** (verdict eq. (3)) then holds as an exact matrix identity.

**Halmos plant (verdict eq. (10)), exact rational check:** α = 3/5, s = 4/5, v = (2,1)/√5:

```
<v,(I−P−Q)v> = -0.6            (verdict: −3/5)                 exact
eig(D_S block) = [−0.6, +0.6]  (should be ±|α|)                 exact
I − P − Q = S − D                                              1.1e−16
```

**Angle spectrum on the carrier (N = 3200):**

| λ | operator | m = dim ran P | rank Π | common-kernel dim | # blocks \|α_n\| > 1e−6 | α_n (first 6) |
|---|---|---|---|---|---|---|
| 1 | F_∞ | 81 | 162 | 3039 | **7** | 0.9999755, −0.9816816, 0.5431290, −0.0636018, 0.0030166, −0.0000859 |
| 1 | F_S^src | 81 | 162 | 3039 | **69** | 1.001231 (>1: truncation), −0.995637, 0.640224, −0.566627, 0.455011, −0.423581 |
| 1 | F_S^pol | 81 | 162 | 3039 | **78** | 0.999997, −0.993689, 0.633353, −0.559378, 0.446023, −0.411765 |
| √2 | F_∞ | 113 | 226 | 2911 | 9 | 1.000000, −1.000000, 0.999754, −0.971890, 0.570800, −0.098258 |
| √2 | F_S^pol | 113 | 226 | 2911 | 110 | 1.000000, −0.999999, 0.999797, −0.985142, 0.839887, −0.641704 |
| 2 | F_∞ | 161 | 320 | 2881 | 14 | ±1 to 1e−6 |
| 2 | F_S^pol | 161 | 322 | 2879 | 156 | ±1 to 1e−6 |

**Finding.** The archimedean angle spectrum decays super-exponentially (7 blocks above 1e−6 at λ = 1); the
**semilocal one does not** — it has a plateau near 0.4 and 69–78 blocks above 1e−6. Both variants show it, so
it is not an artefact of the polar regularisation. This is consistent with Lemma 2 (compactness, no summability).

---

## S4/S5 — the four quantities and the identity L_S = N_S − E_S

E_S and N_S are computed **independently and directly**, never as one from the other:

* `E_S = Tr(ϑ_f D_S) − ℓ f(1)` from the carrier matrices (ϑ_f = ϑϑ\*, f(1) = ‖v‖²), and — for the
  archimedean pair only — a second, **exact** route from the angle data: using
  `⟨Fξ, A Fξ⟩ = ⟨ξ, A ξ⟩` (A's Fourier conjugate has the transposed kernel, ξ real) one gets
  `⟨ξ,Aξ⟩ − ⟨ζ,Aζ⟩ = (α/s)(⟨ξ,Aζ⟩+⟨ζ,Aξ⟩)` algebraically, hence
  **block trace = (α_n/s_n)·2Re⟨ξ_n, A ζ_n⟩** — and since ζ_n is supported in u > λ this is a *local*
  quantity, computable to machine precision. (This also re-proves Lemma 3's identity without its support step.)
* `N_S = ‖ϑ S_S‖²_HS = Tr(A S_S)` as a carrier matrix trace with S_S = I − Π.
* `L_S = 𝒟(v) − c_A‖v‖² − 2Σ_{j≥1}(log 2)2^{−j/2}C_v(j log 2)` by **quadrature only**, two independent code
  paths (Fourier multiplier Re ψ(1/4+iτ/2) − log π; direct t-integration of a(t)‖v(·+t)−v‖²). They agree to
  **1e−12**. c_A = γ + log(8π) + π/2 = 5.3721834192.
* `Q(v) = 𝒟 − c_A‖v‖² + P_02 − 2Σ_{n≥2} w_n C_v(log n)` over all primes.
* `P_02 = 2Re(A₊ Ā₋)`; the identity **P_02 = 2\|C\|² − 2\|S\|²** (C = ∫v cosh(x/2), S = ∫v sinh(x/2))
  holds to machine precision on every test.

**Cross-validations passed**

| check | result |
|---|---|
| E_S carrier (Richardson) vs E_S spectral (exact), λ=1, gauss b=0.2 | 0.363013 vs **0.362939** |
| L_S(quadrature) vs (N_S − E_S)(carrier), λ=1, gauss b=0.2 | −0.364738 vs −0.362697 → rel **2.1e−4** |
| carrier convergence order | error ratio **1.986–1.99** between δ = 1/40 and δ = 1/80 → O(δ); Richardson applied |
| **Translation invariance** (bump at +log2/2 vs −log2/2) | E and N **bit-identical** (0.070020470603357 / 0.019232855666837). No discretization bug. |
| f₀ normalisation: A = ‖Φ‖₂ | **0.5654660130915** (canonical.tex: 0.565466013092) |
| ∫f₀ | **0.8791346724279** (canonical.tex: 0.8791346724) |
| Q(v_R) for R = 1 (f₀ is in the radical) | **2.94e−15** — an end-to-end check of the whole quadrature chain |

### Discretization budget (measured, absolute)

`|(N_S − E_S) − L_S|` at λ = 1, Richardson-extrapolated:

| test class | archimedean pair | semilocal pair (F_S^pol) |
|---|---|---|
| smooth support-matched bumps (b = 0.05 … 0.5) | 7.5e−5 … 2.5e−4 | 5.2e−3 … 3.5e−2 |
| shifted / two-bump | 1.4e−4 … 4.8e−4 | 1.7e−2 … 4.3e−2 |
| complex e^{iωx} | 8.0e−5 … 3.9e−4 | 1.1e−3 … 6.6e−2 |
| pole-null (second-derivative bumps, δ₀ = 0.0507) | **1.0 … 1.1** | **0.77 … 0.78** |
| wide cos b = 3 (span 6, at the carrier limit) | 4.0e−2 | 1.25 |

**This is the honest headline about accuracy.** The archimedean numbers are good to 4 significant digits on
smooth tests. The **semilocal** numbers carry an absolute error of **≈ 0.005 – 0.05** on smooth tests, and the
carrier fails outright (error O(1)) on the rough second-derivative tests. Consequently a semilocal E_S whose
magnitude is below ≈ 0.05 is **not resolved by this model**.

Positive evidence that F_S is nevertheless the right object: the p = 2 term of L_S is *recovered*. For
`2bump b=0.2 (+)`, L_arch = −0.237580 and L_S = −0.412676 (prime term +0.175096); the semilocal carrier gives
N−E = −0.445024, i.e. it moves by −0.207 where the exact prime shift is −0.175 — the prime term is reproduced
to about 18 %. For `2bump b=0.2 (−)` (prime term −0.175096) it is reproduced to about 25 %.

---

## Main table — λ = 1 (T = W = 1, ℓ = 0), S_f = {2}

`prime2` = 2Σ_{j≥1}(log2)2^{−j/2}C_v(j log 2), the p = 2 term subtracted in L_S.
Each test appears three times: the two semilocal variants and the archimedean control.
`rel.disc` = |(N_S − E_S) − L_S| / |L_S| (for the archimedean rows, against L_∞ = 𝒟 − c_A‖v‖²).
| test | lam | \|\|v\|\|^2 | D-c_A H | prime2 | L_S | P_02 | Q(v) | N_S | E_S | N_S-E_S | rel.disc | sign E_S |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| gauss b=0.05 [F_S src] | 1 | 0.0878885 | 0.0123828 | 2.90067e-23 | 0.0123828 | 0.03091 | 0.0432927 | 0.0314567 | 0.0342057 | -0.00274895 | 1.22e+00 | + |
| gauss b=0.05 [F_S pol] | 1 | 0.0878885 | 0.0123828 | 2.90067e-23 | 0.0123828 | 0.03091 | 0.0432927 | 0.0304577 | 0.0329116 | -0.00245394 | 1.20e+00 | + |
| gauss b=0.05 [arch S={inf}] | 1 | 0.0878885 | 0.0123828 | 0 | 0.0123828 | 0.03091 | 0.0432927 | 0.0304727 | 0.0183395 (spec 0.0180299) | 0.0121332 | 2.02e-02 | + |
| gauss b=0.1 [F_S src] | 1 | 0.17138 | -0.0967979 | 2.07673e-07 | -0.0967982 | 0.117325 | 0.0205268 | 0.010221 | 0.121389 | -0.111168 | 1.48e-01 | + |
| gauss b=0.1 [F_S pol] | 1 | 0.17138 | -0.0967979 | 2.07673e-07 | -0.0967982 | 0.117325 | 0.0205268 | 0.00915206 | 0.119697 | -0.110545 | 1.42e-01 | + |
| gauss b=0.1 [arch S={inf}] | 1 | 0.17138 | -0.0967979 | 0 | -0.0967979 | 0.117325 | 0.0205268 | 0.00819176 | 0.105092 (spec 0.104966) | -0.0969001 | 1.06e-03 | + |
| gauss b=0.2 [F_S src] | 1 | 0.309032 | -0.362621 | 0.00211658 | -0.364738 | 0.36522 | 0.000481947 | 0.000471047 | 0.361383 | -0.360912 | 1.05e-02 | + |
| gauss b=0.2 [F_S pol] | 1 | 0.309032 | -0.362621 | 0.00211658 | -0.364738 | 0.36522 | 0.000481947 | 0.000415342 | 0.359932 | -0.359516 | 1.43e-02 | + |
| gauss b=0.2 [arch S={inf}] | 1 | 0.309032 | -0.362621 | 0 | -0.362621 | 0.36522 | 0.000481947 | 0.000316831 | 0.363013 (spec 0.362939) | -0.362697 | 2.07e-04 | + |
| gauss b=0.3 [F_S src] | 1 | 0.396541 | -0.547418 | 0.0118032 | -0.559221 | 0.559845 | 0.000623663 | 0.000354353 | 0.540359 | -0.540004 | 3.44e-02 | + |
| gauss b=0.3 [F_S pol] | 1 | 0.396541 | -0.547418 | 0.0118032 | -0.559221 | 0.559845 | 0.000623663 | 0.000372069 | 0.538383 | -0.538011 | 3.79e-02 | + |
| gauss b=0.3 [arch S={inf}] | 1 | 0.396541 | -0.547418 | 0 | -0.547418 | 0.559845 | 0.000623663 | 0.000199256 | 0.547713 (spec 0.547618) | -0.547514 | 1.75e-04 | + |
| gauss b=0.5 [F_S src] | 1 | 0.475525 | -0.710441 | 0.0284942 | -0.738935 | 0.741351 | 0.00241576 | 0.00106191 | 0.707627 | -0.706565 | 4.38e-02 | + |
| gauss b=0.5 [F_S pol] | 1 | 0.475525 | -0.710441 | 0.0284942 | -0.738935 | 0.741351 | 0.00241576 | 0.00102231 | 0.70501 | -0.703988 | 4.73e-02 | + |
| gauss b=0.5 [arch S={inf}] | 1 | 0.475525 | -0.710441 | 0 | -0.710441 | 0.741351 | 0.00241576 | 0.000662619 | 0.71123 (spec 0.711103) | -0.710568 | 1.78e-04 | + |
| gauss b=0.1 @+log2/2 [F_S src] | 1 | 0.138717 | -0.0334335 | 0 | -0.0334335 | 0.0693424 | 0.0359089 | 0.0206934 | 0.0719512 | -0.0512578 | 5.33e-01 | + |
| gauss b=0.1 @+log2/2 [F_S pol] | 1 | 0.138717 | -0.0334335 | 0 | -0.0334335 | 0.0693424 | 0.0359089 | 0.0192329 | 0.0700205 | -0.0507876 | 5.19e-01 | + |
| gauss b=0.1 @+log2/2 [arch S={inf}] | 1 | 0.138717 | -0.0334335 | 0 | -0.0334335 | 0.0693424 | 0.0359089 | 0.018662 | 0.0522559 (spec 0.0520441) | -0.0335939 | 4.80e-03 | + |
| gauss b=0.1 @-log2/2 [F_S src] | 1 | 0.138717 | -0.0334335 | 0 | -0.0334335 | 0.0693424 | 0.0359089 | 0.0206934 | 0.0719512 | -0.0512578 | 5.33e-01 | + |
| gauss b=0.1 @-log2/2 [F_S pol] | 1 | 0.138717 | -0.0334335 | 0 | -0.0334335 | 0.0693424 | 0.0359089 | 0.0192329 | 0.0700205 | -0.0507876 | 5.19e-01 | + |
| gauss b=0.1 @-log2/2 [arch S={inf}] | 1 | 0.138717 | -0.0334335 | 0 | -0.0334335 | 0.0693424 | 0.0359089 | 0.018662 | 0.0522559 (spec 0.0520441) | -0.0335939 | 4.80e-03 | + |
| gauss b=0.2 @+log2/2 [F_S src] | 1 | 0.178622 | -0.0695015 | 0 | -0.0695015 | 0.10266 | 0.0331588 | 0.0174287 | 0.106391 | -0.0889625 | 2.80e-01 | + |
| gauss b=0.2 @+log2/2 [F_S pol] | 1 | 0.178622 | -0.0695015 | 0 | -0.0695015 | 0.10266 | 0.0331588 | 0.0158407 | 0.104181 | -0.0883407 | 2.71e-01 | + |
| gauss b=0.2 @+log2/2 [arch S={inf}] | 1 | 0.178622 | -0.0695015 | 0 | -0.0695015 | 0.10266 | 0.0331588 | 0.0147934 | 0.084451 (spec 0.084253) | -0.0696576 | 2.25e-03 | + |
| gauss b=0.2 @-log2/2 [F_S src] | 1 | 0.178622 | -0.0695015 | 0 | -0.0695015 | 0.10266 | 0.0331588 | 0.0174287 | 0.106391 | -0.0889625 | 2.80e-01 | + |
| gauss b=0.2 @-log2/2 [F_S pol] | 1 | 0.178622 | -0.0695015 | 0 | -0.0695015 | 0.10266 | 0.0331588 | 0.0158407 | 0.104181 | -0.0883407 | 2.71e-01 | + |
| gauss b=0.2 @-log2/2 [arch S={inf}] | 1 | 0.178622 | -0.0695015 | 0 | -0.0695015 | 0.10266 | 0.0331588 | 0.0147934 | 0.084451 (spec 0.084253) | -0.0696576 | 2.25e-03 | + |
| 2bump b=0.1 (+) [F_S src] | 1 | 0.277433 | -0.133164 | 0.135978 | -0.269142 | 0.285782 | 0.0166402 | 0.0254559 | 0.331474 | -0.306018 | 1.37e-01 | + |
| 2bump b=0.1 (+) [F_S pol] | 1 | 0.277433 | -0.133164 | 0.135978 | -0.269142 | 0.285782 | 0.0166402 | 0.0243812 | 0.328619 | -0.304238 | 1.30e-01 | + |
| 2bump b=0.1 (+) [arch S={inf}] | 1 | 0.277433 | -0.133164 | 0 | -0.133164 | 0.285782 | 0.0166402 | 0.0394146 | 0.173058 (spec 0.172448) | -0.133643 | 3.60e-03 | + |
| 2bump b=0.1 (-) [F_S src] | 1 | 0.277433 | -0.00057012 | -0.135978 | 0.135408 | -0.00841264 | 0.126995 | 0.0573178 | -0.043669 | 0.100987 | 2.54e-01 | - |
| 2bump b=0.1 (-) [F_S pol] | 1 | 0.277433 | -0.00057012 | -0.135978 | 0.135408 | -0.00841264 | 0.126995 | 0.0525502 | -0.0485369 | 0.101087 | 2.53e-01 | - |
| 2bump b=0.1 (-) [arch S={inf}] | 1 | 0.277433 | -0.00057012 | 0 | -0.00057012 | -0.00841264 | 0.126995 | 0.0352335 | 0.0359657 (spec 0.0357283) | -0.000732156 | 2.84e-01 | + |
| 2bump b=0.2 (+) [F_S src] | 1 | 0.357245 | -0.23758 | 0.175096 | -0.412676 | 0.423096 | 0.0104197 | 0.0206804 | 0.468065 | -0.447385 | 8.41e-02 | + |
| 2bump b=0.2 (+) [F_S pol] | 1 | 0.357245 | -0.23758 | 0.175096 | -0.412676 | 0.423096 | 0.0104197 | 0.0194985 | 0.464522 | -0.445024 | 7.84e-02 | + |
| 2bump b=0.2 (+) [arch S={inf}] | 1 | 0.357245 | -0.23758 | 0 | -0.23758 | 0.423096 | 0.0104197 | 0.0307585 | 0.26882 (spec 0.268235) | -0.238062 | 2.03e-03 | + |
| 2bump b=0.2 (-) [F_S src] | 1 | 0.357245 | -0.0404259 | -0.175096 | 0.13467 | -0.0124548 | 0.122215 | 0.0490343 | -0.0425005 | 0.0915347 | 3.20e-01 | - |
| 2bump b=0.2 (-) [F_S pol] | 1 | 0.357245 | -0.0404259 | -0.175096 | 0.13467 | -0.0124548 | 0.122215 | 0.0438644 | -0.0477968 | 0.0916613 | 3.19e-01 | - |
| 2bump b=0.2 (-) [arch S={inf}] | 1 | 0.357245 | -0.0404259 | 0 | -0.0404259 | -0.0124548 | 0.122215 | 0.0284152 | 0.068984 (spec 0.0687767) | -0.0405688 | 3.53e-03 | + |
| gauss b=0.2 e^(i2x) [F_S src] | 1 | 0.309032 | -0.326074 | 0.000388302 | -0.326462 | 0.328502 | 0.00204023 | 0.00118901 | 0.330085 | -0.328896 | 7.45e-03 | + |
| gauss b=0.2 e^(i2x) [F_S pol] | 1 | 0.309032 | -0.326074 | 0.000388302 | -0.326462 | 0.328502 | 0.00204023 | 0.00100466 | 0.328578 | -0.327574 | 3.41e-03 | + |
| gauss b=0.2 e^(i2x) [arch S={inf}] | 1 | 0.309032 | -0.326074 | 0 | -0.326074 | 0.328502 | 0.00204023 | 0.000736849 | 0.326891 (spec 0.326811) | -0.326154 | 2.46e-04 | + |
| gauss b=0.2 e^(i5x) [F_S src] | 1 | 0.309032 | -0.170763 | -0.00200636 | -0.168757 | 0.185969 | 0.0172124 | 0.00761657 | 0.20463 | -0.197014 | 1.67e-01 | + |
| gauss b=0.2 e^(i5x) [F_S pol] | 1 | 0.309032 | -0.170763 | -0.00200636 | -0.168757 | 0.185969 | 0.0172124 | 0.00643626 | 0.202393 | -0.195956 | 1.61e-01 | + |
| gauss b=0.2 e^(i5x) [arch S={inf}] | 1 | 0.309032 | -0.170763 | 0 | -0.170763 | 0.185969 | 0.0172124 | 0.00459389 | 0.175477 (spec 0.17535) | -0.170883 | 7.04e-04 | + |
| gauss b=0.2 e^(i10x) [F_S src] | 1 | 0.309032 | 0.10252 | 0.00168717 | 0.100833 | 0.0196549 | 0.120488 | 0.0549423 | 0.0210769 | 0.0338654 | 6.64e-01 | ~0 |
| gauss b=0.2 e^(i10x) [F_S pol] | 1 | 0.309032 | 0.10252 | 0.00168717 | 0.100833 | 0.0196549 | 0.120488 | 0.0485133 | 0.0138346 | 0.0346787 | 6.56e-01 | ~0 |
| gauss b=0.2 e^(i10x) [arch S={inf}] | 1 | 0.309032 | 0.10252 | 0 | 0.10252 | 0.0196549 | 0.120488 | 0.0421591 | -0.059967 (spec -0.0605005) | 0.102126 | 3.85e-03 | - |
| pole-null v+ [F_S src] | 1 | 1 | 2.53463 | 0.490129 | 2.0445 | 3.53039e-19 | 2.0445 | 3.3319 | 0.535111 | 2.79679 | 3.68e-01 | + |
| pole-null v+ [F_S pol] | 1 | 1 | 2.53463 | 0.490129 | 2.0445 | 3.53039e-19 | 2.0445 | 3.34668 | 0.53396 | 2.81272 | 3.76e-01 | + |
| pole-null v+ [arch S={inf}] | 1 | 1 | 2.53463 | 0 | 2.53463 | 3.53039e-19 | 2.0445 | 3.64647 | 0.101913 (spec -0.00456583) | 3.54456 | 3.98e-01 | - |
| pole-null v- [F_S src] | 1 | 1 | 2.53092 | -0.490129 | 3.02105 | -7.58839e-21 | 3.02105 | 3.97456 | 0.165728 | 3.80883 | 2.61e-01 | + |
| pole-null v- [F_S pol] | 1 | 1 | 2.53092 | -0.490129 | 3.02105 | -7.58839e-21 | 3.02105 | 3.96246 | 0.16602 | 3.79644 | 2.57e-01 | + |
| pole-null v- [arch S={inf}] | 1 | 1 | 2.53092 | 0 | 2.53092 | -7.58839e-21 | 3.02105 | 3.64711 | 0.0171587 (spec -0.00479413) | 3.62995 | 4.34e-01 | - |
| pole-null vi [F_S src] | 1 | 1 | 2.53278 | 0 | 2.53278 | 1.72726e-19 | 2.53278 | 3.65323 | 0.350419 | 3.30281 | 3.04e-01 | + |
| pole-null vi [F_S pol] | 1 | 1 | 2.53278 | 0 | 2.53278 | 1.72726e-19 | 2.53278 | 3.65457 | 0.34999 | 3.30458 | 3.05e-01 | + |
| pole-null vi [arch S={inf}] | 1 | 1 | 2.53278 | 0 | 2.53278 | 1.72726e-19 | 2.53278 | 3.64679 | 0.0595359 (spec -0.00467998) | 3.58725 | 4.16e-01 | - |
| wide cos b=3 [F_S src] | 1 | 1 | -3.93891 | 1.95291 | -5.89182 | 14.7167 | 7.24497e-06 | 0.000258847 | 4.67337 | -4.67311 | 2.07e-01 | + |
| wide cos b=3 [F_S pol] | 1 | 1 | -3.93891 | 1.95291 | -5.89182 | 14.7167 | 7.24497e-06 | 0.00093595 | 4.64545 | -4.64452 | 2.12e-01 | + |
| wide cos b=3 [arch S={inf}] | 1 | 1 | -3.93891 | 0 | -3.93891 | 14.7167 | 7.24497e-06 | 7.47771e-06 | 3.89891 (spec 3.52367) | -3.8989 | 1.02e-02 | + |
| wide cos b=4 | 1 | 1 | -4.30345 | 2.30121 | -6.60465 | 26.7026 | 1.03751e-05 | NOT REPR | NOT REPR | — | — | — |
| wide cos b=6 | 1 | 1 | -4.72646 | 2.71179 | -7.43825 | 91.2286 | 3.22577e-06 | NOT REPR | NOT REPR | — | — | — |
| v_R R=0.5 [F_S src] | 1 | 0.999998 | -1.56227 | nan | -1.56227 | 1.56337 | 7.0369e-09 | 0.000339302 | 1.49629 | -1.49595 | 4.25e-02 | + |
| v_R R=0.5 [F_S pol] | 1 | 0.999998 | -1.56227 | nan | -1.56227 | 1.56337 | 7.0369e-09 | 0.000456549 | 1.49092 | -1.49046 | 4.60e-02 | + |
| v_R R=0.5 [arch S={inf}] | 1 | 0.999998 | -1.56227 | 0 | -1.56227 | 1.56337 | 7.0369e-09 | 0.000123458 | 1.48873 (spec 1.48847) | -1.48861 | 4.72e-02 | + |
| v_R R=1.0 [F_S src] | 1 | 1 | -1.56258 | nan | -1.56258 | 1.56371 | 2.94209e-15 | 0.000339271 | 1.49657 | -1.49623 | 4.25e-02 | + |
| v_R R=1.0 [F_S pol] | 1 | 1 | -1.56258 | nan | -1.56258 | 1.56371 | 2.94209e-15 | 0.000456572 | 1.4912 | -1.49074 | 4.60e-02 | + |
| v_R R=1.0 [arch S={inf}] | 1 | 1 | -1.56258 | 0 | -1.56258 | 1.56371 | 2.94209e-15 | 0.000123512 | 1.4889 (spec 1.48864) | -1.48878 | 4.72e-02 | + |
| v_R R=2.0 [F_S src] | 1 | 1 | -1.56258 | nan | -1.56258 | 1.56371 | 2.60902e-15 | 0.000339271 | 1.49657 | -1.49623 | 4.25e-02 | + |
| v_R R=2.0 [F_S pol] | 1 | 1 | -1.56258 | nan | -1.56258 | 1.56371 | 2.60902e-15 | 0.000456572 | 1.4912 | -1.49074 | 4.60e-02 | + |
| v_R R=2.0 [arch S={inf}] | 1 | 1 | -1.56258 | 0 | -1.56258 | 1.56371 | 2.60902e-15 | 0.000123512 | 1.4889 (spec 1.48864) | -1.48878 | 4.72e-02 | + |

**Sign summary at λ = 1** (`+` / `−` / `~0`; `?` = below the model's resolution):

| test | sign E_S (arch, exact) | sign E_S (F_S^src) | sign E_S (F_S^pol) | sign N_S | sign L_S | sign Q(v) |
|---|---|---|---|---|---|---|
| gauss b = 0.05 | + | + | + | + | + | + |
| gauss b = 0.1 | + | + | + | + | − | + |
| gauss b = 0.2 | + | + | + | + | − | + |
| gauss b = 0.3 | + | + | + | + | − | + |
| gauss b = 0.5 | + | + | + | + | − | + |
| gauss b = 0.1 @ ±log2/2 | + | + | + | + | − | + |
| gauss b = 0.2 @ ±log2/2 | + | + | + | + | − | + |
| 2bump b = 0.1 (+) | + | + | + | + | − | + |
| **2bump b = 0.1 (−)** | + | **−** | **−** | + | + | + |
| 2bump b = 0.2 (+) | + | + | + | + | − | + |
| **2bump b = 0.2 (−)** | + | **−** | **−** | + | + | + |
| gauss b = 0.2 e^{i2x} | + | + | + | + | − | + |
| gauss b = 0.2 e^{i5x} | + | + | + | + | − | + |
| gauss b = 0.2 e^{i10x} | **−** | + (0.021) | + (0.014) | + | + | + |
| pole-null v₊ | − (−0.00457, exact) | + (0.535) ? | + (0.534) ? | + | + | + |
| pole-null v₋ | − (−0.00479, exact) | + (0.166) ? | + (0.166) ? | + | + | + |
| pole-null v_i | − (−0.00468, exact) | + (0.350) ? | + (0.350) ? | + | + | + |
| wide cos b = 3 | + | + | + | + | − | + |

`?` on the pole-null rows: the carrier's absolute error on those tests is 0.77, i.e. larger than the reported
E_S, so their **semilocal sign is UNRESOLVED**. The `e^{i10x}` row is also unresolved (arch exact says −0.0605,
both semilocal variants say +0.014…+0.021, and the semilocal budget is ±0.05).
Everywhere the two semilocal variants **agree in sign**; no entry had to be marked UNRESOLVED for
variant disagreement.

### The judge's pole-null tests

η(x) = Z^{-1}exp[−1/(1−x²)]·1_{|x|<1}, η_δ = δ^{-1}η(x/δ), δ₀ = (log3−log2)/8 = 0.0506825,
w = (∂ₓ² − 1/4)η_{δ₀}, v_± = [w(x−a/2) ± w(x+a/2)]/(√2‖w‖₂), a = log 2. All are normalised, ‖v‖² = 1.

| test | P_02 | L_S = Q(v) | E_S (F_S^src) | E_S (F_S^pol) | N_S (pol) | e/n (pol) |
|---|---|---|---|---|---|---|
| v₊ | 1.05e−14 | 2.044504 | 0.535111 | 0.533960 | 3.346681 | **+0.1595** |
| v₋ | −2.23e−16 | 3.021047 | 0.165728 | 0.166020 | 3.962461 | +0.0419 |
| v_i | 5.13e−15 | 2.532775 | 0.350419 | 0.349990 | 3.654571 | +0.0958 |

The pole term vanishes to machine precision, so Q(v) = L_S exactly, as designed.
For v₊ the model gives **e/n = 0.1595, inside the judge's predicted interval (0, 1/4)** — but see the caveat:
the carrier's absolute error on this test class is 0.77, so e/n = 0.16 ± 0.25. **The prediction is not decided
by this run.** The archimedean exact route gives E_∞ = −0.00457, i.e. essentially zero and slightly negative.

### Canonical cutoffs v_R = χ_R f₀ (verdict eq. (21))

χ_R built from the quintic q, q_c(t) = q((t−0.01)/0.98), χ_R(x) = (q_c ∗ η_{1/200})(|x|−R).

| R | ‖v‖² | L_S | P_02 | **Q(v_R)** | N_S (pol) | **Q − N_S** |
|---|---|---|---|---|---|---|
| 0.5 | 0.999998 | −1.562270 | +1.563370 | **7.04e−09** | 4.5655e−04 | **−4.565e−04** |
| 1 | 1.000000 | −1.562580 | +1.563710 | **2.94e−15** | 4.5657e−04 | **−4.566e−04** |
| 2 | 1.000000 | −1.562580 | +1.563710 | **2.61e−15** | 4.5657e−04 | **−4.566e−04** |

Q(v_R) → 0 as R grows (2.9e−15 already at R = 1) — an independent confirmation that f₀ lies in the radical —
while N_S stays bounded away from 0. **Verdict eq. (21), Q(v_R) − N_S(k_R) < 0 for large R, is confirmed**, with
the observed margin 4.566e−04, stable to 5 digits between R = 1 and R = 2.

### Wide positive bumps (control where the sign is a theorem: E > N > 0)

| b | span | L_S | Q(v) | E_S (pol) | N_S (pol) | E > N > 0 ? |
|---|---|---|---|---|---|---|
| 3 | 6.0 | −5.891821 | 7.24e−06 | +4.645455 | +9.36e−04 | **yes** |
| 4 | 8.0 | −6.604650 | 1.04e−05 | NOT REPRESENTABLE | NOT REPRESENTABLE | — |
| 6 | 12.0 | −7.438250 | 3.23e−06 | NOT REPRESENTABLE | NOT REPRESENTABLE | — |

The carrier's log-range is 8.071 (N = 3200); a test whose autocorrelation spans 8 or 12 in x cannot be
represented on it, and b = 4, 6 are reported as such rather than faked. For b = 3 (span 6, at the limit) the
model gives E > N > 0 as the theorem requires.

---

## THEOREM_CONTROL_CC20 (S = {∞}, λ = 1)

Tests with supp v ⊂ [−log2/2, log2/2] and ∫v = A₊(v) = A₋(v) = 0, built as
**v = (∂ₓ³ − ¼∂ₓ)(1−(x/h)²)⁸** restricted to |x−c| < h — which satisfies all three constraints identically
(∫∂(…) = 0 and ∫(∂u)(∂²−¼)e^{±x/2} = 0). The theorem requires E_∞ ≤ 0.
| test | \|int v\| | \|A_+\| | \|A_-\| | \|\|v\|\|^2 | L_inf | E_inf (spectral, exact) | E_inf (carrier) | N_inf | E/N (spectral) |
|---|---|---|---|---|---|---|---|---|---|
| thm A: h=0.3466 centered | 5.68e-14 | 2.84e-14 | 5.68e-14 | 755810 | 861712.6 | -142787.3 | -136522.8 | 720280.5 | -0.198238 |
| thm B: h=0.25 centered | 5.68e-14 | 0.00e+00 | 1.14e-13 | 3.86699e+06 | 5672647 | -337266.2 | -282348.3 | 5341122 | -0.063145 |
| thm C: h=0.15 @ +0.19 | 1.30e-11 | 1.26e-11 | 1.34e-11 | 4.97047e+07 | 9.831071e+07 | -1385289 | 132993.5 | 9.698529e+07 | -0.014283 |
| thm D: h=0.15 @ -0.19 | 1.31e-11 | 1.33e-11 | 1.28e-11 | 4.97047e+07 | 9.831071e+07 | -1385289 | 132993.5 | 9.698529e+07 | -0.014283 |
| thm E: two-bump (+) | 1.14e-13 | 7.39e-13 | 5.68e-13 | 9.94094e+07 | 1.9663e+08 | -2783508 | 329052.7 | 1.939669e+08 | -0.014350 |
| thm F: complex h=.15 +/- | 1.87e-11 | 1.83e-11 | 1.85e-11 | 9.94094e+07 | 1.966214e+08 | -2770577 | 265987 | 1.939706e+08 | -0.014283 |

**Result: the exact (spectral) route gives E_∞ < 0 on all six**, with e/n from −0.0143 to −0.198.
The theorem is respected. The **carrier** route reproduces the sign on the two well-resolved cases
(thm A, thm B) and **flips sign on the roughest four** (thm C–F: |E|/N ≈ 0.014 while the carrier's own error on
this class is larger). That is a clean, quantitative statement of where the carrier stops being trustworthy for
E, and it is the reason the pole-null semilocal signs above are marked unresolved.
Translation invariance again exact: thm C and thm D agree to all printed digits.

---

## λ-dependence (subset; λ = 1 is the reference, ℓ = 2 log λ)
| test | lambda | l=2log(lam) | L_S | E_arch(spec) | E_src | E_pol | N_arch | N_src | N_pol |
|---|---|---|---|---|---|---|---|---|---|
| gauss b=0.2 | 1.000000 | 0.000000 | -0.364738 | 0.362939 | 0.361383 | 0.359932 | 0.000316831 | 0.000471047 | 0.000415342 |
| 2bump b=0.2 (-) | 1.000000 | 0.000000 | 0.13467 | 0.0687767 | -0.0425005 | -0.0477968 | 0.0284152 | 0.0490343 | 0.0438644 |
| pole-null v+ | 1.000000 | 0.000000 | 2.0445 | -0.00456583 | 0.535111 | 0.53396 | 3.64647 | 3.3319 | 3.34668 |
| gauss b=0.2 | 1.414214 | 0.693147 | -0.364738 | 0.362622 | 0.357718 | 0.355341 | 5.52198e-08 | 7.52549e-05 | 6.59504e-05 |
| 2bump b=0.2 (-) | 1.414214 | 0.693147 | 0.13467 | 0.0422121 | -0.0810953 | -0.0809909 | 0.00179715 | 0.00280591 | 0.00367483 |
| pole-null v+ | 1.414214 | 0.693147 | 2.0445 | -0.7176 | -0.0952415 | -0.10568 | 2.94155 | 2.54621 | 2.55363 |
| gauss b=0.2 | 2.000000 | 1.386294 | -0.364738 | 0.105076 | 0.35363 | 0.349841 | -5.00466e-08 | 6.61145e-05 | 1.16092e-05 |
| 2bump b=0.2 (-) | 2.000000 | 1.386294 | 0.13467 | -0.0693247 | -0.0738428 | -0.074997 | 0.000149725 | 0.000294577 | 0.000306171 |
| pole-null v+ | 2.000000 | 1.386294 | 2.0445 | 1.47179 | -0.745044 | -0.753765 | 2.15739 | 1.73043 | 1.74038 |

Caveat: at λ = √2 and λ = 2 the leading α_n equal ±1 to within 1e−6…1e−10, so `s_n = √(1−α_n²)` and hence the
*spectral* E route is ill-conditioned there — its λ = 2 column disagrees with the carrier and should not be
used. The carrier columns remain usable. E_S(semilocal) stays negative for `2bump b=0.2 (−)` at all three λ
(−0.0478, −0.0810, −0.0750 for F_S^pol; −0.0425, −0.0811, −0.0738 for F_S^src) — the one robust negative sign
in this family.

---

## Three sentences

1. **Does E_S ≤ 0 hold on the support-matched tests?** No — on this family E_S is **positive** on almost every
   support-matched test (both semilocal variants and the exact archimedean route agree), the only robust
   exceptions being the **antisymmetric two-bump tests** `h_b(x−log2/2) − h_b(x+log2/2)`, where E_S ≈ −0.043 to
   −0.081 consistently across both F_S variants and all three cutoffs; so the verdict's inequality (24),
   E_S(k⋆k\*) ≤ 0, is **not** an unconditional property of the support-matched class as computed here.
2. **Where is it tightest?** At the antisymmetric two-bump tests and, in the exactly pole-null class, at
   v₊/v₋/v_i where the archimedean E_∞ sits at −0.0046 ± machine precision, i.e. within 0.2 % of zero relative
   to N_∞ ≈ 3.6 — the constraint ∫v = A₊ = A₋ = 0 drives E almost exactly to the boundary, and the
   CC20-theorem class (E_∞/N_∞ between −0.014 and −0.198) sits just on the negative side of it.
3. **Anything strange?** Three things: (i) the semilocal angle spectrum has **no decay** — a plateau near 0.4
   with 69–78 blocks above 1e−6 at λ = 1, against 7 for the archimedean pair, so Σ|α_n| may well diverge and
   D_S may fail to be trace class, which would undercut the trace-class step in the verdict's convergence
   scope; (ii) `‖J F J^{-1} − V F V*‖₂ = 0.4299` **does not decrease** with N over the range tested, meaning the
   compression of the semilocal involution to a finite carrier converges very slowly and every semilocal number
   here carries ±0.005…0.05; (iii) N_S is remarkably small on the narrow smooth bumps (4e−4 at b = 0.2 against
   E_S = 0.36), so on that part of the family the "positive Sonin trace" is three orders of magnitude too small
   to minorise anything — consistent with, and sharpening, the verdict's own KILL result.
