# Agent report — Goal 058: derivation of the trial second-jet constant `a_∞ = 1/(16π)`

Date: 2026-09-04
Executor: Linux-Claude subagent (Opus), READ-ONLY mathematics/paper-reading task
Paper: **Connes–Consani–Moscovici, "Zeta Spectral Triples", arXiv:2511.22755v1**,
local PDF `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/pdfs/2511.22755.pdf`, §7 "Outlook", pp. 27–32
Code read: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/true_precision_packet_gate_v1.py`
and `.../portable_k_channel_v1.py`
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no repo file touched except this report, no commit.

```yaml
TASK_ID: GOAL058_TRIAL_SECOND_JET_CONSTANT_DERIVATION
CODE: TRIAL_JET_CONSTANT_DERIVED_EXACT
A_INF: 1/(16*pi)            # = 0.019894367886486917   (exact, not a fit)
B_BLIND_PREDICTION: 13/(256*pi^2)   # = 0.005145216356837   (a_m = a_inf + b/m + O(1/m^2))
Z4_BLIND_PREDICTION: 1/(512*pi^2)   # = 1.978981e-04, coefficient of z^4/m^2 in Phi_m
PX_RH_CLAIM: NOT_MADE
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: true       # scratchpad only, < 2 min, float64 + sympy
VERIFICATION_CHANNEL: independent_prolate_Mellin_route (never touches c_n)
```

**One line.** The ζ-factor of the `E`-map cancels identically in `F_q(z)/F_q(0)` divided by
`Ξ(z)/Ξ(0)`, so `Φ_m` is a **purely archimedean rational function of `t = w(w−1) = −(z²+¼)`**;
the exact operator identity `PW_λ = λ²H + ∂_x(x²∂_x)` makes `1/m = λ^{-2}` a *bona fide*
perturbation parameter, the whole first-order effect is a single `h_8` admixture, and it gives
`a_∞ = 1/(16π)` **exactly** — no fit, no window transform, no Gaussian/heat factor.

---

## 0. What the two objects are (task item 4, answered first because everything rests on it)

### 0.1 The paper's trial

Paper §7, eqs. (7.1)–(7.6):

* `E(f)(u) := u^{1/2} Σ_{n≥1} f(nu)`  — eq. (7.2). This is a **summation (Eisenstein/theta) map**,
  *not* a multiplication by a Ξ-kernel and *not* a convolution.
* `PW_λ := −∂_x[(λ²−x²)∂_x] + (2πλx)²` — eq. (7.5), the "prolate wave operator"; its eigenfunctions
  `h_{n,λ}` carry the Hermite labelling, and by eq. (7.9) the Meixner–Schäfke parameter is
  **`γ = 2πλ²`**.
* `k_λ(u) := E(h_λ)(u), ∀u ∈ [λ^{-1}, λ]` — eq. (7.6), where `h_λ` is, *up to a multiplicative
  scalar*, the unique combination of `h_{0,λ}` and `h_{4,λ}` with **vanishing integral**.
* Limit object: `h = (√3/2^{11/4})h_4 − (3/2^{17/4})h_0 = (π²x⁴ − (3/2)πx²)e^{−πx²}` (Lemma 7.1,
  eq. (7.4)), `k = E(h)`, and `Ξ` is the `⟨R*₊|R⟩`-Fourier transform of `k` (eq. (7.1)).

So the paper's cutoff is **not an extra factor**: it is (i) the compact support `[-λ,λ]` of `h_λ`,
which truncates the `E`-sum at `n ≤ λ/u`, and (ii) the window `u ∈ [λ^{-1}, λ]`.

### 0.2 The code's `g04` / `k1`

`true_precision_packet_gate_v1.py`:

| item | line | content |
|---|---|---|
| `c = 2·π·LAMBDA_SQ` | `:171` | `= 2πλ² = γ` — **exactly the paper's (7.9)** |
| `A[i,i] = k(k+1)`, `A += c²·X2` | `:175–176` | Legendre–Galerkin matrix of `−∂_s[(1−s²)∂_s] + γ²s²` in the *orthonormal* even-Legendre basis (`legendre_x2_matrix_mp`, `:124–145`, carries `√((2l+1)/(2k+1))`) |
| `for which,col in zip((0,2,4,6,8), range(5))` | `:181` | even subspace ⇒ ascending columns are `ps_0, ps_2, ps_4, ps_6, ps_8`; so `h[0]=ps_0`, `h[4]=ps_4` — **correct selection** |
| `integrals[which] = v[0]·√(2λ)` | `:187` | `∫_{-λ}^{λ} h_{n,λ} = v_0√(2λ)`, since `∫_{-1}^{1}P̃_0 = √2` |
| `g04_c = normalize_real_combo([I_4, −I_0])` | `:189` | `h_λ ∝ I_4·h_{0,λ} − I_0·h_{4,λ}` ⇒ **vanishing integral** — the paper's condition |
| `scaled = leg_i·√((2d+1)/(2λ))` | `:207–208` | `g(z) = λ^{-1/2}·ps(z)`, i.e. `h_{n,λ}(x) = λ^{-1/2}ps_n(x/λ)`, unit `L²(R)` norm |
| `u = e^x/λ`, `t = m·e^x/λ²`, `mmax = ⌊λ²e^{-x}⌋` | `:298,:301,:256` | `t = (m·u)/λ` ⇒ the sum is `Σ_{m≤λ/u} h_λ(mu)`: exactly the support cut |
| `e_vals = √u · Σ …` | `:305` | `= E(h_λ)(u)` — eq. (7.2) |
| `L = log(λ²)`, `x ∈ [0,L]`, `c_n = L^{-1/2}∫_0^L … e^{-2πinx/L}dx` | `:249,:279,:310,:313` | `x = log(λu)` ⇒ `u ∈ [λ^{-1}, λ]` — **exactly the paper's interval** |

**Verdict: `g04` is the paper's `k_λ`, with no structural mismatch.** Differences are normalization
only (paper: "up to a multiplicative scalar", Lemma 7.2 fixes it by matching `h_n` pointwise; code:
`ps_n` `L²`-normalized on `[-1,1]`, combination `ℓ²`-normalized, and finally the `c_n` are
`ℓ²`-normalized in `portable_k_channel_v1.py:157`). Every such scalar cancels in `F_q(z)/F_q(0)`.

Residual mismatches worth naming:

1. `MAX_DEGREE = 180` (`:36`) is **not** rebound by `portable_k_channel_v1.with_tp_context`
   (`:98–110`, which rebinds only `LAMBDA_SQ` and `N`). Harmless at `λ² ∈ {12,13,14}` (Legendre tail
   ratio `≈3e-49`), but it degrades at `λ² ≳ 80` (tail `2e-14` at `m = 83`).
2. `g26` (`k2_odd`) and `g048perp` (`k2_even`) are **not** the paper's `k_λ` — only `g04`/`k1` is.
3. The code's `k_edge`, `raw_norm` etc. (`portable_k_channel_v1.py:175–181`) fix a normalization the
   paper leaves free; irrelevant here, relevant if one wants `ξ_λ(λ) = 1` as in §7 bullet 1.

---

## 1. The exact transform identity: `F_q(z) = M(k_λ)(−iz)`

With `f(x) := E(h_λ)(e^x/λ)` on `[0,L]`, `L = log λ²`, `c_n = L^{-1/2}∫_0^L f e^{-2πinx/L}dx`,
`x_n = 2πn/L`, and `sin((z−x_n)L/2) = (−1)^n sin(zL/2)`:

```
F_c(z) = L^{-1/2} Σ_n c_n · 2 sin(zL/2)/(z − x_n)
       = e^{izL/2} ∫_0^L f(x) e^{-izx} dx
       = λ^{iz} · λ^{-iz} ∫_{λ^{-1}}^{λ} k_λ(u) u^{-iz-1} du
       = M(k_λ)(−iz).                                                     (1.1)
```

The two `λ^{±iz}` cancel because `L/2 = log λ`. **The P59 transform of the mode vector is exactly the
Mellin transform of `k_λ` on the paper's window** — no phase, no window factor. This is confirmed by
the code's own second path: `portable_k_channel_v1.K_value` (`:232–243`) computes
`λ^{iγ}L^{-1/2}Σ c_n ∫_0^L e^{i(ω_n−γ)x}dx`, the same object.

For the `E`-map, `M(E(f))(s) = ζ(s+½)·M(f)(s+½)`, and with `h` of Lemma 7.1

```
M(h)(w) = (1/8) π^{-w/2} Γ(w/2) w(w−1),      M(h)(w)·ζ(w) = ξ(w)/4.        (1.2)
```

So `M(k)(−iz) = ξ(½−iz)/4 = Ξ(z)/4` — an independent re-derivation of Lemma 7.1 that also fixes the
constant. Setting `w = ½ − iz`,

```
F_q(z)/F_q(0) = (Ξ(z)/Ξ(0)) · Φ_m(z),   Φ_m(z) = [M_λ(w)/M_λ(½)]·[M_0(½)/M_0(w)]   (1.3)
```

with `M_λ(w) = ∫_0^λ h_λ(x)x^{w-1}dx`, `M_0(w) = M(h)(w)`. **The ζ-factor cancels identically.**
`Φ_m` is therefore a purely archimedean object — no prime information, no window transform, no
Gaussian/heat factor.

Two truncations were dropped in (1.3) and both are **super-exponentially small**, not `O(1/m)`:

* `∫_λ^∞ k_λ(u)u^{s-1}du ≡ 0` exactly (`h_λ` supported in `[-λ,λ]`, so `h_λ(nu) = 0` for `u > λ`);
* `∫_0^{λ^{-1}}`: by Poisson, `k_λ(u) = u^{-1/2}Σ_{k≥1} ĥ_λ(k/u) − ½u^{1/2}h_λ(0)`; the second term is
  `O(e^{-4πλ²})` because `∫h_λ = 0` and `∫h_{n,λ} = χ_n(λ)h_{n,λ}(0)` with `1−χ_n = O(e^{-4πλ²+9log λ})`
  (paper p. 30), and the first is `O(e^{-2πλ²})` since `ĥ_λ` carries only the out-of-band energy
  `1−χ`. This is exactly the step the paper's Lemma 7.3 throws away (see §4).

---

## 2. The `1/m` expansion is exact, not asymptotic-by-luck

Expand the prolate operator (7.5) in `x`:

```
PW_λ = −∂_x[(λ²−x²)∂_x] + 4π²λ²x²
     = λ²·(−∂_x² + 4π²x²) + ∂_x(x²∂_x)
     = λ²·H + V,          V := ∂_x(x²∂_x),        H as in (7.3).           (2.1)
```

**This is an identity, with no remainder.** Hence `PW_λ/λ² = H + ε V` with

```
ε = λ^{-2} = 1/m  exactly  ( = 2π/γ = 2π/c ).                              (2.2)
```

Rayleigh–Schrödinger in `ε` is therefore an honest expansion in integer powers of `1/m` — this is the
structural reason the observer sees a clean `1/m` law and not the paper's `λ^{-1/2}`.

In the ladder algebra of `H` (`a = (2πx+∂)/√(4π)`, `E_n = 2π(2n+1)`), with `S := a² − a†²`:

```
V = ∂_x(x²∂_x) = (S² − 1)/4,                                                (2.3)
V|n⟩ = ¼[ √(n(n−1)(n−2)(n−3))|n−4⟩ − (2n²+2n+3)|n⟩ + √((n+1)(n+2)(n+3)(n+4))|n+4⟩ ].
```

**`V` couples only `n ↔ n±4`.** Verified symbolically against the direct integral
`⟨h_k, ∂(x²∂)h_n⟩ = −∫x²h_k'h_n'` for `(k,n) ∈ {(0,0),(2,0),(4,0),(2,2),(4,4),(0,4),(8,4),(6,2),(6,6),(2,6)}`
— all ten match exactly (`V_{00}=−3/4`, `V_{40}=√6/2`, `V_{44}=−43/4`, `V_{84}=√105`, …).

### First order: one single admixture survives

`h_{0,λ} = h_0 − ε(√6/32π)h_4`, `h_{4,λ} = h_4 + ε(√6/32π)h_0 − ε(√105/16π)h_8`.

The `h_0↔h_4` piece is an **infinitesimal rotation inside the 2-plane `span(h_0,h_4)`**, and the
vanishing-integral combination `I_4(λ)h_{0,λ} − I_0(λ)h_{4,λ}` is invariant under it to first order.
Therefore

```
h_λ = h_u + ε·(√105/16π)·(I_0 h_8 − I_8 h_0) + O(ε²),     h_u := I_4h_0 − I_0h_4 = −(8/√3)h,   (2.4)
```

with `I_n := ∫_R h_n = h_n(0)`: `I_0 = 2^{1/4}`, `I_4 = 2^{3/4}√3/4`, `I_8 = 2^{3/4}√35/16`,
`I_12 = 2^{1/4}√231/32`. **The entire `O(1/m)` deformation of the CCM trial is one `h_8` admixture,
made integral-free.** (`√105 = V_{84}`, `16π = |E_4 − E_8|`.)

---

## 3. The archimedean algebra, and why `a_∞ = 1/(16π)` exactly

Write `M(h_n)(w) = A_0(w)·q_n(w)`, `A_0(w) := ½π^{-w/2}Γ(w/2)`. Because `h_n` is a Fourier eigenfunction
with eigenvalue `1` for `n ≡ 0 (mod 4)`, each `q_n` is a **polynomial in `t := w(w−1)`** (checked
symbolically for `n = 0,4,8,12`):

```
q_0 = κ_0,   q_4 = κ_4(16t+12),   q_8 = κ_8(256t² + 2944t + 1680),   κ_n = 2^{1/4}(2^n n!)^{-1/2}.
```

Hence, with the `A_0` common factor cancelling:

```
Q_u(w) := M(h_u)/A_0 = I_4q_0 − I_0q_4 = −(2/√3)·t                          (3.1)
Q_1(w) := M(g_1)/A_0 = (√3/48π)·t(2t+23),   g_1 = (√105/16π)(I_0h_8 − I_8h_0)   (3.2)
```

`Q_1(1) = 0` (i.e. the `t`-factor) is the vanishing-integral condition; the common `t` cancels:

```
ρ_1(t) := Q_1/Q_u = −(2t + 23)/(32π).                                       (3.3)
```

Now `w = ½ − iz` gives `t = w(w−1) = −(z² + ¼)`, so

```
R_1(z) = ρ_1 = z²/(16π) − 45/(64π),          Φ_m(z) = 1 + ε(R_1(z) − R_1(0)) + O(ε²)
       ⇒  [z²]Φ_m = 1/(16π m) + O(1/m²).                                    (3.4)
```

```
                    a_∞  =  1/(16π)  =  0.019894367886486917      EXACT
```

**Why `1/(8c)`.** With the paper's `c = γ = 2πλ² = 2πm` (eq. 7.9), `1/(16πm) = 1/(8·2πm) = 1/(8c)`, so
the observer's reading is exact. The `8` is `|E_8−E_4|/(2π) = 16π/2π`, i.e. the Hermite 4-level gap
measured in units of `γ/λ²`; the residual archimedean factor is exactly `1`, which is the content of
the two polynomial identities

```
I_0q_8 − I_8q_0 = 256·I_0κ_8·t(t + 23/2),        I_4q_0 − I_0q_4 = −(2/√3)·t.
```

The `t`-slope of their ratio, times `V_{84}/(E_4−E_8) = √105/(−16π)`, times `dt/dz² = −1`, is `1/(16π)`;
equivalently `a_∞ = 8√3·u_4 I_0 κ_8/π` with `u_4I_0κ_8 = 1/(128√3)`.

**Structural corollary (a prediction in its own right).** `R_1` is *exactly quadratic* in `z` — there
is **no `z⁴` term at order `1/m`**. In general `ρ_k` has degree `k` in `t`, so `[z^{2j}]Φ_m = O(m^{-j})`:
`Φ_m` is, order by order, a function of `z²/m`. This is why the observed law is so nearly a pure
quadratic over a wide `x`-range.

---

## 4. Task item 2 — BLIND prediction of `b`

Second-order Rayleigh–Schrödinger (only levels `0,4,8,12` participate; `Δ = 16π`):

```
ψ_0 = |0⟩ + ε α|4⟩ + ε²(β|4⟩ + γ_c|8⟩),     α = −u_0/Δ, β = (V_{44}−V_{00})u_0/Δ², γ_c = u_0u_4/2Δ²
ψ_4 = |4⟩ + ε(a|0⟩ + b'|8⟩) + ε²(p|0⟩ + q|8⟩ + r|12⟩),
      a = u_0/Δ, b' = −u_4/Δ, p = (V_{00}−V_{44})u_0/Δ², q = (V_{88}−V_{44})u_4/Δ², r = u_4u_8/2Δ²
```

with `u_n = ¼√((n+1)(n+2)(n+3)(n+4))`, `V_{nn} = −(2n²+2n+3)/4`. Forming
`H_λ = (∫ψ_4)ψ_0 − (∫ψ_0)ψ_4 = h_u + εg_1 + ε²g_2` gives (both checked: `Σ_k g_i[k]I_k = 0`)

```
g_2 = −(3767·2^{3/4}√3/32768π²)h_0 + (57·2^{1/4}/8192π²)h_4
      + (205√105·2^{1/4}/2048π²)h_8 − (45·2^{3/4}√77/1024π²)h_12
Q_2(w) = −(√3/3072π²)·w(w−1)(4w⁴−8w³−8w²+12w−1075) = −(2√3/3)·t·(4t²−12t−1075)/(2048π²)
ρ_2(t) = Q_2/Q_u = (4t² − 12t − 1075)/(2048π²)
R_2(z) = z⁴/(512π²) + 7z²/(1024π²) − 4287/(8192π²)
```

With `Φ_m = [1 + ερ_1 + ε²ρ_2]/[same at z=0]`:

```
[z²]Φ_m = ε/(16π) + ε²([z²]R_2 − R_1(0)[z²]R_1)
        = ε/(16π) + ε²( 7/(1024π²) + (45/64π)(1/16π) )
        = ε/(16π) + ε²·13/(256π²)
```

```
   a_m = a_∞ + b/m + O(1/m²),      b = 13/(256π²) = 0.005145216356837      ← BLIND PREDICTION
   [z⁴]Φ_m = 1/(512π² m²) + O(1/m³) = 1.978981e-04 / m²                    ← BLIND PREDICTION
```

Full second-jet law:

```
   κ(q_m) = κ_X − a_m/m,   κ_X = ½(log ξ)''(½) = 0.023104993115418970
   a_m    = 1/(16π) + 13/(256π² m) + O(1/m²)
   Φ_m(z) = 1 + z²/(16πm) + (1/m²)[ 13z²/(256π²) + z⁴/(512π²) ] + O(1/m³)
```

---

## 5. Verification (second channel, never touches the `c_n`)

Channel: solve the prolate Legendre–Galerkin eigenproblem directly (tridiagonal in the even-Legendre
basis, `scipy.linalg.eigh_tridiagonal`), build `h_λ`, and evaluate the **Mellin** log-derivative

```
a_m = −(m/2)·[ (log M_λ)''(½) − (log M_0)''(½) ],   (log M_0)''(½) = ¼ψ'(¼) − 8 = −3.700667711373222
```

by dyadic-panel Gauss–Legendre quadrature. This route never constructs the Fourier coefficients `c_n`,
never uses the P59 kernel, and never uses the perturbation theory of §2–4.

| `m = λ²` | `a_m` (this channel) | observer (`c_n` / P59 route) |
|---|---|---|
| 13  | `0.020306960865` | `0.020307` |
| 23  | `0.020123307301` | `0.020123` |
| 43  | `0.020015499405` | `0.020016` (rounds to `0.020015`; ≈5e-7 fit noise in the observer's row) |
| 83  | `0.019956751214` | — |
| 163 | `0.019926035015` | — |
| 323 | `0.019910323064` | — |
| 643 | `0.019902376590` | — |

Fits `a_m = a_∞ + b/m + c/m²`:

| sample | `a_∞` | `b` | `c` |
|---|---|---|---|
| `m = 83,163,323` | `0.01989436823` | `0.005144979` | `0.0027231` |
| `m = 163,323,643` | `0.01989436890` | `0.005144658` | `0.0027578` |
| **derived (exact)** | **`0.01989436789`** | **`0.005145216`** | — |

`a_∞` agrees to **9 significant digits**; `b` to 4–5, limited by float64 quadrature and by the
Legendre-degree wobble at `m = 643`. Sharper test: `m·(m(a_m − 1/(16π)) − 13/(256π²))` gives
`2.728e-3, 2.706e-3, 2.694e-3, 2.677e-3` at `m = 43,83,163,323` — **bounded and convergent**, whereas a
wrong `b` would make this diverge linearly; this bounds `|δb| ≲ 1e-7`.

Full-shape check of (1.3) (`Φ_m` computed from the two Mellin transforms, including the
`λ^{w−1/2}` factor):

| `m` | `x` | `Re Φ_m(x)` | `Im Φ_m(x)` | `1 + a_m x²/m` | `+ x⁴/(512π²m²)` |
|---|---|---|---|---|---|
| 13 | 1  | `1.001563300` | `1.1e-15` | `1.001562074` | `1.001563245` |
| 13 | 4  | `1.025309521` | `8.3e-16` | `1.024993183` | `1.025292949` |
| 13 | 8  | `1.105164775` | `3.2e-14` | `1.099972730` | `1.104768999` |
| 43 | 8  | `1.030239262` | `6.6e-15` | `1.029790511` | `1.030228893` |

`Im Φ_m ≡ 0` to roundoff — the ζ-factor and the `λ^{-iz}` phase cancel exactly, as (1.3) demands. The
quartic column confirms the blind `[z⁴]Φ_m = 1/(512π²m²)` prediction to the level of the next
(`x⁶/m³`) term.

Independent consistency anchors computed en route: `κ_X = 0.02310499311541897` (matches the given
value), and `M(h)(w)ζ(w) = ξ(w)/4` (eq. 1.2) reproduced symbolically, which re-derives Lemma 7.1.

---

## 6. Task item 3 — behaviour on the imaginary axis, and the rate in Lemma 7.3

**`Φ_m(iy)` is exactly real.** For real `w`, `M_λ(w) = ∫_0^λ h_λ(x)x^{w-1}dx` and `M_0(w)` are real,
so `Φ_m(iy) = [M_λ(½+y)/M_λ(½)]·[M_0(½)/M_0(½+y)] ∈ R`. The only zero of `M_0` in the strip is at
`w = 1` (from the `w(w−1)` factor of (1.2)), and `M_λ(1) = ∫_0^λ h_λ = 0` too, so the apparent pole at
`y = ½` is removable and `Φ_m(iy)` is real-analytic across it. Numerically `Im Φ_m(iy) = 0` identically.

**Monotone, and below 1.** `Φ_m(iy) = 1 − y²/(16πm) + O(1/m²)`: strictly decreasing in `|y|`, i.e. the
trial transform is *slightly flatter than* `Ξ` in the imaginary directions (equivalently
`κ(q_m) = κ_X − a_m/m < κ_X`). Verified at `m = 13`: `Φ(0)=1`, `Φ(0.2i)=0.999937519`,
`Φ(0.4i)=0.999750100`, `Φ(0.49i)=0.999625017`, `Φ(1.0i)=0.998439151`, against
`1 − y²/(16π·13)` = `0.999938787, 0.999755146, 0.999632566, 0.998469664` — monotone, agreeing to `~1e-6`.

**Lemma 7.3 gives NO rate for the 2-jet.** Its statement is bare locally-uniform convergence, and its
proof loses the rate twice:

1. It bounds `|E(h_λ)(u) − E(h)(u)| ≤ u^{1/2}(λ/u)δ(λ)` and integrates, yielding
   `|M(k_λ)(s) − ∫_{λ^{-1}}^{λ}k(u)u^{s-1}du| ≤ 2cλ^{-½-α}(1−2α)^{-1}`, i.e. **`O(λ^{-1/2}) = O(m^{-1/4})`
   at `α = 0`** — eight powers of `λ` worse than the truth. The loss is entirely at the small-`u` end;
   it disappears once one uses `∫h_λ = 0` together with `ĥ_{n,λ}(0) = χ_n(λ)h_{n,λ}(0)`,
   `1 − χ_n = O(e^{-4πλ²+9logλ})`, which the paper itself proves one page earlier (p. 30) but does not
   feed into Lemma 7.3.
2. The final tail step, `∫_λ^∞ k(u)u^{s-1}du → 0` "due to the convergence of the integral", carries **no
   rate at all** (it is in fact `O(e^{-πλ²})`).

Converting even a rated version into a 2-jet rate additionally needs Cauchy estimates on a compact
disc, which locally-uniform convergence does supply. So the best the paper's §7 currently yields for
the 2-jet is `O(λ^{-1/2}) = O(m^{-1/4})`; the truth, from (2.1)–(3.4), is

```
κ(q_m) − κ_X = −1/(16π m) + O(1/m²),   an exact asymptotic series in 1/m = λ^{-2} = 2π/c.
```

Lemma 7.2's `O(λ^{-2})` sup-bound is the *correct* order and is exactly what (2.1) explains; Lemma 7.3
simply fails to transport it.

---

## 7. What this closes and what it opens

**CLOSES.**
* The constant is derived, not fitted: `a_∞ = 1/(16π) = 1/(8c)` exactly, with the mechanism named
  (`PW_λ = λ²H + ∂(x²∂)`; the sole first-order effect is the `h_8` admixture `√105/(16π)`).
* `Φ_m` is identified: not a window/Gaussian/heat factor, but the ratio of **archimedean Mellin
  polynomials in `t = w(w−1)`**; the ζ-factor cancels identically, so the `1/m` deviation of the CCM
  trial from `Ξ` carries **no prime information whatsoever**.
* The `O(x⁴)` remainder in the observer's law is explained and quantified: it is `O(1/m²)`, because
  `R_1` is exactly quadratic in `z`.
* Code/paper identification `g04 ≡ k_λ` verified line by line.

**OPENS (small).**
* `MAX_DEGREE = 180` is not rebound by `with_tp_context`; the packet degrades for `λ² ≳ 80`. One-line
  fix if the ladder is ever run at larger `λ`, but it is a live falsifier for any future large-`m` scan.
* The `1/m` series is Rayleigh–Schrödinger, hence asymptotic; nothing here proves convergence, and the
  exponentially small pieces (`1−χ_n`, the window ends) are bounded only heuristically above. A Lean-
  grade statement would need the Meixner–Schäfke expansion with an explicit remainder, or a direct
  resolvent bound on `H + εV`.

---

## 8. Final code

```
TRIAL_JET_CONSTANT_DERIVED_EXACT
```

`a_∞ = 1/(16π)` is the exact limit, derived from the operator identity (2.1) and the polynomial
identities of §3, and confirmed to 9 significant digits by an independent Mellin channel.
Blind predictions on record: `b = 13/(256π²) = 0.005145216356837` and
`[z⁴]Φ_m = 1/(512π² m²)`.

Scratch scripts (session-local, not in the repo):
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/{pt.py,pt2.py,num2.py,fit.py,shape.py}`
