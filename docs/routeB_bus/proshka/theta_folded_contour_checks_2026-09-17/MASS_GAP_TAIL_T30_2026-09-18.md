# STATUS: TAIL_REDUCED_TO_RAY_MEAN_T_LEMMA
```yaml
OPERATIVE_CLASS: MASS_GAP_UNIFORM_QUARTER
DATE: 2026-09-18
COMPACT: CERTIFIED_ARB  # 83eb3c8d, 889/889 balls, envelope 0.3758969538 at (1/2, sqrt(20))
TAIL_T_GT_30: REDUCED_NOT_CLOSED
GAMMAINC_USED: false
RH_CLAIM: false
```

The compact `T ∈ [√20, 30] × σ ∈ [1/64, 1/2]` is paid: every arb ball of
`(1 − M₋/M₊)/σ` lies above `1/4`, infimum `0.3758969538` at the corner
`(σ, T) = (1/2, √20)`, `N = 10`, radius `6.8e-74`
(`dh_control/mass_gap_corner_arb.json`, commit `83eb3c8d`).

The tail `T > 30` is **not** paid. What follows is the exact dictionary
(no `gammainc`), the two-ray identity that would give `c = 1/4`, and the
single missing lemma. Textbook stationary-phase / van der Corput constants
do not close that lemma at `T = 30⁺` (cubic phase ≈ 3 rad on a 3σ window).

## 0. Objects, integral only

Cutoff (6.3), `r = 0`: `ϑ = π/4 − 1/(T+1)`, `c = cos 2ϑ`,
`M = ⌈√((T+1)(32 + 20 ln(T+1))/3)⌉`, `N = M − 1`. Source atom and ray
(Proshka enclosure (2.5), (3.1)):

\[
\phi_n(z)=\bigl(4a_n^2 e^{9z/2}-6a_n e^{5z/2}\bigr)e^{-a_n e^{2z}},
\quad a_n=\pi n^2,
\]
\[
I_n(p,\vartheta)=\int_0^\infty\phi_n(t+i\vartheta)\,e^{p(t+i\vartheta)}\,dt,
\quad
I_n(-p,-\vartheta)=\int_0^\infty\phi_n(t-i\vartheta)\,e^{-p(t-i\vartheta)}\,dt.
\]

Write `α_n(t)` and `β_n(t)` for the two integrands, `u` the `2N`-vector of
ray values, `v = ∂_p u`, `w_j = |u_j|^2`, `U^2 = ∑ w_j`. The `t`-moments
and the barycentres (defined wherever `u_j ≠ 0`)

\[
\tau_n^+=\frac{\int_0^\infty t\,\alpha_n(t)\,dt}{I_n(p,\vartheta)},
\qquad
\tau_n^-=\frac{\int_0^\infty t\,\beta_n(t)\,dt}{I_n(-p,-\vartheta)}
\]

give the exact logarithmic derivatives

\[
\partial_p I_n(p,\vartheta)=(\tau_n^+ + i\vartheta)\,I_n(p,\vartheta),
\qquad
\partial_p I_n(-p,-\vartheta)=(i\vartheta - \tau_n^-)\,I_n(-p,-\vartheta).
\]

No incomplete gamma is used. `J = e·u`, `D = e·v`,
`h_N = 4\Re(D\overline J)`, `s = u^*v`,
`λ_± = 2\Re s ± 2√{U^2 V^2 − (\Im s)^2}`, masses `M_±` as in HEAD_SIGN (4.3).
`G := (1 − M_-/M_+)/σ = h_N/(σ M_+)`.

## 1. Exact identities [PAPER]

**1.1.** `D = iϑ J + X_t − Y_t` with `X_t = ∑_n τ_n^+ I_n^+`,
`Y_t = ∑_n τ_n^- I_n^-`. Hence

\[
h_N = 4\Re\bigl((X_t - Y_t)\overline J\bigr).
\]

**1.2.** `Im s = ϑ U^2 + Δ_{\Im}`,
`Δ_{\Im} = \Im(∑_+ w τ^+ − ∑_- w τ^-)`, and the `ϑ`-terms cancel:

\[
\boxed{\mathrm{disc}
  := U^2 V^2 - (\Im s)^2
  = U^2\sum_j w_j|\tau_j|^2 - Δ_{\Im}^2
  \ge U^2\sum_j w_j (\Re\tau_j)^2.}
\]

(The last step is Cauchy–Schwarz on `Δ_{\Im}`.) Therefore

\[
\frac{\sqrt{\mathrm{disc}}}{U^2}\ \ge\ \sqrt{\langle(\Re\tau)^2\rangle},
\qquad
4\frac{\sqrt{\mathrm{disc}}}{U^2}\ \ge\ 4\sqrt{\langle(\Re\tau)^2\rangle}.
\]

**1.3.** On `σ = 0`, conjugacy `β_n(t) = \overline{α_n(t)}` gives
`I_n^- = \overline{I_n^+}`, `τ_n^- = \overline{τ_n^+}`, `h_N = 0`,
`M_+ = M_-`. At a simple axial zero (`J = 0`, `D ≠ 0`)

\[
\lim_{σ\to 0} G = 4\frac{\sqrt{\mathrm{disc}}}{U^2}
  \ \ge\ 4\sqrt{\langle(\Re\tau)^2\rangle}.
\]

This is the identity advertised as `4√⟨τ²⟩`. It is the zero-limit, not a
lower bound at finite `σ`.

**1.4.** `M_+ = h_N/2 + Q/√{\mathrm{disc}}` with
`Q = |D|^2 U^2 + |J|^2 V^2 + 2\Im(D\overline J)\,\Im s`. Hence

\[
G = \frac{4\Re(D\overline J)\,\sqrt{\mathrm{disc}}}
         {σ\bigl(2\Re(D\overline J)\,\sqrt{\mathrm{disc}} + Q\bigr)}.
\]

`G ≥ 1/4` is equivalent to `Re(D\overline J)\,√{\mathrm{disc}} ≥ σ Q / (2(8−σ))`.

## 2. Two-ray identity [PAPER]

Restrict to one pair with a common real barycentre `τ` (the model for the
`n = 1` pair, which carries most of `U^2` at `T = 30^+`; see §4).
`ℓ_+ = iϑ+τ`, `ℓ_- = iϑ−τ`. On `σ = 0`, `|I_+| = |I_-|` by conjugacy.

Let `w_± = |I_±|^2`, `δ = (w_+ − w_-)/U^2`, `U^2 = w_+ + w_-`. Then
`√{\mathrm{disc}} = τ U^2`, `h_N = 4τ(w_+ − w_-)`, and the `μ = \Im(I_+\overline{I_-})`
cross terms cancel in `Q`, giving

\[
G = \frac{2δ}{σ\bigl(1+δ + 2(ϑ/τ)^2 |J|^2/U^2\bigr)}.
\]

Along the axis `∂_σ(w_+ − w_-) = 2τ U^2` at `σ = 0`, so `δ = \tanh(2τσ)`
if `τ` is frozen. Then `|J|^2/U^2 ≤ 2` and

\[
\boxed{G
  \ \ge\
  \frac{e^{4τσ}-1}
       {σ\bigl(e^{4τσ} + 2(ϑ/τ)^2(e^{4τσ}+1)\bigr)}
  =:\ F(τ,ϑ,σ).}
\tag{2.1}
\]

`F` is decreasing in `σ` on `(0, 1/2]` and increasing in `τ` for
`τ ∈ (1/2, 2)`, `ϑ ∈ (3/4, π/4)`. At the left edge of the tail,
`ϑ(30^+) = π/4 − 1/31`, the numerical infimum of `F` on `σ ∈ (0, 1/2]` is
attained at `σ = 1/2`:

| `τ` | `F(τ, ϑ(30), 1/2)` |
|---|---|
| 0.55 | 0.219 < 1/4 |
| 0.583 | 0.256 |
| 0.64 | 0.319 |
| `t_0(30) = 0.783` | 0.488 |

So **`c = 1/4` on `T > 30` follows from a uniform `τ_{\mathrm{rms}} ≥ 0.58`**,
with a 2% margin at the worst `(τ, σ) = (0.583, 1/2)`, once the pair-model
error (unequal `τ_±`, `n ≥ 3`, `Im τ` — the last only helps disc) is absorbed
in that margin.

## 3. Stationary time of ray `n`

Phase of `α_n` along the real `t`-axis:

\[
S_n(t) = T t - a_n\sin(2ϑ)\,e^{2t}.
\]

Unique real critical point

\[
t_0(n,T)
  = \tfrac12\log\frac{T}{2 a_n\sin(2ϑ)}
  = \tfrac12\log\frac{T}{2π n^2\sin(2ϑ)},
\]

interior to `(0, ∞)` iff `n ≤ n_s := √{T/(2π\sin 2ϑ)}` (the bulk).
`S_n''(t_0) = −2T`. Amplitude `e^{(9/2+σ)t − a_n c e^{2t}}` is log-concave
and its mode `t_{\mathrm{mag}}` lies to the **right** of `t_0`
(`t_{\mathrm{mag}}/t_0 → 1` only as `T → ∞`; at `T = 30`, `n = 1`:
`t_0 = 0.783`, `t_{\mathrm{mag}} = 1.20`). For `n = 1`, `T > 30`,

\[
t_0(1,T) \ \ge\ \tfrac12\log\frac{T}{2π} \ \ge\ \tfrac12\log\frac{30}{2π} > 0.782.
\]

Diagnostic (1D `mp.quad` of (2.5), dps 25, no `gammainc`):

| `T` | `σ` | `Re τ_1` | `t_0(1)` | `√⟨|τ|²⟩` | `4√⟨|τ|²⟩` | `G` | `G / 4√⟨|τ|²⟩` |
|---|---|---|---|---|---|---|---|
| 30.42 (γ₄) | 1/64 | 0.847 | 0.790 | 0.748 | 2.99 | 2.89 | 0.967 |
| 31 | 1/64 | 0.867 | 0.799 | 0.761 | 3.04 | 4.61 | 1.51 |
| 31 | 1/2 | 0.901 | 0.799 | 0.811 | 3.24 | 1.79 | 0.55 |
| 40 | 1/64 | 0.853 | 0.926 | 0.685 | 2.74 | 2.18 | 0.79 |
| 40 | 1/2 | 0.835 | 0.926 | 0.729 | 2.92 | 1.35 | 0.46 |
| 60 | 1/2 | 1.395 | 1.129 | 1.311 | 5.24 | 1.85 | 0.35 |

Row γ₄: `G → 4√⟨τ²⟩` to 3%, the identity 1.3. Finite `σ` compresses the
ratio by a factor 0.35–0.55, matching `F(τ,ϑ,σ)/4τ`. `n = 1` carries
76% of `U^2` at `T = 31`; `n ≥ 3` is 1% (quad, not a tail theorem). The
first IBP term `|φ_n(iϑ)|/|T − 2a_n\sin 2ϑ|` at `T = 30`, `n = 4` is
`< 0.04\,|I_1|`; a complete tail theorem needs the `∫|(g/S')'|` remainder
and is not claimed.

If the bulk barycentres satisfy `Re τ_n ≥ t_0(n,T)` (or even
`t_0(n,T) − 6/T`), then `τ_{\mathrm{rms}} ≥ 0.64` at `T = 30^+` with
weights `1/n` on `n ≤ n_s` (and the RMS **grows** like
`√⟨(C − \log n)^2⟩ → √2` as `T → ∞`). Then (2.1) gives `G ≥ 0.32 > 1/4`.

## 4. The missing lemma

**Lemma (open).** For `T > 30`, `0 ≤ σ ≤ 1/2`, and every bulk index
`1 ≤ n ≤ √{T/(2π\sin 2ϑ)}`,

\[
\Re\tau_n(p,ϑ)\ \ge\ t_0(n,T) - \frac6T.
\]

Together with the `n ≥ n_s+2` IBP tail and (2.1), this lemma implies
`G ≥ 1/4` on the tail, hence with the compact, **`c = 1/4` on the whole
domain**.

Why it is not paid here. Localise at `x = √T\,(t − t_0)`:
`S − S(t_0) = −x^2 − (2/(3√T)) x^3 + O(x^4/T)`. On a 3σ window
`|x| ≤ 3`, the cubic is `18/√T` radians: **3.3 rad at `T = 30`**, 1.3 rad
at `T = 200`, 0.3 rad only for `T ≥ 3600`. A quadratic-phase remainder
with tracked constants therefore does not start at `T = 30`. First-order
IBP on `[0, t_0−Δ]` is equally loose at `T = 30` (the bound on the
complement exceeds the Fresnel main term). The left **endpoint** `t = 0`
is in fact negligible (`A(0)/A(t_0) · 1/|S'(0)| ≲ 10^{-2}` of the
central term); the obstruction is the cubic on the peak itself, not the
endpoint.

Empirically `Re τ_1 ∈ (t_0, t_{\mathrm{mag}})` on every computed cell, so
the lemma is plausible with room (`0.867 > 0.799` at `T = 31`). That is
not a proof.

## 5. What closes the tail, and what does not

- Repeating the 889-point 2N-ray arb grid for `T > 30` is the compact
  method again, not an analytic tail.
- A **1-dimensional** arb of the two moments `∫ α_n`, `∫ t α_n` for
  `n = 1, 2` on `T ∈ (30, 80] × σ ∈ \{1/64,…,1/2\}` (flint, MAC, minutes)
  *is* a certificate of the lemma on a bounded interval, after which
  `t_0(1,T) − 6/T ≥ 0.70` already forces `F ≥ 1/4` by (2.1) for all larger
  `T` (the function `F(t_0(T)−6/T, ϑ(T), 1/2)` increases in `T`).
- Sending the open lemma to the judge without a remaining-integral bound
  has VOI = 0: the obstruction is a constant in a remainder, not a
  conceptual fork.

Diagnostic numerics in this file are `mp.quad` of (2.5), dps 25, not
interval certificates. The compact at `T ≤ 30` remains the only certified
piece of `G ≥ 1/4`.
