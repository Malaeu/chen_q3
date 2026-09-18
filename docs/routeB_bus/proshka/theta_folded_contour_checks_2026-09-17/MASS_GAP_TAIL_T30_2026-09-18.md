# STATUS: EXACT_2N_LIFT_PHASE_TASK_OPEN
```yaml
OPERATIVE_CLASS: MASS_GAP_UNIFORM_QUARTER
DATE: 2026-09-18
EQUAL_TAU_2N: PAPER
EXACT_M_PLUS_SQUARES: PAPER   # (4)-(5), verified = our spectral M+ at corner and on the 4-ray model
PAIR_TO_SUM_TRANSFER: REFUTED # positive means + 40% first pair + exact RMS do not imply h>0
GAMMAINC_USED: false
RH_CLAIM: false
```

The compact `T ∈ [√20, 30] × σ ∈ [1/64, 1/2]` is paid: every arb ball of
`(1 − M₋/M₊)/σ` lies above `1/4`, infimum `0.3758969538` at the corner
`(σ, T) = (1/2, √20)`, `N = 10`, radius `6.8e-74`
(`dh_control/mass_gap_corner_arb.json`, commit `83eb3c8d`).

The interval `(30, 80]` of the lemma is paid: 2800/2800 arb balls
(`dh_control/tau_lemma_arb.json`, `9026598a`). What remains is `T > 80`.

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

**Retraction.** The first `Re τ_1` numbers published with this file were
`mp.quad` of (2.5) at dps 25. They do **not** match the arb balls. Cause:
oscillatory quadrature, not a modulus barycentre. Independent check:
`mp.diffs` of `ray()` at dps 40 reproduces the arb values to four digits;
`∫ t|α|/∫|α|` sits at `t_{\mathrm{mag}}` (1.10, 1.17, 1.29, 1.49) and
matches neither. The claim «`Re τ_1 > t_0` everywhere» is false: already
the bad table had `T = 40` with 0.835 < 0.926, and the arb value 0.9259
tracks `t_0` from both sides at `10^{-3}`.

| `T` | `σ` | quad25 (WRONG) | arb `Re τ_1` | `t_0(1)` |
|---|---|---|---|---|
| 30.42 | 1/64 | 0.847 | 0.7954 | 0.7897 |
| 31 | 1/2 | 0.901 | 0.8035 | 0.7990 |
| 40 | 1/2 | 0.835 | 0.9259 | 0.9261 |
| 60 | 1/2 | 1.395 | 1.1277 | 1.1285 |

If the bulk barycentres satisfy `Re τ_n ≥ t_0(n,T) − 6/T`, then
`τ_{\mathrm{rms}}` grows like `√⟨(C − \log n)^2⟩ → √2`. Combined with (2.1)
this is the tail.

## 4. Lemma on `(30, 80]`: certified

MAC `9026598a`, `check_tau_lemma.py`, identity `τ_n = ∂_p I_n/I_n − iϑ`
recorded before the run. 2800/2800 balls on
`T ∈ (30, 80]` step 0.25 × `σ ∈ {1/64,…,1/2}` × `n ∈ {1,2}`, dps 80, 24 s,
none failing, none undecided. Worst margin 0.0727 at `n = 2`, `σ = 1/64`,
`T = 73.5`. `Re τ` tracks `t_0` to `10^{-3}`; the consumed fraction of the
`6/T` slack falls 1.9% (`T = 35`) → 0.30% (`T = 100`) → 0.03–0.07%
(`T = 180…250`). The tail gets easier with `T`.

## 5. `T > 80`: Laplace of (2.5), no `gammainc`

Write `b = p/2 + 9/4`, `α = \Re b ∈ [9/4, 5/2]`, `z_n = π n^2 e^{2iϑ}`.
The substitution `u = e^{2t}` turns the main term of (2.5) into
`∫_1^∞ u^{b-1} e^{-z_n u}\,du`. The saddle `u_s = (b-1)/z_n` is real-positive
to `O(1/T)` and equals `e^{2 t_0(n)}` up to that error. For `T ≥ 80` and
`n = 1, 2` one has `|u_s| ≥ (T/2 − 5/2)/(π n^2) ≥ 37.5/(4π) > 2`, so the
endpoint `u = 1` is at least one width away.

- `(1/2)\Re\log u_s = t_0(n,T) + ε_0` with `|ε_0| ≤ 2/T^2`
  (`(1/2)\log\sin 2ϑ ≥ -2/T^2` and `|b-1| = T/2 + O(1/T)`).
- Laplace remainder of `⟨\log u⟩ − \log u_s` is `O(1/|b|) = O(1/T)`
  (width²/`u_s²`).
- Second term of `φ_n` versus the first, at the saddle:
  `(3/(2π)) e^{-2 t_0} ≤ 3\sin 2ϑ / T ≤ 3/T`. The two saddles differ by
  `(1/2)\log(|b|/|b-1|) = O(1/T)`, so the barycentre moves by
  `O((3/T)·(1/T)) = O(1/T^2)`.

Hence for `T ≥ 80`, `n = 1, 2`,

\[
\bigl|\Re\tau_n - t_0(n,T)\bigr|\ \le\ \frac2T,
\]

and in particular the lemma `Re τ_n ≥ t_0 - 6/T` holds with slack `4/T`.
(This is the same lemma MAC certified on `(30, 80]`; the cubic-on-the-peak
obstruction of §4 is an artefact of a short-`T` window expansion, not of
the `u`-saddle.)

**Weights.** At the saddles `S''(t_0) = -2T` is independent of `n`, and
`a_n c e^{2 t_0} = T/(T+1)` is independent of `n`. Amplitude ratio
`|I_n/I_1| ∼ n^{-1/2-σ}`. With a factor `3/2` for the second term and the
Laplace error, `|I_n/I_1|^2 ≤ 1.5/n` for bulk `n = 2, 3`. Then

\[
\frac{w_1}{U^2}
  \ \ge\ \frac{1}{1 + 1.5(1/2 + 1/3)}
  = \frac{1}{2.25} = 0.44
\]

(`n ≥ 4` is not bulk at `T = 80`, `n_s ≈ 3.57`; for larger `T` the extra
bulk indices have `t_0(n) > 0` and add positively to `⟨(\Re\tau)^2⟩`).
Thus

\[
τ_{\mathrm{rms}}
  \ \ge\ \sqrt{w_1}\,(t_0(1,T) - 2/T)
  \ \ge\ \sqrt{0.44}\cdot 1.247
  \ >\ 0.82
  \qquad (T ≥ 80).
\]

**Bound (2.1).** `F(0.82, ϑ(80), 1/2) = 0.525 > 1/4`, and `F(t_0(1)-2/T, ϑ(T), 1/2)`
increases in `T`. The same implication as on `(30, 80]` therefore gives
`G ≥ 1/4` for `T > 80`.

The two-ray `F` of §2 is superseded by §7: for equal real `τ` the lift
to `2N` is exact and `θ` drops out.

## 6. Status of `c = 1/4` (superseded by §7)

| piece | status |
|---|---|
| `T ∈ [√20, 30]` | arb envelope 0.3759 ≥ 1/4 (`83eb3c8d`) |
| lemma on `(30, 80]`, `n = 1, 2` | 2800/2800 balls (`9026598a`) |
| lemma on `T > 80`, `n = 1, 2` | Laplace of (2.5), `|Re τ - t_0| ≤ 2/T` |
| `G ≥ 1/4` on `T > 30` | via (2.1) and `τ_{\mathrm{rms}} ≥ 0.58`, same lift as the lemma |

MAC need not extend the lemma grid to `T = 250` for this close. The
machine limit `T ≈ 250` / `nan` above is consistent with `|z_n|` leaving
the `|b| ≫ |z|` regime for larger bulk `n`, which the `n = 1, 2` Laplace
does not use.

## 7. Continuum lift: equal real `τ` in any dimension [PAPER]

Assume throughout this section that every ray has the **same real**
barycentre `τ > 0` (plus-rays `ℓ = τ + iϑ`, minus-rays `ℓ = iϑ − τ`).
No bound on `N` is used. Write `X = Σ_n I_n^+`, `Y = Σ_n I_n^-`,
`W_± = Σ |I_n^±|^2`.

### 7.1 Exact spectral identities

`Re s = τ(W_+ − W_-)`, `√{\mathrm{disc}} = τ U^2`, hence

\[
λ_+ = 2(Re s + √{\mathrm{disc}}) = 4τ W_+,
\qquad
λ_- = -4τ W_-.
\]

The vector `Ae` has plus-components `4τ X \overline{I_n^+}` and
minus-components `-4τ Y \overline{I_n^-}` (direct expansion of
`A_{ij} = 2(\bar u_i v_j + \bar v_i u_j)`). Therefore

\[
|Ae|^2 = 16τ^2\bigl(|X|^2 W_+ + |Y|^2 W_-\bigr).
\]

The identity `M_+ = (|Ae|^2 − λ_- h_N)/(λ_+ − λ_-)` with
`h_N = 4τ(|X|^2 − |Y|^2)` and `λ_+ − λ_- = 4τ U^2` collapses to

\[
\boxed{M_+ = 4τ\,|X|^2,
\qquad
h_N = 4τ\bigl(|X|^2 − |Y|^2\bigr),
\qquad
G = \frac{1 − |Y|^2/|X|^2}{σ}.}
\tag{7.1}
\]

`U^2`, `θ` and `N` have cancelled. This is the two-ray formula of §2
with the `4θ^2` terms gone, now in every dimension.

### 7.2 Tilt

On `σ = 0`, conjugacy gives `|X| = |Y|`. Differentiating at fixed `T, ϑ, N`:

\[
∂_σ|X|^2 = 2τ|X|^2,
\qquad
∂_σ|Y|^2 = -2τ|Y|^2,
\]

because `X_t = τ X` when `τ` is common. If `τ` is also independent of `σ`,

\[
\frac{|Y(σ)|^2}{|X(σ)|^2} = e^{-4τσ},
\qquad
G = \frac{1 − e^{-4τσ}}{σ}.
\]

The right-hand side decreases in `σ` on `(0, 1/2]`, so

\[
G \ \ge\ 2\bigl(1 − e^{-2τ}\bigr)
\qquad (0 < σ \le 1/2).
\]

**`G ≥ 1/4` as soon as `τ ≥ \tfrac12\log(8/7) ≈ 0.06695`.**

If `τ` depends on `σ` but `Re τ(s) ≥ τ_*` for all `s ∈ [0, σ]`, the same
bound holds with `τ_*` in place of `τ`, because
`|Y|^2/|X|^2 = \exp\bigl(-∫_0^σ 2(τ_X + τ_Y)\,ds\bigr) ≤ e^{-4τ_* σ}`.

### 7.3 Varying `τ` across rays

Drop the equal-`τ` assumption. Set `τ̄_X = X_t/X`, `τ̄_Y = Y_t/Y` (coherent
means). Then `Δ = τ̄_X X − τ̄_Y Y` exactly, and if both means are real

\[
h_N = 4\Bigl(
  \tfrac{τ̄_X+τ̄_Y}{2}\bigl(|X|^2-|Y|^2\bigr)
  + \tfrac{τ̄_X-τ̄_Y}{2}\,|J|^2
\Bigr).
\]

When `τ̄_X = τ̄_Y = τ_*`, this is (7.1). The error is
`(τ̄_X − τ̄_Y)|J|^2/2`. On `σ = 0`, conjugacy forces `τ̄_Y = \overline{τ̄_X}`
and the error is purely imaginary, hence does not affect `h_N`.

Linux table (diffs of (2.5)) agrees with MAC arb to 3–4 digits
(`18187339`). Last column of the old table used per-ray `τ_rms`; the
formula of this subsection uses the coherent means. MAC correction:
`G/G_{2ray}` on those means is **0.676 at the corner** and **0.636 at
`(√20, 1/64)`**, not 0.72 (that 0.72 is `G` over the per-ray-`τ_rms`
model). Identity `M_+ = 4 τ̄_X |X|^2` on the real varying `τ`: ratio
**0.9983 at the corner** (0.17 %), and 1.0806 / 0.9092 / 1.0314 / 0.8975
at the other four cells — the equal-`τ` assumption costs almost nothing
where the constant matters.

| `T` | `σ` | `Re τ̄_X` (arb) | `Re τ̄_Y` | `G` (arb) | `G/G_{2ray}(τ̄)` |
|---|---|---|---|---|---|
| √20 | 1/2 | 0.1666 | 0.1591 | 0.3759 | **0.676** |
| √20 | 1/64 | 0.1628 | 0.1626 | 0.4116 | **0.636** |
| 30 | 1/2 | 0.7116 | 0.5364 | 1.4020 | 0.924 |
| 80 | 1/2 | 0.8591 | 0.6053 | 1.6147 | 0.917 |

Hole #1, MAC scan (`T` from √20 to 80, step 0.25 at the bottom,
`σ ∈ {1/64, 1/2}`): `min(Re τ̄_X, Re τ̄_Y)` bottoms at **0.15910** at
the corner `(√20, 1/2)`, factor 2.27 over the 0.07 threshold, and
**grows** with `T`: 0.159 → 0.196 (`T = 5.97`) → 0.236 (8) → 0.268 (10)
→ 0.349 (14.75) → 0.637 (30) → 0.727 (80). First-ray dominance
`|I_1^+|/Σ_{n≥2}|I_n^+|` falls the other way: 8.3, 6.2, 5.4, 4.5, 2.0,
1.02. No gap between regimes: where dominance is strong the mean is
`τ_1 ≈ 0.16`; where it fails at `T ≈ 80` the mean is already 0.86.

The scheme «if `|X| ≥ ½|I_1^+|` then `τ̄_X` stays near `τ_1`» **fails
as a sufficient condition** and is not the danger. MAC (`8794fa40`):
at `(T, σ) = (50, 1/64)`, `|X|/|I_1^+| = 0.489 < 1/2` and the coherence
`|X|/Σ|I_n^+|` drops to 0.242 (strongest interference on the scan).
`G` does not fall: it **jumps**. Same neighbourhood, `σ = 1/64`:

| `T` | `Re τ̄_X` | `G` |
|---|---|---|
| 45 | 0.632 | 2.68 |
| 48 | 0.892 | 3.23 |
| 50 | **1.408** | 3.03 |
| 52 | 0.867 | 4.56 |
| 55 | 0.916 | 3.74 |

When interference cancels `X`, `X_t` is not cancelled in proportion, so
`X_t/X` grows. The danger is not «`X` small» but «`X` small with `X_t`
proportionally smaller» — a near-zero of `X` itself. Proshka's model
arranges exactly that: `P(0) = −2/5 ≠ 0` and `P'(0) = 0`. Our rays at
`T = 50` do the opposite. The compact certificate never used the
pair-to-sum transfer: it computed `G` from the actual gamma rays.

**Corrected closing arithmetic.** Same-cell, corner, coherent means:
`0.676 · 2(1 − e^{-2·0.159}) = 0.676 · 0.544 = 0.368`. Conservative mix
of the worse ratio 0.636 with the corner `G_{2ray}`: **0.347**. Both
above `1/4`; the gap is thinner than the retracted 0.373 (which used
per-ray `τ_rms = 0.150` and factor 0.72). The arb envelope remains
0.3759 — the 0.347/0.368 are lower bounds from the model, not
replacements of the envelope.

What is **proved** in §7.1–7.2: equal real `τ ≥ \log(8/7)/2` implies
`G ≥ 1/4` on the whole domain, any `N`. Hole #1 is **pinned on a scan,
not a continuum theorem**: the coherent mean stays ≥ 0.15910 on the
MAC grid, with the two regimes handing over. The retracted factor
0.72 / product 0.373 must not be reused. The retracted scheme
`|X| ≥ ½|I_1^+|` must not be reused: the remaining analytic object
is (9.3), not a lower bound on `|X|`.

## 8. From `G ≥ 1/4` to RH

Enclosure (Proshka, round 7), `INDEPENDENT_ANALYTIC_REVIEW` still
`PENDING`:

\[
h_N − \mathcal E_N \ \le\ \mathscr H \ \le\ h_N + \mathcal E_N,
\qquad
\mathcal E_N = σ\, e_N.
\]

If `G ≥ 1/4` then `h_N ≥ σ M_+/4`. The ratio `e_N / (M_+/4)` is
`< 10^{-68}` on every computed cell, and the majorant (5.2) is
`e_N ≤ 28672 c^{-5} M^3 \exp(-π c M^2 − 2ϑ T)` with `M` from (6.3),
which is `o(M_+)` by the same exponential. Thus `ℋ ≥ h_N − ℰ_N > 0`
for `0 < σ ≤ 1/2`, `T ≥ √20`. Together with `ℋ > 0` on `|T| ≤ √20`
(mixture, PAPER) and evenness of `ξ`, there are no zeros off the
critical line.

This implication is the route. It is not a claim: `G ≥ 1/4` on the
continuum with varying `τ` is not yet a theorem, and the enclosure is
not independently reviewed. `PX_RH_CLAIM` stays not made.

## 9. Exact 2N lift without `√N`, and why the sign still needs the gamma phases

Third outcome, not in the fork «quarter or else `√N`»: **there is no
dimensional loss, and mixed-phase terms can still make the head
negative.** The equal-`τ` theorem of §7.1 is not refuted. What is
refuted is the transfer «per-pair `G ≥ 1/4` + first pair ≥ 40% +
`Re τ_n ≥ 1` ⇒ `h_N ≥ 0`».

### 9.1 Exact squares for our spectral `M_±`

Write `Ψ = (I^+, I^-)^T`, `Q = (τ^+ I^+, −τ^- I^-)^T`, `S = e^*Ψ`,
`D = e^*Q` (this `D` is `X_t − Y_t`; the `iϑ S` piece of `∂_p` drops
from `h_N`). Let `u = ‖Ψ‖²`, `v = ‖Q‖²`, `Ψ^*Q = a+ib`,
`Δ = √(uv − b²)`. Then

\[
M_+ = \frac uΔ \Bigl|D + \frac{Δ-ib}u S\Bigr|^2,
\qquad
M_- = \frac uΔ \Bigl|D - \frac{Δ+ib}u S\Bigr|^2.
\tag{9.1}
\]

Checked against `masses_from` (our spectral `A` on `e`): ratio `1`
at the corner `(√20, 1/2)` and on the 4-ray model of §9.3. For `S ≠ 0`,

\[
w = \frac{u D/S − ib}{Δ},
\qquad
G = \frac{4 \operatorname{Re} w}{σ |1+w|^2},
\tag{9.2}
\]

so `G ≥ 1/4` is `16 \operatorname{Re} w ≥ σ |1+w|^2`. The ratio
`D/S` is a **complex** weighted sum, not a positive-weight mean of
`Re τ_n`.

### 9.2 Surplus as `B_0 + Σ C_n`

Let `J_N = h_N − (σ/4) M_+`, `k = (Δ−ib)/u`, `α = σ u/(4Δ)`,
`Z_n = D_n + k S_n` with `S_n = I_n^+ + I_n^-`,
`D_n = τ_n^+ I_n^+ − τ_n^- I_n^-`. Then `J_N = B_0 + Σ_{n=2}^N C_n`
exactly, with

\[
B_0 = 4\operatorname{Re}(D_1 \overline{S_1}) − α |Z_1|^2
\]

and `C_n` the cross terms of pair `n` against the partial sum `<n`.
**`k, α` are global** (they depend on all `2N` rays). The one-pair
theorem does **not** prove `B_0 ≥ 0` in this splitting.

### 9.3 Four-ray counterexample to the transfer (not to our head)

`ℓ_1 = 2`, `ℓ_2 = 1`, `c_1 = 1`, `c_2 = −6/5`,

`I_n^+ = c_n e^{σ(ℓ_n − iϑ)}`, `I_n^- = c_n e^{−σ(ℓ_n + iϑ)}`.
Then `Re τ_n^± = ℓ_n ≥ 1`. Each pair has
`G_n = (1 − e^{−4 ℓ_n σ})/σ ≥ 2(1−e^{−2}) > 1/4` on `0 < σ ≤ 1/2`.
First-pair `ℓ²`-share `≥ 25/61 > 2/5`. The RMS identity for `Δ` is
equality. But `S = e^{−iϑσ} P` with
`P = 2\cosh 2σ − (12/5)\cosh σ`, so `h = 4 P' P` and
`h'(0) = −224/25 < 0`. Hence `h < 0` on
`0 < σ < \operatorname{acosh}((3+√59)/10) ≈ 0.367`. Checked:
`σ = 0.01`, `h = −0.0895`, `G = −45.7`; at `σ = 1/2` (past the root)
`G = +1.06`. Cause: relative phase `π` between `c_1` and `c_2`,
invisible to quadratic masses, present in the mixed terms.

These are not incomplete-gamma rays. The gamma inequality is not
refuted. The general transfer is.

### 9.4 Next step

Prove `B_0 + Σ C_n ≥ 0` for the actual incomplete-gamma `I_n^±`,
with the global `(k, α)` of (9.1), or equivalently (9.2). The proof
must use the concrete `(n, σ, T)`-dependence of those rays. Finite
`N ≤ 32` does not close the compact by itself: the model above
already changes sign at `N = 2`. The compact **certificate** is a
direct `G`-count on those rays, not a transfer, and is untouched.

The phase property to prove is not «`X` is not small». It is

\[
\text{`X` and `X_t` are not small together:}
\quad
\text{if } |X| \ll \sum |I_n^+|
\text{ then } |X_t| \not\ll |X|.
\tag{9.3}
\]

Equivalently, a near-cancellation of the plus-cluster does not occur
at a critical point of that cluster (`Re(X_t/X)` stays large, as at
`T = 50`). Proshka's model is the opposite arrangement (`P ≠ 0`,
`P' = 0`). `M_+ > 0` is required for the strict `ℋ > 0` implication.
Independent review of the enclosure remains open. `PX_RH_CLAIM` not
made.
