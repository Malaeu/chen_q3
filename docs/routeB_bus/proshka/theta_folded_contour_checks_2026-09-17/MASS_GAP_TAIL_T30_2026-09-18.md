# STATUS: SIGNED_COHERENT_DEFECT_SOURCE_BOUND_OPEN
```yaml
OPERATIVE_CLASS: MASS_GAP_UNIFORM_QUARTER
DATE: 2026-09-18
EQUAL_TAU_2N: PAPER
EQUAL_TAU_THRESHOLD: 0.0667656963   # (1/2)log(8/7); 0.06695 was a Linux rounding error
EXACT_M_PLUS_SQUARES: PAPER
PAIR_TO_SUM_TRANSFER: REFUTED
COHERENT_MEANS_AND_DOMINANCE_TRANSFER: REFUTED  # Proshka 4dd6fe34, analytic, whole (0,1/2]
Q_FORMULA_SECTION_1_4: CORRECTED_MINUS          # plus as first written is false; masses_from does not use it
SIGNED_COHERENT_DEFECT_SOURCE_BOUND: OPEN
PROSHKA_ONE_FIFTH_E_COH_BUDGET: FAILS_ON_SOURCE # epsilon=0.2025 at (sqrt(20),1/64)
GAMMAINC_USED: false
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
```

The compact `T ∈ [√20, 30] × σ ∈ [1/64, 1/2]` is paid: every arb ball of
`(1 − M₋/M₊)/σ` lies above `1/4`, infimum `0.3758969538` at the corner
`(σ, T) = (1/2, √20)`, `N = 10`, radius `6.8e-74`
(`dh_control/mass_gap_corner_arb.json`, commit `83eb3c8d`).

The interval `(30, 80]` of the lemma is paid: 2800/2800 arb balls
(`dh_control/tau_lemma_arb.json`, `9026598a`). The Laplace bound of §5
covers `T>80` for `n=1,2`. What remains is the signed cluster correction
`E_{\rm coh}` for varying `τ` (§10), not another mean-scan.

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

\[
Q = |D|^2 U^2 + |J|^2 V^2 - 2\Im(D\overline J)\,\Im s.
\]

The mixed term carries a **minus**. The plus written here first is false:
the two-vector `u=(1,1)`, `v=(1+i/2,-1+i/2)` has `A=\mathrm{diag}(4,-4)`,
true `M_+=4`; plus gives `8`, minus gives `4` (Proshka `4dd6fe34` §4,
Linux recheck). `masses_from` never uses this `Q`: it uses the spectral
projectors on `A`. The compact arb balls are independent of the typo.

Hence

\[
G = \frac{4\Re(D\overline J)\,\sqrt{\mathrm{disc}}}
         {σ\bigl(2\Re(D\overline J)\,\sqrt{\mathrm{disc}} + Q\bigr)}.
\]

`G ≥ 1/4` is equivalent to `Re(D\overline J)\,√{\mathrm{disc}} ≥ σ Q / (2(8−σ))`,
with this corrected `Q`. Equivalently `R ≥ 0` for

\[
R = 2(8-σ)\sqrt{\mathrm{disc}}\,\Re(D\overline J) - σ Q
  = 4\sqrt{\mathrm{disc}}\Bigl(h_N - \tfracσ4 M_+\Bigr).
\]

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

**`G ≥ 1/4` as soon as `τ ≥ \tfrac12\log(8/7) ≈ 0.0667657`.**
(The value `0.06695` written here first is a rounding error.)

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
`e_N ≤ 28672 c^{-5} M^3 \exp(-π c M^2 − 2ϑ T)` with `M` from (6.3).
That majorant is an **absolute** bound on `e_N`. The phrase
«`o(M_+)` by the same exponential» does **not** by itself prove the
relative claim `e_N < M_+/4`: the exponential in the numerator does
not supply a lower bound on `M_+` (Proshka `4dd6fe34` §6). On the
certified compact the relative bound is a number from the arb balls,
not this sentence. Thus, **if** `G ≥ 1/4` and `M_+ > 4 e_N` on the
domain, `ℋ ≥ h_N − ℰ_N > 0` for `0 < σ ≤ 1/2`, `T ≥ √20`. Together
with `ℋ > 0` on `|T| ≤ √20` (mixture, PAPER) and evenness of `ξ`,
there are no zeros off the critical line.

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

### 9.4 Next step, superseded by §10

`(9.3)` («`X` and `X_t` are not small together») is **not sufficient**.
Proshka's second model (`4dd6fe34`, §10 below) has `|X| > (37/40)|I_1^+|`
and `Re \barτ_{X,Y} > 0.15915` on the whole `(0,1/2]`, and still
`h_N < 0`. The unpaid object is the signed cluster correction `E_{\rm coh}`,
not a lower bound on `|X|`. The compact certificate is untouched.
`M_+ > 0` is required for the strict `ℋ > 0` implication.
Independent review of the enclosure remains open. `PX_RH_CLAIM` not
made.

## 10. Coherent means plus dominance do not give the sign; `E_{\rm coh}` is the unpaid remainder

Proshka `4dd6fe34`, file
`docs/routeB_bus/proshka/PROSHKA_VERDICT_COHERENT_MEANS_SIGN_TRANSFER_2026-09-18.md`.
Linux checked the algebra (fractions and the two-vector for `Q`) and
ran a diagnostic split on the actual `(2.5)` rays. None of this is a
continuum proof. `DIAGNOSTIC_NUMERICS_ONLY_NEVER_A_PROOF` for the table.

### 10.1 Stronger counterexample than §9.3 [PAPER for the model, not for our head]

Two pairs, any real `ϑ`,

\[
a=\tfrac29,\quad k=\tfrac1{20},\quad
I_1^\pm = e^{iϑσ}e^{\pm aσ},\quad
I_2^\pm = -k\, e^{iϑσ}e^{\pm σ}.
\]

Reflection `I_n^-(σ)=\overline{I_n^+(-σ)}` and the derivative dictionary
hold. Each pair has a real constant `τ` and passes the quarter of §7.1.
Coherent means are real and

\[
\barτ_X,\barτ_Y > 53/333 > 0.15915,
\quad
|I_1^+|/|I_2^+| > 40/3 > 13.33,
\quad
|X| > (37/40)|I_1^+|
\]

on `0 ≤ σ ≤ 1/2`. Yet `h_N = 4 P D_0` with
`P = f(σ)+f(-σ) > 37/20`,
`D_0 = 2a\sinh(aσ)-2k\sinhσ < -\sinhσ/810`, so

\[
h_N < -\frac{37}{4050}\sinhσ < 0 \qquad (0<σ\le 1/2).
\]

Checked: `a^2-k=-1/1620`; at `σ=9\log(21/20)` one has `h≈-0.0144233`;
at `σ=1/2`, `h≈-0.01995`. This kills the remaining Linux transfer
«positive coherent means + first-ray dominance + `|X|` large `⇒ h_N≥0`».
It is not a counterexample to the theta-head. Equal-`τ` 2N is not
refuted. The extra structure of `(2.5)` not preserved here is the
absence of a free minus on a higher-`τ` ray: the coefficients of
`φ_n` are not free signs.

### 10.2 Exact split [PAPER]

On `XY ≠ 0`, `α=\barτ_X`, `β=\barτ_Y`, `m=(\Reα+\Reβ)/2`,

\[
\frac{h_N}{4}
 = m\bigl(|X|^2-|Y|^2\bigr) + E_{\rm coh},
\qquad
E_{\rm coh}
 = \frac{\Reα-\Reβ}{2}|X+Y|^2
   -(\Imα+\Imβ)\Im(X\overline Y).
\]

Positive means control `|Y|^2/|X|^2=\exp(-4\int_0^σ m)` and nothing
else. In the model of §10.1 the tilt term is **positive**
(`|X|>|Y|`) and `E_{\rm coh}/\mathrm{tilt}=-1.087` flips the sign
(`ε=0.657`). That is the mechanism.

### 10.3 Diagnostic split on the actual gamma rays

`mp.diffs` of `check_contour.ray` at `dps 20–30`, `ADAPTIVE_R=0`,
identity `h/4 = \mathrm{tilt}+E_{\rm coh}` to `10^{-33}` at the corner.
`G` at the corner matches the arb envelope `0.37589695`.

| `T` | `σ` | `G` | `m` | `ε` | `κ` | `E_{\rm coh}/\mathrm{tilt}` | `arg(I_2^+/I_1^+)` |
|---|---|---|---|---|---|---|---|
| √20 | 1/2 | 0.3759 | 0.163 | 0.172 | 1.021 | **−0.309** | −2.875 |
| √20 | 1/64 | 0.4116 | 0.163 | **0.203** | 1.081 | **−0.313** | −2.936 |
| 8 | 1/2 | 0.825 | 0.236 | −0.154 | 1.099 | +0.205 | 2.511 |
| 14.75 | 1/2 | 1.052 | 0.349 | 0.015 | 0.941 | −0.015 | 0.414 |
| 30 | 1/2 | 1.402 | 0.624 | −0.212 | 1.176 | +0.147 | −1.849 |
| 50 | 1/64 | 3.034 | 1.399 | −1.377 | **2.221** | +0.257 | 2.998 |
| 80 | 1/2 | 1.615 | 0.732 | −0.163 | 1.053 | +0.106 | 1.103 |

`ε = -E_{\rm coh}/(σ m |X|^2)`, `κ = M_+/(4 m |X|^2)`.
Worst `E_{\rm coh}/\mathrm{tilt}` on the low-`T` scan
`T∈[√20,12]×{1/64,1/2}` is **−0.313** at `(√20, 1/64)`, and it
increases with `T` (already positive by `T=7`). Proshka's sufficient
budget `m≥3/20`, `E_{\rm coh}≥−σ m |X|^2/5`, `κ≤6/5` **fails on
source**: `ε=0.2025>1/5` at `(√20,1/64)`, and `κ=2.22` at the
`T=50` cancellation. It is not a necessary budget; its failure does
not kill `G≥1/4`. Do not use it as a theorem.

MAC `863d69dd`, arb dps 80, 224 cells
`T∈[√20,80]×σ∈{1/64,…,1/2}`: identity residual `0` at all 224.
`m≥3/20` holds 224/224 (min `0.1627292704` at `(1/64,√20)`);
`ε≤1/5` holds 222/224 (max `0.2025139970`, same cell);
`κ≤6/5` holds 208/224 (max `2.6391359345` at `(1/2,40)`);
all three 206/224. Taken independently the worst triple gives
`G≥0.1338<1/4`. Jointly `(g_0-ε)/κ≥1/4` at **224/224**, minimum
`0.376082` at the corner against actual `G=0.375897` (0.05%).
At large `κ` the correction is strongly negative (`T=40`:
`κ=2.639` with `ε=-2.814`). A large positive mass arrives with a
strongly negative `ε`. Separate bounds on `ε` and `κ` are the
wrong shape; they have to stay together. `R` does that.

At the corner, truncating to `n=1` gives `G=0.3337>1/4` and
`E_{\rm coh}/\mathrm{tilt}=-0.392`; adding `n=2` raises `G` to
`0.3764`; `n≥3` does not change the printed digits. The compact
corner is a **two-ray source problem** of the actual `n=1,2`
incomplete-gamma pair. Adding the second gamma ray **helps**. The
model of §10.1 does the opposite.

Near-`π` phase between `n=1` and `n=2` occurs both at the compact
corner (`arg≈-2.88`) and at `T=50` (`arg≈3.00`). It is not a kill
by itself: at `T=50` the defect *helps*.

### 10.4 What to prove

Source bound that keeps `ε` and `κ` **together**, enough for `R≥0`
or directly `h_N-ℰ_N>0`. Separate floors (`ε≤1/5`, `κ≤6/5`, or
even `E_{\rm coh}/\mathrm{tilt}≥-1/2` plus a `κ`-cap) are the wrong
shape: MAC's 224 cells already have `κ>2` with `ε<-2`. The identity
`G=(ĝ-ε)/κ` with `ĝ=(1-|Y|^2/|X|^2)/σ` is the joint object.
`R=4δ(h_N-σ M_+/4)` is the same joint object without dividing by
`X`. Prior `0.75` that a source estimate of `R` for the actual
`n=1,2` pair of `(2.5)` at `T=√20` is positive, with `n≥3` a
modulus-ratio remainder. This is a registered prediction, not a
theorem.

`IF_A` that pair has analytic `R≥0` at `T=√20`: the compact
continuum is paid and the tail is the equal-`τ` lift plus the lemma
already in §§4–7. `IF_B` `R` dips on that pair: keep all `2N` in
`R` and use the measured `ε`–`κ` coupling (large `κ` comes with
large negative `ε`). Do not send this to the judge (the gap is a
source remainder). Do not grind a denser grid of the same means.
Do not bound `ε` and `κ` separately. Enclosure review still
`PENDING`. `PX_RH_CLAIM` not made.
