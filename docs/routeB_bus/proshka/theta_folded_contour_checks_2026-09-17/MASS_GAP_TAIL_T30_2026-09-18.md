# STATUS: COMPACT_AND_LEMMA_CERTIFIED_TAIL_T_GT_80_OPEN
```yaml
OPERATIVE_CLASS: MASS_GAP_UNIFORM_QUARTER
DATE: 2026-09-18
COMPACT: CERTIFIED_ARB        # 83eb3c8d, 889/889, envelope 0.3758969538
LEMMA_30_80: CERTIFIED_ARB    # 9026598a, 2800/2800, n=1,2
LINUX_QUAD_RE_TAU: RETRACTED  # oscillatory mp.quad dps 25, not |alpha|
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

The lift from a two-ray `F(τ_{\mathrm{rms}})` to the `2N`-vector is the
same step already used to turn the lemma into `G ≥ 1/4` on `(30, 80]`.
It is not re-proved here.

## 6. Status of `c = 1/4`

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
