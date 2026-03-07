# Target-Cone Audit (2026-03-07)

## Verdict

`pivot required`

Current broad-cone contract is too wide to serve as the honest public Weil target.
The mainline must pivot from the broad even/nonnegative compact-support cone to a
positive-definite / convolution-square cone.

## Current live contract

Lean and paper currently expose the broad target:

- `Q3/Basic/Defs.lean`
  - `Weil_cone := {Φ : ℝ → ℝ | Φ even, Φ ≥ 0, compact support, continuous}`
  - `W_K := {Φ : ℝ → ℝ | Φ continuous, supp Φ ⊆ (-K,K), Φ even, Φ ≥ 0}`
- `full/sections/Main_closure.tex`
  - local closure is phrased on `W_K`
- `full/sections/Weil_linkage.tex`
  - RH is phrased as positivity on the full broad cone `\mathcal W = \bigcup_K W_K`

This is stronger than the classical non-negative-definite formulation.

## Classical contract

The external mathematical shape is quadratic / positive-definite:

- Bombieri's reformulation of Weil's criterion is a positivity statement on a
  quadratic form in test functions, not on all nonnegative bumps.
- In convolution language, the natural test objects are of the form
  `ψ * \check ψ`, equivalently positive-definite even tests.

External cross-checks used in this audit:

- Enrico Bombieri, *The Riemann Hypothesis* (Clay / AIM exposition):
  [AIM article 76](https://www.ams.org/journals/bull/2000-35-03/S0273-0979-99-00837-5/)
- Enrico Bombieri, *A note on Weil's criterion for the Riemann hypothesis*:
  [EuDML entry](https://eudml.org/doc/276642)

These sources support the positive-definite / quadratic-form reading and do not
justify the broad slogan “positivity on every even nonnegative compactly
supported test”.

## Project-level barrier

The project functional is

```math
Q(\Phi)=\int_{\mathbb R} a^*(\xi)\Phi(\xi)\,d\xi-\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}\,\Phi(\xi_n),
\qquad \xi_n=\frac{\log n}{2\pi}.
```

With

```math
a(\xi)=\log\pi-\Re\psi\!\left(\tfrac14+i\pi\xi\right),
\qquad a^*(\xi)=2\pi a(\xi).
```

Live project checks:

- `a(1.5) ≈ -0.4049950988`
- `a(2) ≈ -0.6928830299`
- `a(3) ≈ -1.0984949609`

And on each fixed compact window the prime nodes are finite and discrete:

- `Q3/Proofs/W_sum_finite.lean` gives finiteness of active nodes
- sample node-free gaps are numerically nonzero near `1.55` for `K=1.6`
  and near `1.95` for `K=2.0`

So the broad-cone threat is real:

1. choose a compact window with an interval where `a(ξ) < 0`,
2. place an even smooth bump in a node-free gap,
3. the prime sum vanishes on that bump,
4. the Archimedean integral is strictly negative,
5. hence broad positivity on all current `W_K` is not a credible RH target.

This is enough to reject the broad cone as the public mainline contract, even
before a full formal disproof of every old broad-cone theorem statement.

## Consequences for the project

1. The public target cone must be replaced by a corrected positive-definite cone,
   locally
   `\mathcal W_K^{pd} := \overline{\{ψ * \check ψ\}}`
   and globally
   `\mathcal W^{pd} := \bigcup_K \mathcal W_K^{pd}`.
2. Current shifted A1' density on `R_K = C^+_{\mathrm{even}}([-K,K])` becomes
   auxiliary rather than mainline.
3. The new knife-edge theorem is `A1-pd`:
   density of centered Fejér×heat / autocorrelation packets in
   `\mathcal W_K^{pd}`.
4. Centered `A3 + RKHS` survives as the natural positivity engine.
5. Current `G1-G3` work on the broad cone is background-only until it can be
   reused inside the corrected cone contract.

## Next step

Freeze the corrected cone notation and theorem chain in control docs and the
manuscript, then make `A1-pd` the active frontier.
