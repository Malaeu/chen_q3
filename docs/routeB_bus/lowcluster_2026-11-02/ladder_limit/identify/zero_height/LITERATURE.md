# Primary-source check: low Weil modes and zero height

Read-only literature audit, 2026-11-02. No status promotion or RH claim.

## Sources and what they establish

**[CC23]** A. Connes and C. Consani, *Spectral triples and ζ-cycles*,
Enseign. Math. 69 (2023), 93–148,
[DOI 10.4171/LEM/1049](https://doi.org/10.4171/LEM/1049),
[published PDF](https://ems.press/content/serial-article-files/44477).
Read §§2–6, especially §4, pp.127–128, (4.1)–(4.3), Proposition4.2;
§4.1 numerical tables; Theorem6.4 and Corollary6.5, pp.144–147.

The form is the restricted Weil form on
`L²([λ⁻¹,λ],du/u)`, not the additive prolate concentration operator.
Small Weil eigenvectors are compared with arithmetic sums of prolate vectors.
The later spectral triple uses
`D(λ,k)=(1−Π(λ,k))D₀(λ)(1−Π(λ,k))`, with a prolate-derived rank-k projection,
on the multiplicative circle of circumference `L=2logλ`.

Proposition4.2 selects **E=2πμ=2πλ²**, `μ=λ²`, so that the nonzero
perturbed-Dirac count approximately matches the mean zeta count
`E/(2π) log(E/(2π))−E/(2π)`, for `k` near `2μ`.
This is a mean-count/comparison-range statement, not an individual-zero
error bound through E. The examples are numerical comparisons.
Theorem6.4 concerns exact ζ-cycles: resonance `sL∈2πZ` for critical zeros;
it is not uniform finite-window zero coverage.

**[CCM25]** A. Connes, C. Consani and H. Moscovici, *Zeta Spectral Triples*,
[arXiv:2511.22755v1](https://arxiv.org/html/2511.22755v1),
[author PDF](https://alainconnes.org/wp-content/uploads/zeta-spectral-triples-1.pdf).
Read Theorem1.1; Proposition5.9/(5.25), p.22; Theorem5.10, pp.23–24;
§6, pp.25–27; §8, pp.32–33.

Here ξ is the smallest eigenvector of the **truncated Weil form**, assuming
its minimum is simple and even. Its Fourier–Mellin transform is

`ξ̂(z)=2L⁻¹/² sin(zL/2) Σ_{j=−N}^N ξ_j/(z−2πj/L)`.

Theorem5.10 identifies these zeros with the spectrum of a rank-one perturbed
scaling operator (on the quotient by ξ with its specified form inner product).
It proves reality of the zeros under those hypotheses; it does not identify
them with zeta zeros. Outside the finite band the unchanged lattice
`2πj/L`, `|j|>N`, remains.
Section6 computes N=120, λ=√12,√13,√14 and compares fifty zeta zeros.
Section8 expressly leaves simplicity/evenness and sufficiently accurate
approximation of the actual ground eigenvector unresolved.

**[C26]** A. Connes, *The Riemann Hypothesis: Past, Present and a Letter
Through Time*, [arXiv:2602.04022v1](https://arxiv.org/html/2602.04022v1),
§§6.1,6.3–6.6, especially (19)–(21), Fact6.4.

The logarithmic support convention is again `L=2logλ`.
The additive prolate parameter is `c=2πλ²`, using additive Fourier kernel
`exp(2πixy)` on additive windows `[−λ,λ]`.
The comparison of the prolate-derived `k_λ` with the actual Weil ground
eigenvector is explicitly a remaining step. The proved convergence of
`k̂_λ` to Ξ does not by itself prove convergence of the actual eigenvector
transforms. No quantitative zero-tracking height law is supplied there.

## Dictionary for the present literal schedule

This is an algebraic translation, not an additional literature theorem:

| Quantity | Present schedule N=m, L=log m |
|---|---|
| Multiplicative window | `[m⁻¹/²,m¹/²]` |
| λ, μ=λ² | `√m`, `m` |
| Prime-power cutoff from correlation support | `μ=m` |
| CC23 mean-count comparison height | `E_CC=2πm` |
| Highest retained log-Fourier mode | `T_band=2πN/L=2πm/log m` |
| Ratio `E_CC/T_band` | `log m` |

These heights answer different questions. The first selects a comparison range
for the CC23 prolate-conditioned Dirac construction. The second is the exact
carrier endpoint in our finite trigonometric truncation; it is neither a
rigorous zero-accuracy guarantee nor a universal prohibition on higher transform
zeros. The two constructions use different projections/perturbations.

**Verdict:** published evidence supports the finite-window zero-tracking
phenomenon and explicitly motivates the scale `2πλ²`; it does not prove
that our first fixed number of low vectors reproduce every zeta zero up to
`2πm` or `2πm/log m`. No source-specific cofinal transfer follows from the
three-carrier scan. The UV Connes–Moscovici prolate theorem concerns counting
asymptotics of another selfadjoint extension, not this assertion.

Method: primary-text HTML and PDF text read; web PDF screenshots failed with a
tool content-type error. No numerical results were generated for this note.
