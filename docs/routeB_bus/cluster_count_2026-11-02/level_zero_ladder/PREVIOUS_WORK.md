# Repository archaeology before the level–zero ladder computation

Read-only search completed before any new computations by this reviewer.
Source pin: `Malaeu/chen_q3@a412a678a4ae1df4f03106d1a46cf5453451c65a`
(`rh_clean`, commit title: Record literal even cluster counts for m8–40 and
audit NOESCAPE count hypotheses).

Search scope: complete canonical `docs` tree (5185 entries, not truncated),
root `scripts`, `experiments`, `output` trees; the named Fokas, Mellin-zero,
local-invariant packets; phase5 root outputs and scripts; relevant Q3 KB
insight; bounded keyword search of `docs/Progress_Log.md` fetched by blob.
This is a bounded search, not a claim to have inspected every repository file.
No eigenproblem or root search was executed here.

## Directly reusable prior: own ground-transform roots

| Path at source pin | Git blob |
|---|---|
| `docs/routeB_bus/phase5_codex/xi_row_zeros.py` | `47f0e1da775c7115cb57d4a309bbda461f1792fa` |
| `docs/routeB_bus/phase5_codex/out/xi_row_zeros.md` | `96512178bb86c13bdf4bc2d032da132182d2e494` |
| `docs/Progress_Log.md` | `6d02f28b27be7fe7497dfd768a01025999ab78a4` |

The September4 probe did compute its **own transform roots**, not just values
at supplied zeta zeros, for ground and Xi-sample rows at m=13,23,43.
It forms the degree-2N numerator of the partial-fraction/P59 transform with
lattice `ω_k=2πk/L`, then compares positive roots with `mpmath.zetazero`.
Ground raw coordinates are `c_n=(v_n/v_0)/√2` for n>0 in the even basis;
the Xi-sample row is `c_n=(−1)^n Ξ(ω_n)/Ξ(0)`.
This normalization is a root-location device, not unit physical normalization.

**Critical correction, not optional:** script docstring and Progress_Log
lines3773–3792 contain the explicit ERRATUM. The polynomial root solver
produced roughly 1e−8 accuracy even with high-precision matrix input; a purported
root had `F≈−1.2e−10`, whereas `F(γ_1)≈4.6e−29` at m13. The archived output's
ADDENDUM14 displacement sequence `2e−8,8e−18,2e−36` must **not** be used as
true zero displacements or a decay law. The log replaces it with direct F
evaluation and Newton refinement; the m13 first-root displacement is reported
at roughly1e−26. These remain historical floating diagnostics.
The log also records a genuine complex Xi-row root confirmed on the direct
transform, so agreement of coordinate sign patterns is not a real-zero test.

Reusable lesson: evaluate the entire transform directly, including removable
lattice points, and refine an independently located root by Newton on F.
For a signed first Newton correction use `−F(γ)/F′(γ)`.
Do not interpret polynomial-root residual/precision as physical displacement,
or use float conversion to report differences below float resolution.

## Related packets checked: their relevance and limits

| Packet | Reusable content | What it does not supply |
|---|---|---|
| `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3` | Full literal K=W02−WR−Prime, N=m, moment-factorized arch entries, all prime powers, Gaussian comparison plane | No lifted-level/own-root matching table |
| Same directory `SOURCE_TRANSFER.md`, blob `d564040c1828673835baeeed43978994ff68cd97` | Same-K reference/source ground projection transfer without inverse-gap amplification; m4,8,13 angle diagnostics; remaining compact-transform rate | No eigenvalue-to-zeta-ordinate identity or higher-level root law |
| Same directory `INDEPENDENT_ENERGY_SHIFT.md`, blob `308c2d9c9c8e5a33b2b37203c3d71a6fd2b4af76` | Certified m8 inertia cuts and separate ground-tracking estimate; four-level low cluster | No zero assignment to those four Weil levels |
| `docs/routeB_bus/S2_L2B_MELLIN_ZERO_SCAN_REPORT_2026-08-05.md`, blob `84df0f6241f5688af2dc7c7f179a42c51f4945c7` | Exact rational Mellin numerators for polynomial windows; one interior-zero witness among1468 | Different gauge/window problem; not eigenvector-transform/zeta matching |
| `docs/routeB_bus/LOCAL_ZERO_INVARIANTS_CATALOG_2026-09-08.md`, blob `f987dcc999360edc3cede30521a9d2dfa6022ad9` | Zero-local Weil-block signature and separating-test distinctions; later corrections on multiplicity versus inertia dimension | Catalogue/controls, not a computed ladder |

## Source-paper crosswalk: two different spectra

The repository already acquired
`docs/routeB_bus/imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md`,
blob `c05766698a263a064bbc7560f32d14233bdbdfaf`, and supplement
`THM510_SUPPLEMENT_S8_T36_DELTAN_2026-07-31.md`,
blob `1a2daecf3e268313578025050e443ec4bc00c58e`.

[CCM, Zeta Spectral Triples, arXiv2511.22755v1](https://arxiv.org/html/2511.22755v1),
Proposition5.9/(5.25) and Theorem5.10, distinguishes:

1. Eigenvalues of the **Weil matrix K**: its ground eigenvector determines ξ.
   These eigenvalues are energy levels, often extremely small.
2. Eigenvalues of the **rank-one perturbed scaling operator D**: these coincide
   with zeros of the Fourier–Mellin transform of that ξ, under the theorem's
   simple/even-ground hypotheses and specified quotient inner product.

Numerical approximation of those D eigenvalues to zeta ordinates is not an
identity between K's ordered eigenvalues and zeta ordinates. The source theorem
does not automatically apply to each excited K eigenvector: K−λ_j I is no
longer positive on the entire quotient by that eigenvector.
The repository's August6 crosswalk, blob
`ca9a24b7fb0c58c560a788c5bfec04d48f3cf8b2`, correctly retains the missing
ground-tracking/identification step.

The older KB note
`q3.lean.aristotle/docs/insights/connes_zeta_spectral_triples_2026_01_29.md`,
blob `921df5adb0a0cd53a8256db6815bc3e0482e80cc`, is useful only as a locator.
Its stronger phrases—convergence as accomplished, positivity implying
simple/even ground, and fifty zeros all matching1e−55—are not usable theorem
statements. Use the precise import and primary paper instead.

## Remaining work selected by this search

The bounded search found prior **ground** own-root comparisons and recent
sampling/zero-height methods, but no completed table associating the requested
m=16,24,32,40 higher levels with independently located transform roots.
That is the missing finite experiment; rerunning the old polynomial-root table
would repeat its documented failure mode.

A new diagnostic should retain unit physical vectors and compute each chosen
level's own transform roots, then compare with zeta ordinates without forcing
index equality. Report extra/unmatched roots and do not assume real-rootedness
for excited vectors from the ground-state theorem. Record residual, derivative,
precision replay and lattice-removability checks. No finite matching table
establishes a cofinal level–zero correspondence.
