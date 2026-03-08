# Compact Spectral Weight Route (2026-03-08)

## Core claim

The fastest plausible corrected route inside the current architecture is now the
scalar compact spectral package:

`S1 exact compact spectral identity -> S2 spectral positivity criterion -> S3 corrected compact positivity`.

For each compact `[-K,K]`, define

`a_K^*(\xi)=a^*(\xi)1_{[-K,K]}(\xi)`,

`\Xi_K = {\xi_n : 0 < \xi_n \le K}`,

and

`W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}(2\Lambda(n)/\sqrt n)\cos(u\xi_n)`.

Then the exact compact spectral identity is

`\mathcal Q(\Psi * \widetilde{\Psi}) = (1/2\pi)\int_{\mathbb R} W_K(u)|\widehat{\Psi}(u)|^2\,du`

for every `\Psi \in C_c([-K/2,K/2])`.

If `W_K(u)\ge0` for all `u`, positivity on all local convolution squares follows
directly, and corrected compact positivity on `\mathcal W_K^{pd}` follows by the
same continuity/closure logic already used elsewhere in Q3.

## Why this matters

- This scalar route replaces “all finite dictionaries at once” by one spectral
  inequality per compact.
- It removes the need to make the finite-dictionary packet package the public
  mainline.
- The packet package `P1--P8`, the finite symbol `S_J=A_J-P_J`, and the
  canonical half-atom pilot remain useful, but only as fallback discretization /
  verification for the scalar route.

## Operational decision

- `W_K(u)\ge0` is now the primary live frontier.
- Finite-dictionary `P7` is fallback-only.
- `Herglotz/Bochner` stays secondary diagnostic language.

## File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/abstract.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
