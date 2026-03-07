---
title: 2026-03-07 naive Rayleigh family obstruction review
review status: reviewed
safe for embeddings: `yes`
source: inline user note
date: 2026-03-07
---

# Summary

This note survives review as a stronger correction of the corrected-cone route.

The key point is no longer merely that density and positivity live on two
different families. The sharper obstruction is:

- the naive centered quadratic-form family
  `\Phi_{B,t}|p|^2`
  is itself too large to serve as the public closure family;
- if one combines its full quadratic-form positivity with local continuity and a
  broad density argument, one is pushed toward false local-bump positivity;
- therefore the live mainline must replace the naive Rayleigh family by a
  **smaller operator-controlled packet family inside the corrected
  positive-definite cone**.

# Surviving mathematical content

## 1. Naive quadratic-form family

Lemma 8.8 naturally suggests the family
\[
  \Phi_{B,t,p}(\xi)=\Phi_{B,t}(\xi)\,|p(\xi)|^2,
\]
with `p` a trigonometric polynomial.

This is mathematically natural, but it is not automatically the right closure
family for the corrected Weil cone.

## 2. Why the family is too large

On compact windows with `K<\pi`, a fixed centered window `\Phi_{B,t}` is strictly
positive on `[-K,K]` for `B>K`. Hence any even nonnegative continuous function
`f` on `[-K,K]` can be written as
\[
  f=\Phi_{B,t}\,h,
  \qquad h\ge 0.
\]
By Stone--Weierstrass, even real trigonometric polynomials are dense on
`[-K,K]`, so `r_n^2\to h` uniformly and therefore
\[
  \Phi_{B,t}r_n^2 \to f
\]
uniformly on `[-K,K]`.

Thus the naive family `\Phi_{B,t}|p|^2` is already broad enough to approximate
arbitrary local even nonnegative bumps on those compact windows.

## 3. Why that breaks the closure route

The broad local positivity statement is false.

The Weil functional has the form
\[
  Q(\Phi)=\int_{\mathbb R} a^*(\xi)\Phi(\xi)\,d\xi
  - \sum_{n\ge 2}\frac{2\Lambda(n)}{\sqrt n}\Phi(\xi_n),
  \qquad \xi_n=\frac{\log n}{2\pi},
\]
and the Archimedean density satisfies `a^*(\xi)<0` near sufficiently large
`|\xi|`; in particular the user note isolates `\xi=2` as a concrete negative
point.

Since only finitely many prime nodes lie in each compact window, one can choose a
small interval around such a negative point that contains no active node. Any
even nonnegative bump supported there has zero prime contribution but a strictly
negative Archimedean integral, hence `Q(\eta)<0`.

So the naive family cannot be both:

1. the exact family controlled by the quadratic-form engine, and
2. the family whose closure yields the public RH target.

## 4. New blocker

The honest next theorem is not a same-family bridge through
`\Phi_{B,t}|p|^2`.

It is:

- build a smaller operator-controlled packet family inside
  `\mathcal W_K^{pd}`,
- prove an exact quadratic-form identification on that same family,
- keep the dense autocorrelation family `\mathcal G_{K,\mathrm{dens}}^{pd}` as
  the density side.

# Repo impact

- This note supersedes the earlier `SF-pd` blocker note.
- Public mainline should now say:
  - `A1-pd` remains the corrected density input,
  - the naive packet-Rayleigh family is background-only,
  - the live frontier is `OP-pd`, i.e. the design of a smaller
    operator-controlled packet family on the corrected cone.

# File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/scope_notation.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
