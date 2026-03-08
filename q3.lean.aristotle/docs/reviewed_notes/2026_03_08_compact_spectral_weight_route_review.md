# Reviewed Note: Compact Spectral Weight Route

- reviewed: `yes`
- safe for embeddings: `yes`
- date: `2026-03-08`
- source: `user mathematical note + live corrected route synthesis`
- status: `active`

## Core claim

The scalar compact spectral route is now the primary constructive frontier.

For each compact `[-K,K]`, define

`W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}(2\Lambda(n)/\sqrt n)\cos(u\xi_n)`.

Then:

- exact compact spectral identity (`S1`)
- scalar compact positivity criterion (`S2`)
- corrected compact positivity from `W_K\ge0` (`S3`)

form the fastest plausible route to local Weil positivity in the corrected
positive-definite cone.

## Why this matters

- The finite-dictionary packet package is no longer the public primary route.
- `P7` survives only as fallback discretization / verification.
- This reduces the compact problem to one scalar spectral inequality per `K`.

## File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
