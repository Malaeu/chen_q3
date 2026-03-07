# Reviewed Note: Full-Kernel PSD Frontier

reviewed: yes
safe for embeddings: yes
date: 2026-03-07
source: user mathematical note + live Q3 control-plane comparison
status: active

## Core claim

The honest packet-level theorem target is:

`K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})`

must be positive semidefinite on a dense pre-packet space.

## Surviving structure

- `A1-pd` still looks like the right density theorem.
- Exact packet sesquilinear / Toeplitz identity still survives.
- The literal theorem shape
  `prime-block PSD factorization or Hilbert lift -> Archimedean domination`
  does not survive on dense packet space.

## Exact obstruction

The packet prime block

`K_P(\Psi,\Phi)=\sum_n w(n)(\Psi * \widetilde{\Phi})(\xi_n)`

is not PSD in general on translation packet spaces containing an active node.
So the old constructive Route P is superseded.

## Active constructive route

- primary: direct full-kernel PSD
  `exact identity -> prime-block obstruction -> full-symbol domination or new operator package -> PSD-pd`
- secondary: `Herglotz/Bochner` as diagnostic equivalence language only

## File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
