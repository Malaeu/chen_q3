# Reviewed Note: Route P Primary For PSD-pd (Superseded)

reviewed: yes
safe for embeddings: yes
date: 2026-03-07
source: user mathematical note + live Q3 control-plane comparison
status: superseded

## Supersession note

This reviewed note is kept for provenance only. It was superseded on 2026-03-07
after the sharper packet-space audit showed that standalone PSD factorization of
the packet prime block is false on dense packet dictionaries containing an
active node.

Live replacement:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/reviewed_notes/2026_03_07_full_kernel_psd_frontier_review.md`

## Historical core claim

The honest frontier is:

`K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})`

must be positive semidefinite on a dense pre-packet space.

## Surviving structure

- `A1-pd` still looks like the right density theorem.
- Exact packet-Rayleigh / packet Toeplitz identity still survives.
- The old `A3-pd` uniform-gap route does not survive on a dense packet family.

## Route split

- `Herglotz/Bochner` is the clean equivalence language:
  positive-definite sequence
  <-> Toeplitz-section PSD
  <-> positive measure representation.
- The old reviewed route was:
  exact packet sesquilinear identity
  -> prime-block PSD factorization or Hilbert lift
  -> Archimedean domination criterion
  -> `PSD-pd`.

## Why it looked primary at the time

The current Q3 engine already knows how to win once the prime side is packaged
as a PSD object and once the Archimedean side dominates it. So the natural next
package is packet-level factorization, not a purely abstract Herglotz reformulation.

## File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
