# Route P Primary For PSD-pd (Superseded)

Date: 2026-03-07

## Status

Superseded on 2026-03-07 by the stronger full-kernel audit:

- standalone PSD factorization of the packet prime block is false on dense
  packet spaces containing an active node;
- the live constructive frontier is therefore direct PSD of the full kernel
  `K_Q`, not the literal theorem stack recorded below.

See:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/full_kernel_psd_frontier_2026_03_07.md`

## Historical summary

The corrected positive-definite route now has a primary proof package.

- `Herglotz/Bochner` remains the clean diagnostic equivalence route:
  it reformulates `PSD-pd` as positive-definiteness of the Toeplitz sequence /
  existence of a positive measure representation.
- The then-current constructive route was:
  exact packet sesquilinear identity
  -> prime-block PSD factorization or Hilbert lift
  -> Archimedean domination criterion
  -> `PSD-pd`.

## Why this looked plausible at the time

The new packet theorem is not a patch of the old centered `A3`.
The honest target is the sesquilinear kernel

`K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})`

on a dense pre-packet space. The exact packet identity survives, but the old
uniform-gap mechanism does not survive on a dense packet dictionary with
arbitrarily fine translates.

`Herglotz/Bochner` explains what must be true:
the Toeplitz sequence must be positive-definite. But by itself it does not give
a project-local factorization of the prime packet block.

The old `Route P` stayed much closer to the current Q3 engine. It asked for:

1. exact packet sesquilinear identity;
2. PSD factorization or Hilbert lift of the prime block;
3. an Archimedean domination theorem on that same packet space.

That theorem package is no longer treated as honest after the packet-space
prime-block obstruction.

## Historical operational consequence

- Public manuscript wording should no longer treat literal `Route P` as the
  primary route.
- `Herglotz/Bochner` should remain explicit, but only as a secondary diagnostic
  equivalence route.
- This historical note is now kept only for provenance; active planning no
  longer follows literal `Route P` first.
