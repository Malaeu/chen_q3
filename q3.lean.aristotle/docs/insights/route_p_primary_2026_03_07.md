# Route P Primary For PSD-pd

Date: 2026-03-07

## Summary

The corrected positive-definite route now has a primary proof package.

- `Herglotz/Bochner` remains the clean diagnostic equivalence route:
  it reformulates `PSD-pd` as positive-definiteness of the Toeplitz sequence /
  existence of a positive measure representation.
- The realistic constructive route is now `Route P`:
  exact packet sesquilinear identity
  -> prime-block PSD factorization or Hilbert lift
  -> Archimedean domination criterion
  -> `PSD-pd`.

## Why this is the right split

The new packet theorem is not a patch of the old centered `A3`.
The honest target is the sesquilinear kernel

`K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})`

on a dense pre-packet space. The exact packet identity survives, but the old
uniform-gap mechanism does not survive on a dense packet dictionary with
arbitrarily fine translates.

`Herglotz/Bochner` explains what must be true:
the Toeplitz sequence must be positive-definite. But by itself it does not give
a project-local factorization of the prime packet block.

`Route P` stays much closer to the current Q3 engine. It asks for:

1. exact packet sesquilinear identity;
2. PSD factorization or Hilbert lift of the prime block;
3. an Archimedean domination theorem on that same packet space.

That is the first theorem package that looks both honest and architecturally
compatible with the present Q3 analytic stack.

## Operational consequence

- Public manuscript wording should now treat `Route P` as the primary route.
- `Herglotz/Bochner` should remain explicit, but only as a secondary diagnostic
  equivalence route.
- Aristotle subagents may continue probing both routes, but integration and
  planning should follow `Route P` first.
