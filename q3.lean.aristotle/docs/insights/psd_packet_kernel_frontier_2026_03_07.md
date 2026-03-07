# PSD Packet Kernel Frontier

Date: 2026-03-07

## Status

Accepted as the live corrected-cone frontier.

## Core verdict

- `A1-pd` survives as a density theorem on autocorrelation packets.
- Exact packet-Rayleigh survives as the identity
  `Q^\star(t;\Psi_c * \widetilde{\Psi_c}) = \sum_{i,j} c_i\overline{c_j}\kappa_{i-j}`.
- The old public theorem shape `A3-pd` does **not** survive on the dense packet
  dictionary: one uniform packet-symbol floor / uniform positive gap is too strong.
- The honest missing theorem is now `PSD-pd`:
  positive semidefiniteness of the packet kernel
  `K_Q(g_i,g_j)=Q^\star(t;g_i * \widetilde{g_j})`
  on the dense pre-packet space.

## Why the old `A3-pd` theorem shape fails

Let `g` be a nonzero compactly supported packet profile and define
`Ψ_Δ = g - g(·-Δ)`. Then `Ψ_Δ -> 0` in `L^1` as `Δ ↓ 0`, hence
`Φ_Δ = Ψ_Δ * \widetilde{Ψ_Δ} -> 0` uniformly on every fixed compact. By A2
continuity, `Q^\star(t;Φ_Δ) -> 0`.

Therefore no theorem of the form

`Q^\star(t;\Psi * \widetilde{\Psi}) >= c_K ||c||_2^2`

with one uniform `c_K > 0` can hold on a dense packet dictionary with
arbitrarily fine translates.

## Structural objects that still matter

- `S_{g,Δ} = A_{g,Δ} - P_{g,Δ}` remains useful structure on translate-generated
  packet families.
- But `S_{g,Δ} >= c_K > 0` is no longer the public theorem shape.
- The public theorem shape is the PSD condition on finite packet-kernel matrices:

`[K_Q(g_i,g_j)]_{i,j} >= 0`.

## Recommended public chain

`T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 closure -> LF-pd -> G6 -> RH`

## Strategy families still alive

1. Herglotz/Bochner route:
   interpret the packet-kernel coefficients as a positive-definite sequence or
   measure-theoretic Fourier data.
2. New prime-factorization / kernel route:
   prove PSD of `K_Q` directly from a new structural decomposition of the prime
   and Archimedean pieces on the pre-packet space.
