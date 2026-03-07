---
title: PSD Packet Kernel Frontier Review
date: 2026-03-07
status: reviewed
safe for embeddings: yes
supersedes:
  - 2026_03_07_a3_pd_packet_package_review.md
---

# Summary

This note sharpens the corrected-cone route once more. The exact packet identity
survives, but the old `A3-pd` theorem shape does not: a uniform packet-symbol
floor on the full dense packet dictionary is too strong.

# Surviving statements

1. `A1-pd` remains a plausible density theorem on autocorrelation packets.
2. Exact packet-Rayleigh remains valid on autocorrelation packets:
   `Q^\star(t;\Psi_c * \widetilde{\Psi_c}) = \sum_{i,j} c_i\overline{c_j}\kappa_{i-j}`.
3. The corrected positive-definite cone remains the right public Weil target.

# Rejected theorem shape

The old public frontier

`A3-pd: S_{g,Δ}(θ) >= c_K > 0 on the whole dense packet family`

is too strong. Dense packet dictionaries contain collapsing packets such as
`Ψ_Δ = g - g(·-Δ)`, for which `Ψ_Δ -> 0` in `L^1`, hence
`Φ_Δ = Ψ_Δ * \widetilde{Ψ_Δ} -> 0` uniformly on compacts, so by A2 continuity
`Q^\star(t;Φ_Δ) -> 0`.

# Correct live theorem

The honest missing theorem is:

`PSD-pd`: prove that the packet kernel
`K_Q(g_i,g_j)=Q^\star(t;g_i * \widetilde{g_j})`
is positive semidefinite on the dense pre-packet space.

# Project impact

- Public chain should read:
  `T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 closure -> LF-pd -> G6 -> RH`.
- `A3-pd` survives only as a rejected-too-strong route / contrast note.
- `S_{g,Δ}=A_{g,Δ}-P_{g,Δ}` remains useful structure, but not the public theorem shape.

# File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/scope_notation.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
