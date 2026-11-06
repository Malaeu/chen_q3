# BRIEF TO PROSHKA — prove RH — 2026-11-06 (Ramanujan original)

Repo: https://github.com/Malaeu/chen_q3

**Goal: prove RH.**

## Inputs (all in the repo)

| What | Branch | Commit | Path | Blob |
|---|---|---|---|---|
| Prime-only receiver, Thm 2: RH ⇔ z*B⁽¹⁾z ≤ C·z*Gz on K_m = {z₀ = 0, p_m*z = 0}; exact return (4.2) of B⁽¹⁾ through θ(x) − x | proshka_inbox_2026-10-31 | 115714b7 | docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_POWER_RANK_ONE_2026-11-04.md | 9feeb0571aff5d79c2617694e9ef31f4d9f1a121 |
| Balanced Green form Z_N; E_N ≤ 14Z_N + 9/L²; receiver (20) | proshka_inbox_2026-10-31 | a337b335777c3912694fb058a68a019c47061ffe | docs/routeB_bus/proshka/PROSHKA_VERDICT_BLOCK_B_MULTISCALE_2026-11-06_C.md | 692b10822320c76a8d2c9a82168bb5c35f124d4b |
| R6 B: the universal self-dual return is killed; open item = a Gaussian-specific source return | proshka_inbox_2026-10-31 | 888b8080 | docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_B.md | 33de3e38276671101b701d895509e81d09c0f2e5 |
| Constructor: receivers, paid pieces, killed classes | rh_clean | 7d23fbe9ea357f0369c716f49ad3b9de12c3e25f | docs/routeB_bus/mythos/ROUTE_B_CONSTRUCTOR_PROVEN_2026-11-06.md | dee2c8200d6ad59e3eb7336e497f43e17a273f98 |
| Ramanujan sweep (sources) | rh_clean | 7d23fbe9ea357f0369c716f49ad3b9de12c3e25f | docs/routeB_bus/litreview/LIT_RAMANUJAN_SWEEP_2026-11-06.md | 0ae6bb1abceb27452bdc9799974ee87372c2b179 |

## Owner's practical idea (an idea, not an instruction)

Ramanujan's ORIGINAL formula (Second Notebook, p. 312, as he wrote it, before the Hardy–Littlewood correction). For αβ = π:

    G(α) := √α · Σ_{n≥1} μ(n)/n · e^{−(α/n)²},     G(α) = G(π/α).

It is false. The Hardy–Littlewood correction (simple zeros):

    G(α) − G(β) = −(1/(2√β)) · Σ_ρ Γ((1−ρ)/2) · β^ρ / ζ′(ρ).

RH ⇔ Σ μ(n)/n·e^{−x/n²} = O(x^{−1/4+ε}).

Numerically the original holds to ~10⁻⁵ (DIAG, μ up to 2·10⁵): every zero is damped by |Γ((1−ρ)/2)| ~ e^{−π|γ|/4}. Ramanujan also stated it for an arbitrary Fourier-reciprocal pair (φ, ψ).

Why it may matter here:
- It is an exact symmetry in which μ (multiplication) meets the exact Gaussian / θ-modularity (addition, via Poisson on ℤ).
- Its defect is exactly the zeros, weighted by the Gaussian Mellin factor Γ((1−ρ)/2). That is the Gaussian-specific shape left open by R6 B, on the μ side used by NB / Z_N.
- A second exact piece: the truncated von Mangoldt function Λ_N inside Z_N has the finite Ramanujan expansion Λ_N(n) = Σ_{q≤N} Λ̂_N(q)·c_q(n) (Coppola–Murty–Saha; Laporta arXiv:2204.01581).

## Freedom

Use these, change them, or ignore them. Your own mechanism is welcome, including a short-circuit straight to RH.
