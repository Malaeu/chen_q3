# PROSHKA — ROUND 4 ADDENDUM, IDEA 3: THE σ-FLOW DERIVATIVE IS A SUM OF SQUARES (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3, branch rh_clean (commit given in the owner's message).

This extends the Round-4 request:
docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND4_COUNTER_MONOTONE_2026-11-05.md
(rh_clean 452a2bf0ebcf932e9fd146119f118fca0592095b, blob 998b8e10544eb2a7a96e5d912449608857588c12).

The Round-4 request is not edited. Goal and acceptance are unchanged. This is an owner idea, not an order.

## Idea 3. Time ↔ coordinate is Cauchy–Riemann, and the flow derivative is a square

Write s = σ + it: σ is the flow time, t is the coordinate.

**(i) Cauchy–Riemann (classical).**

  ∂_t arg ξ(σ+it) = ∂_σ log|ξ(σ+it)| = Re ξ′/ξ(σ+it).

The counter's speed in the coordinate equals the growth of |ξ| in time.

Literature:
- Sondow–Dumitrescu, Period. Math. Hungar. 60 (2010) 37–40, arXiv:1005.1104. RH ⇔ for each fixed t, |ξ(σ+it)| increases on σ > 1/2.
- Matiyasevich–Saidak–Zvengrowski, arXiv:1205.2773. Monotonicity holds unconditionally for σ ≥ 1; extending it to σ ≥ 1/2 is equivalent to RH.

**(ii) The time-derivative at the critical line is a sum of squares exactly when the zeros are on the line.** From the Hadamard product, Re ξ′/ξ(s) = Σ_ρ Re 1/(s−ρ), hence

  ∂_σ Re ξ′/ξ(σ+it) = Σ_ρ [(t−γ)² − (σ−β)²] / [(t−γ)² + (σ−β)²]².

At σ = 1/2, where Re ξ′/ξ = 0 off the zero ordinates by the functional equation:
- an on-line zero contributes +1/(t−γ)², a square;
- an off-line pair β = 1/2 ± δ contributes [(t−γ)² − δ²]/[(t−γ)² + δ²]², which is negative for |t−γ| < δ.

So the shape is Perelman's:
- initial value 0, from the symmetry of the functional equation;
- derivative along the flow = Σ squares;
- and the square fails to be a square only at off-line zeros.

This is the Laguerre expression: (Ξ′/Ξ)′(t) = −Σ_γ 1/(t−γ)² under RH. Csordas–Varga (Adv. Appl. Math. 1990, cited from memory — verify) give the infinite family of generalized Laguerre inequalities equivalent to RH.

**(iii) The circularity, and how to break it.** Stated in terms of zeros, (ii) is circular. Perelman's square is written in the flowing object itself, not in its singularities. Our analogue: write the SAME σ-derivative from the arithmetic side, inside the window. Formally,

  ∂_σ[−Σ Λ(n) n^{−σ−it}] = Σ Λ(n)(log n) n^{−σ−it},

plus the Γ and pole terms. Questions:
- Does the window version, at σ = 1/2 and after your pole renormalization, admit a sum-of-squares representation plus a remainder of size polylog(m)?
- Does such a representation give monotonicity in time, and through Cauchy–Riemann the drawdown bound Δ_m ≤ polylog(m) of Round 3?

**(iv) The window form of the time generator — Mythos hypothesis.**
- For harmonic functions in a half-plane, ∂_σ = −|∂_t|, a Hilbert transform of d/dt.
- The Hardy projection P in your f96a9072 identity D = U*PU − P = Sonin + K carries exactly this Hilbert transform.
- Check whether D is the window form of the σ-flow generator. If it is, the Sonin/Hardy machinery of 04.11 is already the Cauchy–Riemann language for this flow.

## False-world bookkeeping for Idea 3 (Mythos observation, verify)

- **DH.** DH has zeros with β > 1, so the time monotonicity already fails at σ = 1. The arithmetic must enter.
- **DMV.** DMV keeps β < 1, so σ = 1 is fine. It fails once σ < its β. The descent must use what DMV lacks.
- **Curve over 𝔽₃.** Every zero is on its line, so the square in (ii) is an honest square for all σ.
