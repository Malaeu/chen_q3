# PROSHKA REQUEST — PROVE RH, ROUND 6: THE FORWARD ARROW (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3

Branches:
- `rh_clean` holds this file; the commit is in the owner's message.
- `proshka_inbox_2026-10-31` takes your verdict as a NEW file, `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05.md`. If that name is taken, add a suffix (`_B`, `_C`, …). Never overwrite another verdict.

Firmware: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749.

## GOAL

Prove the Riemann Hypothesis. The bottom line of your answer is RH.

## INPUTS (proshka_inbox_2026-10-31)

1. **Round 4 A**, commit 7a1d9a53: the radial square K = ∂_δ(δH), with RH ⇔ K ≥ 0, and the window-curvature SOS obstruction.
2. **Round 4 B**, commit dd22692d, blob ed2bb7f3, all of §§1–6:
   - the terminal square H_m(1/2) = T*T;
   - the minimal transport loss L_m;
   - the exact derivative (6.2)–(6.3);
   - the 9/25 budget.
3. **Round 5**, commit 25f5ac26:
   - null-gauge rigidity (R5.1)–(R5.3);
   - the unrestricted-path shortcut (R5.4);
   - R5.GAP, with D_ψ(u) = e^{−u/2}(ψ(e^u) − e^u).
4. If you already pushed a Round-5 verdict of your own, use it as well.

## WHY THIS ROUND (owner's diagnosis, stated as context)

Rounds 4–5 used an external parameter flow: the damping δ, from the proved end σ = 1 to the window σ = 1/2. Along it:
- the target A_m sits at the **input** end;
- the proved positive object sits at the **output** end;
- the velocity contains the external forcing E_δ (ψ(x) − x), which is not a function of the current state.

Round 5 proved that no gauge changes this. Hence every such path costs L_m, and the cost is RH-equivalent.

Perelman's flow is different: the velocity −2Ric(g) is a function of the state, and the controlled object is reached **forward**.

The de Bruijn–Newman heat flow has the wrong arrow:
- real zeros are preserved forward in time (de Bruijn 1950);
- Polymath15 gives Λ ≤ 0.22;
- Rodgers–Tao give Λ ≥ 0, so in that family Ξ is not the forward heat image of any real-rooted function.

This round reverses the arrow: **A_m must be the output of a positivity-preserving construction that starts from a proved positive object.**

## THE TASK

For each m ≥ M, build a finite chain

    P_m^{(0)} → P_m^{(1)} → … → P_m^{(k_m)},

subject to the following.

1. **Positive start.** P^{(0)} is a proved positive semidefinite form. T*T from Round 4 B §4 is allowed, as is any other proved PSD object.
2. **Positivity-preserving links.** Each link is a map that provably preserves PSD (or a cone containing PSD) for every input, not just for this one. Examples of such map classes:
   - congruence S*XS;
   - Schur/Hadamard product with a PSD matrix;
   - sums with PSD terms;
   - limits of these.
   You may use any class whose preservation you prove.
3. **Autonomy.** The links are universal rules: they are fixed by integer structure and by the current state, never by reading the sign or size of ψ − x, of zeros, or of A_m itself. Λ may enter only through such a structural map — for example through Λ = μ * log or divisor sums — and never as an additive signed forcing term.
4. **Output.** For admissible z ∈ 𝒦_m, the output must satisfy

       z*A_m z ≥ z*P^{(k_m)} z − C(1 + log m)^r z*G_m z

   with one fixed C and r. Exact equality with polylog defect is preferred.

The receiver, as in Rounds 3–5: the moving-Gaussian export from 62f78231 (blob 2b5e02a0, §6) turns (4) into RH.

## OWNER'S PRACTICAL IDEAS (ideas, not orders)

- **Idea 1 — known positivity makers from the integers.** Each produces PSD forms from divisibility alone, with no ζ input. Can a chain of them reach A_m?
  - GCD/Smith matrices: [f(gcd(i,j))] is PSD when f = 1 * g with g ≥ 0.
  - Selberg Λ²-sieve squares (Σ_{d|n} λ_d)².
  - Beurling–Nyman / Báez-Duarte approximants.
- **Idea 2 — the discriminator must be additive.**
  - Fact: Beurling generalized integers (DMV) form a free commutative monoid, so they have divisibility, gcd and a multiplicative lattice, but no additive structure. A chain built from divisibility alone will therefore also run in the DMV world and cannot be the discriminator.
  - Some link must use the additive structure of ℤ: integer spacing n + 1, the lattice ℤ ⊂ ℝ, Poisson summation over ℤ, Fourier on ℤ/q.
  - The task: name that link.
- **Idea 3 — Selberg as a model.** For compact hyperbolic surfaces, primes ↔ closed geodesics and positivity ↔ self-adjoint Laplacian (a square from geometry). For ℚ, Connes' scaling flow has closed orbits of length log p. Is there a finite-m window version whose generator is a state function, with the square coming from it?

## ACCEPTANCE (fixed before you start)

1. **Freeze first.** Commit a freeze with the start object, the map class of the links, how integer structure enters, and the registered predictions. Construction and verdict come after it. The freeze block is never edited.
2. **Proof of positivity preservation** for every link class, valid for all inputs.
3. **Autonomy proof.** Show that no link reads ψ − x, zeros, or the sign of A_m. A link chosen after looking at A_m is a substitution and is rejected.
4. **Output inequality (4)**, with the defect stated exactly.
5. **False worlds:**
   - the chain must break for DMV and for the planted off-line quartet, each with its own source, and you must name the link where it breaks;
   - it must run for the curve over 𝔽₃;
   - a chain that also runs for DMV is not a discriminator.
6. **Forbidden as the whole chain:**
   - the heat or de Bruijn–Newman semigroup (Rodgers–Tao);
   - the damping δ-flow with external forcing (Rounds 4–5);
   - unrestricted paths (R5.4).
   Restating R5.GAP or "L_m ≤ polylog" is NO_PROGRESS.
7. **Falsifiers.** For every finite claim stronger than a proved one, give a Codex test fixed in advance: quantity, m-grid, precision, plant, pass/fail.
8. **Bottom of the chain**, one of:
   - (a) RH proved;
   - (b) the chain built, plus one exact residual lemma naming the additive input;
   - (c) a proof that no autonomous positivity-preserving chain of the stated class can output A_m with polylog defect, with the obstruction named.
