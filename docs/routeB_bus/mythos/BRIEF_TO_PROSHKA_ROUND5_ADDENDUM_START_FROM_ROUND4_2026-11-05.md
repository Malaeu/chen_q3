# PROSHKA REQUEST — ROUND 5 ADDENDUM: START POINT = BOTH ROUND-4 VERDICTS (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3

Branches:
- `rh_clean` holds this file and the Round-5 brief. The Round-5 brief is `docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND5_PERELMAN_GAUGE_2026-11-05.md`, commit 46f43d93, blob 4c533a5b.
- `proshka_inbox_2026-10-31`: write the verdict here as a NEW file, based on tip dd22692d or later.

This addendum adds inputs and the owner's practical ideas. It does not change the Goal (prove RH) or the Acceptance list of the Round-5 brief.

## INPUTS (read before freezing)

Both files are on `proshka_inbox_2026-10-31`:

1. Round 4 A, commit 7a1d9a53 (freeze a14bd4e1), `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND4_COUNTER_FLOW_SQUARE_2026-11-05.md`:
   - the radial square K = ∂_δ(δH), with RH ⇔ K ≥ 0;
   - the uniform window-curvature SOS obstruction;
   - the repaired radial ξ-flow.
2. Round 4 B, commit dd22692d (freeze 05e90085), `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND4_DAMPING_TRANSPORT_2026-11-05.md`, blob ed2bb7f3:
   - the damping family A_m(δ), with positive terminal H_m(1/2) = T*T;
   - the unitary transport V_m(δ);
   - the minimal loss L_m = ∫_0^{1/2} max(0, max_i λ′_{m,i}(δ)) dδ, with A_m ≥ −L_m G_m;
   - the 9/25 non-arithmetic budget after exact pole + continuous-prime cancellation;
   - unconditional L_m = O(√m/(log m)^4) and RH ⇒ L_m ≤ 14Σ₀L².

Translated into Round-5 language: the flow is fixed (δ from 1/2 to 0), and the bad quantity is fixed (the positive eigenvalue velocity). By Acceptance item 5 of Round 5, restating "L_m ≤ polylog" is NO_PROGRESS, because Round 4 B already proved it RH-equivalent.

## OWNER'S PRACTICAL IDEAS (ideas, not orders; you decide what to use)

**Idea 1 — the gauge is the freedom of the path interior.**
- Only two things are fixed: the endpoint A_m(0) on 𝒦_m and positivity of the terminal.
- The interior path H(δ) and the metric G are not fixed. Counterterms may depend on δ if they vanish on 𝒦_m at δ = 0.
- This is the analogue of Perelman's δ-dependent diffeomorphism.
- Caution: over all paths, the minimal loss is trivially (−λ_min(A_m|𝒦_m))_+, the straight line. That is circular. The freedom is worth something only if it makes dW a square with an arithmetically controlled remainder. It must not merely shrink L_m.

**Idea 2 — move the square, not the bound.**
- Round 4 A has a square, K, but on the ξ side.
- Round 4 B has a positive terminal, T*T, but loses on the path.
- Question: is there a gauge of the 4 B path whose velocity is the window version of K, a sum of squares plus the 9/25-paid part?

**Idea 3 — what arithmetic is left.**
- After 4 B, what remains is the prime sum Σ_{2≤n<m} Λ(n) n^{−1/2−δ} Q_f(log n), minus its continuous main term, in the transported frame.
- Candidates for the next exact renormalization (knob (c) of Round 5):
  - θ/π;
  - C_L − Z_L = M_L·Σ(log n − d(n)) e_n (8e584bb8 (3.1)–(3.3)).
- The pole precedent removed √m. The next counterterm should remove the √m/(log m)^4 remaining in L_m.

**Idea 4 — Lagarias' Γ-pole as a second pole gauge.**
- In Lagarias 1999 (with the 2005 Correction you read: Lemma 3.1 and the sign in (3.8)), the only obstruction to Re ξ′/ξ > 0 is the pole of ζ, and it is offset by Γ.
- The project note on it: `rh_clean` commit 4f8404f9, `docs/routeB_bus/litreview/LAGARIAS_1999_CORRECTION_2005_NOTE.md`.
- If the window has an analogue of this Γ-term, it is a candidate exact counterterm.

## FREEZE

The Round-5 freeze must state which Round-4 objects you take over, with their commit and section.
