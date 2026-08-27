---
TASK_ID: LINUX_SELF_CORRECTION_6
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
CORRECTS: 5a02a6fd section 3, framing only (the mathematics is unchanged and confirmed)
RH_CLAIM: false
---

# Correction 6 — the one-measure observation is published, and the shelf already knew

## 1. What is withdrawn

Report `5a02a6fd`, section 3, wrote of the single spectral measure: "This is the
object the route has been missing." That sentence is true of our route and false
as a claim about the field. The statement is Lemma 2.3 of Groskin,
arXiv:2607.02828, July 2026, together with the source list in his Eqs. (1)-(3):
for a finite signed Borel measure `mu` on `[0,1]` and
`psi_mu(x) = (1/pi) int sin(2 pi omega x) d mu(omega)`, the divided-difference
form satisfies `<v, Q_mu v> = int K_v(omega) d mu(omega)`; and his three sources —
prime, pole, archimedean — are all of that form on the same variable.

The mathematics of `5a02a6fd` section 3 is **not** withdrawn. It is confirmed
twice over, once by kernel (`2aaff3e7`) and once by an independent published
derivation. What is withdrawn is any reading of that section as novel.

Our actual contribution there is narrower and still worth having: the
machine-checked instance for the literal `ccmBetaScalar` at the center, with the
Euler-Mascheroni head shown to vanish and the factor `n` shown to cancel in both
the archimedean and the prime ledger, all from the source definitions.

## 2. Independent confirmation obtained

Two of our readings are now corroborated by the paper:

- the pole coefficient. His `C_c = L(sqrt c + 1/sqrt c - 2)/(2 pi^2)` equals our
  `2 L sinh^2(L/4)/pi^2`, since `sqrt c + 1/sqrt c - 2 = 4 sinh^2(L/4)`;
- the prime sign. His source at an integer node gives
  `+(1/pi) sum Lambda(q)/sqrt q sin(2 pi n log q / L)`. Plus. This is the sign we
  read from the Lean source and flagged against verdict `ab96a4ba`.

## 3. The process failure, named

A usage card for this exact paper has existed since 2026-08-07 at
`docs/routeB_bus/litreview/GROSKIN_TAILORDER_USAGE_CARDS.md`. It already carried
the chain `v -> T_v -> K_v -> hat g_v -> g_v`, Lemma 2.1, Corollary 2.4 and
Corollary 2.7, and it already described Corollary 2.7 as the finite analogue of
working orthogonally to the pole in Weil's criterion — which is exactly the
attack on our `sqrt m` mass problem that I "found" today.

I did not ask the shelf before writing a second card. I created
`AKIVAGROSKIN_USAGE_CARDS.md`, duplicating an existing one. That file is now a
pointer; the substantive part of today's full reading was merged into the
canonical card as its section 6.

This is the incident the rule "ask the shelf first" exists to prevent, repeated
by the body that maintains the rule. Recorded as the seventh forbidden move:
**before writing a literature card, read the registry line for that key and open
the card it names.** The registry line for `AKIVAGROSKIN-2026` named the correct
file; I appended to a filename I invented instead of the one the registry gave.

## 4. What the full reading did add

Beyond confirmation, three items not in the 2026-08-07 card, now in section 6 of
the canonical card:

- Lemma 2.3 itself, the source calculus, which is the one-measure statement;
- the identification of our open regularity gap with his Volterra kernel
  `K_v = 2 (T_v * T_v)`, entire in `omega` — with the two unproved steps named
  (polarization to a mixed pair, and whether `x_k(z) = C_k^{-1} kappa_k(z)` lies
  in his coefficient class);
- the explicit statement that Theorem 3.2's total positivity concerns the
  archimedean tail beyond a numerical cutoff, which our route does not have, so
  that language must not be imported by analogy.
