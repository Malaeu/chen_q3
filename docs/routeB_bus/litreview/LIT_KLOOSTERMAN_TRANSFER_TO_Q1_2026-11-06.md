# Literature check 2026-11-06: can Kloosterman/Weil √-cancellation (block B) pay the single term q = 1?

Status: Mythos literature check. CHALLENGER / NOT_RH.
Predecessor: `docs/routeB_bus/mythos/PRIME_PROPERTIES_APPLIED_TO_PSI_WALL_2026-11-06.md` (commit 107a205b).

## Facts read

1. **The NB Gram is a twisted second moment of ζ.** d_N² is a weighted ∫|1 − ζ·A_N|²·dt/(¼ + t²). Its off-diagonal is the Vasyunin sum.
   - Maier–Rassias (arXiv:1806.05070) use the relation V(h/k) = −c₀(h̄/k) and Ishibashi's identity c₀(a/q) = 2qπ^{−2}·D_sin(1, ā/q), where D_sin is the Estermann-type sine series Σ d(n) sin(2πnx)/n^s.
   - So the off-diagonal is a form in Kloosterman fractions e(a·m̄/n): addition × multiplication, i.e. block B.
2. **Machinery for such forms:**
   - Duke–Friedlander–Iwaniec 1997 (bilinear);
   - Bettin–Chandee arXiv:1502.00769 (trilinear);
   - Bettin–Chandee–Radziwiłł arXiv:1411.7764: an asymptotic for ∫|ζA|² for arbitrary A of length T^θ, θ < 17/33;
   - arXiv:2601.00292 (2026): improved bilinear bounds.
   - The off-diagonal contributes to the MAIN term (BCR §1).
3. **Ceiling (FACT, BCR abstract):** a conjectural estimate for trilinear sums of Kloosterman fractions implies the **Lindelöf Hypothesis**. The best conceivable input of this kind is pitched at LH, not RH.
4. **Zeros sit in the main term of the Möbius taper (FACT, BCF arXiv:1211.5191, Lemma 2, unconditional):**

       V_N(s) = (1/ζ(s))(1 − ζ′/ζ(s)/log N) + (1/log N)·Σ_ρ R_N(ρ, s) + (1/log N)·F_s(1/N),   0 < Re s < 1.

   An off-line zero enters through R_N(ρ, s) as an explicit residue, not as an error term.
5. **One right zero suffices to kill (FACT, R8 B, 70c4e6b0):** e_N ≥ (2β − 1)/|ρ|² for EVERY N and every right zero ρ. Rarity of off-line zeros (density-type information) cannot pay the receiver; absence is needed.
6. **Maier–Rassias Theorem 2.1:** a power saving for Σ μ(n)·g(n/k), using continued fractions and Vaughan's identity, no Kloosterman. The constants are internally inconsistent (C ≈ 1.602 vs the required C ≥ 1.618). NOT importable.

## Verdict

- Kloosterman/Weil is the one demonstrated unconditional √-source from addition × multiplication, and it sits in our object.
- But:
  - (a) it pays only error terms, while the zeros live in explicit residues of the main term;
  - (b) at its conjectural best it gives LH;
  - (c) LH controls the density of off-line zeros, not their existence;
  - (d) R8 shows that a single zero breaks every N.
- So the transfer “twisted √-control ⇒ q = 1” fails by known theorems.
- Block B, if it decides RH, must enter as an exact identity or a positivity, not as a cancellation estimate.

## What remains (SPEC)

- Weil's own RH over F_q is a positivity statement (Castelnuovo / Hodge index), not a cancellation estimate. The project's `claude/FORK_2026-11-05_FROBENIUS_THETA_SYNTHESIS.md` is the relevant shelf.
- Exact identities with sign from block B: none found beyond row 10 of the dictionary (μ*1 = ε, Selberg symmetry), which pay but give no sign.
