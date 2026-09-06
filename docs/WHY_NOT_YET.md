# Why not yet — the wall from first principles (2026-09-06)

Written on the owner's word: «нам надо понимать, почему никто до сих пор не дошёл; нужна гипотеза, которую можно быстро проверить; нам нужно
найти одно доказуемое из миллиарда». This file is the observer's answer. It changes only when a fact below is refuted.

## 1. One statement, many coordinates

Every formulation we touched in 2026-09-04/06 is the same statement. None is a step toward the others.

| coordinate | statement | equivalence to RH | our record |
|---|---|---|---|
| (DOM) | Σ w_n E_s(log n) + ∫₀^{t₀} bE_s ≥ ∫_{t₀}^∞ |b|E_s ∀s | Weil criterion + (GS) | paper §4, Cor 4.3 |
| Li | λ_n = Σ_ρ[1 − (1 − 1/ρ)^n] ≥ 0 ∀n | Li 1997; = Weil form on tests g_n (Bombieri–Lagarias) | CHAT_DIGESTS part 5 |
| Lagarias / Herglotz | Im(Ξ′/Ξ) ≤ 0 in the upper half-plane; |𝒞| ≤ 1 | Hadamard product | CHAT_DIGESTS «фазовый циркуль» |
| Sondow–Dumitrescu | ∂_y|Ξ(x+iy)|² ≥ 0, 0 < y < ½; Ŵ_y ≥ 0 | 2010 | CHAT_DIGESTS W_y |
| Rouché cover | ∀ rectangle D ⊂ S∖ℝ ∃ real-zero model F_j with sup_∂D|Ξ−F_j|/|F_j| < 1 | Hurwitz/ZeroEscape; supplier = Route B convergence | judge TRY_ADAPTIVE_CONTOUR |
| CCM windows | µ_λ ≥ 0 ∀λ | CCM Cor 3.8 via (3.27) | Goal 058, three years |
| Hermite–Biehler / de Branges | Ξ in Laguerre–Pólya class | classical | Suzuki 2025; the de Branges space that exists unconditionally is E(z) = ξ(1−iz) (shift h = ½), and Conrey–Li refuted de Branges's sufficient conditions for exactly that space (Lagarias math/0601653 §6) |
| Jensen / Laguerre | all J^{d,n} hyperbolic; all Laguerre–Turán inequalities | Pólya 1927 | Williams filter (Farmer: not a route) |

## 2. Why every inequality technique dies

The statement is critical: the margin is exactly zero. Facts, each proved or published:
- no uniform margin on any dense family of tests (paper Prop 5.9; E₋/E₊ → 1 on translated cutoffs of f₀);
- Λ ≥ 0 (Rodgers–Tao): the de Bruijn–Newman threshold sits exactly at 0 if RH holds;
- Nicolas: his inequality, if RH fails, holds and fails infinitely often;
- ∂_y|Ξ|²/|Ξ|² → 0 between zeros as y → 0 (measured 2026-09-06);
- on CCM windows the bottoms decay like e^{−4.5…5.1·m}; the ground transform vanishes at every zeta zero to the leakage scale √λ₁.
An inequality proved with slack cannot reach an exact critical constant. Only an identity can. The identities we own — explicit formula, Hadamard
product, theta modularity, Euler product — are precisely the ones that make the coordinates above equivalent. They never resolve the sign.

## 3. What Weil had that we do not

In the function-field case the second identity is geometric: the Hodge index theorem (Castelnuovo–Severi inequality) gives the positivity of
the intersection form on the surface C × C, and the explicit formula is its arithmetic shadow. For Spec ℤ no such second identity is known;
building one is the Connes–Consani program (adele class space, Sonin spaces, the archimedean place). Our (DOM) is that shadow written with an
explicit signed measure. Every proof attempt in the literature uses the same first identity and then needs the missing second one.

## 4. The filter — what a candidate «one provable property» must satisfy

A hypothesis is admitted to work only if it passes all five, in order, each in minutes:
1. **Not a coordinate.** It is not equivalent to RH by a known dictionary (table §1). If it is, it goes to CHAT_DIGESTS as one line, no probe.
2. **Second-expression shape.** It offers Q(f₀s) (or Σ_z ĝ(z)ĝ(z̄)-conj) as a manifestly nonnegative quantity written WITHOUT zeros and without
   assuming their reality; by Theorem 5.3 of the paper it must be nonlocal and must vanish on the whole radical {U_q f₀, f₀*h}.
3. **Plants.** It fails on (1+16z²)cos 8z, on B(z)(2+cos 4z), and on the mean-prime surrogate Λ(n) → 1 (NEG). A candidate that passes a plant is dead.
4. **Yoshida window.** It reproduces the proved positivity for supports shorter than log 2 (Yoshida 1992, Bombieri 2000 §12), with the known margin.
5. **Exact constant.** It carries no slack: its natural constant is c_A = γ + log 8π + π/2 (or d_A), not «some C».
Only after 1–5 does a candidate get a number on the caches or a batch to the judge.

## 5. What is live under the filter (2026-09-06)

- **First named candidate — KILLED as printed (verdict SECONDEXPR-B, b1efb9e1, 2026-09-06):** Suzuki 2301.00421 defines S_t := S_{−t} and P_t := P_{−t}
  for t < 0 (verified in the PDF). Then P̂_{Dψ} ≡ 0 for every even test while Q(ψ_L) ≥ 2‖ψ_L‖² > 0 on a narrow even bump: the printed Theorem 1.4 is
  inconsistent with the printed definitions (a source defect, not a statement about RH). The judge retracted his endorsement. What survives, zero-free:
  the Volterra identity (11), the bounded-multiplier L² representation (13)–(14), the free Gram kernel (16), the exact remainder (18). A signed-time
  repair (25) is proposed (not author-confirmed); for it the radical-cutoff check (27) is proved unconditionally, and the remaining target is exact:
  (OPEN) ∂_t∂_u V_sgn(t,u) = T(t−u) − 2δ(t−u), T = −g_ξ″ from (17). Plants: Q_H(v) = −2 on explicit tests — the forbidden step is replacing the crossed
  conjugate-zero pairing by a diagonal Parseval metric ((4.5)/(4.9) without real zeros). The compass 𝒞 = −Θ_ξ remains a correct dictionary, not a proof.
  **Reduced (verdict OPENSGN, 9a7a3a9c, 2026-09-06, PARTIAL):** both time integrations of (OPEN) are evaluated (double Laplace in both sign quadrants,
  signed Volterra derivative with the logarithmic endpoint, exact prime shift operators). Falsifier: the η-part (η = Im of X/(X−iX′) on the axis) has
  zero double Laplace transform on equal positive parameters, so «ω carries the archimedean part, η carries the prime atoms» is impossible; all
  arithmetic sits in the Poisson average of ω = X²/(X²+X′²). Lemma 7 (proved): (OPEN) ⟺ one scalar identity
  (P) (1/π)∫_ℝ pX(x)²/((p²+x²)(X²+X′²)) dx = ξ(½+p)/(ξ(½+p)+ξ′(½+p)), p > ½.
  (P) is not proved, and a proof of (P) would exclude every nonreal upper zero (a zero p₀ of ξ(½+p) in Re p > 0 forces m·h(p₀)Ω(p₀) = 0 with Re Ω > 0).
  So the signed Suzuki candidate is a coordinate after all — but with the whole remaining computation done and the wall in one line: (P) says the
  Poisson reconstruction of the bounded boundary function v = X/(X−iX′), |v| ≤ 1, equals the meromorphic continuation F/(F+F′); RH = v has no poles
  inside. Plants (H₁ with the zero p₀ = ¼) fail exactly at this Poisson-reconstruction step, as §4.3 demands. Radical consistency (35) holds.
  Toy calibration X(z) = z (Ω_p = p/(p+1), J_pq = 1/(p+1) − 1/(q+1)) checked numerically by the observer. Judge's directive: independent check of
  (17)–(18), the p = q cancellation, the Hilbert step (27)–(29) — running.
- **Second named candidate (Connes card 2026-09-06, locators verified):** the semilocal trace identity, Connes 2602.04022 eq. (22),
  −Σ_{v∈S}W_v(f) = log(TW)f(1) + Trace(ϑ(f)(1 − P_T^S − P̂_W^S)), carries the primes and is unconditional; the archimedean analogue (CC 2006.13771 Thm 4.7 (83))
  splits as nonnegative HS trace of the Sonin compression minus an explicit prolate remainder. Open question, written by nobody: does (22) admit the same
  splitting with the semilocal Sonin projection? CC 2106.01715 shows the archimedean part alone dies at L = log 2 and the prime 2 restores it — any second
  expression must carry the primes (our §4.4 seen from the other side). Bost–Connes contributes nothing here (ζ as partition function on Re β > 1).
- R1 (COUPLED): a nonlocal positive factor on f₀s with proved annihilation of the radical — no candidate formula exists beyond the two named above.
- R2 (COUPLED/ZG): cutoff-dependent Gram certificates K_m + e_m I ⪰ 0 with e_m → 0 and proved recovery — no rule for e_m exists.
- The frame reading of WEILPROOF (i): K = Γ − c_L I − 2ββ*, i.e. the prime atoms and short shifts form a frame whose optimal lower bound is c_L.
  Frame theory (Beurling–Landau density, Kadec) gives bounds with slack — fails §4.5 unless an identity appears.
- Read 2026-09-06 (card JEFFREYCLAGA_USAGE_CARDS.md): Lagarias–Suzuki 2006 and Lagarias 2006 get zeros on the line for two-term shift combinations
  F(s+c) ± F(s−c) by per-zero dominance whose only input is the zero-free line Re s = 1 (shift c ≥ ¼, h ≥ ½); modularity/Hecke inessential
  (Maass–Selberg used only for the constant term a₀). Transfer to Q(f₀s): none — the mechanism takes zero locations as input (fails §4.2) and is
  indifferent to plants (fails §4.3). Extra discriminator gained: any two-term dominance representation has rigid unit zero spacing, not GUE (Lagarias Thm 4.1).
- Measured tonight (Probe 27): the ground transform's axis remainder is R_ax ≈ e^{−9.42 m}, far below √λ₁; the Rouché certificate of window m
  covers heights up to ≈ 11.6 m. Diagnostic; it locates the failure, it is not a mechanism.

## 6. Standing rule

New coordinates are not work. A new input is read, checked by number, filed in CHAT_DIGESTS in one paragraph, and not probed further unless
it passes §4. The observer's time goes to §5 and to the paper.
