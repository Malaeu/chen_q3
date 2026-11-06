# Ramanujan sweep for Route B (2026-11-06)

Status: Mythos literature sweep. CHALLENGER / NOT_RH.
Labels: FACT = from a cited source; HYP = hypothesis; SPEC = speculation.

The target, from the constructor (`docs/routeB_bus/mythos/ROUTE_B_CONSTRUCTOR_PROVEN_2026-11-06.md`, f26f89f9):
- A4 (115714b7, Thm 2): RH ⇔ z*B⁽¹⁾z ≤ C·z*Gz on K_m, with B⁽¹⁾[f] = Σ_{p<m} (log p/√p)·Q_f(log p).
- In NB coordinates: Z_N (a337b335), with A_N = Λ_N/L − s_N.
- Open item of R6 B (888b8080): a Gaussian-specific source return.

## Items

| # | Ramanujan item | Exact content (FACT) | Addition × multiplication? | What it can do for us | Status |
|---|---|---|---|---|---|
| R1 | **Ramanujan–Hardy–Littlewood identity** (Second Notebook p. 312, corrected by HL 1916) | For αβ = π: √α Σ μ(n)/n·e^{−α²/n²} − √β Σ μ(n)/n·e^{−β²/n²} = −(1/(2√β)) Σ_ρ Γ((1−ρ)/2)β^ρ/ζ′(ρ) (simple zeros). RH ⇔ Σ μ(n)/n·e^{−x/n²} = O(x^{−1/4+ε}) (HL); Riesz 1916: Σ μ(n)/n²·e^{−x/n²} = O(x^{−3/4+ε}) ⇔ RH | μ (×) against the exact Gaussian θ-modularity (Poisson on ℤ, +) | Möbius sums with the EXACT Gaussian kernel and an exact α ↔ β modular symmetry. This is precisely the class R6 B left open (exact, Gaussian-specific, zero tolerance), on the μ side that our NB/E_N uses. The zero side carries 1/ζ′(ρ), as in NB/J₋₁ | ⇔ RH reformulation; HL could not prove rapid convergence of the ρ-series even under RH. Generalisations: Dixit–Roy–Zaharescu (characters, Hecke forms), Agarwal–Garg–Maji PAMS 2022 (arXiv:2202.00637), Garg–Maji GRH (2208.07596) |
| R2 | **Finite Ramanujan expansion of the truncated von Mangoldt function** | Λ_N(n) = Σ_{q≤N} Λ̂_N(q)·c_q(n), exact and finite (Coppola–Murty–Saha JNT 2017; Laporta arXiv:2204.01581) | c_q(n) = sum of additive characters over reduced residues; coefficients multiplicative in q | The head of Z_N (= B⁽¹⁾ in NB coordinates) becomes an exact quadratic form in c_q, q ≤ N, against the positive kernel K̂ | Exact identity. Warning from the constructor: CRT averaging (2cb30501) is not the fixed form; the sign can only come from exact cancellation BETWEEN different q |
| R3 | **Shift-Ramanujan expansions of correlations** | C_{f,g}(N,h) = Σ f(n)g(n+h) = Σ_ℓ Ĉ(N,ℓ)·c_ℓ(h); finite and pure ⇔ Carmichael formula ⇔ REEF (Coppola–Murty). Under the Delange hypothesis this gives HL for 2k-twins (Coppola 2019) | n + h (shift) × divisor structure | The language for n+1 / n+h inside our Gram (unit shift, 2cb30501) | The infinite version is conditional (Delange hypothesis; Hardy's expansion is not absolutely convergent) |
| R4 | **Hardy's expansion** | (φ(n)/n)·Λ(n) = Σ_q μ(q)/φ(q)·c_q(n), pointwise convergent (Hardy 1921) | yes | The heuristic source of singular series / twin constants | Not absolutely convergent; the Wiener–Khintchine step is unjustified |
| R5 | **Ramanujan's Ξ-integrals** (1915 paper; Lost Notebook p. 220; Koshliakov, Guinand formulas) | Modular relations F(α) = F(β) tied to integrals of Ξ(t/2)·\|Γ\|²·cos(½t log α)/(1+t²) (Berndt–Dixit) | θ / Γ (archimedean) × ζ | Exact modular relations; Hardy 1914 (infinitely many zeros on the line) used this kind of integral | Archimedean side, already paid in our chain (B3); positive-proportion type, never excludes zeros |
| R6 | **Farey / Franel–Landau** | Σ over the Farey sequence of order Q of e(γ_j) = M(Q); RH ⇔ Farey discrepancy bound | Farey fractions (+) × μ | Same wall as weak Mertens | Reformulation |
| R7 | **τ(n), Ramanujan conjecture** | \|τ(p)\| ≤ 2p^{11/2}: Deligne, via the Weil conjectures | — | The √-bound came from geometry / positivity, not cancellation (as in LIT_KLOOSTERMAN) | World T2 in Codex task d665cb69 |
| R8 | **Ramanujan graphs** | Ihara zeta satisfies RH ⇔ λ ≤ 2√q (spectral gap) | — | RH = a spectral bound, like our floor A_m ≥ −C | Analogy only |
| R9 | **Mock theta** | quantum modular (Zagier) | — | Bettin–Conrey "nearly" quantum modular; the defect is the pole | Paid (B1); the Codex task was withdrawn (caa97887) |

## Verdict

**HYP: the two items that fit are R1 and R2.**
- R1 is the classical exact identity in which μ (multiplication) meets the exact Gaussian / θ-modularity (addition via Poisson on ℤ). That is the shape R6 B demands for any surviving return.
- R2 makes the head of Z_N an exact finite form in Ramanujan sums.

SPEC: combine them, i.e. evaluate Z_N / B⁽¹⁾ on the Gaussian vector of the Gaussian export (A2, 62f78231) using R2, and exploit the α ↔ β symmetry of R1 as the exact source return.

## Sources

- Agarwal–Garg–Maji, Riesz-type criteria for RH, arXiv:2202.00637 (PAMS).
- Garg–Maji, arXiv:2208.07596.
- Dixit–Roy–Zaharescu, Riesz-type criteria and theta transformation analogues, JNT 160 (2016).
- Coppola–Murty–Saha, JNT 174 (2017), arXiv:1612.03136; Coppola–Murty II, arXiv:1705.07193; Coppola, HRJ 2019.
- Laporta, arXiv:2204.01581.
- Berndt–Dixit, arXiv:0904.1053.
- Murty–Saha, JNT 156 (2015).
