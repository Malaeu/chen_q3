# Synthesis 2026-11-06: “everything is in the primes” vs “the tail” — one object

Status: internal Mythos synthesis. CHALLENGER / NOT_RH.

Labels:
- FACT — a formula, a theorem, or algebra checked in code.
- DIAG — finite numerics.
- HYP — hypothesis.

## 1. The apparent contradiction

- Oct → 5 Nov (window route), docs `claude/INSIGHT_POLE_ECHO_SQRT_WALL_2026-11-05.md` and `claude/SYNTHESIS_ZERO_COUNTER_2026-11-05.md`: the √m wall is the echo of the pole. Everything reduces to the pole-renormalised prime sum Σ(Λ(n) − 1)n^{−1/2+it} and its antiderivative, the windowed zero counter F_m(t). → **everything is in the primes.**
- 6 Nov, Proshka C (a337b335, eq. (16)–(18)): the balanced Green form Z_N splits into an initial square ℓ, k ≤ N (primes, (18)) and the indices N < ℓ ≤ N² (the truncated divisor sum). Mythos then wrote “the difficulty is probably in the tail.” **That was not computed. It is wrong (DIAG below).**

## 2. The identification (FACT)

1. A_N(ℓ) = Λ_N(ℓ)/L − s_N, where Λ_N(ℓ) = Σ_{d|ℓ, d≤N} μ(d) log(N/d) is the Goldston–Yıldırım truncated von Mangoldt function with R = N.
   - For 2 ≤ ℓ ≤ N it equals Λ(ℓ) exactly (checked in code to 1e−15).
   - L·s_N → 1, since the residue of x^s/(s²ζ(1+s)) at 0 is 1. At N = 3000, L·s_N = 0.99968.
   - So the NB Möbius taper μ(n) log(N/n)/log N **is** the GY / Selberg / mollifier weight. Z_N is a weighted second moment of 1 − Λ_N on [1, N²]. The cutoff T = N² means R = √T, which is exactly the classical x^{1/2} edge of truncated-divisor-sum mean values.
2. 1/max(ℓ, k) = (ℓk)^{−1/2} e^{−|log(ℓ/k)|/2}. Hence, with κ(ℓ/k) in place of κ((ℓ+1)/(k+1)):

       Z_N ≈ (1/L²) ∫ |D_N(t)|² K̂(t) dt/2π,
       D_N(t) = Σ_{ℓ≤N²} L(1_{ℓ=1} − A_N(ℓ)) ℓ^{−1/2−it},
       K(u) = e^{−|u|/2} (1 − |u|/log 2)_+.

   - K̂ ≥ 0 by Schur's product theorem (a product of two positive-definite functions).
   - Checked at N = 3000 on the initial square: direct sum 1.28596 vs Fourier 1.28100 (t truncated at ±400). The +1 shift changes the value by ≈ 1.4%.
3. On ℓ ≤ N, D_N(t) = Σ (L s_N − Λ(ℓ)) ℓ^{−1/2−it} + L s_N·[ℓ = 1 term]. This is exactly the pole-subtracted sum of 5 Nov.

**Proshka's head (18) is the 5 Nov object, measured in a positive spectral norm.**

## 3. Where the mass is (DIAG, `/home/claude/wow/zsplit.py`, exact Λ_N up to T = N², t ∈ [−120, 120])

| N | Z_N (Fourier) | head ℓ ≤ N | tail N < ℓ ≤ N² | cross | Z_N·L |
|---|---|---|---|---|---|
| 100 | 0.0754 | 0.0797 | 0.0155 | −0.0199 | 0.347 |
| 200 | 0.0612 | 0.0664 | 0.0138 | −0.0191 | 0.324 |
| 300 | 0.0548 | 0.0527 | 0.0021 | 0.0000 | 0.312 |

- The head carries 96–106% of Z_N; tail plus cross is within ±5–9%.
- |D_N| spikes at the zeros 14.13 and 21.02: 4.6 → 5.3 → 5.7, growing like log N. Away from zeros it is ≈ 1.
- Compare Proshka's direct value Z_64 = 0.1005.
- Small N only; S starts at 43297. Codex addendum baf63568 measures the same split on S. Stake D3 (head < 50%), registered before this run, is now very likely a MISS.

## 4. One picture

| | Window route (Oct–5 Nov) | NB / Green route (6 Nov) |
|---|---|---|
| Arithmetic object | Σ(Λ − 1)n^{−1/2+it}, pole subtracted | the same, as the head of D_N(t); tail = GY truncation N < ℓ ≤ N² |
| Functional | drawdown of the antiderivative F_m (zero counter) | energy ∫\|D_N\|² K̂, with K̂ ≥ 0 |
| What RH needs | drawdown ≤ polylog | Z_N ≤ C infinitely often on S |
| What a right zero does | the counter runs backwards by ~m^δ | \|D_N\|² ~ N^{2β−1} near γ, so Z_N grows |
| Positivity already available | J₋ ≥ 0 from the pole (8.3) | K̂ ≥ 0 (Schur) |

HYP: the two routes are two norms of one function on the critical line. Possible use:
- the drawdown/counter form is “L^∞ of the antiderivative”;
- Z_N is “L²(K̂) of the derivative”.

A bound for one may transfer to the other by a 1-D interpolation, losing at most log factors. Under RH, the heuristic sum over zeros of spikes of height ~L and width ~1/L, weighted by K̂(γ), gives Z_N ≍ c/L. That is consistent with Z_N·L ≈ 0.31–0.35.

## 5. Consequences

1. Retract “the difficulty is in the tail.” On the data, it sits in the head = the primes = the pole-renormalised prime polynomial, as found in Oct–Nov.
2. The tail is still not nothing. It is the GY truncation at the √T edge, and in the bound it must be paid, not neglected. Proshka's (17) pays it only up to a constant.
3. Next questions:
   - (a) the transfer counter-drawdown ⇄ Z_N (1-D, cheap to test numerically on the same D_N);
   - (b) whether the J₋ ≥ 0 pole positivity of (8.3) appears inside Z_N's head as a free positive term.
