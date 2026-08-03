# Kulikov (+Larsen), localization-operator eigenvalue estimates — verified usage cards

Source PDFs (all read verbatim, pages 1–8 = statements section of each):

1. `docs/routeB_bus/litreview/pdfs/2603.07407.pdf` — A. Kulikov, *Sharp estimates for eigenvalues of localization operators before the plunge region*, arXiv:2603.07407v1 [math.CA], 8 Mar 2026.
2. `docs/routeB_bus/litreview/pdfs/2603.23832.pdf` — A. Kulikov & M. D. Larsen, *Sharp estimates for eigenvalues of localization operators with applications to area laws*, arXiv:2603.23832v1 [math.SP], 25 Mar 2026.
3. `docs/routeB_bus/litreview/pdfs/2306.12430.pdf` — A. Kulikov, *Exponential lower bound for the eigenvalues of the time-frequency localization operator before the plunge region*, arXiv:2306.12430v1 [math.CA], 3 Jun 2023 (published ACHA 2024).

Notation used below matches the Q3/Route B labels: λ_n(c) = eigenvalues of the time–frequency localization operator S_{A,B} (= S_{I,J} = P_I F^{-1} P_J F P_I) with c = |A||B| the Shannon-number scaling; plunge region ≈ near n = c; the "before-plunge" regime is n < c.

**IMPORTANT SCOPE NOTE:** All three are harmonic-analysis / spectral-theory papers about time–frequency (prolate / localization) operators. **None proves anything about the Riemann Hypothesis or Q3.** They are TOOLS for the tail/ladder (H4 detector decay, edge-tail truncation). No numeric evaluation here is a proof.

---

## TARGET 1 — Sharp two-sided bound on −log(1−λ_n(c)) BEFORE the plunge — Paper 1

### 1a. Abstract statement of the sharp order — Paper 1, p. 1 (Abstract)
VERBATIM: "We show that for n < c − c^{0.99}, say, in the time-frequency localization case we have − log(1 − λ_n(c)) ≍ (c−n)/log( (2c)/(c−n) ) while in the coherent state transform case we have − log(1 − μ_n(c)) ≍ (√c − √n)^2, which is much smaller if c − n = o(c), so there is indeed a difference between these two cases."
K7-TAG: THEOREM (abstract summary of Theorem 1.6 + Theorem 1.7)
MAPS TO Q3: edge-tail-C3 (controls how fast 1−λ_n grows as n approaches the plunge from below) AND two-level-ladder (sharp order of the spectral gap 1−λ_n).
PROVED-OR-OPEN: proved unconditionally. Two-sided order (≍), but with a domain caveat: the upper bound (Theorem 1.7) is only proved for n < c − log²(c); the lower bound (Theorem 1.6) proven for c > c₀ and n < c (fully) via [14], see 1c below. The `≍` is genuine two-sided in the overlap regime.

### 1b. Lower bound (eigenvalues stay close to 1) — Paper 1, Theorem 1.6, p. 4
VERBATIM: "**Theorem 1.6.** There exist numbers c₀, η > 0 such that for c > c₀ and n < c we have
  λ_n(c) > 1 − exp( −η · (c−n)/log( (2c)/(c−n) ) )."
K7-TAG: THEOREM
MAPS TO Q3: edge-tail-C3 / H4-DetectorDecay (lower bound = eigenvalues below plunge are exponentially close to 1; the complementary "how small is 1−λ" statement).
PROVED-OR-OPEN: proved unconditionally, for all n < c (Remark 1.9: the full n < c range was established by Larsen & the author [14] by purely Fourier-analytic methods; the paper itself proves Theorem 1.6 directly only for n < c − c^{7/8}, filling the rest via Thm 1.3 + Thm 1.4). One-sided (lower).

### 1c. Upper bound (eigenvalues are bounded away from 1) — Paper 1, Theorem 1.7, p. 4
VERBATIM: "**Theorem 1.7.** There exist numbers c₀, κ > 0 such that for c > c₀ and n < c − log²(c) we have
  λ_n(c) < 1 − exp( −κ · (c−n)/log( (2c)/(c−n) ) )."
K7-TAG: THEOREM
MAPS TO Q3: two-level-ladder / edge-tail-C3 (guarantees a *minimum* size for the gap 1−λ_n — i.e. λ_n is not too close to 1, giving a usable spectral separation near the edge).
PROVED-OR-OPEN: proved unconditionally, for n < c − log²(c). One-sided (upper). Remark 1.8: authors suspect but cannot prove the log²(c) cushion can be removed.

---

## TARGET 2 — Plunge counting function + trace estimate — Paper 2 (and Paper 1)

### 2a. Counting function of the plunge (transition) region, general case — Paper 2, Theorem 1.6, p. 5
VERBATIM: "**Theorem 1.6.** Assume that A and B are bounded sets whose boundaries have finite upper Minkowski content and such that both A and B have positive measures. There exists α = α(d, A, B) ≥ 4 such that for all c ≥ 2 and α^{−c} < ε < ½ we have
  Λ_ε(cA, B) ≲ c^{d−1} log(1/ε) log²( (α c)/log(1/ε) ).
For ε ≤ α^{−c} there are no eigenvalues larger than 1 − ε and
  Λ_ε^{−}(cA, B) ≍ ( log(1/ε) / log( log(1/ε)/c ) )^d."
K7-TAG: THEOREM
MAPS TO Q3: two-level-ladder (counts eigenvalues in the intermediate band ε < λ_n ≤ 1−ε, i.e. the plunge width — the "how many detector modes live in the transition" count). Here Λ_ε(A,B) = |{n : 1−ε ≥ λ_n(c) > ε}| (Eq. 1.2, p. 2).
PROVED-OR-OPEN: proved unconditionally under finite-upper-Minkowski-content boundary hypothesis. Upper bound is one-sided (≲) and is "at most a single logarithm" off the conjectural optimum (log² vs conjectured log); the Λ_ε^{−} part is two-sided (≍).

### 2b. Sharp counting bound when one set is a union of parallelepipeds — Paper 2, Theorem 1.3, p. 4
VERBATIM: "**Theorem 1.3.** Assume that A is a bounded set whose boundary has finite upper Minkowski content and B is a finite union of parallelepipeds with disjoint interiors such that both A and B have positive measures. There exists α = α(d, A, B) ≥ 4 such that for all c ≥ 2 and α^{−c} < ε < ½ we have
  Λ_ε(cA, B) ≲ c^{d−1} log(1/ε) log( (α c)/log(1/ε) )."
K7-TAG: THEOREM
MAPS TO Q3: two-level-ladder (this is the SHARP version of the plunge count — single log, no square; the sharpest counting estimate in the paper).
PROVED-OR-OPEN: proved unconditionally; stated as "sharp in the setting of Theorem 1.3" (p. 5, Proof-strategy paragraph and Abstract). One-sided upper (≲) but sharp (matched by lower bound (1.5) for ε < α_d^{−c} in the box case, Theorem 1.1 p. 3).

### 2c. Best-possible counting constant / one-dimensional sharp bound (KRD) — Paper 1, Theorem 1.4, p. 3  (= Paper 3, Theorem 1.2, p. 2)
VERBATIM (Paper 1, Thm 1.4): "For all c > 0 and 0 < ε < ½ we have
  |Λ_ε(c)| ≤ (2/π²) log(50c + 25) log( 5/(ε(1−ε)) ) + 7."
K7-TAG: THEOREM (attributed: Karnik, Romberg, Davenport [10, Theorem 3])
MAPS TO Q3: two-level-ladder (explicit, uniform-in-all-parameters bound on the number of plunge eigenvalues; the constant 2/π² is best possible — Paper 1 note p. 3). Λ_ε(c) = {n : 1−ε > λ_n(c) > ε}.
PROVED-OR-OPEN: proved unconditionally, fully explicit. One-sided upper. NOTE: this is a CITED prior result (KRD), re-used, not original to these papers.

### 2d. Trace / area-law application (the "trace estimate") — Paper 2, §1.5 Area laws, p. 8
VERBATIM: "We are interested in the traces Tr f(S_{A,B}) for general functions f : [0,1] → ℂ. For a compact self-adjoint operator T : H → H with eigenvalues 1 ≥ λ₁ ≥ λ₂ ≥ … ≥ 0 and corresponding normalized eigenvectors v₁, v₂, … we define f(T)(v) := Σ_{n=1}^∞ f(λ_n)⟨v, v_n⟩ v_n. This operator is trace class whenever Tr f(T) = Σ_{n=1}^∞ f(λ_n) converges absolutely."
K7-TAG: THEOREM (framing; the quantitative area-law/two-term-asymptotics for Tr f(S_{A,B}) is the stated application of Theorems 1.3/1.6, Abstract p. 1 and p. 2 "two-term asymptotics for Tr f(S_{A,B}) for very rough functions f").
MAPS TO Q3: edge-tail-C3 (a trace/sum over eigenvalues Σ f(λ_n) is exactly the object a detector-weighted sum W_j·(spectral data) resembles; the counting bounds feed the trace estimate for low-regularity f).
PROVED-OR-OPEN: framing definition is standard; the resulting two-term trace asymptotics are proved unconditionally under the paper's boundary hypotheses. Application, not a standalone inequality — quote the counting theorems (2a/2b) for the load-bearing estimate.

---

## TARGET 3 — Pre-plunge lower bound of the form λ_n(c) > 1 − δ^c — Paper 3 (and Paper 1)

### 3a. Exponential closeness to 1 all the way to the plunge — Paper 3, Theorem 1.4, p. 3
VERBATIM: "**Theorem 1.4.** For any ε > 0 there exists constant 0 < δ = δ(ε) < 1 such that for large enough c we have
  λ_n(c) ≥ 1 − δ^c,
where n = [(1−ε)c]."
K7-TAG: THEOREM
MAPS TO Q3: H4-DetectorDecay / edge-tail-C3 (for any fixed fraction (1−ε) of the Shannon number, the eigenvalues are exponentially (in c) close to 1 — i.e. the "bulk before plunge" is uniformly saturated; complements the smallness of the tail). Note (p. 3): "exponential lower bound is the best we can achieve since this is the best possible bound already for the λ₁(c)."
PROVED-OR-OPEN: proved unconditionally (via Bargmann transform / circle-packing Lemma 1.5). One-sided (lower). Improves Bonami–Jaming–Karoui (who had ε ≥ 0.42) and Fuchs.

### 3b. Same statement restated in Paper 1 — Paper 1, Theorem 1.5, p. 3
VERBATIM: "**Theorem 1.5.** For any δ > 0 there exists γ = γ(δ) < 1 such that for all big enough c and all n < (1−δ)c we have
  λ_n(c) ≥ 1 − γ^c."
K7-TAG: THEOREM (author self-citation [13] = Paper 3)
MAPS TO Q3: H4-DetectorDecay / edge-tail-C3 (same content as 3a, now for ALL n < (1−δ)c uniformly, not just n = [(1−ε)c]).
PROVED-OR-OPEN: proved unconditionally. One-sided (lower). Paper 1 p. 3 notes the exponent γ worsens as δ→0 — which is exactly what Theorems 1.6/1.7 (Target 1) sharpen via the log-factor interpolation.

### 3c. Bonami–Jaming–Karoui explicit lower bound (cited baseline) — Paper 3, Theorem 1.3, p. 3
VERBATIM: "**Theorem 1.3.** For 0 ≤ n ≤ c and c > 100 we have
  1 − ((πc)^n / n!) e^{−(π/2)c} ≤ λ_n(c) < 1."
K7-TAG: THEOREM (cited: Bonami, Jaming, Karoui [2])
MAPS TO Q3: H4-DetectorDecay (explicit finite-c lower bound; note p. 3: meaningful only if (πc)^n/n! · e^{−πc/2} ≤ 1, i.e. n ≲ 0.58c). One-sided (lower), proved unconditionally, CITED prior result.

---

## TARGET 4 — form of each estimate (equality / two-sided / one-sided; proved?)

| Card | Estimate | Type | Direction | Proved unconditionally? |
|------|----------|------|-----------|--------------------------|
| 1a (abstract ≍) | −log(1−λ_n) ≍ (c−n)/log(2c/(c−n)) | sharp two-sided ORDER (≍) | both | yes (overlap n < c − log²c) |
| 1b (Thm 1.6) | λ_n > 1 − exp(−η·…) | inequality | lower | yes, all n<c (via [14]) |
| 1c (Thm 1.7) | λ_n < 1 − exp(−κ·…) | inequality | upper | yes, n < c − log²c |
| 2a (Thm 1.6, P2) | Λ_ε ≲ c^{d−1} logε⁻¹ log²(αc/…) | inequality (+ ≍ for Λ⁻) | upper (Λ), two-sided (Λ⁻) | yes (Minkowski hyp.) |
| 2b (Thm 1.3, P2) | Λ_ε ≲ c^{d−1} logε⁻¹ log(αc/…) | inequality, SHARP | upper | yes |
| 2c (Thm 1.4, P1 / KRD) | \|Λ_ε\| ≤ (2/π²)log(50c+25)log(5/(ε(1−ε)))+7 | explicit inequality, best constant | upper | yes (cited) |
| 3a (Thm 1.4, P3) | λ_n ≥ 1 − δ^c, n=[(1−ε)c] | inequality | lower | yes |
| 3b (Thm 1.5, P1) | λ_n ≥ 1 − γ^c, all n<(1−δ)c | inequality | lower | yes |
| 3c (Thm 1.3, P3 / BJK) | 1 − (πc)^n/n! e^{−πc/2} ≤ λ_n < 1 | explicit inequality | lower | yes (cited) |

No card is an exact equality; the sharpest is the two-sided ORDER relation ≍ (Target 1).

---

## TARGET 5 — DECAY RATE of the small eigenvalues (tail λ_n → 0), for H4 detector decay

### 5a. Uniform exponential singular-value decay (the key tail-decay tool) — Paper 2, Lemma 1.8, p. 8
VERBATIM: "**Lemma 1.8.** There exist τ > 0, C > 0, and r₀ > 0 such that for all r > r₀ and all n ∈ ℕ we have
  σ_n(I_r) ≤ { 1,          n < 10r
             { C e^{−τ n},  n ≥ 10r ,
  σ_n(J_r) ≤ C e^{−τ n}."
where (p. 8) "I_r = Q_{[0,1]} P_{[0,r]}  and  J_r = P_{(−∞,−2r]∪[2r,+∞)} Q_{[0,1]} P_{[−r,r]}. Note that I_r is just the usual time-frequency localization operator."
K7-TAG: LEMMA
MAPS TO Q3: **H4-DetectorDecay** (this is the cleanest usable "tail" statement: past the plunge threshold (n ≥ 10r) the singular values / eigenvalues of the 1-D localization operator decay like e^{−τn} UNIFORMLY in the scale r — exactly a detector weight W_j → 0 exponentially). Paper 2 stresses (p. 8): "The fact that the estimate for σ_n(J_r) does not depend on r is the key new ingredient."
PROVED-OR-OPEN: proved unconditionally. One-sided upper bound on the decay (σ_n ≤ Ce^{−τn}). The constant τ is not made explicit here.

### 5b. Classical super-exponential tail (fixed c) — cited in Paper 1 (Widom) and Paper 3 (Widom), p. 2
VERBATIM (Paper 3, p. 2): "Widom [16] showed that for fixed c the eigenvalues decay like λ_n(c) ∼ ( eπc/(8n+4) )^{2n+1}, and the works of Osipov … established uniform in c upper bounds on λ_n(c), in particular [3, Theorem 1] essentially says that after the plunge region (say, for n > (1+ε)c) the eigenvalues start with an exponential decay and then catch up to the super-exponential decay similar to the Widom's result."
K7-TAG: THEOREM (cited: Widom; Bonami–Jaming–Karoui [3])
MAPS TO Q3: H4-DetectorDecay / edge-tail-C3 (describes the ABOVE-plunge tail λ_n → 0 as super-exponential in n for fixed c; the qualitative statement that past the plunge the detector weights collapse fast).
PROVED-OR-OPEN: proved unconditionally (cited prior results). One-sided (upper bound on tail). Fixed-c asymptotic (∼), not uniform; for uniform-in-c use the Osipov/BJK exponential-then-superexponential statement or 5a.

### 5c. Fuchs fixed-n asymptotic (complementary, near-1 side) — Paper 1 p. 3 / Paper 3 p. 3
VERBATIM (Paper 1, p. 3): "For fixed n Fuchs [6] showed that the eigenvalues satisfy
  1 − λ_n(c) ∼ 4√2 · ((4π)^n / n!) · c^{n−½} e^{−πc},
in particular that they are exponentially close to 1."
K7-TAG: THEOREM (cited: Fuchs [6])
MAPS TO Q3: edge-tail-C3 (fixed-n, c→∞ asymptotic for the gap 1−λ_n; complements 5a/5b by pinning the deep-below-plunge behaviour).
PROVED-OR-OPEN: proved unconditionally (cited). Fixed-n asymptotic (∼), one gap direction. Not uniform in n.

---

## SUMMARY

- **Targets found verbatim:** all 5 target categories located and quoted. 12 distinct quoted statements across the 3 papers (9 original to Kulikov/Larsen + 3 cited baselines KRD/BJK/Fuchs/Widom re-stated). Nothing marked NOT FOUND.
- **Single sharpest λ_n(c) estimate (quote):** the sharp two-sided order from Paper 1 (Abstract, p.1; = Theorems 1.6+1.7):
  "− log(1 − λ_n(c)) ≍ (c−n)/log( (2c)/(c−n) )" — valid for n < c − c^{0.99} (time–frequency case).
- **Unconditional?** YES — every estimate above is proved unconditionally within its stated regime; these are harmonic-analysis theorems with no conjectural input. (The only "gaps" are domain cushions: Theorem 1.7 needs n < c − log²c; Theorem 1.6's full n<c range comes via companion paper [14].)
- **Best single H4 detector-decay tool:** Paper 2, Lemma 1.8 — uniform σ_n ≤ C e^{−τn} for n ≥ 10r, scale-independent.
- **File written:** `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/KULIKOV_PLUNGE_USAGE_CARDS.md`

**Do NOT claim any Q3/RH closure from these papers.** They supply sharp spectral-tail and plunge-count TOOLS only.
