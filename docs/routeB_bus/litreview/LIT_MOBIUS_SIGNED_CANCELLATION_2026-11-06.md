# Literature: signed Möbius cancellation vs Route B condition (26) — 2026-11-06

Purpose. Before Round 11, check what the literature offers for the gap left by R9 and R10 (proshka_inbox b5fc098b, 4a496c5c). That gap is **signed interpacket control** of the true Möbius core H_N on the crossing set S.

Classes already killed:
- moment-only bounds (R9);
- packet-separable positive majorants on the true μ (R10);
- universal rational-frequency o(N²) bounds (R8).

Labels: FACT means read in the source text or abstract retrieved today. ASSESSMENT means Mythos's judgement, not checked by Proshka.

## 1. Where (26) sits classically

**Ng, arXiv:math/0310381 (PLMS 2004).** CONDITIONAL. FACT.

Assuming RH and J_{−1}(T) = Σ_{0<γ<T} |ζ′(ρ)|^{−2} ≪ T, Ng proves:
- M(x) ≪ √x (log x)^{3/2};
- ∫_2^X M(x)²/x dx ≪ X;
- the weak Mertens bound ∫_2^X (M(x)/x)² dx ≪ log X;
- a limiting distribution for e^{−y/2}M(e^y).

**ASSESSMENT.** The head part of H_N is a ψ-version of the weak-Mertens mean square, normalised by 1/log²N. In both:
- RH gives a size of order 1/log N;
- (26) needs only boundedness, and only along S.

(26) is therefore a subsequence form of a classical weak-Mertens-type statement. Restating it is F1, NO_PROGRESS.

**Records.** FACT, from the survey arXiv:2407.17820:
- limsup M(x)/√x > 1.826054;
- liminf M(x)/√x < −1.837625;
- largest known |M(x)|/√x is 0.5857677, at x ≈ 1.16·10^19.

Mertens' conjecture is false. Weak Mertens is open.

## 2. "Möbius randomness": strong, but not at √ scale

| Work | Result (FACT) | Reaches (26)? (ASSESSMENT) |
|---|---|---|
| Matomäki–Radziwiłł, Ann. Math. 183 (2016) | Multiplicative functions in short intervals; o(1) savings | No: qualitative o(1), not √ |
| Matomäki–Radziwiłł–Tao–Teräväinen–Ziegler, Ann. Math. 197 (2023) 739–857 | Higher uniformity of λ in short intervals on average, o(XH) for X^θ ≤ H ≤ X | No |
| Matomäki–Shao–Tao–Teräväinen, Forum Math. Pi 11 (2023) e29 | Σ_{X<n≤X+H}(f − f^♯)·nilsequence ≪ H log^{−A}X for θ = 5/8, f ∈ {Λ, μ, d_k} | No: saves powers of log, not √ |
| Tao, Forum Math. Pi 4 (2016) | Log-averaged two-point Chowla/Elliott | No |
| Tao–Teräväinen | Log Chowla for odd k; even k ≥ 4 open | No |
| Pilatte, arXiv:2310.19357 | Improved quantitative two-point log Chowla bound | No |

**Conclusion (ASSESSMENT).** The parity barrier and short-interval methods give o(1) or log^{−A} savings. Nothing in this family delivers the square-root-scale mean-square control that (26) needs.

## 3. The unlocked mechanism: hidden modular symmetry of the NB Gram

**Bettin–Conrey, "Period functions and cotangent sums", Algebra & Number Theory 7 (2013) 215; arXiv:1111.0931.** FACT.
- d_N² is a quadratic expression in the a_m whose coefficients are **Vasyunin sums**.
- The Vasyunin sum is essentially the cotangent sum c₀ evaluated at h̄/k, where h h̄ ≡ 1 mod k (Maier–Rassias (1.4)).
- c₀ satisfies an exact **reciprocity formula**, h/k ↔ k/h, derived from the period function of the Eisenstein series Σσ_a(n)e(nz).
- This makes c₀ nearly a **quantum modular form** in Zagier's sense, "imperfect" because of a non-smooth correction term.
- The authors read this as a hidden symmetry of the twisted mean square ∫|ζ(½+it)|²(h/k)^{it} dt/(¼+t²).

Related: Auli–Bayad–Beck, Acta Arith. (2017), arXiv:1601.06839, reciprocity theorems for these sums. Link to the Estermann function E(s, r/b, α) = Σσ_α(n)e(nr/b)n^{−s}.

**Maier–Rassias, arXiv:1705.09921 and arXiv:1806.05070 (explicit version).** FACT.
- They estimate Σ_{Bk ≤ h < (1+η)Bk} μ(h)·g(h/k), where g(x) = Σ_l (1 − 2{lx})/l. This is exactly the h-sum of the NB cross terms at fixed k.
- The bound is O((ηBk)^{1−β}), a **power saving**, for k^{2δ} ≤ B ≤ k^D.
- Method: continued fractions, a Gauss-type map, the Wilton function, Fourier series with coefficients d(n)/n.
- They make **no claim** about d_N → 0. Only unbalanced ranges are covered, h ≫ k^{1+2δ}. The full quadratic form is not treated.

**ASSESSMENT: why this is the right door for the R10 gap.**
1. R10 shows that the fixed-p packet diagonal is of order log N (proved). The truth is ≈ 0.14/log N (DIAG). So the off-diagonal must **cancel the diagonal to relative accuracy 1/log²N**. A power-saving upper bound on the off-diagonal is not enough: the off-diagonal main term must equal −(diagonal) + O(1). That is an identity-level requirement.
2. The off-diagonal coefficients are Vasyunin/cotangent sums. Their exact reciprocity — a continued-fraction / Euclid recursion with an analytic period function plus a non-smooth correction — is the only known exact structure that couples different packets (h/k ↔ k/h ↔ h̄/k) with signs.
3. In this structure, integrality enters additively: modular inverses h̄ and continued fractions. Modularity enters through the GL2 Eisenstein period function. A DMV world has no such reciprocity. The plants v_b of R6 B change the archimedean factor, so they should break the exact form of the period function. Both are falsifiable predictions.
4. None of the killed classes covers this: it is not moment-only, not packet-separable, and not a universal frequency bound.

**Honest risks (ASSESSMENT).**
- All known estimates are for unbalanced ranges. The balanced range h ≈ k is the hard core.
- The non-smooth correction term in the reciprocity is exactly where the arithmetic hides. It may carry the full RH-strength difficulty.
- Bettin–Conrey–Farmer obtain the off-diagonal main term only conditionally (RH + H_{−1}).

## 4. Not used

- preprints.org 202506.0772: not peer reviewed; claims a rank-one collapse for a degenerate basis. Irrelevant to the (k mod n)/n dictionary.
- Darses–Hillion and Alouges–Darses–Hillion: probabilistic and generalised NB. Context only.

## 5. Proposal for Round 11 (owner decides)

Content for the owner, not a Proshka hint unless the owner authorises it as a "practical idea":
- Goal: prove RH.
- Input: R8–R10 plus the literature facts in §§1 and 3, as known results.
- Acceptance: the new object must give the off-diagonal **main term** of the true Möbius core on S exactly, up to O(1), not merely an upper bound. The R6 B plants, DMV and the R9 counterarray must fail at a named step of the reciprocity/period-function identity.

K6, to be registered before sending:
- new object with exact main term: 0.12;
- KILL of the reciprocity class with a named obstruction (e.g. the non-smooth correction term): 0.40;
- NO_PROGRESS: 0.40;
- RH: ≤ 0.01.
