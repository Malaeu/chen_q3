# Groskin, Truncated Weil Form (arXiv:2605.20224) — verified usage cards

Source PDF: pdfs/2605.20224.pdf

Full title: Akiva Groskin, "High-Precision Approximation of Riemann Zeros via the
Truncated Weil Form", arXiv:2605.20224v2, dated May 2026 (v2 stamp 26 Jun 2026).
MSC 2020: 11M26 (primary), 65F15, 65N25 (secondary).

CRITICAL FRAMING (read before using any card below): this is an **experimental-mathematics /
numerical** paper. It states explicitly and repeatedly that it proves nothing. Its own §10
non-claim: *"No part of this paper constitutes a proof of anything. This is experimental
mathematics in the literal sense."* Every genuinely-theorem-level statement it relies on is
**cited from Connes–van Suijlekom [9] or Connes–Consani–Moscovici [8]**, not proved here. Do
NOT read any card below as a Q3 wall closure.

---

## 1. Truncated Weil quadratic form — definition — §2.1 (p.4), eq. (1)–(2); Galerkin matrix §2.2 (p.4), eq. (3)–(4)

VERBATIM (§2.1, p.4): "For a cutoff parameter c (controlling the primes p ≤ c in the prime-sum
piece below; c itself need not be prime, as in our c = 14 and c = 100 cells), set L = log c. The
quadratic form acts on L²([0, L]) and decomposes as
    D = D_∞ + D_pole + D_prime,                                                   (1)
where D_∞ is the archimedean contribution, D_pole is the pole contribution from the zeta
function, and D_prime sums over primes p ≤ c."

VERBATIM (§2.1, p.4, eq. 2 — archimedean Mellin multiplier): "h_+(τ) = − log π + Re Ψ(1/4 +
iτ/2), where Ψ denotes the digamma function. This follows from Connes–Consani [5] (Equation 153)
…"

VERBATIM (§2.2, p.4 — the Galerkin realization actually implemented): "Connes–van Suijlekom
Proposition 4.1 defines a function ψ: ℤ → ℝ via
    ψ(x) = (1/π) ∫₀ᴸ sin(2πx(1 − y/L)) D(y) dy,                                   (3)
and the Galerkin matrix entries
    q_{m,n} = (ψ(m) − ψ(n))/(m − n),    q_{n,n} = ψ′(n).                          (4)
The basis is the complex Fourier system {U_n(x) = L^{−1/2} exp(2πinx/L)}_{n∈ℤ} … The even-sector
projection under the involution y ↦ L − y is described in Section 3.4; only that sector is
diagonalized."

K7-TAG: CONVENTION (definition/setup, following CvS [9] and Connes–Consani [5]).
MAPS TO Q3 WALL: H2b (this is the finite/truncated object whose Fourier–Mellin transform is
studied) and the underlying object for H2a. The interval is **L²([0, L]) with L = log c**, NOT
"[0, log c]" as a function space of the eigenvector directly — note the eigenvector lives on the
(2N+1)-dim Fourier truncation E_N of this space.
PROVED-OR-OPEN: This is a definition, not a claim to prove. It is a re-implementation of the
Connes–van Suijlekom Proposition 4.1 Galerkin matrix; the paper claims (its contribution #1) to
be the first public implementation of it. Definition is faithfully transcribed, not derived.

---

## 2. Unique even-sector ground state (→ H2a SIMPLE_EVEN) — Introduction (p.2) + Remark 2.1 (p.5) + footnote 1 (p.5)

VERBATIM (Introduction, p.2, stating the SETUP, attributed to Connes 2026 §6): "for each value of
a cutoff parameter c … the truncated Weil quadratic form on L²([0, log c]) admits a unique
even-sector ground state whose Fourier–Mellin zeros provably lie on the critical line."

VERBATIM (Remark 2.1, p.5 — the paper's OWN status statement, this is the load-bearing caveat):
"Connes–Consani–Moscovici Theorem 1.1 takes its starting point as ε_N, the smallest eigenvalue of
QW_λ^N, **assumed simple and with even eigenvector.** At the cutoffs c ≤ 67 studied in Section 5,
the finite-N Galerkin matrix Q_c^even is observed positive on every cell at N = 100, its smallest
eigenvalue is numerically simple and coincides with its smallest-positive eigenvalue, and the
corresponding eigenvector projects predominantly onto the even sector — so the finite-dimensional
data are **consistent with the Connes–Consani–Moscovici Theorem 1.1 ground-state hypotheses (as
numerical conditions, not as analytically established hypotheses of the continuum theorem).**"

VERBATIM (footnote 1, p.5): "At c ≤ 67 with N = 100 the matrix is observed positive on every cell,
so the smallest eigenvalue coincides with the smallest-positive one and our ξ_N coincides with
the Connes–Consani–Moscovici Theorem 1.1 ground state …" — and (§2.4 body, p.5): the object used
is "the empirically distinguished smallest-positive eigenvector of the finite-N even-sector matrix
Q_c^even(c, N) — **a selection criterion, not a theorem-derived ground-state identification.**"

K7-TAG: NUMERICAL (the simplicity + evenness is *observed*, not proved; the theorem that would
supply it, CCM Thm 1.1, is *cited* and *assumes* it as a hypothesis).
MAPS TO Q3 WALL: H2a SIMPLE_EVEN — directly the same statement (smallest eigenvalue simple, even
eigenvector).
PROVED-OR-OPEN: **OPEN / ASSUMED.** This paper does NOT prove simplicity or evenness of the ground
state. It (a) cites CCM Theorem 1.1 which *assumes* "ε_N simple and even" as a hypothesis, and (b)
verifies numerically that the finite-N matrix is consistent with it. Simplicity/evenness is a
selection criterion + numerical observation here, explicitly "not a theorem-derived
identification." Cannot be used to close H2a.

---

## 3. Ground-state Fourier–Mellin zeros lie on the critical line (→ H2b) — Introduction (p.2) + §9.2 (p.33)

VERBATIM (Introduction, p.2): "The criticality statement is a theorem. Connes–van Suijlekom [9]
establish (Theorem 6.1) that the zeros of η̂_c are real for every finite c, so the open question
is specifically about convergence, not about criticality. If the convergence holds, RH follows by
Hurwitz's theorem applied to the Mellin transforms — but the convergence itself is unproven."

VERBATIM (§9.2, p.33): "Connes–van Suijlekom [9] provide the mathematical foundation: Theorem 6.1
establishes that the zeros of η̂_c lie on the critical line for every finite c. The Galerkin
matrix q_{m,n} of Proposition 4.1 is the object we implement."

K7-TAG: THEOREM — but a **CITED** theorem (Connes–van Suijlekom [9], Theorem 6.1), NOT proved in
this paper.
MAPS TO Q3 WALL: H2b real-zero bridge — exactly matches ("finite/truncated object whose
Fourier–Mellin transform has all zeros on the critical line"). Note the paper's phrasing: "zeros
of η̂_c are real" ≡ "lie on the critical line" under its Mellin/duality convention (§2.4).
PROVED-OR-OPEN: **PROVED — but ELSEWHERE (Connes–van Suijlekom [9] Thm 6.1), not in Groskin.**
Groskin only cites and numerically exercises it. For Q3/H2b the value of this card is the pointer
to CvS Theorem 6.1 as the primary source; Groskin is a secondary/numerical witness, not a proof
source. Verify the CvS Theorem 6.1 statement against reference [9] directly before any H2b use.

---

## 4. c → ∞ convergence (zeros → Riemann zeros) (→ C3-B) — Abstract (p.1) + Introduction (p.2) + §8.9 (p.32) + §10 (p.35)

VERBATIM (Abstract, p.1): "The Connes–van Suijlekom truncated Weil quadratic form, indexed by a
cutoff parameter c … produces a ground state whose Fourier–Mellin zeros provably lie on the
critical line; **whether they converge to the Riemann zeros as c → ∞ is open** (Connes 2026;
Connes–Consani–Moscovici 2025)."

VERBATIM (Introduction, p.2): "Do these zeros converge to the actual Riemann zeros as c → ∞? …
the open question is specifically about convergence, not about criticality. … the convergence
itself is unproven."

VERBATIM (§8.9, p.32, "Two interpretations"): "1. Finite limit. If α remains above 1, the
first-zero error converges to a nonzero value (∼ 10^{−274}). The CvS operator would converge to a
function whose first zero is extremely close to, but not exactly at, γ₁. 2. Exponent drift. The
exponent α = 1.48 is measured over only c ∈ [31, 67]. At larger cutoffs, α could decrease below 1,
in which case the series diverges and |γ₁ error| → 0 (full convergence). With 15 data points,
these scenarios cannot be distinguished."

VERBATIM (§10 non-claims, p.35): "We do not claim any progress on RH. The Connes–van Suijlekom
framework's Hurwitz-type convergence argument is a conjecture. We compute some numbers in the
neighborhood of that conjecture without bearing on its truth."

K7-TAG: CONJECTURE / NUMERICAL. The convergence is an open conjecture; the paper supplies only
numerical extrapolation (Aitken-Δ², power-law fits) that it explicitly refuses to elevate to a
proof or even a statistical test.
MAPS TO Q3 WALL: C3-B ground→trial ("the main approximation wall": finite-object zeros → actual
Riemann zeros as cutoff → ∞).
PROVED-OR-OPEN: **OPEN — numerically-supported-only, and even the numerics are two-way ambiguous**
(finite-limit vs full-convergence "cannot be distinguished" on the available 15 points). This is
the paper's central open question. Provides NO closure and NO decisive numerical direction for
C3-B; if anything it flags that the finite-N power law is an *upper-bound-from-above* sequence
(§6.7), a caution for any C3-B numerical argument.

---

## 5. Fuchs prolate eigenvalue theorem / PSWF machinery — §6.4 (p.16) + §9.5 (p.34)

VERBATIM (§6.4 discussion, p.16): "Connes 2026 §6.4 itself is a heuristic statement based on the
empirical agreement (their Figure 1) between 1 − χ₂(λ) and ε(λ) for λ ≤ 14; the prefactor
(2^14/3)√2 π^5 is derived from **Fuchs's prolate-spheroidal eigenvalue theorem and is therefore
rigorous**, while the identification of ε with 1 − χ₂ at large λ is the heuristic step."

VERBATIM (§9.5, p.34): "Connes–Consani–Moscovici [7] introduce the prolate wave operator, which
appears in the Connes-program framework as the approximation construction for the limit k_λ
(Connes 2026 [4] §6.3–§6.4 and the 'educated guess' of Connes–Consani–Moscovici [8] §7). The
Connes–Consani–Moscovici 2025 Galerkin computations themselves use the trigonometric basis, as is
evident from Connes–Consani–Moscovici [8] Lemma 5.1."

K7-TAG: THEOREM (Fuchs's prolate-spheroidal eigenvalue theorem, cited as rigorous) — but used only
to supply the *prefactor constant* inside a Connes-2026 *heuristic* asymptotic. The prolate wave
operator (CCM [7]) is named as the continuum-limit construction, not used computationally here
(the actual computation uses the trigonometric/Fourier basis, not a PSWF basis).
MAPS TO Q3 WALL: other — relevant to C3-B convergence-rate heuristics only (the continuum
asymptotic of the ground-state eigenvalue), not to STEP34/H2a/H2b directly. Flags that a
prolate-basis (Slepian/PSWF) implementation is a *distinct, unrealized* path (see §4.3, p.8: "A
prolate-basis implementation of the CvS Galerkin would be a genuinely distinct path in the
literature … but is not yet reported by any group").
PROVED-OR-OPEN: The Fuchs theorem itself is rigorous (cited). Its *use* here is inside a heuristic
whose key identification step is explicitly non-rigorous. No PSWF computation is performed in this
paper.

---

## 6. Archimedean / Guinand–Weil (explicit-formula) dictionary (→ STEP34) — §2.1 eq.(1)–(2) (p.4) + §2.5 (p.6); §9.1/§9.4

VERBATIM (§2.5, p.6 — the three-piece decomposition = the Weil explicit-formula split): "The
integral defining ψ(x) decomposes into three pieces corresponding to the three terms of D: 1.
**Archimedean piece (D_∞):** involves the Mellin-multiplier integral ∫₀ᵀ h_+(τ) K(x, τ) dτ where K
is a trigonometric kernel. This piece admits a closed-form expression for the − log π component
and requires numerical quadrature for the digamma component. 2. **Pole piece (D_pole):** a
rank-one correction arising from the simple pole of ζ(s) at s = 1. 3. **Prime piece (D_prime):** a
finite sum over primes p ≤ c involving log p and the von Mangoldt-type kernel."

VERBATIM (§9.1, p.33): "The present work sits within the specific thread initiated by Connes' 2026
paper [4], which revisits the connection between the Weil explicit formula and the spectral action
principle."

VERBATIM (§9.4, p.34): "Connes–Consani [5] provide the explicit formula for the archimedean Mellin
multiplier h_+(τ) used in our implementation."

K7-TAG: CONVENTION (the Guinand–Weil / explicit-formula decomposition of the Weil quadratic form
into archimedean + pole + prime pieces).
MAPS TO Q3 WALL: STEP34 / Arch−prime wall — **PARTIAL MATCH ONLY.** The paper supplies the same
structural ingredients STEP34 lives in: the archimedean piece D_∞ (with multiplier h_+(τ) = −log π
+ Re Ψ(1/4 + iτ/2)) and the prime piece D_prime (finite sum over p ≤ c of log p × von-Mangoldt
kernel). This is the Weil-explicit-formula dictionary STEP34 needs.
PROVED-OR-OPEN: The **domination inequality itself (P_prime ⪯ A_arch, prime measure dominated by
archimedean square-energy on a square/autocorrelation class) is NOT FOUND in this paper.** Groskin
gives the additive decomposition D = D_∞ + D_pole + D_prime and studies positivity of the *total*
even-sector form numerically, but states NO inequality bounding the prime piece by the archimedean
piece. Note also (§6.6, §8.10) that the paper reports the even-sector matrix's finite-cutoff
*negative* blocks are archimedean-truncation (finite-T) artifacts that vanish as T → ∞ — i.e. its
positivity discussion is about the assembled operator, not an arch-dominates-prime bound. For
STEP34 the usable content is the decomposition + the exact archimedean multiplier; the actual
STEP34 inequality has no counterpart here.

---

## Summary

Items found VERBATIM: **6 of 6** (each of the six requested targets has an exact quoted location;
item 6's *domination inequality* sub-target is a verified NOT FOUND).

- **Even-sector ground state simple/even (H2a SIMPLE_EVEN):** **OPEN / ASSUMED in this paper.**
  Numerically observed; the enabling theorem (CCM Thm 1.1) is cited and *assumes* it as a
  hypothesis; the paper calls its own object "a selection criterion, not a theorem-derived
  ground-state identification" (Remark 2.1).
- **Critical-line zeros of the truncated object (H2b):** **PROVED — but by Connes–van Suijlekom
  [9] Theorem 6.1 (cited), NOT proved in Groskin.** Groskin is a numerical witness only. Use CvS
  [9] Thm 6.1 as the primary source and verify it directly.
- **c → ∞ convergence to Riemann zeros (C3-B):** **OPEN**, explicitly a conjecture; numerically
  supported only, and the numerics are two-way ambiguous (finite-limit ∼10⁻²⁷⁴ vs full
  convergence "cannot be distinguished").
- **Fuchs / PSWF (item 5):** Fuchs prolate theorem cited as rigorous but used only for a prefactor
  inside a Connes-2026 heuristic; no PSWF computation performed (trigonometric basis used
  throughout); prolate-basis path noted as unrealized.
- **STEP34 arch−prime (item 6):** decomposition + exact archimedean multiplier present; the
  prime-dominated-by-archimedean **inequality is NOT FOUND**.

No Q3 wall is closed by this paper. Its own §10: "No part of this paper constitutes a proof of
anything."

File: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/GROSKIN_TWF_USAGE_CARDS.md
