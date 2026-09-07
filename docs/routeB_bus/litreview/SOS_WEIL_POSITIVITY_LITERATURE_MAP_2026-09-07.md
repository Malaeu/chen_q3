# Weil positivity as a sum of squares from primes + archimedean place — literature map
Compiled 2026-09-07. Question: has anyone written Weil's quadratic form `Q(f)` as a sum of squares built only from primes and the archimedean place, without the zeros? Who, what was proved, why it stopped. **[read]** = verified against a local PDF in `pdfs/` or a full-text extract; otherwise web-verified metadata only. No proof claim of ours is made here.

## 0. The criterion and the shape of the question
**Weil 1952/1972.** RH ⟺ the geometric (local) side of the explicit formula is ≤ 0 on `f = g*ḡ^♯`. Cited as Medd. Lunds Univ. Mat. Sem. 1952, 252–265; Izv. Akad. Nauk SSSR 36 (1972) 3–18. **Weil's own text unread** (bibliography cross-checked in Suzuki 2606.09096 [15,16], CCM 2511.22755 [16], Connes 2602.04022 [109,110]).

**Bombieri, Clay problem description (2000) [read].** The decisive framing. In char p positivity is *easy*: "In the geometric case of curves over a finite field, this negativity is a rather easy consequence of the algebraic index theorem for surfaces" — Severi 1906: the self-intersection form on degree-0 divisors is negative semidefinite. Over ℚ, verbatim: "Is there a general index theorem by which one can prove the classical Riemann hypothesis? We are here in the realm of conjectures and speculation."
→ The only *proved* SOS mechanism for Weil positivity anywhere is intersection-theoretic, not prime-by-prime. The number-field analogue is stated as unknown, not as impossible.

**Structural fact everyone below uses** (Connes–Consani 2020, eq. (2) **[read]**): on compactly supported `g` the geometric side "involves only finitely many primes". A finite-prime positive representation *is* a finite-window certificate; the whole fight is how the window scales.

## 1. Weil positivity and equivalents
- **Bombieri, "Remarks on Weil's quadratic functional…, I"**, Rend. Mat. Acc. Lincei s.9 v.11 (2000) 183–233 **[read]**. Thm 1: RH ⟺ `Σ_ρ ĝ(ρ)ĝ(1−ρ) > 0` for every `0 ≢ g ∈ C₀^∞((0,∞))`. §§4–13: variational equation, resolvent, eigenvalues of finite approximations, "sets of positivity", numerics. Unconditional: the finite-approximation apparatus + Thm 12 (§3 below). Not delivered: any window containing a prime.
- **Li 1997**, J. Number Theory 65, 325–333: RH ⟺ `λ_n = Σ_ρ[1−(1−1/ρ)^n] ≥ 0` ∀n.
- **Bombieri–Lagarias 1999**, J. Number Theory 77, 274–287: Li's criterion is a corollary of a general inequality for an *arbitrary* multiset of complex numbers, "not specific to zeta functions". Standing warning: a positivity criterion with no prime input in it cannot carry the arithmetic.

## 2. de Branges (1986–94) — the road that is closed
**Conrey & Li**, *A note on some positivity conditions related to zeta and L-functions*, arXiv:math/9812166 (3 Dec 1998), IMRN 2000 no.18, 929–940, communicated by Sarnak **[read, full text]**. Two conditions, each implying GRH, each refuted:
- **(3.1)**, `E(z)=ξ(1−iz)`: `⟨F(z),F(z+i)⟩_{H(E)} ≥ 0` for all `F∈H(E)` with `F(z+i)∈H(E)`. By de Branges' Thm 1 this forces `ℜ{Ē'(w)E(w+i)/2πi} ≥ 0` at zeros of `E`. At the **34th zeta zero** `ρ = 1/2 + i·111.0295355431696745…`: `ℜ[−ξ'(ρ)ξ(1+ρ)] = −5.389100507182945…×10⁻⁶⁹ < 0` (3.2). Condition fails.
- **(3.3)**, `W(z)=1/ξ(1−iz)`: fails since `ℜ[ξ(1+i282)/ξ(2+i282)] = −0.000131957 < 0` (3.4).
- Both failures reproduced for `L(s,χ₄)` ((3.7),(3.8)). Conclusion verbatim: "It is possible that these positivity conditions are too strong for Hilbert spaces of entire functions associated with the Riemann zeta function".
- **Sarnak's remark (p. 938) is the killer** — it removes the numerics. With `F(s)=ξ(s)/ξ(s+1)`, `ℑ log F(s) = ℑ log ζ(s) + O(1)`; since the values of `log ζ(s)` are dense in `1/2<ℜs<2` (Titchmarsh ch. XI), some `s₀` has `π/2 < ℑ log F(s₀) < π`, hence `ℜ{W(z₀)/W(z₀+i)} < 0`. Same for every `L(s,χ)`.
- **Why it stopped:** not a delicate near-miss. The condition is refuted by generic behaviour of `log ζ` off the line. No repair inside that class was proposed by anyone since.

## 3. Yoshida → Suzuki: how far unconditional positivity actually reaches
- **Yoshida 1992**, *On Hermitian forms attached to zeta functions*, Adv. Stud. Pure Math. 21, 281–325, DOI 10.2969/aspm/02110281 **[read]**. **Thm 1 (p.310):** for `a = (log 2)/2`, `(φ,φ) > 0` for all `φ ∈ K(a)`, equality iff `φ=0`. Method: positivity of an explicit **10×10** matrix `U` + tail bound (`C²=0.3321…`, `k ≥ 200`) — a finite computation. **Lemma 3 (p.288):** honest `L²` floor `(φ,φ) ≥ µ‖φ‖²_{L²}` on `K_N(a)` for `N` large; constants explicit, and `C₂(a) = #{(p,m) : m·log N(p) ≤ 2a}` **is literally the prime count inside the window**. Unconditional; stops exactly where `C₂` first becomes nonzero.
- **Bombieri 2000, Thm 12 (p.226) [read]:** `|I| < log 2` ⟹ `Σ_γ|F̂(γ)|² ≥ (log(1/|I|) − log log(1/|I|) − O(1))‖F‖²`. Proof opens by noting that for such support "the contribution of the sum involving Λ(n) vanishes". `O(1)` never made explicit → shape of a bound, no numerical threshold.
- **Suzuki 2023** (JLMS 108, arXiv:2206.03682) **[read]**: `g` is a Krein–Langer screw function ⟺ RH.
- **Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096 (8 Jun 2026, rev. 17 Aug 2026), 30 pp. [read].** Abstract: "a unified framework for understanding the results on the Weil quadratic form obtained by Yoshida (1992), Bombieri (2001, 2003), Connes–Consani (2023), and Connes–Consani–Moscovici (2025+)", all "obtained without assuming the Riemann Hypothesis". **Thm 1.4:** for small `a`, `λ_a = log(1/a) + µ₁ − log 2π + ψ(2) − 1 + O(a) > 0`, even eigenfunction — but the expansion is derived **for `0 < a < (1/2)log 2`**, the same wall; `µ₁ > 0` uncomputed, "sufficiently small" not digitized. **Thm 1.3:** `λ_a` continuous in `a` (unconditional). **Cor. 1.6 is a conjecture:** if `θ(a), φ(a,z)` exist with `lim_{a→∞} e^{φ(a,z)}W(a,θ;z) = z²ξ(1/2−iz)/ξ'(1/2−iz)` uniformly on compacts, then RH. Everything unconditional lives at small `a`; the `a→∞` limit is the open step.
- **Groskin, arXiv:2607.02828** (*A finite Guinand–Weil dictionary and archimedean tail order…*, 15 pp.): each real even Galerkin vector `v` yields in closed form a band-limited test function whose zero sum equals `⟨v,Qv⟩` exactly; beyond the band the omitted archimedean tail is a **totally positive Cauchy–Stieltjes increment**. **arXiv:2607.24830** — numerical realization of Suzuki's operator, "an operator form of Weil's positivity criterion". Reproducibility packages; no unconditional extension past the classical window.

## 4. Connes' program — is it a sum of squares? Yes, at one place only
- **Connes 1999**, Selecta Math. (N.S.) 5, 29–106: explicit formula as trace of the scaling action on the adele class space; RH ⟺ positivity of that trace.
- **Connes–Consani, *Weil positivity and trace formula, the archimedean place*, arXiv:2006.13771 (24 Jun 2020), Selecta Math. 27 (2021) Paper 77, DOI 10.1007/s00029-021-00689-4 [read].** This *is* the SOS move, made explicit: with `S` the Sonin projection (even functions vanishing together with their Fourier transform on `[−1,1]`), the functional `f ↦ Tr(ϑ(f)S)` is "positive definite by construction, since when evaluated on `f = g*g^*` it is the trace `Tr(ϑ(g)Sϑ(g)^*)` of a positive operator" — an honest `‖·‖²`.
  - **Thm 1:** `g ∈ C_c^∞` supported in `[2^{−1/2},2^{1/2}]`, `ĝ(i/2)=ĝ(0)=0` ⟹ `W_∞(g*g^*) ≥ Tr(ϑ(g)Sϑ(g)^*)`.
  - **Thm 6.11:** `W_∞(g*g^*) ≥ Tr(ϑ(g)Sϑ(g)^*) − c|ĝ(0)|²` with **`13 < c < 17`**.
  - Mechanism: archimedean term `= −2·Id + compact` (Thm 3.6); positivity bought by finite codimension; the gap between Weil distribution and Sonin trace controlled by prolate spheroidal wave functions + hermitian Toeplitz theory.
  - **Named obstruction, §2 verbatim:** "the obstruction to get Weil's positivity at the archimedean place is due to the specific contribution of the small square Δ".
  - **Scope, abstract verbatim:** "All the ingredients and tools used above make sense in the general semi-local case, where Weil positivity implies RH." — the prime-containing case is future work. Support `(1/2,2)`: **no prime inside**.
- **CCM, *Zeta zeros and prolate wave operators*, arXiv:2310.18423 (27 Oct 2023, rev. 4 May 2024) [read]:** semilocal prolate wave operator; spectral realization of low-lying zeros via the positive part of its spectrum and of their UV behaviour via the Sonin space.
- **CCM, *Zeta spectral triples*, arXiv:2511.22755 (27 Nov 2025) [read].** Thm 3.6: `A_λ` has discrete lower-bounded spectrum. Thm 5.10: **assuming** the lowest eigenvalue `ε_N` of `QW_λ^N` is simple with even eigenvector, `det_reg(D_log − z) = −iλ^{−iz}ξ̂(z)` and all zeros of `ξ̂` are real. Numerics: spectra converge to zeros of `ζ(1/2+is)`; "A rigorous proof of this convergence would establish the Riemann Hypothesis."
- **Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*, arXiv:2602.04022 (3 Feb 2026) [read].** Thm 6.1 (with van Suijlekom): a lower-bounded form whose spectral minimum is a simple isolated eigenvalue with even eigenfunction `η` ⟹ all zeros of `η̂` are real. Two open steps, verbatim: §6.6 "one needs to show that the smallest eigenvalue of the Weil quadratic form `QW_λ` is simple with even eigenvector"; and on the cutoff limit, "This is something which at this point is not proved." Letter p.25: "we have a firm grasp on your zeros, without at any point involving the infinity of the collection of all primes" — the program's own statement of what primes-only buys: the finite object, not the limit.

## 5. Compact-window certificates and the measured barrier
**Xuefeng Zhu, *Weil positivity in compact windows: a finite reduction, certified two-sided bounds, and a Landau–Widom decay law*, arXiv:2608.24827v2 (2 Sep 2026), 35 pp. [read; numerically cross-walked against our caches to 0.03 %].**
- Certified **unconditional** `Q(f) ≥ 8.9·10⁻¹⁸‖f‖²` for `supp f ⊆ [−0.8,0.8]`, i.e. `L = 0.8` against the classical `(log 2)/2 = 0.3466` — ≈2.3× further, with prime content `{2,3,4}` **inside** the window. Author's caveat (§6, p.14): the normalization dictionary against CCM [9] was "not carried out" line by line.
- **Landau–Widom decay law** (§1.3, Conj. 12.1): `−ln λ*(L) = C·N(T*)/ln N(T*)·(1+o(1))`, `C = 20.13… ≈ 2π²`, `T*(L) = 2πe^{2L}`; Rem. 12.2 — the constant "is read off the plateau and is not derived here". Mechanism: `f̂` of exponential type `L` has real-zero density ≤ `L/π`; the zero density of `ζ` exhausts that budget exactly at `T* = 2πe^{2L}`.
- **The barrier theorem — the sharpest explicit no-go found for this road** (§1, §16, verbatim):
  > "(Barrier for pointwise-envelope certificates.) Any application of Theorem 1.1 requires `T♯ > T₁(L) = 2πe^{A_L}`, and `A_L = (4+o(1))e^L` … hence the matrix size `N ≍ L T₁` and the number of quadrature nodes grow doubly exponentially in `L`. Moreover `sup_t` of the prime comb equals `A_L` exactly (Lemma 3.2), so within the class of certificates that bound the comb pointwise the threshold `T₁` cannot be lowered."
  > "Defeating positivity … is governed by `T* = 2πe^{2L}`, singly exponential … Certifying positivity through the geometric side is governed by `T₁ = 2πe^{(4+o(1))e^L}`, doubly exponential … The gap between `e^{2L}` and `e^{4e^L}` is the gap between knowing where the zeros are and proving that the primes cannot conspire. Closing it is an arithmetic problem."
- Note the quantifier: the no-go is **class-relative** — pointwise envelope bounds on the prime comb. It forbids nothing about a positive representation of a different type.

## 6. Explicit "local / finite-prime is not enough" statements in the literature
1. **Bombieri (Clay):** char p gets its SOS from the algebraic index theorem; over ℚ such an index theorem is "conjectures and speculation". Canonical no-go framing.
2. **Bombieri–Lagarias 1999:** Li-type positivity holds for arbitrary multisets — no arithmetic content by itself.
3. **Sarnak (in Conrey–Li):** de Branges positivity dies from density of the values of `log ζ` off the line — a global fact, not a computational accident.
4. **Connes–Consani 2020:** semi-local (prime-containing) case explicitly deferred; archimedean obstruction localized to the square Δ.
5. **Connes 2602.04022:** the finite-cutoff object is prime-finite by design; the convergence of its zeros to zeta's is "not proved" — the missing input is the *limit*, not the primes.
6. **Zhu 2608.24827 §16:** quantitative version — certifying is doubly exponential in the window; "the primes cannot conspire" named as the arithmetic content.
7. **Burnol**, C. R. Acad. Sci. Paris 331 (2000) 423–428, arXiv:math/0101068: local terms explained by the dilation-invariant conductor operator `log|x|_ν + log|y|_ν`; verbatim: "We also check Weil's positivity criterion under a support condition." Same barrier from the local-operator side. Also arXiv:math/9809119 (probabilistic reading of Weil positivity) and arXiv:math/9902080 (conductor operator, positive cuspidal spectrum at a finite place).
8. **Haran** (*The Mysteries of the Real Prime*, OUP 2001): all local terms in one identical form; explicit formula as an *additive* convolution. A uniformization of the local terms, not a positivity result.

## 7. SDP / SOS / LP certificates for explicit-formula positivity
- **Stark–Odlyzko–Serre–Poitou–Mestre positivity technique**, surveyed and extended in **S. D. Miller, *The highest lowest zero and other applications of positivity*, Duke Math. J. 112 (2002) 83–116, arXiv:math/0112196**: pick a test function positive on a range, evaluate the explicit formula, read off zero-location or non-existence. The oldest working tradition of finite-prime positive certificates — but aimed at discriminant/lowest-zero bounds, never at RH.
- **Chirre, Gonçalves, de Laat**, *Pair correlation estimates for the zeros of the zeta function via semidefinite programming*, arXiv:1810.08843, Adv. Math. 361 (2020) 106926: a genuine SDP over the Montgomery pair-correlation/explicit-formula setup (proportion of distinct zeros, small gaps, multiplicity sums). "Assuming RH, improve constants" — not an attack on positivity itself.
- **Cohn–Elkies-class LP transplanted to zeta:** Carneiro–Chirre–Milinovich, arXiv:1710.10362 (Publ. Mat. 63 (2019) 601–661), arXiv:2310.01913, arXiv:2411.05095. Extremal Fourier problems over the explicit formula, used for bounds; no Weil-SOS.
- **Zhu 2608.24827** is, as far as this sweep found, the **only** paper running a certified finite-dimensional positivity program directly on the Weil form with primes inside the window (interval arithmetic, Legendre/sine Galerkin bases, hashes).
- **Not found:** any Positivstellensatz/SOS-modulo-ideal formulation of `Q(f) ≥ 0`; any SDP whose feasible point would be a Weil certificate valid for all windows; any "designer zeta" LP dual.

## Synthesis
1. The road is **open, not dead** — but every published attempt at a *pure* SOS either died (de Branges) or stalled at a wall whose position is now measured.
2. The only proved SOS mechanism for Weil positivity anywhere is char p / Severi's index theorem; Bombieri states in the Clay text that the number-field analogue is unknown.
3. de Branges' route is cleanly closed: Conrey–Li give explicit failures, Sarnak shows the failure is generic in `log ζ`, not numerical bad luck.
4. Connes–Consani 2020 **is** a sum-of-squares construction — `Tr(ϑ(g)Sϑ(g)^*)`, positive by construction — proved unconditionally, but only at the archimedean place, on a window containing **no prime**, and only up to a rank-one defect `c|ĝ(0)|²`, `13<c<17`.
5. Yoshida 1992 and Bombieri Thm 12 are the same window from two sides: positivity is unconditional exactly where the `Λ(n)` sum is empty, `L ≤ log 2`.
6. Suzuki 2606.09096 unifies all four lines through the screw function, unconditionally, and hands the entire difficulty to one conjectural `a → ∞` limit (Cor. 1.6).
7. Zhu 2608.24827 is the first certified crossing of the log 2 wall (`L = 0.8`, primes `{2,3,4}` inside) and simultaneously the first paper to *price* the road: singly exponential to defeat positivity, doubly exponential to certify it, the gap named as an arithmetic problem about the primes.
8. Nothing in the literature proves a finite-prime positive representation cannot reach RH. The one sharp no-go (Zhu §16) is class-relative: it kills pointwise-envelope certificates only.
9. **Equivalence to Hilbert–Pólya: not established.** Connes 2602.04022 Thm 6.1 and CCM 2511.22755 Thm 5.10 give one direction *under a hypothesis* (simple + even lowest eigenvalue ⟹ self-adjoint operator whose real spectrum is the zero set of `ξ̂`). Bombieri–Lagarias warns from the other side that zero-multiset positivity carries no arithmetic. SOS-from-primes and Hilbert–Pólya are linked by the simple-even hypothesis, not by a theorem.
10. **Where our own objects sit.** A pole-gauged positive Fourier extension on a fixed two-lobe class is the same species as Connes–Consani's `−2·Id + compact` plus finite codimension (Thm 3.6 + Cor. 3.8) and as Yoshida's Lemma 3 (`L²` floor after killing `N` moments): positivity bought by removing finitely many linear conditions on a fixed window. What would be new relative to all of the above is (a) a floor that does **not** degrade as the window swallows primes — i.e. not of the shape `log(1/a) − C₂(a)` — and (b) an error term that is **not** a pointwise envelope on the prime comb, the only class Zhu's barrier forecloses. A direct energy/moment theorem is closest to Yoshida's `C₁(a)`/`C₂(a)` accounting and to Groskin's "archimedean tail is a totally positive Cauchy–Stieltjes increment" (2607.02828). The discriminating novelty question is whether the moment identity survives **with prime terms inside the window**, since every published unconditional statement of this shape holds only where they are absent.

## References
- Bombieri, E. *Problems of the Millennium: the Riemann Hypothesis*. Clay Mathematics Institute, 2000.
- Bombieri, E. *Remarks on Weil's quadratic functional in the theory of prime numbers, I*. Rend. Mat. Acc. Lincei s.9 v.11 (2000) 183–233. eudml.org/doc/252338
- Bombieri, E., Lagarias, J. C. *Complements to Li's criterion for the Riemann hypothesis*. J. Number Theory 77 (1999) 274–287.
- Burnol, J.-F. *The explicit formula and a propagator*. arXiv:math/9809119.
- Burnol, J.-F. *The explicit formula and the conductor operator*. arXiv:math/9902080.
- Burnol, J.-F. *Sur les formules explicites I: analyse invariante*. C. R. Acad. Sci. Paris 331 (2000) 423–428. arXiv:math/0101068.
- Carneiro, E., Chirre, A., Milinovich, M. B. *Bandlimited approximations and estimates for the Riemann zeta-function*. Publ. Mat. 63 (2019) 601–661. arXiv:1710.10362.
- Carneiro, E., Chirre, A., Milinovich, M. B. *Fourier optimization and Montgomery's pair correlation conjecture*. arXiv:2310.01913; *…and consequences of the GRH*. arXiv:2411.05095.
- Chirre, A., Gonçalves, F., de Laat, D. *Pair correlation estimates for the zeros of the zeta function via semidefinite programming*. Adv. Math. 361 (2020) 106926. arXiv:1810.08843.
- Connes, A. *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*. Selecta Math. (N.S.) 5 (1999) 29–106.
- Connes, A., Consani, C. *Weil positivity and trace formula, the archimedean place*. Selecta Math. 27 (2021) Paper 77. arXiv:2006.13771. DOI 10.1007/s00029-021-00689-4
- Connes, A., Consani, C., Moscovici, H. *Zeta zeros and prolate wave operators*. arXiv:2310.18423.
- Connes, A., Consani, C., Moscovici, H. *Zeta spectral triples*. arXiv:2511.22755.
- Connes, A. *The Riemann Hypothesis: Past, Present and a Letter Through Time*. arXiv:2602.04022.
- Conrey, J. B., Li, X.-J. *A note on some positivity conditions related to zeta and L-functions*. IMRN 2000 no. 18, 929–940. arXiv:math/9812166.
- Groskin, A. *A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form*. arXiv:2607.02828.
- Groskin, A. *A numerical realization of Suzuki's Weil-quadratic-form operator*. arXiv:2607.24830.
- Haran, M. J. Sh. *The Mysteries of the Real Prime*. LMS Monographs 25, OUP, 2001.
- Li, X.-J. *The positivity of a sequence of numbers and the Riemann hypothesis*. J. Number Theory 65 (1997) 325–333.
- Miller, S. D. *The highest lowest zero and other applications of positivity*. Duke Math. J. 112 (2002) 83–116. arXiv:math/0112196.
- Suzuki, M. *Aspects of the screw function corresponding to the Riemann zeta-function*. J. London Math. Soc. 108 (2023). arXiv:2206.03682. DOI 10.1112/jlms.12785
- Suzuki, M. *Weil's quadratic form via the screw function*. arXiv:2606.09096.
- Weil, A. *Sur les "formules explicites" de la théorie des nombres premiers*. Medd. Lunds Univ. Mat. Sem. 1952, 252–265; Izv. Akad. Nauk SSSR 36 (1972) 3–18. **[bibliography verified, text unread]**
- Yoshida, H. *On Hermitian forms attached to zeta functions*. Adv. Stud. Pure Math. 21 (1992) 281–325. DOI 10.2969/aspm/02110281
- Zhu, X. *Weil positivity in compact windows: a finite reduction, certified two-sided bounds, and a Landau–Widom decay law*. arXiv:2608.24827.
