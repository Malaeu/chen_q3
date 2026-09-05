# NOVELTY PASS — claims A–E of WALL_OBJECT_CARD_2026-09-03
Read-only pass, 2026-09-05. Every locator below was seen in downloaded full text (PDFs in this folder).
Nothing here is from memory; there are no [MEMORY, UNVERIFIED] items.

## Sources actually opened (full text, not abstracts)
arXiv:2006.13771 Connes–Consani *Weil positivity and Trace formula, the archimedean place* · arXiv:2112.05500
Connes–Moscovici *Prolate spheroidal operator and zeta* · **arXiv:2511.22755 Connes–Consani–Moscovici *Zeta
Spectral Triples* (27.11.2025, 32 pp)** · arXiv:2301.00421v3 Suzuki *On the Hilbert space derived from the Weil
distribution* · arXiv:2404.13427 Xian-Jin Li · **Bombieri 2000, full 53 pp — open at
`http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0&fmt=pdf`, not paywalled** · **arXiv:2606.09096v2 Suzuki,
*Weil's quadratic form via the screw function* (Aug 2026) — found by search, decisive** · arXiv:2602.04022
Connes, *RH: Past, Present and a Letter Through Time* (Feb 2026) · arXiv:2606.29555 Freedman (Jun 2026,
102 pp) · arXiv:2605.20224 + arXiv:2607.02828 Groskin · arXiv:2607.24830 VIDRAFT (math.GM).

**Quality flag.** The last four are 2026 preprints of an emerging cluster around the CCM truncation
(2607.24830 is math.GM from an "AI Research" group with an `arxigpt@gmail.com` contact; 2606.29555 is an
independent researcher, 102 pp of numerics). They are *prior art in print* — a referee will find them — but
they are unrefereed and must be cited as preprints, not leaned on.

## (A) Canonical test f₀ = Φ/‖Φ‖, Φ(x)=4e^{x/2}Σₙh(neˣ), FΦ = Ξ, f₀ in the radical

**KNOWN — the function and its Fourier property.** CCM 2025, arXiv:2511.22755, §7 "Outlook", eq. (7.1)–(7.2)
and **Lemma 7.1**:

> `k(u) = E(h)(u), h(u) = (π/2)u²(2πu² − 3)e^{−πu²}` (7.1); `E(f)(u) := u^{1/2} Σ_{n≥1} f(nu)` (7.2)
> "**Lemma 7.1.** The Ξ function of Riemann is the Fourier transform of k = E(h) where h is, up to a
> multiplicative scalar, the only linear combination of h₀, h₄ with vanishing integral."

`(π/2)u²(2πu²−3) = π²u⁴ − (3/2)πu²` — h is **identical** to ours, not merely proportional. CCM attribute the
object to Riemann himself ([10] = Riemann 1859) — "when reading Riemann's paper one finds that … he
understood his Ξ-function as the Fourier transform … of the function (7.1)". CCM also give the
Hermite-function characterisation `h = (3/2^{11/4})h₄ − (3/2^{17/4})h₀`, (7.4).

**KNOWN — the "factor 4 / log-variable" repair.** Freedman, arXiv:2606.29555, eq. (1), p. 3:
`Φ(x) = Σ_{n≥1} 2(2π²n⁴e^{9x/2} − 3πn²e^{5x/2})e^{−πn²e^{2x}}`, x ≥ 0, extended evenly, with
`ξ(½+iz) = ∫Φ(t)e^{izt}dt` — our `4e^{x/2}h(neˣ)` expanded, term by term. Verified **independently by
computation** (mpmath, 40 dps): the two Φ agree to 20 digits at x = 0.3, 1.0; Φ is even to 20 digits;
`2∫₀^∞Φ(t)cos(zt)dt = ξ(½+iz)` to 15 digits at z = 0, 1, 2.5 and at the first zero z = 14.134725 (both
sides 1.9598e−10). The scale is right and it is *not* new: CCM (7.1)+(7.2) in x = log u, already in print.

**PARTIALLY KNOWN — f₀ as a null vector.** The *finite* picture is CCM's whole method: 2511.22755 §5.2
assumes `T ≥ 0` with `Ker T = Cξ` one-dimensional (Def. 5.3 "even-simple", Lemma 5.4, "the Hilbert space H
… is the quotient of E_N by the radical Ker T = Cξ"), and (7.6) proposes `k_λ = E(h_λ)` as the "educated
guess" for ξ_λ — i.e. our f₀ is precisely the λ→∞ limit of their radical vector. They say plainly:
"Justifying rigorously this step is the main remaining obstacle to our approach to RH."

**NOT FOUND — the infinite-dimensional radical.** Nobody writes: *all* translates U_q f₀ and *all*
convolutions f₀∗h lie in the radical, on the canonical (non-compactly-supported) class. Print points the
other way, and must be cited as the reason the enlarged test class is needed:
- **Suzuki 2301.00421**, §1: under RH the Weil form is positive *definite* on C_c^∞(ℝ) — "W(ψ∗ψ̃) > 0 for
  every nonzero ψ ∈ C_c^∞(ℝ)"; his Hermitian form (1.2) is `⟨ψ₁,ψ₂⟩_W = Σ_γ m_γ ψ̂₁(−γ)(ψ̂₂)^♯(−γ)`, from
  which "radical = {ψ̂ vanishes on all γ}" is one line, but he never exhibits an element.
- **Bombieri 2000, §8 Lemma 10 (p. 209)**: "The matrix H(Γ;t) admits the eigenvalue 0 if and only if there
  is γ ∈ Γ with multiplicity greater than 1, in which case the multiplicity of 0 … is exactly Σ*[m(γ)−1]."
  (Same for the second problem, p. 210.) So every finite truncation is non-degenerate for simple zeros.
- Bombieri, Introduction, alternative (iii): "The question of linear independence which arises in (iii) is of
  some interest and, although probably quite difficult, deserves study" — linear independence of `{x^{−ρ}}` on
  an interval is his open question; (C)'s proof uses the analogous independence of translates. **Cite him.**

*Verdict:* test function and FΦ = Ξ are **KNOWN** (Riemann → CCM 2025 Lemma 7.1; log-form in Freedman 2026).
Only the infinite-dimensional translated radical is **NOT FOUND** — a short argument: a lemma, not a headline.

## (B) Ground-state representation with the signed measure dν = b(t)dt + Σ(Λ(n)/√n)δ_{log n}

**KNOWN — the signed-measure form of the Weil quadratic form.** Suzuki, arXiv:2606.09096, **§2.5
"Distributional formulas", eq. (2.9)–(2.11)**:

> `Q_W^a(v) = ∬ g(x−y)v′(y)v′(x) dx dy = ∬ (−g″(x−y))v(y)v(x) dx dy`  (2.9)
> `−g″(t) = −½ Pf(1/|t|) − (2A+1)δ(t) − Σ_n (Λ(n)/√n)[δ(t−log n) + δ(t+log n)] − r″(t)`

with the screw function given in closed form at (1.3):
`g(t) = −4(e^{t/2}+e^{−t/2}−2) + Σ_{n≤exp|t|}(Λ(n)/√n)(|t|−log n) − (|t|/2)(ψ(¼)−log π) − ¼(Φ(1,2,¼) − e^{−|t|/2}Φ(e^{−2|t|},2,¼))`.
Suzuki adds: "This was already observed in [13, Section 3.5]" (= Suzuki 2301.00421) and "(2.10) provides an
alternative representation of **Bombieri's Lagrangian** ([1, Lemma 1], [2, Sections 5–6])".

So the prime atoms `Σ(Λ(n)/√n)δ_{log n}`, the archimedean density with its `½·1/|t|` singularity, and the
*signed* kernel acting on **differences** — all in print, twice.

**KNOWN — the conditional-positivity / Lévy–Khintchine framing.** Suzuki 2606.09096, §1: "A function g on ℝ
satisfying g(t)=g(−t) is called a **screw function** … if the kernel `g(t−u) − g(t) − g(−u) + g(0)` is
nonnegative … the above function g is a screw function in the sense of **Krein–Langer** [8, §5] **if and only
if RH holds**" — this *is* the conditionally-positive-definite statement, and Suzuki 2301.00421 eq. (2.3)
gives the Lévy–Khintchine integral representation
`g(t) = g(0) + ibt + ∫(e^{iλt} − 1 − iλt/(1+λ²))dτ(λ)/λ²`. Our "RH ⟺ ν-form ≥ 0" is this criterion.

**NOT FOUND — the ground-state substitution g = f₀·s.** No paper I read performs the Doob / Frank–Seiringer
substitution that converts the form into `½∬ f₀(x)f₀(x′)ν(|x−x′|)|s(x)−s(x′)|²`. Suzuki's differences come
from `D = i d/dx` (his (1.6) `B_a = D*G_aD`), i.e. from a *derivative*, not from a zero mode. Replacing D by
multiplication-by-f₀ is the genuinely new move, and it is exactly the nonlinear/nonlocal ground-state
representation of **Frank–Seiringer, arXiv:0803.0503, JFA 255 (2008) 3407–3430** (verified: "we develop a
non-linear and non-local version of the ground state representation, which even yields a remainder term").

**NOT FOUND — b(t) = e^{−5t/2}/(1−e^{−2t}) − e^{t/2} and the plastic-number threshold.** No hit anywhere,
including a targeted search on "plastic number"/1.324718 with zeta and the explicit formula. `b(t)=0 ⟺
y³=y+1`, y=eᵗ; consistent with Suzuki's `−½Pf(1/|t|)` since `e^{−t/2}/(e^{2t}−1) ~ 1/(2t)` as t↓0. Present
b(t) as an elementary evaluation of a known density, the plastic number as the new observation.

## (C) Obstruction: no nonnegative finite-stencil minorant

**NOT FOUND.** Searched: full text of all eleven sources for `radical / stencil / minorant / sum of squares /
translate`; WebSearch for "Weil positivity obstruction sum of squares certificate impossible". What exists:

- **Connes 2602.04022, §7.2, Theorem 7.1**: `W_∞(g∗g*) ≥ Tr(ϑ(g)Sϑ(g)*)` for g supported in
  `[2^{−1/2}, 2^{1/2}]` with Fourier transform vanishing at 2i and 0 — a *nonlocal* positive minorant via the
  Sonin projection S. This is the closest thing in the literature to what (C) forbids, and it survives (C)
  because the Sonin projection is not a finite stencil. **Our theorem should be stated against it**: it says
  the CC archimedean minorant cannot be localised.
- **Freedman 2606.29555, §8** lists rejected routes — 8.1 layerwise local source positivity (indefinite), 8.2
  finite-core Hermite–Biehler counterexample near z ≈ 70+0.885i, 8.3 "generic smooth-even positivity is false",
  8.5 finite anti-Loewner index, §4 anti-Wick. All are *numerical counterexamples for other constructions*;
  none is a theorem that every nonnegative finite-stencil minorant vanishes, none uses the translated radical.
- Bombieri's linear-independence question (above) is the classical ancestor of the mechanism, not the result.

*Verdict:* **(C) is the strongest new claim.** No prior no-certificate theorem of this shape found.

## (D) Margin–density tradeoff; absolute Schur-type bounds fail

**NOT FOUND.** Searched full text of all eleven sources for `Schur / margin / dense family / uniform bound`,
plus a WebSearch pairing Schur test / signed Laplacian with Weil positivity and dense test families. The
literature has only the positive-direction difficulty (densification needs explicit uniform bounds), never a
proof that density and a uniform margin are incompatible. Nothing to cite for priority; cite Bombieri §4
(existence of the minimiser in the unit sphere) as the variational setting for the tradeoff.

## (E) Explicit invariants d_A, 𝒥_∞, 𝒮_∞, C₀, mass numbers

**PARTIALLY KNOWN — the constant.** CCM 2025, arXiv:2511.22755, **eq. (4.12), p. 15**:
`c(L)+w(L) = ½log((e^{L/2}−1)/(e^{L/2}+1)) + tan^{-1}(e^{L/2}) − π/4 + γ/2 + ½log(8π)`.
Letting L→∞ gives `π/4 + γ/2 + ½log 8π`, i.e. **exactly d_A/2 + 2**: our `d_A = γ + log8π + π/2 − 4` is
twice their limit minus 4. So the combination `γ + log 8π + π/2` is in print; the `−4` and the name d_A are
ours. Related classical anchor: the archimedean term `−(log 4π + γ)f(1) − ∫₁^∞(f(x)+f*(x)−2f(1)/x)·x dx/(x²−1)`
in **Bombieri 2000, §2, Explicit Formula (p. 186)**, and `W_ℝ(f) := (log 4π + γ)f(1) + …` in
**CC 2006.13771** (Appendix B / §"the archimedean place").

**NOT FOUND — everything evaluated on f₀.** 𝒥_∞ = 0.5706416, 𝒮_∞ = 0.801542, the splitting 𝒥_∞ + 𝒮_∞ = d_A,
C₀ = 0.083642 (negative mass), 0.037599 (prime atoms), and the 2.2× ratio: no occurrence anywhere.

## Negative findings worth recording

- **CC 2006.13771**: the positivity mechanism is compression of the scaling action to **Sonin's space** (§4
  Def. 4.4; §5 "The functional E∘Q and the compact operator K_I"; §6). Full-text grep: no *radical*, no
  *screw*, no *Lévy*, no signed-measure kernel, no ground-state/Doob transform, Φ never a test — Toeplitz + prolate.
- **CCM 2112.05500**: prolate W_sa, negative eigenvalues tracking squares of zeros, eigenfunctions in Sonin
  space (§3). Its only "non-degenerate form" (p. 4, eq. (6)) is the boundary form Ω on Dom(W_max)/Dom(W_min) —
  unrelated to the Weil radical. No Φ, no ν.
- **Li 2404.13427**: Thms 1.1–1.4, a positive T on L²(C_S), V(h)T trace class with nonnegative eigenvalues, and
  tr V(h)T vs Δ(h). No radical, no positive/negative decomposition, no translates. Least relevant of the five.
- **Bombieri 2000**: the "Laplacian" at Lemma 1 (`𝒟 = −D − D²`) regularises the Sobolev norm in the variational
  problem, it is **not** a representation of the Weil form. No no-certificate theorem.

## Recommendation — what can be presented as new, and how to cite

Present **(C)** as the paper's theorem and **(B)'s ground-state step** as its engine; present **(A)** as setup,
not as a discovery. Concretely: the canonical test must be introduced as *Riemann's* function in the
Connes–Consani–Moscovici normalisation — cite **Riemann 1859**, **CCM arXiv:2511.22755 Lemma 7.1 and
eq. (7.1)–(7.2)** for `FE(h) = Ξ`, and **Freedman arXiv:2606.29555 eq. (1)** for the identical log-variable
form with the factor 4 (a preprint, but it removes any claim of novelty for the "scale repair"); the only
new sentence in (A) is that the translates of f₀ and f₀∗h span an infinite-dimensional radical on the
non-compactly-supported class, stated against **Suzuki arXiv:2301.00421 §1** (positive definiteness on
C_c^∞) and **Bombieri 2000 Lemma 10** (truncations non-degenerate), which are what make the enlargement
necessary rather than trivial. In (B), the signed measure itself must be attributed: **Suzuki
arXiv:2606.09096 §2.5 eq. (2.9)–(2.11)** and **arXiv:2301.00421 §3.5** already give
`Q_W(v) = ∬(−g″(x−y))v(x)v(y)` with the prime atoms `Λ(n)/√n` at ±log n, and **Krein–Langer / Suzuki
Thm 1.2** already give "screw function ⟺ RH", i.e. the conditional positivity; what is ours is the
substitution `g = f₀·s`, which is **Frank–Seiringer, arXiv:0803.0503, JFA 255 (2008) 3407–3430** applied to a
*signed* Lévy measure with a *radical* zero mode instead of a genuine ground state — say that explicitly, and
say what breaks (ν is not a positive Lévy measure). The closed form `b(t)` and the plastic-number threshold
`e^t < ρ, ρ³ = ρ+1` appear to be new and should be labelled as an evaluation, not a theorem. **(C)** is the
publishable result: state it against **Connes arXiv:2602.04022 Theorem 7.1** (the existing *nonlocal* Sonin
minorant, which the theorem shows cannot be localised) and against **Freedman §8**'s numerical exclusions,
and credit **Bombieri 2000, Introduction (iii)** for raising linear independence of `{x^{−ρ}}` as the hard
question the proof's translate-independence step answers in a special case. **(D)** and the f₀-evaluated
constants in **(E)** are unfound and can stand as new, with **CCM eq. (4.12)** cited for the constant
`γ + log 8π + π/2` and **Bombieri §2/§4** for the archimedean term and the variational frame.
Mandatory background citations regardless: **Weil 1952**, **Yoshida 1992** (positivity on small support,
via Bombieri §12), **Bombieri 2000**, **Connes–Consani 2021 (Selecta, arXiv:2006.13771)**,
**CCM 2021/2025**, **Suzuki 2023 + 2026**, **Li 2024**, **Frank–Seiringer 2008**. Finally: the 2026 preprint
cluster (Freedman, Groskin ×2, VIDRAFT) is unrefereed but public and overlaps our object; not citing it
would look like non-disclosure, so cite it as preprints with one sentence each on what it does and does not
establish.
