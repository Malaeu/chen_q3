# KERNELCHECK — independent audit of PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md
Directive §8.4 KERNEL_REFERENCE_METRIC_RADICAL_AND_MINORANT_AUDIT. Fresh checker, no repo writes.
Every number below is from my own sympy/mpmath/scipy runs in this directory (s1b, s2, s3, s4b, s5, s6, s7, s8).

## VERDICT
**No incorrect equation found. Failure code KERNEL_REFERENCE_DOMAIN_OR_RADICAL_IDENTIFICATION_GAP is NOT raised.**
All four success conditions hold: same bounded X on (K7); exact kernel (K2); (K13) an equivalence with the
sign unproved; strict upper witness (K30). One citation debt inherited from the ALIGN audit is **now closed by
direct reading** — I downloaded CC20 and read Appendix C.

## 0. CC20 Appendix C — **READ** (arXiv:2006.13771v1, pdftotext, local copy `cc20.pdf`)
Verbatim, line 4846 ff.: *"Proposition C.1 Let Z ⊂ ℂ be the set of non-trivial zeros … and F ⊂ ℂ a finite set
disjoint from Z and containing {0,1}, then  RH ⟺ Σ_v W_v(g∗ḡ^♯) ≤ 0, ∀g ∈ C_c^∞(ℝ*_+) | g̃(z)=0, ∀z ∈ F.  (155)"*
- The verdict's §4.2 reading is **substantively CORRECT**. With F={0,1} and the crosswalk g̃(s)=F_f(s−1/2) the
  two conditions are exactly g̃(0)=M_−=0, g̃(1)=M_+=0, i.e. membership in ℋ; and Q = f̃(0)+f̃(1) − Σ_v W_v = −Σ_v W_v
  on that class, so Q ≥ 0 ⟺ RH with (K6)'s sign. The compact-support class of (155) is the §2.2 core.
- **Label DEFECT (cosmetic):** the result is labelled **Proposition C.1**, not "Proposition 1". "Proposition 1"
  in that appendix belongs to ref **[34] = H. Yoshida, *On Hermitian forms attached to zeta functions***, cited
  inside the proof. Equation number (155) and the content are right.

## 1. Item-by-item
| Item | Status | My evidence |
|---|---|---|
| (K6) source form, c_A | **CORRECT** | c_A = γ+log8π+π/2 = 5.3721834192256655822 = log π − ψ(1/4) (agree to 9.2e−41). |
| 𝒟 symbol a(t)=Reψ(1/4+it/2)−ψ(1/4) | **CORRECT — derived** | From ψ(z)=∫₀^∞(e^{−t}/t − e^{−zt}/(1−e^{−t}))dt with t=2u: Reψ(1/4+ir/2)−ψ(1/4) = 2∫₀^∞A₀(u)(1−cos ru)du. Numerically: r=0.7 and 3 agree to 0.0e0 (18 digits), r=12 to 4.1e−18. |
| (K7) ℰ, ℋ closed | **CORRECT** | 𝒲 closed multiplication form + 𝒟 closed multiplier form ⇒ Hilbert norm; M_± bounded on ℰ by (K8) ⇒ ℋ closed of codim ≤ 2. 𝒲<∞ ⇒ f∈L². |
| (1+a)≍log(2+\|t\|) | **CORRECT** | ratio ∈ [0.591, 2.184] over t ∈ {0,…,10^14}. |
| §2.2 core density | **CORRECT** | Operator identity U_t((1−χ_R)f)−(1−χ_R)f = (1−U_tχ_R)(U_tf−f)+(χ_R−U_tχ_R)f verified algebraically term by term. Both dominations valid: term 1 ≤ ‖U_tf−f‖² (A₀-integrable); term 2 ≤ min(4,C²t²)‖f‖² with ∫A₀min(4,C²t²)dt<∞ (A₀ ≤ 1+1/(2t): 0 violations on a 2000-point grid). Mollifier multiplier ≤1 → 1 pointwise ⇒ 𝒟-convergence by DCT against 4a\|ĝ\|². Moment determinant: columns (e^{1/2}M₊, e^{−1/2}M₋)ᵗ, (e^{−1/2}M₊, e^{1/2}M₋)ᵗ ⇒ det = (e−e^{−1})M₊(b)M₋(b) ≠ 0 for b ≥ 0 nonzero. Coefficients → 0 because M_± are ℰ-continuous and vanish on the limit. |
| (K8) both bounds | **CORRECT** | \|x\|+\|x−t\| ≥ \|t\| + Cauchy–Schwarz; ∫e^{x−2\|x\|}dx = 1.3333333333333333333 exactly = 4/3. |
| (K9) 65/3 ledger | **CORRECT** | c_A = 5.37218 < 7; Σ_{m≥2} log m/m^{3/2} = −ζ′(3/2) = 3.93223973743 < 6 (appendix's route f(2)+∫₂^∞ = 4.05375 < 2log2+4 = 5.38629 < 6). Prime factor 2·6 = 12; pole 2·(4/3) = 8/3. 7+12+8/3 = 65/3 = 21.6666… < 22. Two-component Cauchy step valid since 65/3 ≥ 1. |
| (K10) Riesz, ‖A‖ ≤ 65/3, A=A* | **CORRECT** | Q Hermitian checked term by term (prime bracket is j-symmetric; pole pair is self-conjugate). |
| (K11) B ∈ [1/66, 131/66], A−A²/22 = B^{1/2}AB^{1/2} | **CORRECT** | sympy: A − A²/22 − BA ≡ 0; (65/3)/22 = 65/66 = 0.98484848…; 1∓65/66 = 1/66, 131/66. |
| (K12) R ≥ 0 ⟺ A ≥ 0 ⟺ Q ≥ 0 | **CORRECT** | B^{1/2} positive invertible ⇒ congruence preserves spectral sign. Also A²/22 + (A−A²/22) − A ≡ 0. |
| (K13) ⟺ RH | **CORRECT, equivalence only** | (K12) + §2.2 density + (K9) continuity + CC20 (155) read above. |
| (K14) nontriviality, d = 2^{−24} | **CORRECT** | 2∫_d^1 A₀ = 17.0953786301 > 8 (their crude route e^{−1/2}·24log2 = 10.0899604 > 8; the written ledger 0.5·24·(2/3) lands on exactly 8, strict only through strict inequalities). 2∫_d^∞A₀ − c_A = 14.2204395723 > 1. 2A₀(t) ≥ e^{−1/2}/t on (0,1]: 0 violations on a 1000-point grid (proof: 1−e^{−2t} ≤ 2t and e^{−t/2} ≥ e^{−1/2}). d = 5.96e−8 < log 2 ⇒ prime autocorrelations vanish. |
| (K15) strip bound | **CORRECT** | sup_{\|σ\|≤1/2} [1/(2−2σ)+1/(2+2σ)] = 4/3 at σ=±1/2 (min 1 at 0). Unconditional for zeros since \|Re λ\| ≤ 1/2 in the critical strip. |
| **(K16) explicit formula** | **IMPORTED — verified numerically by me** | Source side (K6) vs zero side, five tests, dps=40: Gaussian σ=0.15 rel **2.6e−39**; σ=0.30 rel **2.1e−34**; σ=0.50 rel **8.7e−19** on a value 6.385e−22 obtained by cancelling arch −2.2379 + prime 1.1064 + pole 3.3442 (**22-digit cancellation**); pole-null (∂²−1/4)Gaussian σ=0.15 rel **9.1e−41**, σ=0.30 rel **6.8e−37**. Falsification controls: c_A→γ+log4π+π/2 breaks it outright; c_A×(1+10^{−6}) already gives −2.84e−6 vs 1.755e−8. The test has teeth. |
| (K17) 𝒩_pt ⊆ rad Q | **CORRECT — independently reproduced from source data only** | Purely x-space (theta series + Λ(m) + c_A, **no zero locations**): ‖g₀‖²=97.4705135804, 𝒟[g₀]=521.9304716, c_A‖g₀‖²=523.6294769, prime=−1.6990044965 ⇒ **Q[g₀] = −8.04e−7, i.e. −8.2e−9 of ‖g₀‖²** — a 9-digit cancellation against a zero side that is exactly 0. Residual is stable under refinement and sits entirely in my float64 𝒟-quadrature. M_±(g₀) = −3.7e−15. |
| (K18) F_Φ = Λ_ξ | **CORRECT** | Own quadrature of the series at z ∈ {0, ±0.5, 1.3, 2.5, 3i, 0.25+5i, −0.4+i}: \|diff\| ≤ **1.3e−51** (dps 50). Evenness from the two-sided series: rel 2.3e−50 (x=0.4), 9.4e−48 (0.8), 1.8e−39 (1.2). Teeth: doubling Φ breaks the match by 0.517. |
| (K19) two expressions for J_λ | **CORRECT** | Requires F_Φ(λ)=0; right- and left-tail forms agree to 2e−17 … 1.4e−15 at x ∈ {−1,−0.3,0,0.3,1}. |
| J_λΦ decay | **CORRECT** | \|J\| = 6.0e−9 (x=1), 1.0e−25 (1.5), 3.0e−72 (2), 1.1e−199 (2.5); same on the left. Double-exponential, tracking Φ (Φ(2)=1.0e−69). Matches Appendix A.7's C′exp(−c′e^{2\|x\|}). |
| **(K20) F_{J_λv}(z)=F_v(z)/(λ−z)** | **CORRECT — derived and verified** | One integration by parts; both boundary terms vanish, the one at +∞ **only because F_v(λ)=0**. With v=Φ, λ=iγ₁=14.134725141734694i: agreement ≤ **5.6e−17** at z ∈ {0, 0.7, −0.4, 0.2+2i, 5i, ±0.5}. Teeth: comparing with Λ_ξ(z)/(λ+z) is off by 3.5e−3. |
| (K21) h_λ ∈ ℋ, entire transform | **CORRECT** | (z²−1/4) factor forces M_±(h_λ)=F_{h_λ}(±1/2)=0; Λ_ξ(z)/(λ−z)^r entire because r = m_λ exactly. |
| (K22) F_{h_λ}(λ) ≠ 0 | **CORRECT** | r=1, λ=iγ₁: formula (λ²−1/4)(−1)Λ′_ξ(λ) = **0.2765997555122432i**, matches lim_{z→λ}(z²−1/4)Λ_ξ(z)/(λ−z) to 1.2e−13. λ²−1/4 = −200.0404548 ≠ 0 because ξ(0)=ξ(1)=1/2. Vanishing at other distinct zeros and their mirrors: ≤ 4.3e−34. |
| **(K23) ker X = ker A = rad Q = 𝒩_pt** | **CORRECT, and free of RH** | rad = ker A is the Riesz definition. ⊆ from (K16) + j-stability of Z_c (from ξ(s̄)=conj ξ(s), ξ(1−s)=ξ(s)) + §2.2 density + (K9). ⊇ from (K17). Separation uses only that λ has *some* finite order r=m_λ; **no simplicity, no zero location**. |
| (K23a) off-line witness | **CORRECT** | Q[u] = m_λ·conj(−1)·1 + m_{jλ}·conj(1)·(−1) = −2m_λ < 0, with jλ ≠ λ exactly off the line. |
| (K24) ĝ₀ = −(t²+1/4)Ξ(t) | **CORRECT** | Φ̂(t)=F_Φ(−it)=Λ_ξ(−it)=Ξ(−t)=Ξ(t); ∂²→−t². Nonzero a.e. since Ξ entire ≢ 0. |
| **(K25) ordinary-L² obstruction** | **CORRECT — all four steps** | (i) U_bg₀ ∈ 𝒩_pt (factor e^{bz} zero-free, poles preserved). (ii) b ↦ ⟨U_bg₀,u⟩ is the inverse FT of conj(ĝ₀)û ∈ L¹ (Cauchy–Schwarz); identically zero ⇒ product 0 a.e. ⇒ û=0 ⇒ u=0. (iii) graph closure contains (u,0) for every u ∈ L². (iv) single-valuedness ⇒ Ȳ=0 ⇒ Y=0. I found no gap. Holds under either truth value of RH. |
| (K26) projection | **CORRECT** | Spectral theorem: A²(A²+ε)^{−1} ↑ 1_{(0,∞)}(A²), strong limit = Π_{(ker A)^⊥}; every resolvent is of a proved ≥ εI operator. |
| (K27)–(K29) | **CORRECT** | ĝ_k = −(it)^k(t²+1/4)Ξ(t) ≠ 0 a.e. ⇒ multiplication injective ⇒ T_{g_k}C = 0 ⇒ C = 0. HS square strictly positive-or-infinite. |
| **(K30) fixed-S falsifier** | **CORRECT** | ‖T_{g_{0,R}}S_S‖²_HS ≥ ‖T_{g_{0,R}}ψ‖² needs S_Sψ=ψ; **verified in CC20 Theorem 4.7 (line 2537): "Let S be the orthogonal projection of L²(ℝ)_ev on the closed subspace S(1,1)"**, so ψ ∈ ran S_S is legitimate. Q[g_{0,R}]→0 by (K17)+(K9); ‖T_{g_{0,R}}−T_{g₀}‖_op ≤ ‖g_{0,R}−g₀‖_{L¹}→0. Thresholds a_S/4, 3a_S/4 ⇒ upper bound −a_S/2. Scope (fixed S, global support, not CC20's local theorem) is stated correctly. |
| (K31) D_S = P+Q_S−I+S_S, PD_SP=(PF_SP)*(PF_SP) | **ASSERTED-NOT-DERIVED (not checkable here)** | Rests on [SF]'s Euler formula and CCM23 §4.8; those files are outside my permitted read set. |
| **(K32) dilation coefficient** | **CORRECT** | Own computation of ½Σ_{j≥0}b(2^ju) − ½b(u/2) for b = e^{−s²}, 3e^{−2s}, sech s: empirical slope in log(1/u) = 0.721347519051 / 2.163954514912 / 0.721347519748 vs b(0)/(2log2) = 0.721347520444 / 2.164042561333 / 0.721347520445. Remainder bounded over a full 2-adic period (e.g. −0.458872 … −0.457500), so the O(1) is genuine (log-periodic, not drifting). |
| (K33) r-fold | **PARTIAL** | The lattice asymptotic #{j ∈ ℤ_{≥0}^r : Σj_p log p ≤ L} = L^r/(r!∏log p) + O((1+L)^{r−1}) **CORRECT**: err/(1+L)^{r−1} = 0.15–0.58 (r=1), 1.157–1.168 (r=2), 0.676–0.692 (r=3), flat in L. The prefactor b(0)∏(1−p^{−1}) is **ASSERTED** — it comes from [SF]'s Euler factors, unreadable here; it is at least *consistent* at r=1, S={2}: (1−1/2)/log2 = 1/(2log2), matching (K32). |
| (K34) classification | **CORRECT** | Cauchy–Schwarz for the positive form P; B = Π_{N^⊥}BΠ_{N^⊥} ⟺ vanishing on N. |
| (K35)–(K39) | **CORRECT** | (K36) sup attained at h=Af. (K37) restricting the sup to span{e_i} gives q*G^{−1}q ≤ ‖Af‖², hence an **upper** bound on R — correctly labelled. (K39) ‖Af−y‖ ≤ ε ⇒ ‖Af‖ ∈ [max(0,‖y‖−ε), ‖y‖+ε]; envelope directions correct. |
| (K5) toy | **CORRECT** | R = z² − 4z² = −3z², ker X = N = rad Q, Q ≥ 0. Refutes the general inference. |
| §6.1 toy | **CORRECT** | 0_N⊕I₂ and 0_N⊕diag(−1,1) both have radical N (nondegenerate on ℂ²), opposite positivity. |
| §1.2 multiplicity | **CORRECT** | With Λ_ξ = (z−λ)²u: (z²−1/4)Λ_ξ(z)/(λ−z) = −(z²−1/4)(z−λ)u(z), order one short at λ, zero at every distinct zero. Correctly labelled conditional. |

## 2. First asserted-not-derived step
**Document order: (K16), §3.1** — the signed explicit formula is *imported* ([ALIGN A27], [CC20 Appendix B]),
not proved in the verdict. This is a legitimate import of a classical theorem, and I confirmed it numerically
to 34–41 relative digits with a falsification control (§1 above), so it carries no risk.

**First load-bearing, non-classical asserted-not-derived step: the uniform-in-cutoff vertical decay,
§3.2 last paragraph + Appendix A.8** — "bounds compact approximants of (K21) by C_N(1+|T|)^{−N}, uniformly in
cutoff". This is what licenses passing (K16) to the limit for g = h_λ, and therefore the ⊇ half of (K23).
The mechanism is right (χ_R corrections carry Φ-derivatives of size e^{−πe^{2R}}; my J_λΦ(2.5)=1.1e−199
confirms the scale) but **no constant is exhibited**. *Weakest repair:* state N=4 and the explicit constant
C_4 = sup_R ‖(∂_x^{4})[e^{|x|/2}(∂²−1/4)(χ_R J_λ^rΦ)]‖_{L¹}, finite by Appendix A.7; then Σ_λ m_λ(1+|γ|)^{−4} < ∞
by the O(T log T) count. This is bookkeeping, not a hole.

Genuinely unverifiable here: **(K31)** and the Euler prefactor of **(K33)** (source files outside my read set).

## 3. Tight spots
1. **(K9): 65/3 vs 22 has 1.5% slack**, and 22 is hard-wired into (K11), (K35), (K37), (K39). The "12" is very
   loose (true 2Σ Λ(m)/m^{3/2} = 3.0105), so 22 is safe — but any change of reference norm re-opens every one
   of those equations. The calibration constant is a fixed choice, not a derived one.
2. **(K14) as written lands exactly on 8**: 0.5·24·(2/3) = 8.0000 precisely; strictness comes only from
   e^{−1/2} > 1/2 and log 2 > 2/3 being strict. True value 2∫_d^1A₀ = 17.095, so the *statement* is safe with
   a factor >2 to spare; the *written ledger* has zero visible margin. Recommend printing 10.089 instead.
3. **(K30) depends on S_S being an orthogonal projection.** True for CC20 (Thm 4.7). Any restatement with a
   non-idempotent Sonin operator (e.g. the bare D_S, which the verdict itself declines to call HS) needs
   ‖T S‖²_HS ≥ ‖Tψ‖² re-proved.
4. **§5.1's dictionary "T_f is the Fourier multiplier f̂ in the common Mellin model"** is the pivot of
   (K28)–(K30). Correct for CC20's ϑ(g) under x=e^u, but it is a normalization claim across three papers and
   the verdict flags it only in one clause ("a different global adelic representation would need its own argument").
5. **(K13)'s RH leg is one citation deep.** Now read (CC20 (155)) — but note that (155) requires F ∩ Z = ∅;
   F = {0,1} qualifies only because 0,1 ∉ Z. That is unconditional, so no circularity, but it is the single
   published fact the whole equivalence rests on.
6. Q[g₀] = 0 is numerically *inaccessible* below ~1e−9 in float64 because 𝒟 needs a nested quadrature; the
   null family can never become a numerical negative witness. Supports the verdict's refusal to claim Q < 0.

## 4. Adjudication of the three registrations
| Registration | Stated p | My adjudication |
|---|---:|---|
| P_KERNEL_RIESZ_RADICAL_AUDIT_SURVIVES | 0.85 | **SURVIVES.** (K9)'s ledger, (K23)'s exact kernel and (K13)'s calibrated equivalence all reconstructed from the geometric source with no new RH premise and no replacement of ℋ. The one thing that could have sunk it — the CC20 sufficiency citation — I read directly and it holds. **0.85 was under-confident; warranted ≈ 0.95.** |
| P_KERNEL_L2_TOPOLOGY_OBSTRUCTION_SURVIVES | 0.96 | **SURVIVES.** Four elementary steps, each re-derived; the L¹-product/Fourier-uniqueness step is exactly right and the graph-closure step is airtight. **0.96 is if anything low; ≈ 0.99.** |
| P_KERNEL_FIXED_S_RANK_ONE_FALSIFIER_SURVIVES | 0.91 | **SURVIVES for (K30)**, with the projection premise now confirmed in CC20. The D₂ half is *split*: (K32)'s dilation coefficient I verified to 8 digits for three test functions, but (K31) and (K33)'s Euler prefactor rest on [SF], which I could not open. **0.91 is about right; I would not raise it.** |

## 5. Plain answers
- **Does (K23) ker A = 𝒩_pt stand without RH?** **Yes.** Nothing in the proof uses a zero's location. The
  inputs are: (K16) (classical, unconditional), j-stability of Z_c (functional equation + reality of ξ on ℝ),
  |Re λ| ≤ 1/2 for zeros (critical strip, unconditional), the O(T log T) count (unconditional), the §2.2 core,
  and the existence of J_λ^{m_λ} for the *actual* order m_λ. **Simplicity is not assumed anywhere** — §1.2
  even exhibits, conditionally on a multiple zero, an element separating (K2) from the multiplicity ideal (K3).
  What the zeros *are* used for is proving what the kernel is; they are not inputs to A or X. That distinction
  is stated correctly and I found no place where it is violated.
- **Is (K13) an equivalence and not a proof?** **Yes, and the verdict says so itself.** R ≥ 0 ⟺ A ≥ 0 ⟺ Q ≥ 0
  on ℋ ⟺ RH. (K11) is a congruence by a uniformly positive B, so it *preserves* the positive and negative
  spectral subspaces: the representation cannot create, hide or pay a sign. The remainder (K35) carries exactly
  the original burden, and the verdict's own "strongest attack" ("you used Q to define A, squared it, and moved
  the unknown sign into R") is conceded as correct. **No sign theorem, no RH progress — an object answer only.**
