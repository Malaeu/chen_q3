# ALIGNCHECK — independent audit of PROSHKA_VERDICT_GOAL058_ALIGN_2026-09-08.md
Directive: ALIGN_COVERAGE_AND_NEAR_NULL_SOURCE_AUDIT (§8.4). Fresh checker, no repo writes.
All numbers below are from my own sympy/mpmath/numpy runs in this directory (scripts s1..s8, core.py, fast.py).

## VERDICT OF THE AUDIT
**No incorrect equation found.** (A8)–(A9), (A15)–(A21), (A22)–(A35), §7.2–7.3 and Appendix A are
ACCEPTED as written, with two citation-borne steps flagged below. Failure code
ALIGN_COVERAGE_OR_NEAR_NULL_SOURCE_MISMATCH is **not** raised.

## 0. False-inference controls (checked first, as directed)
| Item | Result | Witness |
|---|---|---|
| (A7) star identity | CORRECT | sympy residual exactly 0 for symbolic weights w_1..w_3 and 2-vector profiles |
| (A8) perfect alignment, constant energy | CORRECT | h_1=h, h_p=(w_p/W)h ⇒ H_w=Wh ⇒ both bracket terms of (A7) vanish identically; Σ energies / product norm² = (2D(h))/(2‖h‖²) = D(h)/‖h‖², leaf-count-free. h=(∂²−1/4)η has M_±=0 because (∂²−1/4)e^{±x/2}=0 (verified symbolically), and h≠0 since ker(∂²−1/4)=span{e^{±x/2}} contains no compactly supported function. |
| (A9) diag control | CORRECT | H−K = diag(1,−1/2) exactly; H[e₁]=3>2=K[e₁] while (H−K)[e₂]=−1/2<0. A strict counterexample to the *inference rule*, not to Weil positivity — labelled correctly. |
| §1.2 zero-synthesis obstruction | CORRECT | overlap at 29,31 exists: log31−log29 = 0.0666913745 < 2δ = 0.1013662770 (equivalently 2·31⁴=1847042 < 3·29⁴=2121843, exactly the verdict's criterion). Both translated pieces sit compactly inside (−δ,δ); the separation argument via span{e^{±x/2}} is valid. |

## 1. Conventions re-derived (not taken on trust)
- A(t)=Σ_{j≥0}e^{−(2j+1/2)t}; ∫₀^∞A(t)·2(1−cos tξ)dt = (ξ/2)²/((j+1/4)((j+1/4)²+(ξ/2)²)) summed = **(A5) exactly**.
  Numerically a(ξ)=Reψ(1/4+iξ/2)−ψ(1/4) matches the series to 0.0e0 at ξ=0.7, 3, 12. So (A4)+(A5) are derived, even, increasing, unbounded.
- c_A = log π − ψ(1/4) = 5.3721834192256655822 — identical to γ_E+log(8π)+π/2 to 20 digits. The two archimedean
  normalisations (verdict §1.1 vs the task's Reψ−log π form) are therefore the same object. Verified.
- **Archimedean identity checked directly, not assumed**: 𝒟(g_0)=∫₀^∞A(t)‖U_tg−g‖²dt computed in x-space from the
  theta series = 521.9304724236; (1/2π)∫a|ĝ|²dt from Ξ = 521.9304724236 (rel. 1.1e−15). Same for g_1 (5.5e−15).

## 2. (A15)–(A21) — coverage
| Claim | Result | Evidence |
|---|---|---|
| (A15) translation invariance | CORRECT | M_±(U_bf)=e^{±b/2}M_±(f), so the pole product 2Re{M₊ conj M₋} is invariant; 𝒟, ‖·‖, Π invariant by unitarity. Q(U_bf)=Q(f). |
| (A3) exact synthesis identity | CORRECT | subordinate smooth partition of unity on the open cover; only the *total* moment is imposed. Standard, no gap. |
| (A6) prime formula + cutoff m ≤ ⌈P e^{2δ}⌉ | CORRECT | nonzero correlation needs log m < 2δ + x_p − x_q ≤ 2δ + log P. |
| (A10) L² floor for 𝒟 | CORRECT | disjoint supports for t>d_P. Sample values: P=2 → 2∫_{d_P}^∞A = 2.8129451; P=47 → 0.55466628. |
| (A16)/(A17) PNT cover | CORRECT | log p_{j+1}−log p_j → 0 is immediate from p_j ~ j log j. Sampled log-gaps: j=10 → 6.67e−2, j=10³ → 1.01e−3, j=10⁵ → 9.23e−6; δ/2 = 2.534e−2. The translated support argument is exact representation, not density. |
| (A19) explicit integer law | CORRECT | δ = 0.050683138513520547747; 4/δ = 78.921710796; m₀ = ⌈4/δ⌉ = **79**; 1/m₀ = 0.0126582278 ≤ δ/4 = 0.0126707846 (holds, 1% slack); log 80 − log 79 = 0.0125787822 < 1/79. R=1,2,3: first centre = −R exactly, last centre = 1.0004531 / 2.000173 / 3.0000039 ≥ R, max centre gap 0.01258 < 2δ = 0.10137. Cover verified. |
| (A18) inf/sup transfer | CORRECT | both directions from inclusion C_P ⊂ H₀₀^c and (A15)+(A17); β_P nonincreasing, ρ_P nondecreasing since Ω_P ⊂ Ω_{P'}. |
| §3.4 non-density | CORRECT | M_± are continuous on the fixed-window form domain (|M_±(f)| ≤ e^{W/2}‖f‖₁ ≤ C‖f‖₂), joint kernel closed of codim 2; a nonnegative bump has M₊>0. |
| (A20) Mellin crosswalk | CORRECT | u=e^x gives g̃(s)=∫f e^{(s−1/2)x}dx=F(s−1/2); g̃(0)=M₋, g̃(1)=M₊. Re-derived. |
| (A21) chain | see §6 | first ⟺ derived and correct; second ⟺ is citation-borne. |

## 3. (A22)–(A28) — the theta function and the SIGNED explicit formula
| Claim | Result | Evidence |
|---|---|---|
| (A22) Φ from v, exact factor | CORRECT | sympy: (∂²−1/4)[e^{x/2}e^{−a e^{2x}}] − (4a²e^{9x/2}−6a e^{5x/2})e^{−a e^{2x}} = **0** identically, with a=πm². (∂²−1/4)e^{x/2}=0 kills the "1" in 1+2Θ. |
| Φ even | CORRECT | two-sided direct series at dps=80: rel. diff 2.8e−80 (x=0.5), 1.1e−70 (x=1.0), 1.6e−52 (x=1.4). Parity of g_k confirmed to ~1e−65 for k=0..4. |
| **(A23)** ∫Φe^{zx}dx = ξ(1/2+z) | **CORRECT** | z = 0, ±0.5, 1.3, 2.5, 3i, 0.25+5i, −0.4+i, 14.134725142i: |LHS−RHS| ≤ 7.4e−32 (dps 30). At z=14.134725142i both sides = −3.67e−13 (first zero). Doubling the prefactor breaks the match by a factor 2, so the test has teeth. **The numerical factor produced by the two integrations by parts (a(2a−1)=s(s−1)/2) is right.** |
| (A24) zero pole moments | CORRECT | ∫g_k e^{±x/2}dx: k=0 → 1.60e−34; k=1 → ∓7.44e−34; k=2 → 1.83e−32; k=3 → ±3.09e−32; k=4 → −2.93e−30. |
| ĝ_k(t) = (it)^k·(−(t²+1/4)Ξ(t)) | CORRECT | x-space ‖g_k‖² vs Ξ-channel ‖g_k‖²: rel. 1.3e−15 (k=0) … 1.9e−14 (k=4). Values 97.4705135804, 4534.7451110738, 283989.906930416, 22102598.6955376, 2077408645.86180. |
| **(A27)–(A28)** Q(g_k)=0 without RH | **CORRECT — decisive test passed** | Q computed with the archimedean part from the Ξ/digamma symbol and Π from the *theta-series x-space autocorrelations* (two genuinely independent channels): Q(g_0)= 6.68e−14 (6.9e−16 of ‖g_0‖²), Q(g_1)= 1.36e−12 (3.0e−16), Q(g_2)= −5.82e−10 (2.1e−15), Q(g_3)= 5.59e−9 (2.5e−16), Q(g_4)= 4.41e−6 (2.1e−15). Π(g_0) = −1.6990044965. |
| conjugation convention | CORRECT | on ρ=1/2+iγ the summand F(ρ−1/2)·conj(F(1/2−conj ρ)) = |F(iγ)|² ≥ 0; off the line it is a product at two mirrored points and is *not* a square — as the verdict states. **Independent generic test:** for f=(∂²−1/4)e^{−x²/2σ²}, σ=0.30, Q(source)=7.023890856495e−4 vs Σ_ρ|F(iγ)|² = 7.023890856558e−4 (rel. 9.0e−12, first 59 zeros). |
| pole term normalisation in (A1) | CORRECT | with f=e^{−x²/2σ²} (M_±≠0), σ=0.30: Q(source, incl. +2Re{M₊conj M₋}) = 1.755262535e−8 vs Σ_ρ = 1.755262551e−8 (9.2e−9). Dropping the pole term gives −1.1567 — so the sign and the factor 2 are confirmed, not merely assumed. |
| unconditionality | CORRECT | F_k(ρ−1/2) ∝ ξ(ρ)=0 and F_k(1/2−conj ρ) ∝ ξ(1−conj ρ)=0; 1−conj ρ is a zero by the functional equation whatever Re ρ is. No zero is placed on the line anywhere in the argument. |
| (A25) ledger | CORRECT | ∫t²A dt = 16.165967492192115 < 2026/125 = 16.208 < 18 (direct quadrature agrees: 16.165967492192058). Σ_{m≥2}log m/m^{3/2} = 3.10226 ≤ 2log2+4 = 5.38629 < 6, so the factor 12 stands (Λ(m)≤log m, e^{−|t|} from |x|+|x−t|≥|t|). ∫e^{x−2|x|}dx = 4/3 → pole bound 8/3. c_A = 5.37218 < 7. 7+12+8/3 = 65/3 = 21.667 < 22 and 18 < 22, so the two-component Cauchy step gives 22. |
| (A26) cutoff convergence | CORRECT | M_±(g_{k,R})=0 exactly by parts; the error terms carry χ'(x/R)/R, χ''(x/R)/R² times Φ-derivatives on R≤|x|≤2R, which are doubly exponentially small (Φ(1.5)=1.3e−23, Φ(2.0)=1.0e−69, Φ(2.5)=9.8e−197), so e^{2R}·error → 0 in the X-norm. Derivatives through order k+3 are exactly what ‖·‖_X needs. |

## 4. (A29)–(A35) — near-null family and unbounded prime part
- (A29)–(A30): CORRECT. Q(g_{k,R})→0, ‖g_{k,R}‖²→‖g_k‖²>0, 𝒟(g_{k,R})→𝒟(g_k)>0 (𝒟=0 would force translation invariance). Since
  (c_A‖f‖²+Π)/𝒟 = 1 − Q/𝒟 on pole-null f, ρ_P ≥ 1 in the limit and β_P ≤ 0 in the limit. Monotonicity gives existence of the limits.
- **No uniform positive floor: CONFIRMED.** For each c>0 some finite P carries f with Q(f)/‖f‖² < c/2, hence Q(f)−c‖f‖²<0.
- **No claim of Q<0 and no claim ρ≤1: CONFIRMED absent.** §4.3, §5 and §8.5 state the opposite explicitly
  ("no negative sign for Q is asserted"; "the existence of near-null tests supplies no upper bound on rho_P"). I found no place where a sign is smuggled in.
- (A31) dichotomy: CORRECT as stated.
- §4.3 ℓ² control (De_j=je_j, Q=I): CORRECT — ρ_n = 1 − inf‖f‖²/⟨Df,f⟩ = 1−1/n → 1 while the L² bottom stays 1.
- (A32)–(A33): CORRECT. |ĝ_k|²=(t²+1/4)²t^{2k}Ξ(t)²; the normalized mass in [−B,B] is ≤ (B/C)^{2k}·(fixed ratio) → 0, denominator positive since Ξ is analytic and ≢0.
- **(A34) growth: CONFIRMED numerically.**

  | k | 0 | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
  |---|---|---|---|---|---|---|---|---|---|---|
  | 𝒟/‖g_k‖² | 5.35475 | 5.53711 | 5.66077 | 5.85319 | 6.31912 | 6.80196 | 7.36352 | 7.99685 | 8.65013 | 9.33611 |
  | Π/‖g_k‖² | −0.01743 | 0.16492 | 0.28859 | 0.48100 | 0.94694 | 1.42977 | 1.99133 | 2.62467 | 3.27795 | 3.96392 |

  Both increase monotonically, ≈ +0.68 per doubling of k (i.e. ~log k, matching a(t)~log t at t*≈4k/π). Π/‖g‖² passes 1.84 at k≈48
  and reaches 3.96 at k=256, so the **1.84 "saturation" cannot be an all-test cap** — (A35) stands. For k=0,1,2 the Π values were
  computed independently in x-space (Π(g_0)=−1.6990044965 → −0.017431 per norm²) and agree with 𝒟/‖g‖²−c_A to 1e−15.

## 5. §7.2–7.3 — COMPENSATE §4.2 domain completion
- Log-norm ≍ shifted archimedean form norm: VERIFIED numerically. (1+a(t))/(1+log(2+|t|)) ∈ [0.591, 2.184] for t ∈ {0, 0.5, 1, 2, 5, 20, 100, 10⁴, 10⁸} — bounded above and away from 0. CORRECT.
- Dilation bound 1+log(2+|t|/r) ≤ 1+log(2+|t|)+|log r| for 0<r≤1: CORRECT (2+|t|/r ≤ (2+|t|)/r). It does give the uniform bound that upgrades dense-set strong convergence to the whole space. Mollification with support below the interior margin: correct.
- Surjectivity of L onto ℂ⁸ from the dense core: CORRECT (a nontrivial annihilator on the core extends by continuity, contradicting independence).
- **(A38): CORRECT.** L y_r⁰ = Ly_r − C C^{-1} L y_r = 0 exactly, and y_r⁰ → y because Ly_r → Ly = 0. All eight constraints, not two. 47/6000 passes to the closed tail by continuity.
- §7.3: indicator/restricted-exponential transforms are O((1+|t|)^{-1}); (log|t|)/(1+|t|) ∈ L² (∫(log t)²/t² < ∞), so the archimedean multiplier does give an L² representative. Bounded prime/pole additions preserve it. Schur completion legitimate. CORRECT.
- Appendix A.7 arithmetic re-derived exactly: 1049/2000+1−3/2−1/60 = **47/6000**; 47/6000−1/1000 = **41/6000**; 6000/41 = 146.34. Appendix A.8: (1/10)²=1/100, (7/50)²=49/2500, (1/20)²=1/400. Appendix A.1: log(3/2) = 2Σ(1/5)^{2j+1}/(2j+1) ∈ (2/5, 73/180) ⊂ (2/5, 51/125); δ ∈ (1/20, 51/1000). Appendix A.4: Taylor lower sum 1+4+8+32/3+32/3 = 103/3 > 32 > 8π ⇒ log(8π)<4 ⇒ c_A<7. All CORRECT.

## 6. ASSERTED-NOT-DERIVED
1. **First asserted-not-derived step (document order): the RH leg of (A21)**, §3.4: "[CC20, Appendix C, Proposition 1, (155)] says that the compact smooth test ideal with those two vanishing conditions already suffices for RH." The source is outside my sandbox and outside the documents I was permitted to open; I could neither confirm the proposition number nor its exact quantifiers. Everything *else* in (A15)–(A21) I re-derived. The verdict does label it "a verified published consumer" rather than deriving it, so the flag is bookkeeping, not a contradiction.
2. The Weil explicit formula itself (A27) is imported, not derived. I verified it numerically to 9–12 significant digits on two generic tests (with and without pole moments), which is as strong a check as this sandbox allows.
3. "Uniformly in R" vertical decay of F_{k,R} in (A27) is asserted with a one-line justification. It is true — the cutoff corrections carry doubly-exponentially small Φ-derivatives — but the uniform constant is not exhibited.
4. §7.2's independence of the six ordinary means and the two exponential representers is *inherited* from [CHECK], not re-derived in this verdict.
5. §7.1's "original prospective probabilities were 0.90, 0.86, 0.95" and the §1.3 table values 2.4518 / 1.839 are reported-source bookkeeping, unverifiable here.

## 7. Tight spots (correct, but with little slack)
- (A19): 1/m₀ ≤ δ/4 holds with ~1% margin (0.0126582 vs 0.0126708). The δ/4 target is itself far stronger than the 2δ actually needed for coverage, so the law is safe; but the m₀ = ⌈4/δ⌉ formula is not robust to a redefinition of δ.
- (A25) prime constant: the ledger proves Σ log m/m^{3/2} < 6 via 2log2+4 = 5.386; the true value is 3.102 (and Σ Λ(m)/m^{3/2} = 1.5052). Loose but valid; the "12" is not tight.
- The near-null family is *extremely* near-null: Φ(2.0)=1.0e−69, so for R≥2 the cutoff error in Q(g_{k,R}) is below any floating-point or even interval resolution. Consequence: this family can never be promoted into a numerical negative witness, and its Q-sign is not merely unknown but numerically inaccessible. This supports, rather than weakens, the verdict's refusal to claim Q<0.
- Π(g_0)/‖g_0‖² is *negative* (−0.0174). The unbounded-prime conclusion is a k→∞ statement, not visible at k=0.

## 8. Adjudication of the three new registrations
| Registration | Stated p | My adjudication |
|---|---:|---|
| P_ALIGN_COVERAGE_SURVIVES_INDEPENDENT_REVIEW | 0.92 | **SURVIVES.** (A15)–(A20) fully re-derived with the same δ, the same total-moment convention and the same physical norm; (A19) verified numerically. The only unverified element is the CC20 leg of (A21). Warranted, arguably conservative for (A15)–(A20) alone. |
| P_ALIGN_NEAR_NULL_AND_UNBOUNDED_PRIME_SURVIVE | 0.85 | **SURVIVES.** The theta normalisation is exactly right ((A23) to 3e−31), the signed conjugation convention is right, Q(g_k)=0 is confirmed across two independent channels at 1e−15 relative, and the prime growth is confirmed to k=256. 0.85 was under-confident given how sharply the two attacks named in §8.4 fail. |
| P_ALIGN_DOMAIN_COMPLETION_SURVIVES | 0.90 | **SURVIVES**, with the qualification that the completion imports the six-mean/two-representer independence from [CHECK] rather than re-proving it. No new analytic premise is introduced; (A38) is exact. |

## 9. Plain answers to the two questions asked
- **Does the chain «Q ≥ 0 on every C_P ⟺ Q ≥ 0 on H₀₀^c ⟺ RH» (A21) stand as written?**
  The **first equivalence stands, fully derived and independently reproduced** here: it follows from (A3) synthesis, (A15) translation invariance of Q and of the total-pole-nullity, and (A17)/(A19) fixed-width exact coverage. It is exact representation, not density, and I found no gap.
  The **second equivalence stands only as far as its citation does.** It is not proved in this verdict; it is the imported Connes–Consani statement that the compact smooth pole-null ideal is a sufficient test class for RH. I could not open that source. Anyone reading (A21) as "proved here" would be over-reading it; the verdict itself does not.
- **Is the near-null family unconditional?**
  **Yes.** Φ, g_k = (∂²−1/4)∂^kΦ, the vanishing of both pole moments and the vanishing of F_k at every nontrivial zero
  use only the Gaussian Poisson identity, the ξ functional equation and analytic continuation. Both factors of each
  explicit-formula summand vanish for *every* zero regardless of its real part, so no zero is assumed to lie on the
  critical line and no unknown zero is used to select a parameter. My Q(g_k)=0 check used the digamma symbol and the
  theta-series prime correlations only — no zero locations entered it at all. The family therefore refutes a uniform
  positive floor unconditionally, and it says nothing whatever about the sign of Q.

## 10. What would still kill the near-null argument (for the next reviewer)
Not the theta factor, not the conjugation, not the X-continuity, not the cutoff — those are now checked numerically and symbolically.
The remaining exposure is entirely (i) the CC20 sufficiency statement behind the RH leg of (A21), and (ii) the uniform-in-R
vertical-decay claim in (A27) if someone insists on an explicit constant. Neither touches (A14), which remains the unpaid inequality.
