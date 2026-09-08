# SCREWCHECK — independent adversarial audit of PROSHKA_VERDICT_GOAL058_SCREW_2026-09-08.md

Checker: fresh Claude agent. Every number below is from my own sympy/mpmath run in
`/home/chirurgie/.claude/jobs/4b35770d/tmp/screwcheck/` (`c1.py`,`c2.py`,`c3b.py`,`c4b.py`,`c5.py`,`c6.py`,`c7.py`,`c8.py`,`c9.py`).
No repository file was modified. Definitions taken only from KERNEL (K6),(K16),(K19)–(K24) and the Suzuki screw card.
Constants: L=log2=0.693147180560, w=log2/√2=**0.490129071734274**.

## Item-by-item

### (1) §3 first-prime onset (S14)–(S18) — **CORRECT**
- **(S14) corner integral.** sympy: ∫₀^d∫₀^{d−u}(d−u−v)²dv du = **d⁴/12** exactly; doubled = d⁴/6. So ‖H_a‖_HS = d²/√6 and the 1/√6 is exact, not fitted. Independent check on the actual ramp kernel (|x−y|−L)₊ at a=0.5 (d=0.30685281944): quadrature ‖H_a‖²_HS = 1.47764198282643e−3 vs d⁴/6 = 1.47764198279881e−3 (rel. 1.9e−11). Projection non-increasing in HS: correct.
- **(S15).** I re-derived it, not read it. For u∈H¹₀(−a,a), Du=iu′ has ∫Du=0 so P_a is idle; the two i's cancel; two integrations by parts (boundary terms vanish on H¹₀) give Δq(u) = −∫∫ ū(x) g₂″(x−y) u(y). With g₂=w(|t|−L)₊, g₂″=w(δ_L+δ_{−L}) (the |t| kink at 0 contributes nothing since L>0). Hence Δq = −w[⟨u,C_au⟩+⟨u,C_a*u⟩]. **Sign and factor confirmed.**
- **Cross-convention check (independent channel).** The same quantity computed straight from (K6)'s prime sum, −w{⟨f,U_L f⟩+⟨f,U_{−L}f⟩} = −2w Re∫f̄(x)f(x−L)dx, agrees identically with the g₂″ route. The screw-g convention and the (K6) convention give the *same* prime-2 term with the *same* sign. This is a real consistency result, not a transcription.
- **Strip algebra.** I₋=(−a,a−L), I₊=(L−a,a), each of length d, disjoint iff a≤L. C_a*C_a=1_{I₋}, C_aC_a*=1_{I₊}; C_a²=0 needs a<L (regime a<½log3=0.549306<L ✓). V=C_a+C_a* then satisfies V²=1_{I₋∪I₊}, a symmetry ⇒ ‖V‖=1, eigenvalues ±1 of infinite multiplicity. **(S16) ‖A_a−A_a^{(0)}‖=w confirmed on the stated regime.** Not rank one: correct.
- **(S17)–(S18) detector, numeric.** η(x)=exp(−1/(s(1−s))), s=x/d, on (0,d); k=(∂²−¼)η, ‖k‖₂=1.000000000; M₊(k)=−6.4e−36, M₋(k)=−5.5e−36 (zero to working precision, and exactly zero analytically since (∂²−¼)e^{±x/2}=0). f_±=2^{−1/2}(U_{−a}k ± U_{L−a}k) at a=0.5:
  | | ‖f‖² | M₊ | M₋ | ∫_{I₋}f(x+L)f(x) | ΔQ |
  |---|---|---|---|---|---|
  | f₊ | 1.000000000 | −1.5e−38 | −1.5e−38 | **+0.5** | **−0.490129071734274 = −w** |
  | f₋ | 1.000000000 | +9.8e−39 | −9.8e−39 | **−0.5** | **+0.490129071734274 = +w** |
  Exact to full precision. (S18) **CORRECT**; A2's "cross correlation exactly ±1/2" **CORRECT**.
- **Scoping flaw (minor, not a defect of §3).** The box (S16) carries the qualifier "(d>0)" only; the true qualifier is L/2<a≤L. I computed ‖C_a+C_a*‖ by discretisation (N=3000): 1.000000 for a=0.40,0.50,0.60,0.6931; **1.414214** at a=0.75; 1.732051 at a=1.5; 1.984229 at a=8 (→2, the symbol 2cos(Lξ)). So the boxed identity is false for a>L, though every use of it in the verdict lies in a<½log3. Recommend the box read "(L/2<a≤L)".
- §3.3's endpoint germ −2wd·Re{f̄(a)f(−a)} is **correct** as the d→0 leading term of (S17) (I₋≈(−a,−a+d), x+L≈a).

### (2) §4 monotonicity, λ_∞≤0, dichotomy (S24) — **CORRECT (modulo two [K] imports)**
- **(S21).** Support inclusion C_c^∞(−a,a)⊂C_c^∞(−b,b) plus the fact that Q of (K6) is window-independent ⇒ inf over the larger set is ≤. Trivially sound.
- **(S22).** Sound: g₀=(∂²−¼)Φ has F_{g₀}(z)=(z²−¼)Λ_ξ(z), vanishing at every zero, so Q[g₀]=0 by (K16); compact pole-null approximants give Rayleigh→0 with denominator→‖g₀‖₂²≠0. λ_∞≤0 follows. Imports (K16),(K24).
- **(S23)/(S24) transform bookkeeping — I re-derived it.** F_{U_b f}(z)=e^{bz}F_f(z) ✓. With j(z)=−z̄ (so jλ=−α+iβ for λ=α+iβ; j fixes exactly Re z=0), u_T = e^{−iβT}U_T h_λ − e^{iβT}U_{−T}h_{jλ} gives
  F_{u_T}(λ)=e^{−iβT}e^{(α+iβ)T}=**e^{αT}**, F_{u_T}(jλ)=−e^{iβT}e^{−(−α+iβ)T}=**−e^{αT}**, all other zero-values 0.
  (K16) then gives two equal terms: Q[u_T]=m·(−e^{αT})(e^{αT}) + m·(e^{αT})(−e^{αT}) = **−2m e^{2αT}** ✓. Norm: ‖u_T‖₂ ≤ ‖h_λ‖+‖h_{jλ}‖, T-independent (|e^{±iβT}|=1, translations isometric) ✓. Rayleigh ≤ −2m e^{2αT}/C → −∞ ✓. Pole-nullity of h_λ is automatic from the (z²−¼) factor in (K21), and survives translation.
- **Verdict: the dichotomy (S24) stands.** Its two inputs I did not re-derive are (K16) (signed explicit formula on ℰ) and (K19)–(K22) (existence/normalisation of h_λ). Given those, the derivation is airtight.

### (3) §5.1 poles — **CORRECT**, and the version fact is **CONFIRMED**
- **(a) R₁.** With ξ(s)=½s(s−1)π^{−s/2}Γ(s/2)ζ(s), X(t)=ξ(½−it) is real. γ₁=14.134725142, γ₂=21.022039639. Rolle ⇒ interior critical point; I located **t\* = 15.585708589829342**, with **X(t\*) = −8.01562752967474e−4 ≠ 0**, X′(t\*)=−3.2e−60 (zero), X″(t\*)=4.4896e−4>0. A5's identity ξ′_s(½−iz)=iX′(z) verified. Blow-up: |R₁(t\*+ε)| = 4.34e5, 4.34e6, 4.34e7, 4.34e8 for ε=1e−3…1e−6, and |ε·R₁(t\*+ε)| → **433.700** — a genuine simple pole with nonzero residue.
- **(b) R₂.** L_ξ(2) from the closed form 3/2 − ½logπ − ½γ_E + ζ′(2)/ζ(2) = **0.0690662315300007**, identical to a direct ξ′/ξ(2) evaluation. **<1** ✓ (the verdict's argument logπ=1.1447>1, γ_E>0, ζ′/ζ(2)<0 is valid). L_ξ(−1) = −0.0690662315300007 = −L_ξ(2) ✓ (from ξ(s)=ξ(1−s)). 1+L_ξ(−1)=0.930934>0; 1+L_ξ decreases through −1,−2,−5,−10,−30 (0.8856, 0.7569, 0.5763, 0.1527) to a root at **s\* = −42.2779170181904** (<−1 ✓), with **ξ(s\*)=2.7047828e11 > 0** ✓ and ξ(s\*)+ξ′(s\*)=7.3e−39. Then **z\* = i(s\*−½) = −42.7779170181904 i**, and |(z−z\*)R₂| → **93.188591**: genuine simple pole. (Note it sits in the *lower* half-plane, i.e. at a Hermite–Biehler zero of E — consistent with de Branges theory, no contradiction.)
- **(c) Cauchy/Weierstrass logic:** correct and trivial — a locally uniform limit of entire functions is entire, hence pole-free.
- **Version facts, fetched independently from arXiv:** v1 submitted 8 Jun 2026, v2 17 Aug 2026. v1 (1.12) RHS = `z² ξ(1/2−iz)/ξ′(1/2−iz)`; v2 (1.12) RHS = `ξ(1/2−iz)/(ξ(1/2−iz)+ξ′(1/2−iz))`. **The verdict's R₁/R₂ split is exactly right.** v2 §6.3 ("Eigenfunctions of 𝒟_a*") and §7.8 (heuristics for the limit) exist as claimed. Both versions require of φ only "≠∞ for any a>0 and z∈ℂ" — **not** holomorphy. See adjudication below.

### (4) §5.2 toy (S26)–(S27) — **CORRECT**
Sherman–Morrison verified: (cI+|1⟩⟨1|)v_+ = e^x pointwise to 18 digits at x=−0.7,0,0.9 for c=1,2 (⟨1,1⟩=2, ⟨1,e^x⟩=2sinh1). Reflection gives equal T-norms: ‖v₊‖²_T=‖v₋‖²_T = 1.78539661379126 (c=1), 1.12288128115260 (c=2). Feeding (1.11) with θ=π and quadrature, W_num agrees with the claimed closed form −(4i sinh1/c)(cos z − (2/(c+2))sin z/z) to 14+ digits at z=0.7, 1.9, 3.3+0.4i for both c (the reductions (z−i)/(1+iz)=(z+i)/(iz−1)=−i and sinh(1+iz)+sinh(1−iz)=2sinh1·cos z are exact). Bracket(0)=c/(c+2)>0, bracket(π/2)=−(2/(c+2))(2/π)<0. **Least positive roots: 0.96740263817469972 (c=1) and 1.16556118520721131 (c=2), separation 0.19815854703251**, both in (0,π/2). Shared nonzero zero impossible: subtracting forces sin z=0, then cos z=±1≠0. **The abstract shift-independence inference is refuted.**

### (5) §5.3 (S28)–(S29) — **CORRECT**
(S28) is one line: Q = t_σ + σ⟨·,·⟩₂, so Q[Σc_je_j] = Σ|c_j|² + σ·(physical Gram form). (S29): Q(f,g)=⟨f,g⟩_T + σ⟨f,T^{−1}g⟩_T ⇒ representative I+σT^{−1}, eigenvalue 1+σ/(μ−σ) = μ/(μ−σ), denominator >0 ⇒ sign preserved. Control: A=diag(−1,1), σ=−2 ⇒ T=diag(1,3)>0, I+σT^{−1}=**diag(−1, 0.3333333)** = (μ/(μ−σ)) ✓. §4.3's control also checks: v=(1,1)/√2 has ⟨v,Av⟩=0.0 and ‖Av‖=1.0.

### (6) §6.1 budget — **VALID but loose; the "16" is right and the doubling is unstated**
c_A = γ_E+log(8π)+π/2 = **5.37218341922567 < 7** ✓. 4 sinh1 = **4.70080477458 < 6** ✓ (2sinh1=2.35040 <3 ✓). max_x (log x)/√x = 2/e = 0.735759 < 1 ✓. The crude 16 = **2 (two shift directions in (K6)) × 8 integers × 1** — arithmetically correct, but the text writes only "eight integers … each <1", never naming the factor 2; a reader gets 8, not 16. Recommend one clause. **Sharper values:** Σ_{m=2..9}Λ(m)/√m = **3.53750281427** (doubled 7.07500562853); at a=1 only m≤7 are active (e²=7.389), Σ_{m=2..7} = **2.92623418218** (doubled 5.85246836435). Sharp floor c_A+2Σ+4sinh1 = **15.9254565582**, i.e. A₁ > −16I. The stated A₁>−29I is therefore true but ~13 loose; σ=−32,−33 are legal and the claimed gaps 3 and 4 hold a fortiori. Budgeting m=8,9 is over-budgeting, expressly permitted by A4. (S31)'s constant also checks: ‖e^{izx}‖_{L²(−1,1)} ≤ √2 e^{|Im z|}, so the √2 e^{|Im z|}(|z−i|+|z+i|)ε shape is right.

### (7) Appendix B, C₄ — **CORRECT, no R-dependence leaks**
χ_R^{(k)}(x)=R^{−k}χ^{(k)}(x/R), so |χ_R^{(k)}|≤D_k for R≥1 (with room to spare). Leibniz on a_R^{(j)} = (χ_R v)^{(j+2)} − ¼(χ_R v)^{(j)} gives exactly B_j. Then ‖∂^q(e^{sx}a_R)‖₁ ≤ Σ_j C(q,j)|s|^{q−j}B_j ≤ Σ_j C(q,j)2^{−(q−j)}B_j for |s|≤½, using |e^{sx}|≤e^{|x|/2}. Applying (1−∂²)² and integrating by parts against e^{iTx} (boundary terms vanish, χ_R compact) gives (1+T²)²|F| ≤ ‖h‖₁+2‖h″‖₁+‖h⁗‖₁, which is precisely the printed three-block C₄. All V_j are fixed integrals of the fixed v=J_λ^rΦ. **No R enters.**

### (8) §2.2 erratum detector — **HALF DERIVED, HALF ASSERTED**
Derivable half, verified numerically. ψ even real ⇒ ψ′ odd ⇒ Dψ=iψ′ odd ✓ (trivial). For ψ(x)=cos²(πx/δ) on |x|<δ/2, evaluating (K6) term by term (D-form by quadrature, prime terms zero for δ<log2, pole term 2M₊M₋≥0):
| δ | ‖ψ‖² | D[ψ] | prime | pole | **Q[ψ]** | Q/‖ψ‖² |
|---|---|---|---|---|---|---|
| 0.2 | 0.075 | 0.4340124691 | 0 | 0.020006536 | **+0.05110524813** | 0.681403 |
| 0.05 | 0.01875 | 0.1349626676 | 0 | 0.0012500255 | **+0.03548425402** | 1.892494 |
**Q[ψ]>0 confirmed.** One caveat on the *stated* floor: 2∫_δ^∞A₀ − c_A is positive only for **δ < 0.0856281664** (I solved for the threshold; at δ=0.2 the coefficient is −0.9047, yet Q is still positive because the t<δ part of D was discarded). So "with d small" is true but needs d≲0.086 to be the *stated* inequality; [K,(K14)]'s d=2^{−24} gives coefficient +14.2204.
**Asserted half:** that the even-time extension forces 𝒫̂_{Dψ}=0 on odd input rests entirely on [S23]'s printed definition of 𝔓_t, which the verdict labels READ but does not reproduce. I cannot verify it from the material I was given.

## Tight spots
1. **(S16)'s printed qualifier "(d>0)"** is wrong outside a≤L (‖V‖=1.414214 already at a=0.75). Harmless inside §3, but the box travels.
2. **The §5.2 toy kills shift-independence at *fixed θ*.** Cor. 1.6 lets θ=θ(a) float. The verdict says this ("An adjustment of theta is an additional object"), so the scoping is honest — but the kill is weaker than the table row reads at a glance.
3. **§6.1's "16"** needs the words "two shift directions"; and the sharp floor is −16, not −29.
4. **(S24) is only as strong as (K16) and (K19)–(K22).** Neither was re-derived here or in this verdict; both are [K] imports under a separate audit.
5. **s\* = −42.28 is far out.** The verdict's "some s\*<−1" is correct but the reader should not picture it near −1; 1+L_ξ decays like ½log|s| and only crosses zero at ≈−42.3.

## First asserted-not-derived step
**§2.2: "The even-time definition makes 𝒫̂_{Dψ}=0."** Everything preceding it in §1 is either derived in-document, explicitly conditional, or a labelled citation. This is the first load-bearing step that is neither derived nor checkable from the supplied definitions. (Second: §3.4's "the deficiency formula … has a weak-form repair" — the repair sketch is given, but that it repairs *Section 6.2's* actual step is asserted.)

## Adjudication of the three registrations
- **P_SCREW_FIRST_PRIME_SHIFT_AUDIT, p=0.94 → CONFIRMED.** I accept (S14)–(S20): the d⁴/6 constant, the −w(C_a+C_a*) identity with its sign, the strip algebra, ‖·‖=w with infinite-multiplicity ±1, and the pole-null two-sided detector giving exactly ∓w. Every one reproduced independently. The one blemish is (S16)'s qualifier, not its content. Calibration comment: 0.94 was if anything too modest — these are elementary and were going to survive.
- **P_SCREW_QUOTIENT_AND_LIMIT_DICHOTOMY_AUDIT, p=0.88 → CONFIRMED, conditional on the [K] imports.** The completion dictionary (S5)–(S9) is internally sound (I re-derived (S8)'s moment matrix [[1,e^{−R}],[e^{−R},1]], the literal inverse, translation-invariance of Q *including its pole term* — M₊(U_bf)M₋(U_bf) is b-independent — and the O(e^{−R/2}) Q-norm decay), and it is honestly flagged as premised on positivity. (S24) survives with no positivity premise. The conditionality on (K16)/(K19)–(K22) should be stated in the registration text; as written it reads self-contained.
- **P_SCREW_SOURCE_SHIFT_SEPARATED, p=0.70 → CANNOT BE SCORED.** It is a prediction about the outcome of the §6 computation, and **no run was performed** (the verdict itself records NUMERICAL_RUN_PERFORMED: false). Nothing in my audit moves it. The one thing I can report is that its declared *prerequisite* — the analytic toy control detecting different roots for c=1,2 — passes with separation 0.198158547, so the gate in front of the run is open.

## Two plain statements
1. **The dichotomy (S24) stands.** λ_∞=0 under RH, λ_∞=−∞ if an off-line zero exists. I reproduced the transform bookkeeping (F_{u_T}(λ)=e^{αT}, F_{u_T}(jλ)=−e^{αT}, Q[u_T]=−2m e^{2αT}) and the T-uniform norm bound from scratch. It is a genuine theorem given [K]'s (K16) and h_λ construction, and it selects neither branch.
2. **The pole obstruction to Cor. 1.6 *as printed* does NOT stand.** The two pole facts are real — I located both poles and their residues — but I also fetched both printed statements: φ(a,z) is required only to satisfy "≠∞ for any a>0 and z∈ℂ", never to be holomorphic. A locally uniform limit of non-holomorphic e^{φ}W may perfectly well have poles. What the poles do refute is the **strengthened holomorphic-gauge reading**, under which e^{φ}W is entire and the limit must be entire — there the hypothesis is unsatisfiable and the implication is vacuous, not false. The verdict's own header flags (`COROLLARY_1_6_LOGICAL_IMPLICATION_REFUTED: false`, `LITERAL_ALL_C_HOLOMORPHIC_GAUGE_LIMIT: impossible`) are correctly scoped; only the §5.1 prose ("A precise literal obstruction") invites the stronger misreading.

**No DEFECT found.** One scoping error ((S16)'s qualifier), one exposition gap (the factor 2 behind "16"), one threshold left implicit (δ<0.0856 in §2.2). All eight items check out on my own computation.
