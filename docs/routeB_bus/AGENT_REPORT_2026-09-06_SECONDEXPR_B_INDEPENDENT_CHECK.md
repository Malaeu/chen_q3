# SEBCHECK — independent check of PROSHKA_VERDICT_GOAL058_..._SUZUKI_KERNEL_IDENTITY_2026-09-06

Sources opened: arXiv:2301.00421v3 (`suzuki.pdf`, sha256 e4100e52…, "Version of November 10, 2025")
and the verdict. Nothing else in the repo — in particular **[R1] was not opened**; the project's Q
and c_A are re-derived below from the paper's own explicit formula (3.3).
Scripts: c1 (constants), c2 (Lemma 2), c3 (Volterra), c4 ((1.6) vs (3.2)), c5 (g). mpmath, dps 20–30.
pdftotext drops overlines; they are restored where the paper's own text fixes them.

## 1. SOURCE CONVENTION — **CORRECT**
Verbatim, p.3 after (1.6): "for a nonnegative real number t and a complex number z, where Λ(n) is the
von Mangoldt function … **For negative t, we set St(z) := S−t(z).** The definition of Pt(z) is quite
complicated." Verbatim, §3.1 after (3.2): "for nonnegative t. **For negative t, we set Pt(z) := P−t(z).**
The series on the right-hand side of (3.2) converges absolutely and uniformly…".
(1.7)/Prop.1.3: "P̂ϕ(z) := ∫_{−∞}^{∞} S♯t(z) ϕ(t) dt = ∫_{−∞}^{∞} \overline{St(z̄)} ϕ(t) dt", with
"F♯(z) := \overline{F(z̄)}" (p.1) and (1.8) "(Dψ)(t) := iψ′(t)".
CONFIRMED: P̂_{Dψ} ≡ 0 for every even ψ ∈ C_c^∞. Exactly three parity facts:
(i) ψ even ⇒ ψ′ odd ⇒ Dψ odd; (ii) the printed rule makes t ↦ S_t even as an L²-valued map, and ♯
acts pointwise in z, so t ↦ S♯_t(x) is even too; (iii) Prop.1.2+1.3 (L² membership, local-uniform norm
bound) make the Bochner integral of the odd L²-valued integrand exist and vanish. No zero property used.
Hence printed (1.9) forces ⟨ψ,ψ⟩_W = 0 for all even ψ — false already under RH (positive definiteness,
stated p.1); item 2 makes it unconditional.
Independent second witness (verdict's (6)): K_ar(t,u)=G_g(t,u), g even, g(0)=0 ⇒ K_ar(t,t)=−2g(t),
K_ar(t,−t)=g(2t)−2g(t), while (EVEN) forces K_norm(t,t)=K_norm(t,−t); so R(t,t)−R(t,−t)=−g(2t).
Computed g: g(0)=0, g(.001)=−2.747e−3, g(.1)=−5.313e−2, g(1)=−4.401e−2, g(2)=−5.334e−2 — never 0;
g(t)=½t log t+O(t) near 0 confirmed. So (4.4) fails inside the paper already for t>0>u.
This is a definition defect, not RH.

## 2. LEMMA 2 — **CORRECT** (Q form and c_A also verified against the paper)
From (3.3) with φ=ψ∗ψ̃, φ(0)=‖ψ‖², a(x)=e^{x/2}/(e^x−e^{−x})=e^{−x/2}/(1−e^{−2x}) (= verdict's a), and
φ(x)+φ(−x)−2φ(0)=−‖ψ(·+x)−ψ‖²:
Q(ψ)=D(ψ)+2Re(A₊Ā₋)−2Σw_n Re C_ψ(log n)−[γ+log4π+2∫₀^∞a(x)(1−e^{−x/2})dx]‖ψ‖², A_±=∫ψe^{±t/2}.
Analytically ∫₀^∞a(1−e^{−x/2})dx = ½log2+π/4 (u=e^{−x}, then u=w², giving ∫₀¹2dw/((1+w)(1+w²))),
so the bracket = γ+log8π+π/2 = c_A **exactly**. Numerics: 2∫ = 2.2639435073548419286 = log2+π/2 (29 d.p.);
c_A = 5.3721834192256655822. The verdict's Q, a(t) and c_A are the paper's own objects.
Each inequality: a(t)≥1/(4t) on (0,1] (1−e^{−2t}≤2t, e^{−t/2}≥0.6065>½) ✓; disjoint supports for t≥L
(supp = [−L/2,L/2], diameter L) ⇒ ‖Δ_tψ‖²=2‖ψ‖² ✓; 2∫_L^∞a ≥ ½log(1/L) = c_A+2 at L=e^{−2(c_A+2)} ✓;
pole term 2Re(A₊Ā₋)=2A₊²≥0 for real even ψ ✓; L*=3.9500522730e−7 < log2 so all C_ψ(log n)=0 ✓.
At L* the true value 2∫_{L*}^∞a = 17.7015, so Q/‖ψ‖² ≥ 17.7015−5.3722 = 12.33 (chain lossy but valid).
Mechanism at moderate L (exact quadrature, primes still absent):
| L | D/‖ψ‖² | pole/‖ψ‖² | **Q/‖ψ‖²** |
|---|---|---|---|
| 0.3 | 5.2587 | 0.4448 | **0.3312** |
| 0.05 | 7.0964 | 0.0741 | **1.7982** |
| 0.001 | 11.0174 | 0.0015 | **5.6467** |
Q>0 already at L=0.3; the bound ≥2 needs L≲0.04, so L* is amply sufficient. (KILL) holds
unconditionally: left norm exactly 0, right side ≥ 2π‖ψ_L‖² > 0.

## 3. VOLTERRA (11) — **CORRECT**, residual ~1e−25 relative
P_t(z) implemented literally from (1.6)/(7) (mpmath.lerchphi, zeta(s,derivative=1), digamma,
w_n=Λ(n)/√n over n≤e^t); g′ from (9); ∫₀^t e^{−iz(t−r)}g′(r)dr split at the hinges r=log2, log3 and at
the integrable log singularity at 0. h(z)=X′/X analytic (−i ξ′/ξ(s)) vs mp.diff: both −0.140710380083223.
| t | z | P_t(z) from (7) | \|LHS−RHS\| | rel |
|---|---|---|---|---|
|0.5|3|0.0405416605074+0.00101153279036i|1.1e−26|2.8e−25|
|0.5|10|0.0462709558325+0.00763197423071i|5.8e−27|1.2e−25|
|0.5|0.7|0.0401827159122+0.000222980146i|3.5e−26|8.8e−25|
|1.2|3|0.0442972298094−0.00234274631941i|2.2e−26|5.0e−25|
|1.2|10|0.0580930398541−0.0143978973443i|6.7e−27|1.1e−25|
|1.2|0.7|0.0436046096702−0.000524672745i|5.2e−26|1.2e−24|
ψ_d(1/4) = −4.2274535333762654081 = −γ−π/2−3log2 (29 d.p.) ✓. i·h(z) = 1/s+1/(s−1)−½logπ+½ψ_d(s/2)
+ζ′/ζ(s), s=1/2−iz, is d/ds log ξ combined with d/dz log X = −i(ξ′/ξ)(s) ✓.
Verdict's (8) is verbatim the paper's (4.3): its linear coefficient −½[ψ_d(1/4)−logπ] = c_A/2 exactly —
that is where c_A enters the paper. (9)=d(8)/dt verified term by term.
Transcription cross-check of (1.6) against (3.2) (400 zero pairs, t=0.5, z=3): 0.03788+0.0010115i vs
0.040542+0.0010115i; the real gap 2.66e−3 matches the analytic tail 2∫_{693}^∞(log(x/2π)/2π)x^{−2}dx
= 2.62e−3. Prop. 3.1 consistent.

## 4. (12) and (16) — **CORRECT**, one notational defect in the verdict
(12): for real x, X and X′=dX/dz are real, so (X′²+X²)/(X²+X′²)=1.
**Defect (presentational):** the verdict writes "E=X+iX′, E♯=X−iX′", but the paper's dash is d/ds
((1.3): "the dash … means differentiation of ξ(s) with respect to s"), giving E=X+X′, E♯=X−X′ (its own
(3.1)). The two agree only via ξ′(1/2−iz)=i·dX/dz; the verdict silently uses X′=dX/dz throughout
(h, u, v, (11), (21)) and never says so. With the paper's dash, X−iX′ is not real on R and (12) fails.
Its (1) is nonetheless right: (1+Θ♯)/2 = A/E♯ = X/(X−i dX/dz), since A=ξ(1/2−iz)=X.
(16): S_r=uA_r−ivB_r from (1)+(11) with A_r(x)=i(e^{−ixr}−1)/x, B_r(x)=∫₀^r g′(ρ)e^{−ix(r−ρ)}dρ.
Expanding S_r conj(S_s) with |u|²=1−ω and u v̄ = v ū = η real yields A_rĀ_s + πV(r,s) with V exactly (15).
Plancherel constant checked directly: Re∫(e^{−ixr}−1)(e^{ixs}−1)x^{−2}dx = π(r+s−|s−r|) = 2π min(r,s)
via ∫(1−cos ax)/x²=π|a|; odd part vanishes in p.v. Divide by π ⇒ 2min(r,s)+V ✓.
Also ∂_t∂_u[2min(|t|,|u|)] = 2δ(t−u)−2δ(t+u), so (18) is right; for the signed kernel |t|+|u|−|t−u|
the anti-diagonal delta is genuinely absent, so (OPEN) is the correct remaining target.

## 5. (17) — **CORRECT**
From (8): for t>0 off hinges g″ = −2cosh(t/2)+a(t) (using d/dt[e^{−t/2}Φ(e^{−2t},1,¼)] = −2a(t)),
plus jumps +w_n in g′ at log n. Regularising −a(|t|) ~ −1/(2|t|) in the stated Pf convention:
−∫_{|t|>ε}a(|t|)φ + 2φ(0)∫_ε^∞ae^{−t/2} = −½⟨Pf(1/|t|),φ⟩ − ∫(a(|t|)−1/(2|t|))φ + (log2−c₀)φ(0)+o(1),
c₀=γ+log4π ⇒ δ₀ coefficient = log2−γ−log4π = **−(γ+log2π)** ✓.
The stated integral is exact: ∫_ε^∞a e^{−t/2}dt = artanh(e^{−ε}), so −2∫ = log tanh(ε/2); numerically
ε=0.3: −1.90458085728337379834886104937 both sides; ε=0.01: −5.29832569983275924138357081715 both sides.
Its expansion −logε+log2+O(ε²) is what cancels the +logε of Pf.
r_*(0): a(t)=1/(2t)+1/4−t/24+O(t²) ⇒ 2−1/4 = 7/4; numerically r_*(1e−5)=1.7500002083614583,
r_*(1e−7)=1.7500000020833361 ✓. Signs (minus before finite part and before prime atoms) correct.

## 6. (25)/(27) — **CORRECT** (algebra); convergence machinery UNVERIFIED
For t=−τ<0: P_τ(−z)=Σm_γ(e^{−iγτ}−1)/(γ(−z−γ)); reindex γ↦−γ, legal because the paper states Γ is
symmetric with m_γ=m_{−γ} ("if γ belongs to Γ, then both −γ and γ̄ also belong to Γ with the same
multiplicity"); result Σm_γ(e^{iγτ}−1)/(γ(z−γ)) = the signed unconditional expansion ✓. No reality used.
This is exactly the extension (4.5)/(4.6) silently assume (they carry e^{−iγt}, e^{iγu} for both signs).
With F₊f=X/A and F₊ψ(z)=∫ψ(t)e^{izt}dt: ∫(e^{iγt}−1)f′(t−q)dt = −iγ∫e^{iγt}f(t−q)dt =
−iγe^{iγq}(F₊f)(γ) = −iγe^{iγq}X(γ)/A, and X(γ)=0 on Γ ✓ (boundary terms killed by the
double-exponential envelope). The conjugated transform meets γ̄, and X(γ̄)=0 since Γ is
conjugation-symmetric ✓.
UNVERIFIABLE here without substantial extra work: the Σ_γ ↔ ∫dq interchange and the L² convergence
behind (19)/(20)/(21), and Lemma 6's nonvanishing endgame. Shapes are plausible; not reconstructed.

## Minor
* The paper prints "≤ π Σ m_γ/|γ|²" before (4.5); with |e^{−iγt}−1|≤2 it should be 4π Σ m_γ/|γ|².
  The verdict's remark is right and the conclusion (finiteness) is unaffected.
* Verdict §5 "an actual identity would give ‖P̂(Dψ)‖² = πQ(ψ)" matches printed (1.9) ✓.

## Overall
Items 1, 2, 3, 5 and the checkable parts of 4 and 6 reproduce **CORRECT**, with Q and c_A derived from
the paper rather than from the verdict's own shelf. One presentational defect (undeclared change of the
meaning of the dash, item 4). This check confirms P_SEB_INDEPENDENT_PARITY_WITNESS and
P_SEB_INDEPENDENT_VOLTERRA_GRAM_SIGNS; P_SEB_INDEPENDENT_TRANSLATED_RADICAL_REPAIR is confirmed for
(27) and its algebra, and stays PENDING for (21)'s convergence machinery.
