# SEMISIGNCHECK — independent check of PROSHKA_VERDICT_GOAL058_SEMILOCAL_SIGN_MECHANISM_2026-09-06

Object: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_SIGN_MECHANISM_2026-09-06.md` (690 lines)
Definitions from parent `..._SEMILOCAL_SONIN_SECOND_EXPRESSION_2026-09-06.md` (692 lines): (6) block matrices §1 Lemma 3; (11) Sonin projector §3 Lemma 4; (14)-(15) `L_S`,`Q`,`P_02`,`a(t)`,`D(v)` §4; (16) `c_A`; (17) `18` bound.
Scripts: `chk1.py chk2.py chk3.py chk45.py chk4b.py chk7.py` in this directory. No source outside the four permitted was opened.

**Bottom line: no error found. All eight items check out. RESULT codes Q1=PARTIAL_WITH_PRECISE_REMAINDER, Q2=OBSTRUCTION_NAMED, Q3=COMPUTATION_SPECIFIED stand unchanged.** Four notes (N1-N4) are cost/scope remarks, not defects.

---

## 1. Lemma 1, eq. (3)-(4) — CORRECT

Parent (6): `D_n = [[α², αs],[αs, −α²]]`, `s=√(1−α²)`. Trace 0, det `−α²` ⇒ eigenvalues `±|α_n| = ±a_n`. Explicit eigenvectors (the verdict says "computed from the matrix in parent (6)" but does **not** print them — supplied here):

    e_n^+ ∝ (α² + |α|, αs),      e_n^- ∝ (αs, −(α² + |α|)).

`D = Σ_n a_n(|e_n^+><e_n^+| − |e_n^-><e_n^-|)` ⇒ `Tr(T_v*T_v D) = Σ_n a_n(‖T_v e_n^+‖² − ‖T_v e_n^-‖²)`; subtract `ℓ‖v‖²` from (1) ⇒ (3). Rearranged ⇒ (4).
Numeric (`chk1.py`): random α, random psd `T*T`: `D e^± ∓ a e^± = 2.8e-17`, `<e^+,e^-> = 0`; single block `Tr(T*T D)=0.004202962628` vs RHS identical, diff `2.05e-16`; 6-block sum `−1.019261032871` both sides, diff `0.00e+00`.
Injectivity remark (§1) also correct: `T_v` is convolution by `v`, multiplier `v̂` entire (Paley–Wiener) and ≢0 ⇒ nonzero a.e. ⇒ injective on `L²`, so blockwise annihilation `T_v e_n^+ = 0` forces `e_n^+ = 0`.
**N1.** (3) inherits the parent's *declared* trace domain (parent §2 "Trace and convergence scope"); the verdict states this in its own proof. Not independently established here or there.

## 2. Lemma 2, eq. (6)-(7) — CORRECT

`B*B = (I−rU*)(I−rU) = (1+r²)I − r(U+U*)`, verified exactly (residual `0.0`, `chk2.py`). Compression by `P₀` ⇒ `G = (1+r²)(I − qA)`, `A = ½P₀(U+U*)P₀`, `q = 2r/(1+r²)`.
`q = 0.942809041582 = 2√2/3` ✓. `(1+r²)(1−q) = 0.085786437626905 = (1−r)²` ✓ (identity `(1+r²)−2r=(1−r)²`).
`‖A‖ ≤ 1`: `½(U+U*)` is the real part of a unitary, norm ≤ 1; compression cannot increase it. Numeric: `‖½(U+U*)‖ = 1.000000`, `‖A‖ = 0.707107` ✓. `A = A*` ⇒ spec ⊆ [−1,1].
(7): on `x∈[−1,1]`, `Σ_{j=0}^{2d+1}(qx)^j = (1−(qx)^{2d+2})/(1−qx) > 0`; the gap to `1/(1−qx)` is `(qx)^{2d+2}/(1−qx) ≥ 0` (even exponent — this is exactly why the odd top index `2d+1` is used) and `≤ q^{2d+2}/(1−q)`; divide by `(1+r²)` and use `(1+r²)(1−q)=(1−r)²=a_*²` ⇒ `ε_d = q^{2d+2}/a_*²`. Numeric, `A=diag(U[−1,1])`, dim 12, `d∈{0,1,2,3,5}` × 3 random draws: `min eig R_d > 0`, `min eig(G⁻¹−R_d) ≥ 0`, `min eig(R_d+ε_d−G⁻¹) ≥ 0` in all 15 cases.
Also verified (not asked): `T_{Bv} = BT_v = T_vB` (convolutions commute) ⇒ (8) `m(v)=‖T_vBP₀‖²_HS = n_∞(Bv)` is correct, and `n_λ(v)=Tr(C_vG⁻¹C_v*)` follows from parent (11).
**N2 (cost, not error).** `ε_d = 10.36·0.8889^d`. `ε_0=10.36`, `ε_30=0.303`, `ε_60=0.00884`. The verdict's own §6.3 tolerance `w₂/100 = 0.00490` needs `d ≥ 65`, i.e. **operator polynomial degree 131 and ~132 traces `Tr_{H0}(A^j C_v*C_v)`**, each with its own quadrature enclosure. The series converges as claimed; the certificate is expensive.

## 3. Eq. (9)-(11) — CORRECT

(9) is (7) sandwiched by `Tr(C_v·C_v*)`, plus `e = n − L_S` from (1); the Loewner/polarization step to (10) is standard.
(11): `X = XF + X(I−F)` gives three residual terms; two cross terms `≤ ‖X‖_HS‖H‖‖X(I−F)‖_HS` each, last `≤ ‖H‖τ²`, with `‖H‖ ≤ a_*⁻²` from `G ≥ a_*²I`. Total `a_*⁻²(2√m·τ + τ²)` ✓.
Numeric (`chk3.py`): 400 random trials, `n=30`, `H = G⁻¹` psd with `‖H‖ ≤ a_*⁻²`, random rank-M `F`: (11) held every time, worst `lhs/rhs = 0.2005`. Identity `τ_M² = m(v) − Σ_{j≤M}‖Xe_j‖²` verified to `1e-8`.

## 4. Lemma 3, eq. (12) — CORRECT; proof complete under one imported hypothesis

Pole conditions: for `w = (∂²−1/4)g`, `g` compactly supported, two by-parts give `∫w e^{±x/2} = ∫g(e^{±x/2})'' − ¼∫g e^{±x/2} = 0` because `(e^{±x/2})'' − ¼e^{±x/2} ≡ 0` (sympy: `0` for both signs). Numeric with the actual `V_j h`, `h=exp(−1/(1−x²))`, `M_j = 6π/log2`: `A_±(V_jh) = 4.7e-35` ✓.
Expansion `V_jh = e^{iMx}[−h + (2i/M)h' + M⁻²(h''−h/4)]` reproduced exactly.
Digamma: `m_A(t) = Re ψ(1/4+it/2) − log π`. `m_A(0) = −5.37218341923 = −c_A` (independent confirmation of parent (16)). `m_A(t) − log|t| → −log 2π = −1.837877066` (t=10: −1.838294; t=10⁸: −1.837877). So `m_A(t)=log|t|+O(1)` ✓. I also verified independently that `m_A` **is** the Fourier multiplier of `D(v)−c_A‖v‖²`: `2∫₀^∞a(t)(1−cos τt)dt − c_A` equals `Re ψ(1/4+iτ/2)−log π` at τ=0,0.5,1,3,10 to 12 digits (`chk4b.py`).
`S_λ → 0` strongly: `ran S_λ ⊥ ran P_λ = {supp ⊆ x ≤ log λ}` ⇒ `ran S_λ ⊆ {f=0 a.e. on x≤log λ}`; ranges decrease in λ; a decreasing net of projections converges strongly to the projection onto `∩ ran`, which is `{0}`. Correct consequence of the parent's definition `S_S=(ran P_T ∨ ran Q_W)^⊥`. Then `‖T_vS_λ‖_HS → 0` by dominated convergence on `‖S_λK*e_j‖²`.
Quantifiers: `∃j₀ ∀j≥j₀ ∃λ₀(j,H) ∀λ≥λ₀` — sound. `H` finite-dimensional ⇒ seminorm convergence and form convergence are uniform on its unit sphere; `V_j` injective on `C_c^∞` (else `e^{iMx}h ∈ span{e^{±x/2}}`, not compactly supported). `C_{V_jh}(log2) → C_h(log2) > 0` because `e^{iM_j log2}=1` — verified: `C_v(t)=Re[e^{iMt}∫ḡ g(·+t)]`.
The one imported hypothesis is again **N1** (`T_vS_1` Hilbert–Schmidt "by the established trace domain"). Declared, not proved.
**N3 (scope, not error).** The mechanism of (12) is thin: `e_λ = n_λ − L_S`, `n_λ → 0`, so (12) reduces to `L_S > 0` on high-frequency packets, which is the classical `m_A(t) ≈ log|t| → +∞`. The prime-2 term is genuinely nonzero but `O(1)` against `log M_j → ∞`, so "prime-active" is true but the prime plays no role in the sign. The verdict's own §2 Scope paragraph says as much.

## 5. Eq. (13), (15), (16)-(17) — CORRECT

(13): `A_± = C ± S` ⇒ `2Re(A_+ conj(A_-)) = 2(|C|²−|S|²) + 2Re(SC̄ − CS̄)` and `SC̄ − CS̄` is purely imaginary. sympy: difference `= 0` exactly.
(15): `T_{U_cv} = U_cT_v` (convolution), `‖U_cX‖_HS = ‖X‖_HS` — no commutation with `S_{S,λ}` needed; `L_S` depends only on `‖v‖₂`, `C_v(·)`, `D(v)`, all translation-invariant ⇒ `e_λ(U_cv)=e_λ(v)` ✓.
`h_d = cos(πx/2d)1_{|x|≤d}`: sympy exactly `‖h_d‖² = d`, `‖h_d'‖² = π²/(4d)`, ratio `π/(2d)` ✓; `h_d ∈ H¹` (vanishes at ±d).
Mollification: `‖(h_d*η_δ)'‖ ≤ ‖h_d'‖`, `‖h_d*η_δ‖ ≥ ‖h_d‖ − δ‖h_d'‖` ⇒ `‖v_b'‖ ≤ (π/2d)/(1−δπ/2d) = π/(2d−δπ) = π/(2b−δ(2+π))` with `d=b−δ` ✓ (algebra exact).
`∫₀^∞ t²a(t)dt = 2Σ_{n≥0}(2n+½)⁻³ = **16.1659674922** ≤ 18` ✓ (both computations agree to 12 digits; matches the "expect 16.166" target).
`c_A = γ + log(8π) + π/2 = **5.37218341923**` ✓ (verdict's 5.3721834192).
(16)-(17) at the three b: `b=3: −0.428913`; `b=4: −2.592786`; `b=6: −4.137425` — all `< 0` ✓. The verdict's rational argument at `b=3` also checks: `18·(22/7 / (6−δ(2+22/7)))² = 4.94725 < 5 < c_A` ✓ (margin only 0.053 — tight but valid).

## 6. Q2: (18), C99 scope, (19) — CORRECT

C99 `math_9811068.txt`. **Theorem 5** (line 1971, page footer 41 immediately above ⇒ **p.42**), verbatim: *"Theorem 5. Let k be a global field of positive characteritic and QΛ be the orthogonal projection..."* — condition (a) is printed as *"Trace (QΛ U (h)) = 2h(1) log′ Λ + Σ_v ∫′_{k_v*} h(u−1)/|1−u| d∗u + o(1)"* with *"Let h ∈ S(Ck ) have compact support"*. Verdict (18) reproduces this exactly, including the primed normalization and the per-`h` `o(1)`. **The positive-characteristic scope claim is CORRECT.**
Number-field modification is printed **afterwards**, pp.45–47: *"Let us now explain how the above results extend to number fields k"* (p.45), *"The first obvious difficulty is that when v is an Archimedian place there exists no non-zero function on kv which vanishes as well as its Fourier transform for |x| > Λ"* (p.46), closing with *"This gives the analogue of Lemma 1, Theorem 5, and Lemma 3."* (p.47). ✓ `SOURCE_CORRECTIONS.C99_Theorem5_as_printed_first_has_positive_characteristic_scope: true` is **CORRECT**.
**Lemma 3** (line 2068, between footers 43 and 44 ⇒ **p.44**, proof to p.45): *"Let us now show that b) implies a). We shall compute from the zeros of L-functions and independently of any hypothesis the limit of the distributions ∆Λ when Λ → ∞."* and *"Lemma 3. The limit of the distributions ∆Λ when Λ → ∞ is given by, ∆∞(f) = Σ_{L(χ̃,½+ρ)=0} N(χ̃,½+ρ) ∫_{z∈iR} f̂(χ̃,z) dµρ(z)"* with *"dµρ(z) is the harmonic measure of ρ with respect to the line iR ⊂ C"*. **So the harmonic-measure claim is CORRECT** and `C99_also_computes_a_harmonic_measure_limit_beyond_Poisson_inclusion: true` holds. (Poisson appears only inside the proof at (29).)
Harmonic-vs-arithmetic mode comparison also checks: `∫e^{itx}(1/π)|σ|/((t−γ)²+σ²)dt = e^{iγx}e^{−|σ||x|}` ≠ `e^{(σ+iγ)x}`; symmetric pair gives `2cosh(σx)` vs `2e^{−|σ||x|}` ✓.
"Inclusion alone does not compute `r_Λ`": correct — C99 uses (a) explicitly (*"One has Trace (SΛ V (f)) = 2f(1) log′ Λ, thus using a) we see that the limit of ∆Λ..."*), and `Q'=0` trivially satisfies (23).
(19) `W_Λ S_{S,Λ}=0`: `W_Λ = 1_{[−logΛ,logΛ]} = W_ΛP_Λ` and `P_ΛS_{S,Λ}=0` ⇒ `W_ΛS=0` ✓. `R_Λ S = 0` from `0≤R_Λ≤W_Λ` and `<ξ,W_Λξ>=0` on `ran S`. Mutual non-domination argument valid. ✓
Finite-Euler tail (§5 Q2(b)): `(J_Sh)(x₀−j log p) = p^{−j/2}h(x₀)` since `J_S = Σ_{n∈M_S}n^{−1/2}U_{−log n}` and only `n=p^j` contributes when `supp h` has width `< log p` ✓.

## 7. Q3: (20)-(27) — CORRECT

(20) vs parent (14): with `F(t)=∫v̄(x)v(x+t)dx`, `2C_v(t)=F(t)+F(−t)` and `‖v(·+t)−v‖² = 2F(0)−F(t)−F(−t)`, so `<D,F>` and the `δ_{±j log p}` sum reproduce (14) exactly ✓. (21), (22) are then arithmetic on `N−E=L_S`; `w_{p^j}=(log p)p^{−j/2}` ✓. `2δ₀−δ_a−δ_{−a} ↦ ‖U_av−v‖² ≥ 0` ✓.
Convention identity: `2∫₀^∞a(t)(1−e^{−t/2})dt = **2.26394350735** = log2+π/2 = **2.26394350735**` ✓ (closed form `2∫₀¹du/((1+u)(1+u²)) = ½log2+π/4`, doubled). Hence `c_A = c₀ + log2 + π/2` exactly ✓ and consistent with parent (16).
(23) `S'₀`: derived independently. `G_r=(1+r²)I−rP₀(U+U*)P₀`, `G_0=I`, `(G⁻¹)'₀=+P₀(U+U*)P₀`; differentiating `B_rP₀G_r⁻¹P₀B_r*` gives `−U_aP₀ + P₀(U_a+U_a*)P₀ − P₀U_a*` = `−(I−P₀)U_aP₀ − P₀U_a*(I−P₀)` ✓. Numeric central difference (n=7, shift unitary, rank-3 `P₀`): `‖numeric − claimed‖ = 2.45e-12` against `‖claimed‖ = 2.449`; `S₀ = P₀` ✓. Not proportional to `U+U*` (`‖S'₀+(U+U*)‖ = 2.83 ≠ 0`) — the verdict's point stands.
(25): `F_{z_±}(t) = 2γ(t) ± (γ(t−a)+γ(t+a))` ⇒ `(F_{z_+}−F_{z_-})/4 = F_δ(t)` — verified to `0.000e+00` at t = 0, a, a−δ, −a, 0.5. Then `F_δ(0)=0` (contact drops), `F_δ(±a)=½` (prime term `−w_{p^j}`), `<D,F_δ> = −∫a(t)γ_δ(t−a)dt = −I_{a,δ}`. Full numeric with `u=η/‖η‖₂`, `δ=1/64`, `a=log2`: `<L_S,F_δ> = −0.511952223964`, `−w₂−I_{a,δ} = −0.511952223964`, **diff `0.00e+00`** ✓.
(26): `γ_δ(0)=1.0000000000`, `∫γ_δ = 0.0231441429 = δ‖u‖₁²` ✓, `I_{a,δ} = 0.02182315 ≤ 0.02265109 = δ‖u‖₁²·sup a` ✓.
(27): follows from `n−e=L_S` and `2δ<log2` (0.0312 < 0.6931) ✓.

## 8. CCM23 v2 source correction — CORRECT

PDF is v2 (`arXiv:2310.18423v2 [math.NT] 4 May 2024`). **Definition 4.5 (p.21)** is a *set* definition, not an operator theorem: *"Let λ > 0. The semilocal Sonin space Sλ(XS, α) is the subspace of the Hilbert space L2(XS)^{KS} defined as follows Sλ(XS,α) := {f ∈ L2(XS)^{KS} | f(x)=0 & FS f(x)=0 ∀x, |x| < λ}"*.
**Theorem 4.6 (p.23)**: *"Let S ∋ ∞ be a finite set of places and λ > 0. Then the map θS is a hilbertian isomorphism of the Sonin spaces θS : Sλ(R, e∞) → Sλ(XS, α) where α is the normalized character."* — a bounded invertible map, not an isometry, and **no self-adjoint operator, no domain, no commutation with `P_λ` or `Q_λ`**. A grep of the whole v2 text for "commut" finds only the grading commutation (line 375) and commutative diagrams.
**Definition 2.2 (p.6)** confirms the domain caveat verbatim: *"This definition is formal inasmuch as it does not give precisely the domain of the operator. ... It is clear in that case that the obtained formal operator is symmetric and finding the relevant selfadjoint extension is delicate."*
⇒ `CCM23_Def4_5_Thm4_6_are_not_a_commuting_prolate_operator_theorem: true` is **CORRECT**.
**N4.** For completeness: a commuting prolate operator *does* exist at the single archimedean place — C99 (32), p.46, `H_Λψ = −∂((Λ²−x²)∂)ψ + (2πΛx)²ψ`, *"actually commutes with the projections PΛ, P̂Λ"* (Landau–Pollak–Slepian). The verdict's correction is about the **semilocal** claim and about CCM23's locators, and remains correct; but "a commuting operator does not exist" would be false at `S={∞}`, and the verdict does not say that (§1: "Even a proven operator commuting with both projections would label the blocks without determining the profiles" — that reading is right).

---

## Consequence for the RESULT codes

None. Every derivation I could redo independently reproduced the verdict's statement, constant and sign; every source sentence I could locate said what the verdict says it says, at the page the verdict cites (C99 pp.42, 44–45, 45–47; CCM23 v2 pp.6, 21, 23; C20 Thm 4.7 p.27 "∀f ∈ C_c^∞(R*_+)" — arbitrary support, as (8) requires; C20 Thm 6.11 p.48 does carry its support + `ĝ(−i/2)=0` conditions).
The verdict's self-declared limits are also accurate: `FROZEN_CUTOFF_CLASS_SIGN_PROVED: false`, `NUMERICAL_RUN_PERFORMED: false`, and the statement that (10)'s upper matrix `≤ 0` is the first unproved inequality. N1 (imported HS/trace domain), N2 (degree ~131 for the verdict's own tolerance), N3 (the (12) class is prime-active but prime-irrelevant to its sign) and N4 are the four things a reader should carry forward; none of them changes Q1/Q2/Q3.
