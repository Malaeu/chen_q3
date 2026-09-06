# SEMICHECK — independent check of PROSHKA_VERDICT_GOAL058_SEMILOCAL_SONIN_SECOND_EXPRESSION_2026-09-06

Channels: own derivation + sympy/mpmath + source text. Nothing else in the repo opened.
Sources used: the verdict at `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_SONIN_SECOND_EXPRESSION_2026-09-06.md`;
`/home/chirurgie/.claude/jobs/4b35770d/tmp/bostconnes/{2006.13771,2602.04022,math_9811068,2106.01715}.txt`;
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/pdfs/2310.18423.pdf` — **the shelf copy is v2**
(`arXiv:2310.18423v2 [math.NT] 4 May 2024`, 30 pp.), not the v1 the verdict pins;
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/paper_weil/sections/{setup.tex,canonical.tex}`;
scripts `/home/chirurgie/.claude/jobs/4b35770d/tmp/semicheck/check{1,2,3}.py`.

## 1. Lemma 1 — finite-Euler intertwiners (1)–(2): **CORRECT** (locator defect, see §L)

- `J_S = Π(I−r_pU_{−a_p})^{-1} = Σ_{n∈M_S} n^{−1/2}U_{−log n}`: verified numerically to 1.7e−15 for
  S={2,3,5}, τ∈{0, 0.7, −2.3} (`check3.py`, corrected series with per-prime geometric truncation).
- Multipliers with `v̂(τ)=∫v e^{−iτx}`: `U_{−a}↦e^{iτa}` ⟹ `J_S ↦ Π(1−p^{−1/2+iτ})^{−1}`,
  `B_S ↦ Π(1−p^{−1/2−iτ})`. Identical to CCM23 v2 **(47)** (η_S) and **(57)/(58)** (θ_S). Convention
  matches: CCM's `F_µ g(s)=∫g(u)u^{−is}d*u`.
- `B_S = J_S^{−*}` with the stated shift signs: **CORRECT**. Checked two ways: `|B_mult − conj(1/J_mult)| ≤ 2.2e−16`;
  and structurally from CCM23 v2 Prop. 4.7(iii) `⟨θ_S f|η_S g⟩=⟨f|g⟩` ⟹ `θ_S^*η_S = I` ⟹ `θ_S = η_S^{−*}`.
- Bounds (2): `a_S ≤ ‖B_Sv‖/‖v‖ ≤ b_S`. For S={2,3,5}: a_S=0.068430, b_S=3.896920; sampled min|multiplier|
  = 0.068430 (a_S sharp, at τ=0), max = 3.826165 ≤ b_S. **CORRECT** (b_S valid, not attained).
- Multiplicative-line dictionary: `J_S ↔ u^{1/2}Σ_{n∈M_S}f(nu)` re-derived by hand (g(x)=e^{x/2}f(e^x) ⟹
  E(f)(e^y)=Σ n^{−1/2}g(y+log n)); `B_S` one prime `↦ w_∞f(u) − p^{−1/2}(w_∞f)(u/p)` is **verbatim** the
  display in CCM23 v2 proof of Prop. 4.6(ii). `F_S J_S = J_S F_∞` is Prop. 4.1(iii); `F_S B_S = B_S F_∞` is
  Prop. 4.7(i) (also derived by me from the first by adjoint+inverse). **CORRECT.**

## 2. Lemma 2 — position / compactness / dimension: **CORRECT**

1. `ran P_λ ∩ ran Q_λ = {0}`: J_S, J_S^{−1} contain only left shifts ⟹ both preserve `{x ≤ log λ}` and map it
   onto itself; transport gives f, F_∞f both compactly supported ⟹ f=0. Verified; and the model is legitimate:
   CCM23 v2 Def. 4.5 defines the semilocal Sonin space inside `L²(X_S)^{K_S}` by vanishing of f and F_S f on
   `|x|<λ`, i.e. in log coordinates exactly `(ran 1_{x≤logλ} ∨ ran F_S 1_{x≤logλ})^⊥`. Matches the verdict's P_T.
2. Compactness of `PF_SP`: `PF_SP = P J_S F_∞ P J_S^{−1}P` (legitimate: J_S^{−1}P = PJ_S^{−1}P); each
   `P U_{−log n}F_∞P` is HS; `Σ_{n∈M_S}n^{−1/2} = Π(1−p^{−1/2})^{−1} < ∞` gives norm convergence. **CORRECT.**
3. Infinite-dimensional common kernel: `ker P ∩ ker Q = (ran P ∨ ran Q)^⊥ = ran 𝖲_S`. The cited theorem is
   **Theorem 4.6 in the on-disk v2, p.23** (not "4.13"): *"the map θ_S is a hilbertian isomorphism of the Sonin
   spaces θ_S : S_λ(R,e_∞) → S_λ(X_S,α)"*, proved via "bounded with bounded inverse". CC20 states Sonin's
   infinite-dimensionality on **p.6** (verified by `pdftotext -f 6 -l 6`), as the verdict says.
   **The judge's reading is CORRECT: isomorphism, not isometry.** `⟨θ_Sf,θ_Sg⟩=⟨f,B_S^*B_Sg⟩` and
   `|1−p^{−1/2−is}|²≠1`; CCM23 §4.8 itself says "the choice of S plays a key role in fixing the inner product".

## 3. Lemma 3 — angle blocks (6)–(9) and the Halmos plant (10): **CORRECT**

sympy (`check2.py`), exact rationals and symbols:
- `F=[[α,s],[s,−α]]` satisfies `F²=I`; `Q=FPF=[[α²,αs],[αs,s²]]`; `D_S=P+Q−I=[[α²,αs],[αs,−α²]]`
  (S=0 on the generic block) — all three match (6) exactly. Eigenvalues of D_S: `{−α, +α}` ⟹ **±|α_n|** ✓.
- Block trace: `Tr(A D_S) = α²(X−Z) + αs(Y1+Y2)` — identical to (7).
- Covariance identity re-derived independently from `⟨Fξ,AFξ⟩=⟨ξ,FAFξ⟩=⟨ξ,A^{−1}ξ⟩=⟨ξ,Aξ⟩`:
  `X−Z = (α/s)(Y1+Y2)`. This is **CC20 (87), p.28** with `τ(n)=λ(n)/√(1−λ(n)²)` — exact match.
  Substituting: `Tr(AD_S) = (α/√(1−α²))(Y1+Y2)`, sympy-confirmed.
- Vanishing cross term for ρ≥1: `Pζ = (PF_SPξ − αξ)/s = 0`, so ζ ⊥ ran P, and `θ(ρ^{−1})=U_{−logρ}`
  preserves ran P. This is **CC20 (82), p.27**. (8) then reads
  `ε_{S,n}(ρ)=(α_n/√(1−α_n²))⟨ξ_n,θ(ρ^{−1})ζ_n⟩` = **CC20 (84)** verbatim in form. **CORRECT.**
- Exact Halmos plant (10): α=3/5, s=4/5, v=(2,1)/√5 (unit; it is the +3/5 eigenvector of D_S):
  `⟨v,(I−P−Q)v⟩ = −3/5` exactly, `𝖲v=0`. **CORRECT** (sympy, rationals).
- (4)–(5) import: C26 **(22), p.32** reads `−Σ_{v∈S}W_v(f) = log(TW)f(1) + Trace(ϑ(f)(1−P^S_T−P̂^S_W))`.
  With (3) `I−P−Q=𝖲−D_S` this gives exactly `L_S = N_S − E_S`, `E_S = Tr(ϑD_S) − ℓk(1)`. Sign of the
  contact term **CORRECT**; C99 Thm 4 is indeed about `R_Λ = P̂_Λ P_Λ` ((13), p.30) with o(1), as the verdict says.

## 4. Lemma 4 — corrected Sonin projector (11), comparison (12): **CORRECT**

Hand derivation: `⟨B_Su,B_Sv⟩=⟨u,G_Sv⟩` on H_0 ⟹ `W=B_S|_{H_0}G_S^{−1/2}` is an isometry onto `B_S(H_0)`,
`WW* = B_S𝖲_∞G_S^{−1}𝖲_∞B_S^*` = (11); `a_S²≤G_S≤b_S²` from (2); `‖ϑ(k)𝖲_S‖_HS=‖ϑ(k)W‖_HS` and two
applications of `‖BX‖_HS≤‖B‖‖X‖_HS` give (12) in both directions.
Numerical plant (`check3.py`, n=40, rank-12 Sonin, B_S normal with spectrum in the annulus [a_S,b_S]):
W-isometry error 2.9e−15; `𝖲_S=WW*` error 9.8e−16; `𝖲_S²=𝖲_S` error 2.2e−16; rank 12; G-spectrum inside
[a_S²,b_S²]; (12) held in all 4 random trials. **CORRECT.**

## 5. (13) prime shells, (14)–(16) dictionary, Lemma 5 constant: **CORRECT**

- (13): shells `|u|_p=p^{−j}` ⟹ `|1−u|_p=1`, `h(u^{−1})=h(p^j)=p^{−j/2}k(p^j)`; shells `|u|_p=p^{j}` ⟹
  `|1−u|_p=p^j`, `h(p^{−j})/p^j=p^{−j/2}k(p^{−j})`. With shell mass log p:
  `W_p(k)=log p Σ_j p^{−j/2}(k(p^j)+k(p^{−j}))`. Independently corroborated by **CC20 (149)** and by
  setup.tex's `w_n=Λ(n)/√n`: for n=p^j, `w_n=log p·p^{−j/2}`. `θ(k)=U(h)`, `h(ρ)=ρ^{−1/2}k(ρ)` is right
  because C99's U lacks the λ^{−1/2}. C99 Thm 4 is on **p.31**, Appendix II normalization on **pp.71–72** ✓.
- (14)/(15) vs setup.tex `\eqref{eq:Q}` `Q(g)=𝒟(g)−c_AH(g)+2Re(A_+Ā_-)−2Σ_{n≥2}w_nC_g(log n)`: splitting
  `Σ_{n≥2}=Σ_{p∈S_f}+Σ_{p∉S_f}` gives exactly (15). **Yes: L_S omits exactly P_02 and the primes outside S**
  (item 6's precondition); `a(t)=e^{−t/2}/(1−e^{−2t})` identical in both. **CORRECT.**
- Lemma 5: `I=∫_0^∞(1−e^{−t/2})a(t)dt`. Substituting u=e^{−t/2}: `I=2∫_0^1du/((1+u)(1+u²))`, partial
  fractions `=½log2+π/4`. mpmath, 20 digits: direct quad 1.1319717536774209643 = subst form = closed form.
  `c_0+2I = 5.3721834192256655822 = γ+log(8π)+π/2 = c_A` (agree to 1e−25) — and c_A is literally setup.tex's
  definition. `c_0=γ+log4π` is corroborated by **CC20 (150)** `W_R(f):=(log4π+γ)f(1)+…`. I also re-derived
  the conversion by hand: `𝒟(v)−c_AH(v) = −Reg(v)−c_0H(v)` with `Reg(v)=∫a(t)(2C_v(t)−2e^{−t/2}‖v‖²)dt`.
  Cross-check of the setup.tex multiplier: `2∫a(t)(1−cos ut)dt = Reψ(¼+iu/2)−ψ(¼)` verified at
  u=0.3/1.0/2.5/7.0 to ≥12 digits; `ψ(¼)=−γ−π/2−3log2` to 18 digits; `𝒟−c_AH ↦ Reψ(¼+iu/2)−log π` ✓.
  **CORRECT — I = 1.13197175368, c_A = 5.37218341923.**
- The CC20 remark is right: the γ in Thm 6.11's `c=4γ/log2` is **γ≈2.94355** (CC20 line before (140)),
  not Euler's constant. **CORRECT.**

## 6. Lemma 6 plant (17): **CORRECT**

`a(t)=Σ_{m≥0}e^{−(2m+½)t}` ⟹ `∫t²a(t)dt = Σ_m 2/(2m+½)³ = 2Σ_{j≥0}(2j+½)^{−3}`. mpmath: quad and series
both **16.165967492192115042 ≤ 18** ✓; the stated "first term (16) + tail integral bound (2)" is exact.
`‖v_b‖=‖h‖=1`, `‖v_b'‖²=‖h'‖²/b²`, `‖v(·+t)−v‖≤|t|‖v'‖`, and `C_{v_b}≥0` for h≥0 kills the prime terms in
sign. Hence `L_S(k_b⋆k_b^*) ≤ −c_A + 18‖h'‖²/b²`, and `≤ −c_A/2` for `b²≥36‖h'‖²/c_A`. **CORRECT.**

## 7. Lemmas 8–9 (density; (20)–(21) fixed-S counterexample): **CORRECT**

- Lemma 8: `ĥ·conj(f̂_0)∈L¹` by Cauchy–Schwarz and is the FT of the identically-zero correlation ⟹ =0 a.e.;
  `f̂_0=Ξ/A`, Ξ entire ≢0 ⟹ real zeros discrete ⟹ h=0; no RH used; (19) then contradicts Lemma 2(3). And
  (20): `‖ϑ(f_0)h‖²=(1/2π)∫|f̂_0|²|ĥ|²=(1/2πA²)∫|Ξ|²|ĥ|²>0` (Plancherel, setup.tex's `ĝ(z)=∫ge^{−izx}dx`).
  **CORRECT.**
- **The radical claim is exactly what canonical.tex proves.** Verbatim, `\begin{proposition}[radical]`:
  *"$\B(f_0,v)=0$ for all $v\in\Xf$. More generally, $U_qf_0\in\operatorname{rad}\B$ for every $q\in\R$, and
  $f_0*h\in\operatorname{rad}\B$ for every $h\in C_c^\infty$."* Its Remark also confirms the verdict's caution:
  *"The radical … is closed and **contains** the closed span of the displayed translates and convolutions."*
  Hence `Q(v_R)=𝔅(e_R,e_R)`, `|Q(v_R)|≤C_X‖v_R−f_0‖_X²` with setup.tex's `C_X=|c_A|+14`. **CORRECT.**
- Young + `‖ϑ(k_R)𝖲‖²_HS ≥ ‖ϑ(k_R)h‖² ≥ ε_h/4` and `|Q(v_R)| ≤ ε_h/8` give (21) `≤ −ε_h/8`. Arithmetic ✓.
- **Explicit budget re-derived and it matches to the digit.** With a=π/2, q=0, `c_χ=2`, and canonical.tex's
  `Lemma[cutoffnorm]`: `‖e^{|x|}e_R‖²≤M_0²/(2a)E`, `‖e_R'‖²≤(M_1²+4M_0²)/a·E`, `‖e_R‖²≤M_0²/(2a)E`,
  `𝒟(u)≤⅔‖u'‖²+32/3‖u‖²`, `E=e^{−2ae^{2R}}`:
  `‖e_R‖_X² ≤ E/a·[M_0²/2 + (2M_1²+8M_0²)/3 + 16M_0²/3] = E/a·[17M_0²/2 + 2M_1²/3]` = the verdict's
  `C_cut = a^{−1}(17M_0²/2 + 2M_1²/3)`. L¹ bound `≤(M_0/a)e^{−ae^{2R}}` also reproduced. **CORRECT.**
- Consistency of the surrounding dictionary: `A_±(f_0)=f̂_0(±i/2)=ξ(0)/A=ξ(1)/A=1/(2A)=0.884226440535`,
  `P_02(f_0)=1/(2A²)=1.56371279628 ≠ 0`; and `Ξ(0)/A = 0.879134672427` reproduces canonical.tex's
  0.8791346724 from `ξ(1/2)=0.497120778188`. **CORRECT.** (`θ(λ)=U_{logλ}` cross-checked vs C26's `ϑ_λ`.)

## 8. Plant (iii), (22)–(23): **CORRECT**

sympy: `M_p(1−s)−M_p(s)=0` identically; the factorization `M_p=−p^{a−1+s}(1−p^{a−s})(1−p^{1−a−s})` is exact.
Zeros `M_2(0.75+2πik/log2)=M_2(0.25+2πik/log2)=0` (residual ≤1.4e−27, k=0,1,−2). (23) checked against
`mp.diff` at (p,s)=(2,1.6),(3,2.2),(5,1.9): 15 digits. `p^{ja}+p^{j(1−a)}=2p^{j/2}cosh((a−½)j log p)` ✓.
The remark that `(1−χ(p)p^{−s})^{−1}` has poles, not off-line zeros, is right.

## 9. §8 — the logical claim: the judge is **RIGHT**

Logical equivalence is about truth values in every model, not about derivability from given premises by a
given method, so "P ⟺ RH" says nothing about whether P is reachable by the tools at hand — that the Weil,
Nyman–Beurling and Li criteria are all equivalent to RH is exactly why one *chooses* among them, a choice
that would be vacuous if equivalence meant equal accessibility. Circularity is *using* an unproved
RH-equivalent as a **premise**; deriving one as a **conclusion** from independent facts is the shape of any
proof of RH there could be, so a blanket "file it away if RH-equivalent" rule discards the whole target class.
The policy's only legitimate residue is heuristic: an equivalent form that reproduces the same obstruction
under renaming is worthless — but that must be shown by exhibiting the obstruction, as this verdict does
with (10)/(17)/(21), not inferred from the equivalence.

## L. Errors found (all locator-class; none touches the mathematics)

| # | Place | Finding | Consequence |
|---|---|---|---|
| L1 | Sources block, §1–3, Lemma 2(3), Lemma 4 | CCM23 is cited as v1 with `Definition 4.10`, `Proposition 4.11–4.12`, `Theorem 4.13`, `(43)`, `(46)`, pp.23–25. The shelf copy is **v2**, where these are `Definition 4.5`, `Proposition 4.6–4.7`, **`Theorem 4.6` (p.23)**, `(47)`, `(57)/(58)`. `grep "4.13"` over the whole v2 text: no hit. Note the citation is *internally inconsistent*: `(57)` matches v2 exactly while `(43)` is off by 4 (v2's `(47)`). | **UNVERIFIABLE as pinned**; content verified against v2 and correct. The §10 directive "check … against the pinned sources" cannot be executed with these labels. No change to `RESULT`. |
| L2 | Lemma 7, (18) | cites `[CCM23, Proposition 4.1(iv)]` for the *position*-cutoff image. In v2 that is item **(ii)**; (iv) is the Fourier-transform version. | cosmetic; the statement used is true. |
| L3 | (5) vs Lemma 4 / Lemma 9 | `N_S` is overloaded: `N_S(k)=Tr(ϑ(k)𝖲)` in (5) but `N_S(k)=‖ϑ(k)𝖲_S‖²_HS = Tr(ϑ(k⋆k^*)𝖲)` in Lemma 4/(21). Resolvable (§7 uses them consistently: `Q(v)=N_S(k)−E_S(k⋆k^*)`), but the same symbol takes two different functionals. | presentational; recommend renaming one before the paper. |

## Verdict on the verdict

Every load-bearing new lemma checked here — (1)–(2), Lemma 2(1)(2)(3), (6)–(9), the exact plant (10),
(11)–(12), (13)–(16), (17), (19)–(21) with its budget constant, (22)–(23) — is **CORRECT** by my own
derivation and by computation. I found **no mathematical error**. `RESULT: SECOND_EXPRESSION_CANDIDATE`
and `ANSWER: A_WITH_EXPLICIT_SCOPE_REPAIRS` stand unchanged; the three findings above are citation and
notation defects. The two source corrections the verdict insists on are both confirmed at the source:
C26 (22) p.32 carries the `log(TW)f(1)` contact term, and C99 (21)/(23) pp.42–43 defines `S_Λ` as the
**multiplicative window** `{ξ : ξ(g)=0 for |g|∉[Λ^{-1},Λ]}`, which is not the Sonin projection.
