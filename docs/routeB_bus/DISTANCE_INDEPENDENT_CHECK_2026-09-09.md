# DISTANCE verdict — independent check (2026-09-09)

Target: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md`
(686 lines, blob of the checked bytes below).
Checker: fresh adversarial agent, own derivations only. Every number below comes from my own
run in `/tmp/dchk/` (`chk1b.py` … `chk9.py`); tools: python3 + mpmath 1.2.1 (dps 15–40),
numpy 1.26.4, scipy 1.11.4, sympy; `pdftotext` for [S26]; WebFetch for [Z] and [S23].
Cross-read: request `PROSHKA_REQUEST_GOAL058_DISTANCE_2026-09-09.txt`, KERNEL verdict
(K6)–(K26), `WINDOW_TAIL_DERIVATIVE_PROBE_2026-09-09.md`, cache
`phase5_codex/six_centre/out/window_derivative_K36.json`, script `window_derivative.py`.
Repository not modified except this file. No commit, no push.

**Pins re-checked myself (all match the verdict header / research log):**

| Object | Verdict claims | I compute |
|---|---|---|
| request blob | `5ba3cb9c…` | `5ba3cb9ce440e3b3c4e1004f1aefc5b518de2e32` ✓ |
| request SHA-256 | `9fbe548d…c565ffd` | identical ✓ |
| request bytes / lines | 14066 / 90 | 14066 / 90 ✓ |
| request commit | `19054597…` | exists, subject `[Linux-Claude][rh_clean][Goal058] Request REQ-2026-09-09-DISTANCE` ✓ |
| [K] KERNEL blob | `d171a2fb…` | ✓ |
| [H] HODGE blob | `4e68922d…` | ✓ |
| [J] K36 cache blob | `021d8e40…` | ✓ (sha256 prefix `c681983cb3b0c13c` = request shelf) ✓ |
| [P] probe blob | `11cf942a…` | now `66937ae2…` — **the probe was edited after the verdict** (D15 correction applied in place, commit `7cc9da0e`). Not a defect of the verdict. |
| script blob | `d5969fef…` | object exists in the repo (3436 bytes); working tree now `ddce881c…` (matrix saving added after the verdict, per its §9(c)). ✓ |

## Independent second channel for the whole convention (D2/D4/D6/D7)

Before checking individual displays I rebuilt the geometric side of D2 from scratch
(`chk8b.py`, `chk8c.py`, `chk9.py`) — no zero data — and compared with the zero side of D6:

* Test `f(x)=exp(-1/(1-x²))·1_{|x|<1}` (real, compactly supported, **not** pole-null: pole term
  `2M₊M₋ = 0.41011089`, i.e. 3270× the answer, so the pole convention is genuinely under test).
  Geometric side D2: `𝒟 = 0.40908402438094`, `c_A·g(0) = 0.71496305173254`,
  primes (m = 2,3,4,5,7) `= 0.10410643807617`, pole `= 0.41011089240134`
  → **Q[f] = 1.2542697356e-4**.
  Zero side D6 over the first 160 zero pairs (mpmath `zetazero`) → **1.2542697356e-4**,
  difference `-1.47e-15`, **relative 1.2e-11**.
* D7 directly: `Q(φ,g)` from the geometric side only (all primes m ≤ 4000, `M₊(φ)=M₋(φ)=1/4`)
  = **-5.58e-15** against individual terms of size 0.28–0.47 → relative residual **1.2e-14**.

So `A₀(t)=e^{-t/2}/(1-e^{-2t})`, `c_A=γ+log 8π+π/2`, `w_m=Λ(m)/√m`, the **+** sign on the pole
pair, D4, D6 and D7 are all confirmed simultaneously by a channel that shares no input with
the verdict's derivation. `c_A = 5.37218341923`.

Extra convention cross-check: `Re ψ(1/4+it/2) − ψ(1/4) − c_A = Re ψ(1/4+it/2) − log π`
(exactly, since `ψ(1/4) = −γ−3log2−π/2`), which is Zhu's symbol (3) minus its prime sum.
The verdict's "its symbol (3) matches D2 on the even real class" is therefore right; I also
confirmed from the [Z] source that Zhu's form is *rank-one pole term + multiplier* with the
pole `2f̂(i/2)f̂(−i/2)`, `+2(∫f cosh(x/2))²` even / `−2(∫f sinh(x/2))²` odd — same object as D2.

## Per-display results

| D# | Claim | Status | Reason / number |
|---|---|---|---|
| D2 | Source Q = 𝒟 − c_A⟨,⟩ − Σ w_m{…} + M̄₊M₋ + M̄₋M₊ | **VERIFIED** | Byte-identical to KERNEL (K6); reproduced numerically against the zero side to rel. 1.2e-11 (above). |
| D3 | ℰ, 𝒲, ‖·‖_E | **VERIFIED** | = (K7) minus the pole-null intersection. The widening to full ℰ is *required* here and correctly flagged: `M±(φ)=1/4≠0`. |
| D4 | `F_φ(z) = ½ ξ(½+z)`, `Θ=2φ`, `M±(φ)=¼` | **VERIFIED** | Symbolic: the displayed Mellin step `π^{-s/2}ζ(s){Γ(s/2+2)−(3/2)Γ(s/2+1)} = ¼s(s−1)π^{-s/2}Γ(s/2)ζ(s)` is exact. Numeric (mpmath, dps 30) at z = 0, ±½, 1, i·14.134725…, 0.3+2i, 0.1+25i: max \|F_φ − ½ξ(½+z)\| = **2.6e-35**. `F_φ(±½)=0.25` exactly. |
| D5 | `\|Q(f,g)\| ≤ 22‖f‖_E‖g‖_E`; `\|⟨f,U_t g⟩\| ≤ e^{-\|t\|}𝒲^{½}𝒲^{½}`; `\|M±\| ≤ √(4/3)𝒲^{½}` | **VERIFIED** (both estimates **proved**, not just plausible) | Translation estimate: `e^{-\|x\|}e^{-\|x-t\|} ≤ e^{-\|t\|}` from `\|x\|+\|x-t\| ≥ \|t\|`, then Cauchy–Schwarz in the `e^{\|x\|}`-weighted pairing — proof complete. `∫e^{x-2\|x\|}dx = 4/3` exactly. Constants: `c_A = 5.37218 < 7` ✓; `Σ_{m≥2} log m·m^{-3/2} = −ζ'(3/2) = 3.93224 < 6` ✓ (true `Σ Λ(m)m^{-3/2} = 1.50076`). Assembled: `7 + 2·6 + 2·(4/3) = 65/3 = 21.667 < 22` ✓. |
| D6 | signed explicit formula on ℰ × C_c^∞ | **VERIFIED** numerically; extension argument PLAUSIBLE | 160-zero check above, rel. 1.2e-11, on a **non**-pole-null test. The f-extension (core + (K15) + zero count) is (K16)'s argument, correctly re-stated. |
| D7 | `Q(φ,g)=0 ∀g∈ℰ`; radical, not isotropy | **VERIFIED** | Geometric-side residual −5.58e-15 vs terms of size 0.47 (rel. 1.2e-14). |
| D8 | `‖U_t v − v‖² ≤ C_v t + C'_v t²`; `‖e_ε‖_E² = O(ε(1+\|log ε\|))` | **VERIFIED** | `‖U_te−e‖² ≤ min(2‖e‖_∞·V·t, 4‖e‖²) = O(min(t,ε))`; `∫₀^1 A₀(t)min(t,ε)dt ≍ ε/2 + (ε/2)log(1/ε)` since `A₀ ~ 1/(2t)`. Both endpoints handled. `v_o ∈ ℰ` correct: `∫₀^1 A₀(t)·C t dt < ∞`. |
| D9 | `V_a = {f∈ℰ: f=0 a.e. outside (−a,a)}` via the H^{1/4} multiplier | **VERIFIED** with one omitted technical step (see below) | Coefficient arithmetic exact: averaging `y∈(16x,32x)` with weight `x^{-2s}` produces **exactly** `2·16^{2s−1}(2^{2s}−1)/(2s)`; sympy gives the same closed form `(1024^s−256^s)/(16s)`, `= √2−1 = 0.41421356 < 1` at `s=1/4` ✓. Crossing term of `[1_{x>0}f]_{H^s}²` `= (1/2s)∫\|f(u)\|²u^{-2s}du` — I re-derived it, exact. `‖P_jMP_k‖ ≤ C2^{-\|j−k\|/4}` follows from M bounded on L²∩H^{1/4} + Bernstein (verdict compresses it to one line, but it is right). `√(1+j)/√(1+k) ≤ √(1+\|j−k\|)` ✓. `1+Re ψ(1/4+it/2)−ψ(1/4) ≍ log(2+\|t\|)` ✓ from (K7). |
| D10 | `λ_a = inf_{w≠v_i} Q[v_o+w]/‖v_i−w‖²` | **VERIFIED** | Random 9-dim model with an exact radical vector (`‖Qφ‖ = 8.9e-16`): `λ_a = −1.708418029424698` from the generalised eigenproblem, `Q[v_o+w]/‖v_i−w‖²` at `w=v_i−f_a` = `−1.708418029424697`; 2·10⁵ random `w` never go below (best `−1.70692`). 0/0 exclusion is genuinely necessary. |
| D11 | dichotomy `d_a ∈ {0, −∞}` | **VERIFIED** | Pure homogeneity: `d_a = inf_{f∈V_a}Q[f]` after the affine bijection; V_a linear, Q quadratic. Model: `Q[φ]=−1.3e-17`, min eig of `Q\|_V = −1.708 < 0` ⇒ −∞ branch. |
| D12 | `dist_Q(−v_o,V_a)² = 0` under RH | **VERIFIED** | `w=v_i` gives `Q[φ]=0`; RH ⇒ `Q ≥ 0` on ℰ by D6 (all `jλ=λ`) + D5 + core density. The ε-argument for the punctured infimum is correct (`Q[φ−εf₀]=ε²Q[f₀]→0`). |
| D13 | `inf_{‖v_i−w‖²=M} Q[v_o+w] = Mλ_a` | **VERIFIED** | Model: `M=3.7`, `Mλ_a = −6.321146708871383`, achieved `−6.321146708871378`. `‖v_i‖² = (1−T)‖φ‖²` ✓. |
| D14 | `λ_a ≥ −C_a`, `C_a = c_A + 2Σ_{m≤e^{2a}}Λ(m)/√m + 4 sinh a` | **VERIFIED**, factor 4 is right | Pole: `\|M±(f)\|² ≤ ‖f‖²∫_{−a}^{a}e^{±x}dx = 2 sinh(a)‖f‖²`, so `2Re(M̄₊M₋) ≥ −2\|M₊\|\|M₋\| ≥ −4 sinh(a)‖f‖²` ✓ (the factor is 4, not 2). Prime overlap needs `log m < 2a` ✓. 𝒟 ≥ 0 ✓. Values: `C_{0.3}=6.590`, `C_{0.5}=8.437`, `C_{0.7}=11.349`, `C_{1.0}=15.926`, `C_{2.0}=44.263`. Compact-resolvent claim also correct (uniform support + log-Fourier weight ⇒ Riesz–Kolmogorov compactness; the perturbation of 𝒟 is L²-bounded on a finite window). |
| D15 | `T(a) ~ (2π³/I)e^{7a}e^{−2πe^{2a}}`, `T² ~ e^{−4πe^{2a}}` | **VERIFIED** | Derivation reproduced by hand (`y=e^{2x}`, `∫_Y^∞ y^{3.5}e^{−2πy}dy ~ Y^{3.5}e^{−2πY}/2π`, both tails). Numeric (`I = 0.07993795299040532`): ratio T/asym = 0.8055 (a=0.3), 0.8639 (0.5), 0.9064 (0.7), 0.9362 (0.9), 0.9568 (1.1), 0.9708 (1.3), **0.9788 (1.5)** — monotone → 1. My `T(0.5)=8.486018e-4` and `T(0.7)=8.1178e-7` match the cache exactly. **The probe's `λ_a ≈ c·e^{−2πe^{2a}}` was an error** (that is T, not T²); it has since been corrected in the probe file itself. |
| D16 | `λ_a ≤ Q[v_i]/‖v_i‖² = Q[v_o]/‖v_i‖² ≤ 22‖v_o‖_E²/((1−T)I)` | **VERIFIED** | `Q[v_i]=Q[φ−v_o]=Q[v_o]` by D7 + `Q[φ]=0`; `v_i ∈ V_a` by D9. |
| D17 | `λ_a ≤ Ce^{4a}T/(1−T)`; the three ratios | **VERIFIED**, all three ratios confirmed and the constants identified | Numerics (a = 0.6/0.8/1.0/1.2/1.4): `\|φ(a)\|²/(IT)` = 17.24, 27.54, 42.87, 65.72, 99.80, i.e. `/e^{2a}` = 5.193 → **6.069** vs predicted `2π = 6.2832`; `‖φ'1‖²/(IT)/e^{4a}` = 27.10 → **36.84** vs predicted `4π² = 39.478`; `𝒲[v_o]/(IT)/e^{2a}` = 1.0574 → **1.0100** vs predicted 1. All three grow no faster than stated. `‖U_tv_o−v_o‖² ≤ 3t²‖φ'1‖² + 6t\|φ(a)\|²` re-derived (each jump occupies an x-set of measure t). `max_{(0,1]} t·A₀(t) = 0.70146 ≤ 2` ✓, `max_{t≥1} A₀(t)e^{t/2} = 1.15652 ≤ 2` ✓. |
| D18 | abstract counterexample: floor T, rescaled floor T⁴ | **VERIFIED** | By hand and numerically (T = 0.01/0.1/0.5/0.9): `Q_T[n_T]=0` (radical), outside mass = T, `Q_T[(n_T)_o] = T(1−T)` exactly, window floor over `ℂe₁` = **T** exactly. Scaling `Q_T → T³Q_T` gives floor `T⁴`. The inference "radical + first-order tail energy ⇒ T²" is genuinely killed. |
| D19 | `Q(h,v_o+w_a) = −λ_a⟨h,v_i−w_a⟩` | **VERIFIED** | Algebra re-derived from `Q(h,f_a)=λ_a⟨h,f_a⟩` + `Q(h,φ)=0`. Model residual `max\|LHS−RHS\| = 6.7e-16`. It is indeed **not** `Q(h,v_o+w_a)=0`. |
| D20 | weak equation `A_a f = λ_a f` on (−a,a) | **VERIFIED** | Pairing `⟨h,A_af⟩` term by term reproduces D2 exactly, including `⟨h,e^{x/2}M₋(f)⟩ = M̄₊(h)M₋(f)` and `⟨h,e^{−x/2}M₊(f)⟩ = M̄₋(h)M₊(f)`. This **derives** the form↔operator dictionary the SCREW/SIGNATURE check flagged as ASSERTED-NOT-DERIVED, and which §5 of the request listed as an outstanding debt. |
| D21 | `g(t) = −Σ m_λ(e^{λt}−1)/λ²`, `−g''=K_Q`, `Q(h,f)=⟨Dh,G_aDf⟩` | **VERIFIED**, sign correct | `g'' = −Σ m_λ e^{λt}` so `−g'' = Σ m_λ e^{λt} = K_Q`, and `Q(h,f) = ∬K_Q(x−y)h̄(x)f(y)` follows from D6 because `conj(F_h(jλ))F_f(λ) = ∬ h̄(x)f(y)e^{λ(y−x)}`; `K_Q` is even because `Λ_ξ` is even and `m_λ=m_{−λ}`. Two integrations by parts give `∬g(x−y)h̄'f'`. `g(0)=0`, g even ✓. Convergence: `Σ m_λ/\|λ\|² < ∞` from `N(T)=O(T log T)`, `\|e^{λt}\| ≤ e^{\|t\|/2}` ✓. **Cross-checked against the source**: [S26] (1.3)–(1.6) read from the local PDF — Suzuki's `g` is even with `g(0)=0`, `G_a = P_aGP_a` on the zero-mean subspace, `B_a = D*G_aD` with `D(B_a)=H₀¹(−a,a)`, Theorem 1.1 = *A_a is the Friedrichs extension of B_a*, (1.8) `Q_W^a(v)=⟨B_av,v⟩`. The verdict's statements ("Closure yields the Friedrichs realization of D*G_aD. It does **not** yield Q[f]=⟨f,G_af⟩", "the zero-mean projection is harmless because derivatives of compact tests have integral zero") are exactly right. |
| D22 | Schur complement `s₀ = r − b*C^{-1}b`, `‖p−y‖²=1+‖y‖²` | **VERIFIED** | Model: `Q[p−V_c y] = 0.6821464552911803` vs `s₀ = 0.6821464552911805`; `‖p−y‖² = 3.757330427670478` vs `1+‖y‖² = 3.757330427670477`. |
| D23 | secular equation `r − λ − b*(C−λ)^{-1}b = 0` | **VERIFIED** | Model: `f(λ_a) = 1.8e-14`. |
| D24 | the unpaid inequality | N/A — correctly labelled **CONDITIONAL / not proved** | The verdict does not claim it. Honest. |
| D25 | `J_λ`, `F_{J_λ v}=F_v/(λ−z)`, `d_λ`, `F_{q_λ}(λ)=1` | **VERIFIED** | `F_{u'}(z) = −zF_u(z)` ⇒ `(λ−z)F_u=F_v`. `Λ(z)/(λ−z)^r → (−1)^rΛ^{(r)}(λ)/r! = d_λ` at `z=λ` ✓, vanishing at every other distinct zero ✓. |
| D26 | `Q[q_λ]=Q[q_{jλ}]=0`, `Q(q_λ,q_{jλ}) = r` | **VERIFIED**, and the `jλ` bookkeeping is the right way round | `Q[q_λ]=Σ_μ m_μ conj(F_{q_λ}(jμ))F_{q_λ}(μ)`: only `μ=λ` survives on the right factor, and `F_{q_λ}(jλ)=0` since `jλ≠λ` is another distinct zero ⇒ 0. `Q(q_λ,q_{jλ}) = m_{jλ}·conj(F_{q_λ}(j(jλ)))·F_{q_{jλ}}(jλ) = r·1·1`, using `j(jλ)=λ`. So `F_q(λ)=1` is the value that is 1 and `F_q(jλ)=0` — matches the verdict. |
| D27 | `Q[u_b] = −2re^{2δb}`, `‖u_b‖² ≤ D` | **VERIFIED** | `F_{U_bf}(z)=e^{bz}F_f(z)`. At `λ=δ+iγ`: `e^{-ibγ}e^{(δ+iγ)b} = e^{δb}`. At `jλ=−δ+iγ`: `−e^{ibγ}e^{−(−δ+iγ)b} = −e^{δb}`. Both zeros contribute `−re^{2δb}` ⇒ total `−2re^{2δb}` ✓. `‖u_b‖² ≤ 2(‖q_λ‖²+‖q_{jλ}‖²)` by translation invariance ✓. |
| D28 | B, D positive and finite | **VERIFIED** | `q_λ = J_λ^rΘ/d_λ` keeps double-exponential decay of all derivatives ((K19)–(K20)), so the `e^{4\|x\|}` weight converges. The verdict is right to refuse to hide B and r. |
| D29 | `𝒟[h] ≤ ‖h'‖² + 16‖h‖²` | **VERIFIED** with margin | Splitting at t = 1: `∫₀¹A₀(t)t²dt = 0.3224053782 ≤ 1` and `4∫₁^∞A₀(t)dt = 4.994488723 ≤ 16`. |
| D30 | `‖(1−χ_a)v‖_E² ≤ (e^{-2s}+24e^{-4s})B(v) ≤ 25e^{-2s}B(v)` | **VERIFIED**, the 24 is exactly right | 𝒲-part `≤ e^{-2s}B(v)`; 𝒟-part `≤ ‖u'‖²+16‖u‖² ≤ (2·1 + 2·4 + 16)e^{-4s}B(v) = 24e^{-4s}B(v)` using `\|χ'\|≤2`. `e^{-2s}+24e^{-4s} ≤ 25e^{-2s}` for `s≥0` ✓ (checked at s = 0, .01, .1, 1, 5). |
| D31 | `B(u_b)≤2e^{4b}B`, `‖u_b‖_E ≤ √(34B)e^b`, `e ≤ 5√(2B)e^{-s+2b}`, `\|Q[f_a]−Q[u_b]\| ≤ 3000Be^{-s/4}` at `b=s/4` | **VERIFIED**, constants exact | The 34 is *sharp*, not a slip: `𝒟[u_b] ≤ ‖u_b'‖²+16‖u_b‖² ≤ 2A'+32A ≤ 32(A+A') ≤ 32B` (translation-invariant, no `e^{4b}`), `𝒲[u_b] ≤ 2e^{2b}B`, total `≤ 34Be^{2b}`. Then `e ≤ 5e^{-s}√(B(u_b)) = 5√(2B)e^{-s+2b}` ✓, and `22·e·2‖u_b‖_E = 44·5√2·√34·B·e^{-s+3b} = 220√68·Be^{-s+3b}` — `5√2·22·2·√34 = 1814.16647527177` and `220√68 = 1814.16647527177`, identical to 12 digits ✓. `22e² = 1100Be^{-2s+4b}` ✓. At `b=s/4`: `220√68 + 1100 = 2914.166 < 3000` ✓. |
| D32 | `a₀(λ) = 1 + 4 log max{1, 3000B/r}` | **VERIFIED** | `3000Be^{-s/4} ≤ r ⟺ s ≥ 4log(3000B/r)`, `s=a−1` ✓. |
| D33 | `Q[f_a] ≤ −re^{δ(a−1)/2}`, `λ_a ≤ −(r/D)e^{δ(a−1)/2}` | **VERIFIED**, exponent right | With `b=s/4`, `2δb = δ(a−1)/2` ✓. `Q[f_a] ≤ −2re^{δs/2} + r ≤ −re^{δs/2}` since `r ≤ re^{δs/2}` for `δ,s ≥ 0` ✓. Dividing by `‖f_a‖² ≤ D` with a **negative** numerator preserves the direction ✓. `f_a ≠ 0` because `Q[f_a]<0` ✓. |
| D34 | signed-squares split `Q = P₊ − N₋` | **VERIFIED** | Pair contribution `2m_λRe(x̄_{jλ}x_λ) = ½m_λ(\|x_λ+x_{jλ}\|² − \|x_λ−x_{jλ}\|²)`; fixed points `jλ=λ` give `m_λ\|x_λ\|²`. Exactly D34. The caveat about separate convergence of the two sums is correctly stated. |
| D35 | pair contribution `2m_λ Re(conj F_{f_a}(jλ)·F_{f_a}(λ))` | **VERIFIED** | `F_{φ−f_a} = −F_{f_a}` at zeros; the two minus signs cancel. For `u_b`: `2r·Re(−e^{δb}·e^{δb}) = −2re^{2δb}` ✓. |
| D36 | `Q[f] ≥ (2∫_{2a}^∞A₀ − c_A − 4 sinh a)‖f‖²` for `2a<log 2` | **VERIFIED as an inequality**; the "strictly positive small windows" claim is true but only far below the stated regime | Disjoint translates for `t>2a` give `‖U_tf−f‖²=2‖f‖²` ✓, no prime overlap for `2a<log2` ✓, pole `≥ −4 sinh a` ✓. **Numbers**: bracket = **−1.30532** (a=0.1), **−2.49950** (a=0.2), **−3.41049** (a=0.3), −3.79210 (a=0.3465 = log2/2). The bracket only crosses zero at **a\* = 0.0371153**; it is `+1.4469` at a=0.01, `+4.4902` at a=0.0005 (log-divergent, as claimed). At a = 0.3 the bound −3.410 is a **valid but vacuous** lower bound below the probe's observed floor `λ_{0.3} = +7.57e-3`, so no contradiction. D14 gives the weaker `−C_{0.3}=−6.590`. |
| D37 | `E=1−c²`, `μ_⊥=(R−l₁c²)/E`, `H=μ_⊥/l₂`; threshold `E>1e-8, l₂>0, H≥100` at a = 0.60, 0.65, 0.70 | **VERIFIED, and the threshold PASSES** | The algebra is right: `eigh(Q,G)` gives G-orthonormal eigenvectors, `Q(g,v)=λ₁⟨g,v⟩_G=0`, so `R = c²λ₁ + (1−c²)Q[v]`. The script stores exactly the G-normalised overlap and G-Rayleigh value (`ov = \|v₀ᵀGc\|/√((v₀ᵀGv₀)(cᵀGc))`, `ray = cᵀQc/cᵀGc`) — so the diagnostic is well-defined. My run on blob `021d8e40…`: see table below. |

### D37 executed (input blob `021d8e401d81dec35070bccf0b526d6750a325ed`, sha256 `c681983cb3b0c13c…`)

| a | lam1 | lam2 | R | c | E = 1−c² | μ_⊥ | H = μ_⊥/l₂ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.35 | 1.193748e-03 | 6.548825e-02 | 2.421824e-02 | 0.9860015378 | 2.78010e-02 | 8.29384e-01 | 12.67 |
| 0.40 | 1.816004e-04 | 1.472636e-02 | 9.299181e-03 | 0.9867946854 | 2.62362e-02 | 3.47700e-01 | 23.61 |
| 0.45 | 1.621588e-05 | 2.411958e-03 | 2.901041e-03 | 0.9889150399 | 2.20470e-02 | 1.30865e-01 | 54.26 |
| 0.50 | 9.382272e-07 | 1.948588e-04 | 7.036732e-04 | 0.9908270936 | 1.82617e-02 | 3.84824e-02 | 197.49 |
| 0.55 | 5.370925e-08 | 1.439241e-05 | 2.729713e-04 | 0.9929062244 | 1.41372e-02 | 1.93049e-02 | 1341.3 |
| 0.60 | 1.639769e-09 | 6.052401e-07 | 5.517336e-05 | 0.9944547646 | 1.10597e-02 | 4.98853e-03 | **8242.2** |
| 0.65 | 4.061599e-11 | 1.882444e-08 | 8.390882e-06 | 0.9957018131 | 8.57790e-03 | 9.78193e-04 | **51964.0** |
| 0.70 | 4.367618e-13 | 2.742883e-10 | 1.280709e-06 | 0.9966015180 | 6.78541e-03 | 1.88744e-04 | **688123.8** |

All rows well-formed; no sign repair, no absolute values taken. At a = 0.60/0.65/0.70:
`E > 1e-8` ✓, `l₂ > 0` ✓, `H ≥ 100` ✓ (by 2–4 orders). **Threshold PASSES → ЕСЛИ_A.**
(The observer had already executed this in commit `7cc9da0e`; my run is independent of that.)

## Sections 1–5, non-displayed claims

| Claim | Status | Reason |
|---|---|---|
| §1.1 "This is the full space, not the smaller pole-null ℋ" and "We retain both pole terms throughout" | **VERIFIED and load-bearing** | `M±(φ)=1/4 ≠ 0` (my numeric: exactly 0.25). Without widening from (K7)'s ℋ to ℰ, D7 would not be available for φ at all. Correct and necessary. |
| §1.1 "The factor two is immaterial for T and Rayleigh quotients, but must not be hidden in an exact transform identity" | **VERIFIED** | Both are ratios. KERNEL (K18)'s Φ has coefficients 4π²/6π; the request's φ has 2π²/3π = Φ/2. |
| §2 "Consequently the literal upper bound in Q2(a) holds, without RH, with C=0" | **VERIFIED** | `w=v_i` gives `Q[φ]=0`; any `C≥0` works. Vacuous, as stated. |
| §2 "the proposed positive lower bound in Q2(b) under RH is false… T(a)>0" | **VERIFIED** | `inf = 0 < c(a)T²‖φ‖²` for every `c(a)>0`; `T(0.3)=0.05441`, `T(0.7)=8.118e-7`, all `>0`. |
| §3.1 "the request's a=1.19 extrapolation cannot follow" | **VERIFIED** | The request wrote `e^{−2πe^{2·1.19}} ≈ 1e-30`; with `λ_a ≍ T²` the exponent is `4π`, giving `e^{−4π·10.805} = e^{−135.8} ≈ 6e-60`. The probe has since been corrected to 10^{-59}. |
| §3.3 "F_{v_o} is entire of infinite exponential type; `log F_φ(z) = (z/2)log z + O(z)`" | **VERIFIED** | Stirling on `Γ(s/2)` with `s=1/2+z`; the compact part `F_{v_i}` has type ≤ a and cannot cancel it. |
| §3.4 "The request's HODGE H17 locator is not verified in the pinned artifact; the verified equality-case statement is Section 10.4" | **VERIFIED** | The HODGE verdict's displays stop at **(H15)**; there is no (H17). §10.4 "One exact missing lemma" exists and states `Q[f]=0 ⇒ Af=0`. |
| §3.5 [Z] "at a=0.8 … 8.9e-18 ≤ λ_{0.8} ≤ 2.27e-17 … factor ≈ 2.55 … Theorem 1.3 gives exp(−a e^a) under RH … Landau–Widom is Conjecture 12.1" | **VERIFIED against the source** | arXiv:2608.24827 (Xuefeng Zhu, *"Weil positivity in compact windows: a finite reduction, certified two-sided bounds, and a Landau–Widom decay law"*, v1 25 Aug 2026, v2 2 Sep 2026) — abstract carries "at L=0.8 the two halves enclose the profile, 8.9e-18 ≤ lambda_min(0.8) ≤ 2.27e-17" and "Under RH, lambda_min(L) ≤ exp(−L e^L)". HTML: Theorem 1.2 = certified positivity at support 1.6; Theorem 1.3 = the RH-conditional `exp(−L e^L)`; Corollary 6.3 = extension to arbitrary complex tests (the "odd-sector extension"); Table 3 = certified variational upper bounds for `L∈[0.5,2.0]`; Conjecture 12.1 = the empirical scaling law. `2.27e-17/8.9e-18 = 2.5506` ✓. The verdict does **not** overstate: it says the certificate was not rerun. |
| §5 refutation table (5 rows) | **VERIFIED** row by row | Each cites a display I verified above (D11–D13, D12, D19, D14, D18). None of the five is overstated: all are labelled THEOREM_SHAPE, not ROUTE_FAMILY. |
| §5 "Strongest surviving objection: D22–D24 isolate a cancellation but do not pay it" | **VERIFIED (honest)** | Correct self-assessment. |
| K8A contract, `ORIGINAL_OBJECT_IS: NOT_NECESSARY` | **VERIFIED** | Follows from D12 + the consumer being the sign, not a rate. |

## The request's (D1) as written — asked explicitly

**The request's displayed (D1) already carried the denominator** `‖v_in − w‖²`:

> `λ_a := inf_{f∈W_a} Q[f]/‖f‖² = inf_{w∈W_a} Q[v_out + w] / ‖v_in − w‖²`

That formula **is** the normalised object, and it **is** D10 — the verdict adds only the
`w ≠ v_i` exclusion (necessary: that point is exactly 0/0) and the ℰ-closure domain. So the
verdict's "fatal distance reading" kills:

1. the **prose** of the request §1 ("Reading: the window floor is the Q-distance² of the theta
   TAIL to the window space") and the same prose in the probe's reading 2 — because under RH
   the ordinary distance is 0 by D12 and the phrase "Q-distance²" is only a distance if the
   denominator is carried along;
2. the **literal statements of Q2(a) and Q2(b)**, which drop the denominator
   (`inf_w Q[v_out+w] ≤ C(a)T²‖Φ‖²` / `≥ c(a)T²‖Φ‖²`) — the first is vacuous, the second false;
3. the request's Q1(c) rider "the best of them is the object" — D10 shows all radical
   representatives give the *same* value.

It does **not** kill the displayed (D1). The verdict says this itself in its header
(`D1_WITH_NONZERO_DENOMINATOR: valid_on_full_local_logarithmic_form_domain`) and in §0
("The affine identity survives"). This is a fair reading of the request, not a strawman.

## Section 6 scoring — is it fair?

Yes, and it errs against the verdict's own interest rather than in its favour.

* `P_IDENTITY_ON_CLOSURE` (0.85) → CONFIRMED WITH REPAIR: correct; the only "repair" is the
  0/0 exclusion, which is real.
* `P_FAMILY` (0.60) → CONFIRMED ON THE E-RADICAL: correct, with the honest rider that all
  representatives give one value (killing the request's "best of them").
* `P_UPPER_T2` (0.55) → NOT ESTABLISHED. **Strictly, the literal prediction was satisfied**
  (an unconditional upper bound with `C=0`). The verdict refuses that win explicitly ("The
  literal numerator bound is vacuous") and scores the meaningful event instead. Harsher on
  itself than the letter requires; not unfair.
* `P_LOWER_T2_UNDER_RH` (0.30 / alt 0.55) → LITERAL REFUTED; NORMALIZED UNRESOLVED. This is
  the **one debatable cell**: the observer's registered alternative ("no rate, only ≥ 0") is
  in fact what holds for the *normalised* object under RH, and the verdict declines to award
  it on the ground that it was registered about the unnormalised object. Defensible, but a
  reader could reasonably score the alternative as CONFIRMED-for-the-normalised-question.
  Flagged, not counted as an error.
* `P_MECHANISM_NAMED` (0.60) → REFUTED AS THE REGISTERED PROJECTION CLAIM: correct — D19 is
  not an unconstrained projection. Note that the *other half* of the prediction (an explicit
  integral equation with the screw kernel on (−a,a)) **is** delivered by D20/D21; the verdict
  does not claim that half as a win.
* `P_OFFLINE_WINDOW` (0.50) → CONFIRMED WITH CONDITIONING DISCLOSED: correct, and the
  disclosure is material — the request asked for `a₀(δ,γ)`, and D32 gives `a₀(B,r)`, which
  depends on the zero's multiplicity and on `Λ^{(r)}(λ)`, not on `(δ,γ)` alone. Said plainly.
* `P_COERCIVE_EMPTY` (0.70) → REFUTED AS STATED: correct (D14 is a genuine unconditional
  finite floor; D36 is genuinely positive for `a < 0.0371`), with the substantive part of the
  prediction (no vanishing all-window error) explicitly preserved.

No prediction is re-defined in the verdict's favour; two are scored against it.

## Research-log locators

| Locator | Status |
|---|---|
| [S26] arXiv 2606.09096v1, (1.3), (1.5)–(1.8), Theorem 1.1, Corollary 1.2, Lemma 3.1 | **VERIFIED** from the local PDF `docs/routeB_bus/litreview/pdfs/2606.09096.pdf` (Suzuki, *Weil's quadratic form via the screw function*). Line hits: (1.3) screw function with the `−4(e^{t/2}+e^{−t/2}−2)` pole part; (1.5) `G_a=P_aGP_a`; (1.6) `B_a=D*G_aD`, `D(B_a)=H₀¹`; Theorem 1.1 Friedrichs extension; (1.7) the variational `λ_a`; (1.8) `Q_W^a(v)=⟨B_av,v⟩`; Corollary 1.2 on the minimiser's domain; Lemma 3.1 cited at line 283. Every use the verdict makes of [S26] is accurate. |
| [S23] arXiv 2301.00421v3, Theorem 1.1, (1.1)–(1.4) | **PARTLY VERIFIED** (WebFetch, abstract only). Abstract confirms both load-bearing points the verdict uses: the completion is taken **"under the Riemann hypothesis"**, and the space "is isomorphic to a de Branges space by a composition of the Fourier transform" — i.e. an equivalence-class identification, not a pointwise window-interpolation bound. The exact content of Theorem 1.1 I could not read (abstract page only). |
| [Z] arXiv 2608.24827v2, Theorems 1.2–1.3, Corollary 6.3, Table 3, Conjecture 12.1 | **VERIFIED** (WebFetch of abs + html). Paper exists, title/author/versions as above; every one of the five locators resolves to a statement matching the verdict's description. |
| [K], [H], [P], [J], script, sc_build blobs | **VERIFIED** as listed in the pin table at the top. |

## First incorrect statement

**None found in D2–D37 or in sections 1–5.**

I attacked the two places most likely to hide an arithmetic slip:

* the chain `B(u_b) ≤ 2e^{4b}B` → `‖u_b‖_E ≤ √(34B)e^b` → `e ≤ 5√(2B)e^{−s+2b}` →
  `220√68·Be^{−s+3b} + 1100Be^{−2s+4b}` → `3000Be^{−s/4}`. My first pass thought the `e^b` in
  `‖u_b‖_E` should be `e^{2b}` (which would have destroyed the `b=s/4` choice). It should not:
  the Dirichlet part of `‖u_b‖_E` is **translation-invariant**, so only 𝒲 picks up `e^{2b}`,
  and `32B + 2e^{2b}B ≤ 34Be^{2b}` is exactly right. The constant 34 is sharp for this route
  and 220√68 = 1814.166… follows to 12 digits. The verdict is correct here;
* the pole factor in D14. `2 sinh(a)` per moment, so `4 sinh(a)` for the pair — the verdict's 4.

The only statements I would call *presentationally* risky:

1. §4.4 reads "There are also strictly positive sufficiently small windows: **if 2a < log 2**,
   … [D36]". The inequality D36 is valid on all of `2a<log 2`, but the bracket is **negative**
   on essentially all of that range: it crosses zero only at `a* = 0.0371153`, and is
   −1.305/−2.500/−3.410 at a = 0.1/0.2/0.3. "Sufficiently small" is doing all the work and
   `2a<log 2` is only the no-prime-overlap condition. Nothing false is asserted, but a reader
   who takes `2a<log 2` as the positivity regime will be wrong by an order of magnitude in a.
   Recommend adding the number `a < 0.0371` where D36 is used.
2. §6's `P_LOWER_T2_UNDER_RH` cell (see above): defensible but the observer's registered
   alternative is arguably confirmed for the normalised question.

## What I could not check

* The `f`-extension of D6 from the compact smooth core to all of ℰ (dominated zero-side
  majorant, rapid vertical decay of `F_g`, `N(T)=O(T log T)`) — I verified the identity
  numerically on a compact smooth non-pole-null test to 1.2e-11, and re-read (K16)'s argument,
  but I did not re-prove the majorant.
* One technical step in D9's fractional-Hardy absorption: `N ≤ (√2−1)N' + C[f]²` and its mirror
  are added and absorbed, which requires `N, N' < ∞` a priori. Standard (prove for `f∈C_c^∞`
  vanishing near 0, then pass to the limit) but the verdict does not say it. Not an error;
  an unstated step.
* The `‖P_jMP_k‖ ≤ C2^{−|j−k|/4}` line is one sentence in the verdict; I reconstructed the
  proof (M bounded on L² and on H^{1/4}, Bernstein on dyadic blocks, duality for `k>j`) and it
  works, but I did not verify it as literally written.
* Whether `q_λ, q_{jλ}` and the `J_λ` iteration keep double-exponential decay of *all*
  derivatives (D25/D28) — I took (K19)–(K20) as read, as the verdict does.
* [S23] Theorem 1.1's exact statement (abstract only; the PDF is not on the shelf).
* The [Z] certificates themselves (interval arithmetic) — the verdict explicitly does not
  rerun them either, and neither did I.
* D24's inequality and the all-vector sampling lower bound under RH — these are the verdict's
  own declared open remainders, not claims.
* Whether the compact-smooth core statement of §1.2 holds verbatim on the full ℰ (as opposed
  to (K7)'s ℋ, where KERNEL §2.2 proves it). The verdict's version drops the moment-restoration
  step, which is legitimate because no moment constraint is imposed on ℰ; I did not re-prove it.

## Verdict

**ACCEPTED WITH CORRECTIONS**

Corrections (none of them mathematical errors in a display; all presentational):

1. **§4.4 / D36** — add the crossover: the bracket
   `2∫_{2a}^∞A₀ − c_A − 4 sinh a` is positive only for `a < a* = 0.0371153`, not throughout
   `2a < log 2`. Values: −1.30532 (a=0.1), −2.49950 (0.2), −3.41049 (0.3). At a = 0.3 the bound
   is valid but sits 3.4 below the observed floor `+7.57e-3`.
2. **§6, `P_LOWER_T2_UNDER_RH`** — state whether the observer's registered alternative
   ("no rate, only ≥ 0", 0.55) is awarded for the *normalised* question; as written the cell
   declines it on a technicality about which object was registered.
3. **§6, `P_MECHANISM_NAMED`** — the verdict delivers the second half of the registered
   prediction (explicit integral equation with the screw kernel on (−a,a), D20/D21) and does
   not say so; only the projection half is refuted.
4. **Research log, [P] row** — the pinned probe blob `11cf942a…` no longer matches the working
   tree (`66937ae2…`); the probe was corrected in place after the verdict, applying D15. Worth
   a line in the next batch so the pin chain stays readable.
5. **D9** — one sentence on why the two half-line weighted norms may be assumed finite before
   they are absorbed into each other.

Everything else stands. In particular D4, D5, D6, D7, D14, D15, D17, D18, D19, D20, D21,
D26, D27, D29, D30, D31, D32, D33, D34, D36 and D37 were each checked by explicit computation
and are correct as printed, the explicit-formula convention of D2 was reproduced from scratch
against 160 zeta zeros to relative 1.2e-11 on a non-pole-null test, the request's displayed
(D1) is confirmed to be the normalised object that survives, D20 **derives** the form↔operator
dictionary that the SCREW/SIGNATURE independent check had flagged as ASSERTED-NOT-DERIVED,
and the D37 threshold **passes** (H = 8242 / 51964 / 688124 at a = 0.60 / 0.65 / 0.70,
against a threshold of 100) → branch **ЕСЛИ_A**.
