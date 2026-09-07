# CHAINCHECK — independent check of PROSHKA_VERDICT_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07

Method: own re-derivation of every step + independent numerics. Two computational channels for §8.4
(real-space `𝒟`-form matrix algebra vs. pointwise grid + FFT autocorrelation) — they agree to 7 digits.
Scripts `chk1..chk9.py` in this directory. Read set: CHAIN verdict, PROFILES §1/§3, PROFILESCHECK.

---

## 1. §2.1 (C2)–(C4) three-lobe witness — **CORRECT**

`M_±(U_sη)=e^{±s/2}M_±(η)` (PROFILES §1, confirmed there) ⟹ total-moment rows on `Σz_iU_{x_i}η` are
`Σz_ie^{x_i/2}` and `Σz_ie^{−x_i/2}`; with `x=(0,log2,log3)` this is exactly
`V₃=[[1,√2,√3],[1,1/√2,1/√3]]` ✓ **reconstructed, not copied**.
`V₃z=(0,0)` exactly (sympy), `‖z‖²=12` ✓; sympy nullspace is 1-dimensional with basis
`(√3/3,−2√6/3,1) = −z/√3` — so `z` spans the **entire** kernel, "true kernel" is right.
Witness: `η=1_{[−δ/2,δ/2]}*ρ`, `∫η=δ` ✓, `‖η‖²≤‖1‖²‖ρ‖₁²=δ` (Young; asserted in the text, not proved).
Ratio `Σ|∫h_i|²/Σ‖h_i‖² = ‖z‖²δ²/(‖z‖²‖η‖²) = δ²/‖η‖² ≥ δ` ✓.
`δ=(log3−log2)/8=0.05068314 > 1/20` (from `log(3/2)=0.4054651>2/5` ✓) `> d/25=13/3125=0.00416` ✓.
Admissibility: supp η ⊂ (−3δ/4,3δ/4), width `1.5δ=0.0760 < d=0.104` ✓ — inside P1's own support class.
`R₃=(b+2δ)/2 = 0.599989282847575 = (5log3−log2)/8` ✓ (15 digits).
**Scope statement is accurate:** this refutes the *copied* (P17), not Theorem P1 on its own two-lobe domain.

## 2. §2.2 (C5)–(C7) energy budget — **CORRECT**

(C5) is asserted ("P's energy argument gives"), **not derived**. I derived it: (P18) applies lobewise
(pairwise centre gaps `0.4055, 0.6931, 1.0986` all `> d`), cross-archimedean cost `≤ 2J(|x_i−x_j|,d)‖h_i‖‖h_j‖`,
prime cost `≤ 2w_n‖h_i‖‖h_j‖` at the lags that are logs of integers. Lags: `log2`(w₂), `log3`(w₃),
`log(3/2)` — **not** a log of an integer, so no prime atom ✓ as stated. Γ as printed is right.
Rational chain, every step verified numerically:

| step | claim | value | ok |
|---|---|---|---|
| `dA(d)` | `< 3/5` | 0.525739625293 | ✓ |
| `coth(d/4) ≤ 1+4/d` | | 38.4702 ≤ 39.4615 | ✓ |
| `(1+4/d)/(8π)` with `π>3` | `= 171/104` | exact (Fraction) | ✓ |
| `log(171/104) < 1/2` via `e^{1/2}>79/48` | | 0.497273 < 0.5; 1.648721 > 1.645833 | ✓ |
| `log coth(d/4) − log 8π < 1/2` | | 0.425713 | ✓ |
| `2arctan e^{−d/2} < π/2` | | 1.518820 < 1.570796 | ✓ |
| `γ_E > H₆−log7 > 1/2`, `e^{39/20}>7` | | 0.504090 > 0.5; 7.02869 (8 Taylor terms: 7.02211>7) | ✓ |
| `2∫_d^∞A − c_A < 0` | | −0.203480 | ✓ |
| `√(w₂²+w₃²) > 3/5` | `w₂>4/9, w₃>4/7` | 0.801588; rational floor `√(16/81+16/49)=0.723921` | ✓ |
| Perron argument | `λ_max(Γ) ≥ λ_max(star)` | valid: `Γ ⪰ S` entrywise, `x≥0` Perron vector | ✓ |

**Exact bracket:** with the full Γ (`λ_max(Γ)=1.198697`), `B₃(d) = −0.876437155818`.
With only the stated prime-star floor, `B₃(d) ≤ −0.479327701084`. Strictly negative either way ✓.
(C7): prime part on `z` `= (−2w₂z₀z₁−2w₃z₀z₂)/‖z‖² = (4log2−2log3)/12 = log(4/3)/6 = 0.0479470121` — sympy
exact identity ✓, and reproduced to 1e-16 by the independent 9×9 assembly in §7 below.
**Scope statement accurate:** (C6) is a negative *sufficient budget*, never an upper bound on Q.

## 3. §2.3 (C8)–(C9) large radius — **CORRECT**

(C8) bracket asserted, derived here: `∫₀^L‖U_tf−f‖²dt = 2L‖f‖²−|m|²`, `|m|²≤L‖f‖²`, `A` decreasing
⟹ `𝒟(f) ≥ [LA(L)+2∫_L^∞A]‖f‖²` ✓ exactly as printed.
PNT: `Σ_{n≤x}Λ(n)n^{−1/2} = ψ(x)/√x + ½∫₁^xψ(t)t^{−3/2}dt ~ 2√x`; at `x=e^{2R}` that is `2e^R` ✓.
Numeric ratio `Σw_n/(2e^R)`: R=3 → 0.9359, R=4 → 0.9778, R=5 → 0.9905, R=6 → 0.9968 ✓.
First two terms of (C8) → 0 ✓, so `B_gross(R) ~ −4e^R → −∞` ✓.
`J_A = 2Σ(2j+½)^{−3} = ζ(3,¼)/4 = 16.1659674922 < 18` ✓ (`∫₀^∞A(t)t²dt` with `A=Σe^{−(2j+½)t}` ✓,
`‖U_tf−f‖≤t‖f'‖` ✓). Pole moments of `h_R=(∂²−¼)g_R` vanish exactly (two integrations by parts) ✓.
`‖h_R‖→‖g‖/4`, `‖h_R'‖=O(1/R)` ✓. Explicit constant `1152(‖g'‖/4+‖g'''‖)²/(R²‖g‖²)` re-derived: it is
`64·J_A` with `J_A<18` and `‖h_R‖≥‖g‖/8` under `R²≥8‖g''‖/‖g‖` ✓.
Numerics, `g=(1−x²)⁴`, spectral form `𝒟=(2π)^{-1}∫W|ĥ|²`:

| R | `𝒟/‖h‖²` | `R²·ratio` | `[𝒟−c_A‖h‖²]/‖h‖²` |
|---|---|---|---|
| 4 | 2.968723e+00 | 47.500 | −2.403461 |
| 16 | 3.197398e−01 | 81.853 | −5.052444 |
| 64 | 1.930869e−02 | 79.088 | −5.352875 |

`R²·ratio → J_A‖g'‖²/‖g‖² = 78.5` (predicted independently) ✓ ⟹ `O(R^{−2})` confirmed and the constant
`J_A` is asymptotically sharp (`W(ξ)/ξ² → J_A`: 16.1596 at ξ=0.01 ✓). Ratio → `−c_A=−5.372183` ✓.

## 4. §4 explicit tail (R6) — **CORRECT**; §4.4 domain/core argument **sketch-level**

(C10): `q(0)=−c_A` to 15 digits ✓. Series `q(ξ)+c_A = Σ(ξ/2)²/[(j+¼)((j+¼)²+(ξ/2)²)]` matches
`Reψ(¼+iξ/2)−ψ(¼)` at ξ=0.5, 2, 10 to 15 digits ✓; each summand increasing in |ξ| ✓ ⟹ monotone ✓
(values −5.3722, −3.3320, −2.0251, −1.1616, −0.2301, 1.1578, 5.0699 at ξ=0,½,1,2,5,20,1000).
(C11): summand `≥1/[2(j+¼)]` when `j+¼≤ξ/2` ✓; `Σ_{j≤J}1/(j+¼) ≥ log(4J+5) ≥ log 2T` with
`J=⌊T/2−¼⌋` ⟹ in fact `q(T) ≥ ½log(2T) − c_A`, stronger than printed. Tested:

| T | q(T) | `½log(T/2)−c_A` | partial harmonic sum | `½log 2T` |
|---|---|---|---|---|
| 2 | −1.161557 | −5.372183 | 2.0000 | 0.6931 |
| 5 | −0.230118 | −4.914038 | 2.6222 | 1.1513 |
| 100 | 2.767289 | −3.416172 | 4.0672 | 2.6492 |
| 10⁴ | 7.372463 | −1.113587 | 6.3723 | 4.9517 |

(C12): `h_n=2n/m_n ≤ 1/(2K_n)` ✓ by `m_n=⌈4nK_n⌉`. (C14) re-derived in full: `y⊥1_{J_i}` ⟹
`⟨y,g⟩=Σ∫_{J_i}ȳ(g−g_{J_i})`, `‖g−g_J‖_{L²(J)}≤|J|‖g'‖_{L²(J)}` ✓, Bernstein `‖g'‖≤K‖g‖` ✓,
`g=P_Ky` ⟹ `‖P_Ky‖²=⟨y,P_Ky⟩ ≤ ½‖y‖‖P_Ky‖` ⟹ `‖P_Ky‖² ≤ ¼‖y‖²` ✓ — **constant is right**.
(C15) reconstructed exactly as the task states: arch `= (2π)^{-1}∫q|ŷ|² ≥ q(K)·¾‖y‖² − c_A·¼‖y‖²`
(`q(K)>0` here, so the mass lower bound on `|ξ|>K` is used in the right direction ✓); primes
`≥ −2W_n‖y‖²` from `|C_y(t)|≤‖y‖²` ✓; pole `=0` since `y⊥e^{±x/2}` ✓.
Arithmetic verified symbolically: `¾(2C_n−c_A)−¼c_A−2W_n = 3C_n/2−c_A−2W_n = ½c_A+W_n+3/2` ✓ (sympy),
`≥ ½c_A+3/2 = 4.1861 > 1` ✓. `q(K_n)≥2C_n−c_A` follows from `K_n≥2e^{4C_n}` and (C11) ✓.
**No gap found in R6.** Cost, as the verdict itself says: `n=1` already gives `W₁=2.9262`, `C₁=12.2247`,
`K₁≈10^{21.5}`, `m₁≈10^{22.1}` cells — an existence bound only.
**Named gap:** §4.4 (form domain, boundedness of the cross map, `C_c^∞` a core) is a two-sentence sketch.
It is load-bearing for (C17) applied to smooth `f`, and for the converse in item 8.

## 5. §5 (C16)–(C21) — **CORRECT**

`v_z ⊥ y` (`y∈V_n^⊥`) ⟹ `‖v_z+y‖² = z*G_nz+‖y‖²`; minimising the quadratic in `y` gives
`y_min=−(B_n+ε)^{−1}E_nz` and exactly (C17) ✓, hence R7 in **both** directions ✓ (`B_n+ε` invertible by
`B_n⪰I` from (C15), which is proved before it is used — no circularity).
(C18) expanded by hand: `Z*(B+ε)^{−1}Z = E*(B+ε)^{−1}E + E*Y + Y*E + Y*(B+ε)Y`, so
`C^Y − Z*(B+ε)^{−1}Z = A+εG−E*(B+ε)^{−1}E = S_n(ε)` ✓ identity.
(C19): `B+ε ⪰ (1+ε)I` ⟹ `(B+ε)^{−1} ⪯ (1+ε)^{−1}I` ⟹ both envelopes ✓.
2×2 detector: `S(0)=1−2·1·2=−3` ✓; `[[1,2],[2,1]]` on `(1,−1)` gives `−2` ✓.
(C21): `S_n(1/n)⪰0 ⟹ Q(f) ≥ −‖f‖²/n` on `𝒟_n`; `Q(f)` is defined by (C1) on `f` alone, so it is the
same number for every `n` with `f∈𝒟_n`; `n→∞` ⟹ `Q(f)≥0` ✓. Sound, no uniform gap needed.
Notation clash worth fixing: `C_n` is the scalar of (C12) **and** the matrix `C_n^Y` of (C18).

## 6. §3's correction of the observer — **Прошка is right, and the observer's point survives**

Logically he is right: `∪_n𝒟_n = C_c^∞`, so `Q|_{𝒟_n} ≥ −(1/n)‖·‖²` for every `n` already forces `Q≥0`;
no uniform positive gap, and no identity, is required — an inequality whose slack vanishes suffices.
The observer's claim is about *technique*, not sufficiency: if the certified per-window margin collapses
super-exponentially, no estimate carrying a fixed absolute loss can be transported from window `n` to
window `n+1`, so the family `{c_n}` must come from **one** finite argument valid for all `n`, not from
window-by-window certificates. Both statements are true and do not conflict; Прошка's own
"finite per support is not finite proof of all supports" is the same observation.

## 7. §8.4 nine-generator diagnostic — **CORRECT**, and I ran the floor

Integration by parts (η even, compact): `M_±(η')=∓½M_±(η)`, `M_±(η''−η/4)=¼M_±(η)−¼M_±(η)=0` ✓.
Numerically (`δ=0.0506831`, standard bump): `m_η=0.0112516428520306`, `M_±(φ₁)=∓0.00562582142602`
`= ∓m_η/2` ✓, `M_±(φ₂)=3.7e−33` ✓. The 2×9 row matrix `e^{±x_i/2}(1,∓½,0)` has singular values
`(2.8875, 1.2059)` ⟹ **rank 2, kernel dimension 7** ✓.
Beyond the task: I assembled the full 9×9 source form from (C1) — archimedean `𝒟−c_A G` from the exact
autocorrelation algebra (all `ρ_{ab}` reduced to `A₀^{(k)}`, `k≤4`), prime atoms at `log2`/`log3` only
(verified: no other pair-lag is a log of an integer), pole term — and diagonalised it against the exact
physical Gram on the 7-dim kernel:

`generalized eigenvalues = [1.7443, 2.0888, 2.8899, 3.3307, 3.6916, 4.2069, 4.9374]`, **floor 1.7443**.

Independent second channel (build `f` pointwise on a 2e−6 grid, FFT autocorrelation, numeric `M_±`):
`Q/‖f‖²` = 4.36768548 / 4.13155508 / 1.81315971 (matrix channel) vs 4.36768500 / 4.13155468 / 1.81315939
(grid channel) on three kernel vectors — agreement to 7 digits. The lost mean direction `z⊗φ₀` itself gives
`Q/‖f‖² = 1.8132 > 0`, consistent with (C7). `cond(G)=2.2e8`, so the floor is good to ~1e−6.
This is **not** a certified enclosure and not the whole three-lobe class (C22) — only the frozen packet.

## 8. Overall

**IRREDUCIBLE_ATOM with ATOM = «`S_n(1/n)⪰0` ∀n» is a correct summary of the state, and the atom is
equivalent — not weaker, not stronger — to the terminal statement.** Forward: (C21) ⟹ `Q≥0` on all
compact smooth tests ⟹ RH by R10. Converse: `Q≥0` on `C_c^∞((−n,n))` extends by density (§4.4's core
claim) to the form domain of `𝒟_n`, whence `Q+(1/n)‖·‖²≥0` and, by R7, `S_n(1/n)⪰0`. So "RH in
finite-head coordinates" is the right description, and the document's own strongest-attack line — "you
have only moved the original unknown into `S_n`" ... "for the universal sign this objection is correct" —
is the accurate reading. The genuinely new content is R4/(C2)–(C3), (C9), and R6/(C10)–(C15), not a
reduction of RH. `IRREDUCIBLE_MEANS: relative to this shelf` is stated correctly; no proof of the atom
is asserted anywhere; `PX_RH_CLAIM: NOT_MADE` matches the content.

**First asserted-not-derived step.** Literally first: `‖η‖²≤δ` inside (C3) (Young's inequality, one line,
unstated). First *substantive* one: **(C5), §2.2** — "P's energy argument gives" the three-lobe
`b₀(d)H−A(d)‖m‖²−u^tΓu` with the stated Γ; the generalisation of (P19)–(P20) to three centres and the
identification of Γ's entries are not shown. I re-derived it; it is correct.

**Registrations.**
- `P_CHAIN_THREE_LOBE_MEAN_FALSIFIER_SURVIVES` (0.98) — **ACCEPT**. (C2),(C3),(C6),(C7) verified exactly,
  scope statements accurate. 0.98 is if anything low.
- `P_CHAIN_EXPLICIT_FULL_SUPPORT_TAIL_SURVIVES` (0.90) — **ACCEPT WITH CAVEAT**. (C10)–(C19) verified in
  full. The clause "including the form domain" is accepted only at sketch level: §4.4 is a two-sentence
  argument for the core/density and the boundedness of the cross functionals, and it is load-bearing.
- `P_CHAIN_FROZEN_SEVEN_DIMENSIONAL_THREE_LOBE_FLOOR` (0.65) — **NOT YET ACCEPTABLE AS REGISTERED, but
  numerically supported far beyond the threshold**: my two-channel computation gives floor 1.744 vs the
  registered 1/100. What is missing is the certified part (proved envelopes with error ≤1/1000 in the
  exact Gram norm); at double precision with `cond(G)=2.2e8` I have ~1e−6, not a certificate. Given the
  120× margin, 0.65 is far too low as a probability; the residual risk is the error ledger, not the sign.

**Gaps found:** none in R1–R7, R9, R10 as *derivations*. Named: (i) §4.4 sketch (above); (ii) (C5) and
(C8) brackets asserted without derivation (both correct); (iii) `C_n` notation collision; (iv) the tail
constants make `dim V_n ≈ 10^{22}` at `n=1`, which the verdict itself flags. No arithmetic or sign error
was found anywhere in §2, §4, §5 or §8.4.
