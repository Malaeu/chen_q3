# RESONANCECHECK — independent audit of PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06

Own re-derivation + own computation (mpmath/numpy). Opened: the verdict, its parent [PP], the CCM23
PDF, `density_fine_N4096.npy`. Scripts: `i1.py … i8b.py` in this directory.
**No error found that changes any RESULT code.** All eleven items CORRECT at the level a paper check
reaches; the purely analytic justifications stay UNVERIFIABLE from here (§12).

| # | Object | Verdict |
|---|---|---|
| 1 | (2)–(3) symbol, `\|γ_S\|=1`, `γ'/γ = i q_S` | CORRECT |
| 2 | Lemma 1 (4) half-line diagonal `(i/2π)m'/m = q_S/2π` | CORRECT |
| 3 | Lemma 2 (9), ±\|α\| spectrum, (6)–(7) | CORRECT |
| 4 | Lemma 3 (11)–(12) oscillatory exponents | CORRECT |
| 5 | Thm 4 (15)–(17), `∫(1−cosθ)g_2 = w`; array `C_1(X)` | CORRECT (array carrier-limited) |
| 6 | Lemma 5 (20), (28), (29) | CORRECT |
| 7 | (24)–(27) phase law, `h_T`, `ν → −w_p` | CORRECT; (26) complete, in fact stronger |
| 8 | §5.2 odd-lattice zeros ⇒ `h = 0` | CORRECT |
| 9 | §6 (30)–(34), Theorem 6, bound `a r²` | CORRECT |
| 10 | (36) false-factor refutation, `δ_M` | CORRECT given [PP]'s `Q_M` |
| 11 | Normalization repair: `q_∞`, not `q_∞/2π` | CORRECT |

## 1. (2)–(3) — CORRECT
`|γ_S|=1` since `Γ(¼−iξ/2)=conj Γ(¼+iξ/2)` and `b_S(−ξ)=conj b_S(ξ)`; confirmed to 30 dps, P={2,3,5}.
Archimedean factor by direct integration as asked: `∫_0^∞cos(2πuv)v^{s−1}dv=(2πu)^{−s}Γ(s)cos(πs/2)`,
`s=½+iξ`, gives `γ_∞=2(2π)^{−½−iξ}Γ(½+iξ)cos(π/4+iπξ/2)`; ratio to `π^{−iξ}Γ(¼+iξ/2)/Γ(¼−iξ/2)` is
`1+O(1e−31)` at ξ = 0, 0.5, 1, 3, 7.3, 20. Phase: `log γ_S` differentiates to
`i(Reψ(¼+iξ/2)−logπ) − 2iΣ_p a_pΣ_j r_p^j cos(ja_pξ)`; `(γ_S'/γ_S)/i` vs `q_S` agree to 1e−29 at
ξ = 0.7, 1, 3, 10, 25.4. Also verified (19) (`arg c_p = −2arg(1−re^{iaξ})`) and (8) as the exact
expansion of `(1−re^{−iaξ})/(1−re^{iaξ})`.

## 2. Lemma 1 (4) — CORRECT (sign and factor)
With `f̂=∫f e^{−iξx}dx`, multiplication by χ has Fourier kernel `(1/2π)χ̂(ξ−η)`; `1_{(−∞,0]}=(1−sgn)/2`,
`ŝgn=2/(iζ)` ⇒ kernel `½δ + (i/2π)pv(ξ−η)^{−1}` — the verdict's kernel. `|m|=1` kills the δ-part in
`C_mPC_m^*−P`; `m(ξ)conj m(η)−1 ≈ m·conj m'·(η−ξ)` gives diagonal `−(i/2π)m conj m' = −φ'/2π =
(i/2π)m'/m`. Factor and sign confirmed. `m_S(ξ)=γ_S(−ξ)` with `q_S` even ⇒ diagonal `= q_S/2π`.
Structural step also checked: `F_S=C_mR=RC_m^*` (needs `conj m(−ξ)=m(ξ)`, true), so `RPR=I−P` gives
`R_S=I−P−Q_S=C_mPC_m^*−P`.

## 3. Lemma 2 (9), (6), (7) — CORRECT
Finite model (n=12, k=5, random real symmetric involution F, random isometry E):
`Gram−[[I,A],[A,I]]` 1.1e−15 · `WW*−(P+Q)` 2.2e−16 · `D−W[[−A²Z,AZ],[AZ,−A²Z]]W*` 5.2e−15 ·
`(S−R)−D` 1.1e−16 · nonzero eig D `= ±{0.1880,0.3988,0.6379,0.8164,0.9617} = ±eig A` · `Tr D=−1.1e−15`.
`MG=[[0,A],[A,0]]` to 2e−15 — that is why the spectrum is `±|α_j|` and `Tr D_S=0`, so §2.4's "no
globally one-signed `d_∞`" is sound. (6) as an identity: for `V=(φ, γ·conj φ)`, `|γ|=1`, A real
symmetric, `⟨V,MV⟩ = 2Re{γ[t+⟨u,AZ conj u⟩]} − 2⟨u,Zu⟩` to 0.0. (7) holds; my derivation gives the
same constant, `‖AZ‖+‖Z‖=(α+1)/(1−α²)=1/(1−α)`.
Constants of (10) re-derived by hand: `u_p=√(2/π)Σc_jI(β_ju,ξ)` and `t_p=(1/π)Σc_jJ(β_j,−ξ)` — the
**1/π and the opposite frequency in `t_p` are right** — and `β_{−1}=2π/p, c_{−1}=−1/p, β_j=2πp^j,
c_j=1−1/p` follow from (8) plus the stated unitary. (13), (14), the `2(1+α)‖u‖²α^{2d+2}/(1−α²)`
replacement cost and the `(1+r)r^{J+1}` Euler tail all reproduce exactly.

## 4. Lemma 3 (11)–(12) — CORRECT (exponents)
Note on my own first run: naive `mp.quad` on `∫_0^1v^{−½+iξ}cos(βv)dv` fails at T ≥ 100 (reported
`T|I|≈67` at T=1000, β=0, where the exact value is 1). Redone with the exact series
`I=Σ_m(−1)^mβ^{2m}/((2m)!(2m+½+iξ))`, `J` with the denominator squared, `dps≈0.435β+60`; sanity
β=0, T=100 reproduces `1/(½+100i)`.

    beta <= T/2 :  T|I| in [0.10,1.30] ,  T^2|J| in [0.21,2.18]        (T = 10 ... 3000)
    beta >  T/2 :  sqrt(b)|I| in [0.05,1.45] , sqrt(b)|J|/(1+log(2b/T)) in [0.0007,0.92]
    (12) L2     :  ||I(bu,xi)||_{L2(0,1)} / stated bound in [0.34,0.84]

All four exponents of (11) and both branches of (12) hold, observed `C ≲ 2.2`. `sqrt(β)|I| → 1.28`
saturates, so the `β^{−1/2}` exponent is sharp. Not a proved constant — the verdict says so itself.

## 5. Theorem 4 (15)–(17) + diagnostic — CORRECT / carrier-limited
`(q_p−q_∞)/2π = g_p(aξ)` via `Σ_{j≥1}r^jcos jθ=(rcosθ−r²)/(1−2rcosθ+r²)`, so (16) ⇔ (17).

    g_2(pi) = 0.091390257925556   (log2/pi)(sqrt2-1) = 0.091390257925556
    g_2(0)  = -0.532661458230859  -(log2/pi)(sqrt2+1)= -0.532661458230859
    cos coeff j=1,2,3: -0.1560129, -0.1103178, -0.0780065  = -a r^j/pi (exact)
    int_0^{2pi}(1-cos t)g_2(t)dt = 0.490129071734274 = w = log2/sqrt2  (exact)

`g_p` is strictly monotone in `cosθ` (`df/dc=r(1−r²)/(…)²>0`), so one max at π, one min at 0 per
period — §2.4's "no doublet from the leading term" is right.
DIAGNOSTIC `density_fine_N4096.npy`, `C_1(X)` over one period `2π/log2`, target `−ar/π=−0.156013`:

    X      5     20     50     95    110    125    140    170    200    245    290    350    500
    C_1  -.038  -.133  -.145  -.150  -.150  -.151  -.144  -.107  -.071  -.025  -.003  -.001  -.000
    sine coefficient |S_1| < 8e-4 throughout

Best `−0.1511` at X ≈ 125, 3.1% below target, residual shrinking like a decaying `X^{−1/2}` constant
(0.101 → 0.075 → 0.055 at X = 20, 50, 125). **Beyond X ≈ 280 it collapses to zero — that is the
carrier, not the theorem.** Corroboration: `k_arch − q_∞/2π` (estimate of `d_∞`) gives
`ξ²d_∞ ≈ −5…−10` for 10 ≤ ξ ≤ 150 (consistent with `O(ξ^{−2})`), then diverges (`−0.055` at ξ=400,
`−0.133` at ξ=600) exactly where `C_1` dies. Fixed N=4096 with growing ξ is the wrong order of limits,
as the verdict states. The array also gives `q_∞(0)/2π = −0.855009 = −c_A/2π` with `k_arch(0)=3.1e−9`,
i.e. §2.4's failure of the pointwise ordering.

## 6. Lemma 5 (20), (28), (29) — CORRECT
`Σ_k|ĥ((θ+2πk)/a)|² = aH`, a=log2, δ=0.3, K=2·10^5 shifts: ratio `0.999999` for `h=1_{(−.3,.3)}` and
`1.000000` for the smooth pole-null `h=(∂²−¼)η` (moments 3e−13), flat in θ at θ = 0, 1, 2.3, π, 5 —
Haar, with and without the pole conditions, as claimed. (28) by direct ξ-integration on [−4000,4000]:

    beta         0.3      pi/4      1.0      2.0
    measured   .00143   .024925  .050462  .347173
    (b-sin b)/pi .00143  .024921  .050464  .347175

(29): `β_2 = arccos(2^{−1/2}) = π/4`, fraction `= ¼ − 1/(π√2) = 0.0249209` — matches the β=π/4 row.
The positive band of the leading multiplier is `−g_p>0 ⇔ cosθ>r_p`, as stated.

## 7. §4.2–4.4 — CORRECT; (26) complete and stronger than stated
Pole-nullness of `h_T=(∂²−¼)(η cos Tx)` exact (moments 1e−12). `ĥ_T=−(ξ²+¼)(η̂(ξ−T)+η̂(ξ+T))/2` and
`‖h_T‖²/(T⁴‖η‖²/2)` = 2.010, 1.152, 1.038, 1.009, 1.0015, 1.0004, 1.00004 at T = 20, 50, 100, 200,
500, 1000, 3000 (needs `T² ≫ 6‖η'‖²/‖η‖²`). On (26): I re-derived the coefficient and the Euler part
is **exact, not asymptotic** — with `C_h(ja_q±b)=0` off the matching atom,
`(1/H)∫cos(bξ)cos(aξ)|ĥ|²dξ = π`, so the Euler contribution to ν is `−(ar/π)·π = −a_pr_p = −w_p` for
every T. Only two pieces need the limit: `(1/2πH)∫cos(bξ)|ĥ|²q_∞dξ = −J_b` and the `d_S` integral.
`J_b(h_T)` = 3.6e−3, 2.1e−3, 4.1e−4, 6.0e−6, 7.1e−10, 8.5e−14, 2.4e−17 at T = 0, 5, 10, 20, 50, 100,
200. Since `ν+J_b+W_{S,b} = (1/H)∫cos(bξ)|ĥ|²d_S dξ` identically, `e_S(v_θ)→0` follows from (15)/(18)
alone. §4.1's table re-derived: the binding conditions are `2δ<log(4/3)`, `2δ<log(5/4)`, `2δ<log(8/7)`
for separations `log3, log5, log7`; at `δ_0=(log3−log2)/8`, `2δ_0=0.1014 < 0.1335=log(8/7)`; the
full-window prime columns are right (`e^{log7+0.101}=7.75`). (27) is sound: one pair `(p,h_{p,T})`
with `log p>2C` refutes a claim quantified over all primes and all inputs; the limit is in T at fixed
p, as declared.

## 8. §5.2 — CORRECT
`g(x)=h(x)e^{−iπx/a}` extended by zero to an interval of length `a` has Fourier-series coefficients
`ĥ(π/a+2πn/a)=ĥ((2n+1)π/a)`, all zero by hypothesis, so `g=0`, so `h=0`. Only `supp h` shorter than
`a` is used. The corollary about finite lists follows since (28) depends on support alone.

## 9. §6 (30)–(34) — CORRECT
`C_v(ℓa)=Re A_ℓ/s_c` by expanding the autocorrelation ⇒ (30). Theorem 6: `P(−1)=0`, `s_c=6`, `A_1=1`,
`A_2=−2`, `𝒜_2(P)=0.06767270294189061` vs `(log2/3)(1−1/√2)=0.06767270294189055`.
`|P(e^{iθ})|²=6+2cosθ−4cos2θ` (max deviation 5e−15). (32) by quadrature:

    beta        0.3      pi/4      1.0      2.0
    measured  .066938  .218923  .311113  .813398
    (32)      .066938  .218923  .311113  .813398

small-β expansion `2β/(3π)+O(β³)` — linear, unlike (28). (33): with `(u,u+v,v)`, `s=u+v`, `d=u−v`,
`s_c=(3|s|²+|d|²)/2`, `ReA_1=|s|²`, `ReA_2=(|s|²−|d|²)/4`, giving exactly
`a(r²|d|²−(4r+r²)|s|²)/(3|s|²+|d|²)`; tested on 2·10^5 random complex `(u,v)`, identity to 1e−10
relative, sample max `0.3465646 ≤ ar²=0.3465736`, attained at `s=0` (`P∝1−z²`, middle lobe zero), and
`ar²=0.3466 < a/√2=0.4901`. (34): `(1/s_c)∫_0^{2π}|P(e^{−iθ})|²g_2 dθ = 0.06767270294189094 = 𝒜_2(P)`.

## 10. (36) — CORRECT given [PP]
[PP §4.1] fixes `Q_M(v)=2a‖v‖²+4aΣ_{j≥1}cosh(ja/4)C_v(ja)`. With `‖v_-‖²=1`, `C_{v_-}(a)=−½`,
`C_{v_-}(ja)=0` for `j≥2`: `Q_M(v_-)=2a−2a cosh(a/4)=−0.020866177122149` and
`δ_M=2a(cosh(a/4)−1)=0.020866177122149` — identical. `Q_M(v_{−,T})` is shape-independent (it uses only
`C_v` at lattice points, fixed by the lobe structure), so `m_♯(h_T)=m(h_T)−δ_M` for all T, and
`m(h_T)=−∫W_{h_T}d_2→0` by (15). (36) follows; it refutes whole-class survival only, which is what the
verdict claims.

## 11. Normalization repair — CORRECT
It is `q_∞`. From `ψ(z)=−γ+∫(e^{−t}−e^{−zt})/(1−e^{−t})dt` with `t=2s`:
`Reψ(¼+iξ/2)−logπ = 2∫a_∞(s)(1−cos ξs)ds − c_A`, `c_A = γ+3log2+π/2+logπ = 5.3721834192257`
(equivalently `c_A=−(ψ(¼)−logπ)`). Both sides at ξ = 1, 3, 10: `−2.0251461931034672` /
`−2.0251461931034672`; `−0.7442440597403975` / `−0.7442440597402702`; `0.4642906268649303` /
`0.4642907459420310` (residual = quadrature). `q_∞/2π` is off by 2π at every ξ (`−0.3223`, `−0.1185`,
`+0.0739`). The array's row 1 is `q_∞/2π`, so [DF]'s normalization is the one the verdict describes.

## 12. Not covered (UNVERIFIABLE from here)
(i) trace-class justification of `T_hPF_SP` and the Hankel/commutator splitting; (ii) the
regularization making `⟨f_ξ,D_Sf_ξ⟩` the a.e. density representative in (6), incl. the `u=ε` passage;
(iii) `α_S<1` as a numerical value (strictness argument fine, certified bound absent); (iv) `TrD_∞=0`
needs `Σ|α_j|<∞`, asserted not proved; (v) (18)'s multi-prime shell count; (vi) constants `C` in
(11)–(13) — my measured `C ≲ 2.2` is diagnostic, not an interval certificate.
One wording remark, not an error: §4.3 calls (26) "exact phase averaging", but the Euler part is an
exact support/orthogonality identity at every T; only `J_b` and `∫d_S` need `T→∞`.

## Consequence for the RESULT codes
None. `Q2: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE`, `Q1a`/`Q3a: PROVED_ON_CLASS` and all three
`SCOPED_REFUTATIONS` (uniform `C·r_p`; all-odd-lattice zeros; whole-class false-factor survival) are
supported by everything I could reach. The `PARTIAL_WITH_PRECISE_REMAINDER` codes are honest: (R-INC)
and (R-SIGN) stay open and nothing here closes them. The diagnostic array agrees with the amplitude
law where the carrier is valid (ξ ≲ 150, 3% at best) and fails above ξ ≈ 280 — the carrier artefact
the verdict itself predicts, not evidence against Theorem 4.
