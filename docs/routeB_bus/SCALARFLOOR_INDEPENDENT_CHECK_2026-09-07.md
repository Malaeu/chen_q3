# Independent check — PROSHKA_VERDICT_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07

Independent re-derivation + own computation (sympy/mpmath/numpy). Read only: the verdict, its parent
(RESERVOIR_RESONANCE 2026-09-06), `prod_op.py`, `prod_t.py`. Scripts: `chk_*.py` in this directory.
**Headline: no mathematical error found in the verdict; item 10 is STRONGER than the verdict states.**

## 1. Theorem 1 — (4), (5), (6) — CORRECT

(4) re-derived: `K=P+Q`, `PS₀=QS₀=0 ⇒ KS₀=S₀K=0`, so `D²=K²−2K+I−S₀`, `D+D²=K²−K=PQ+QP`.
Numerics: 6 random complex projection pairs (n=9) + one forced 3-dim common kernel, max error 5.6e-16.
(5): `Tr(T_vD²T_v*)=‖T_vD‖²_HS ≥ 0` (diff 2.1e-14) — the remainder sign is an identity, not an assumption;
with `n_S−L_S=Tr(T_vD_ST_v*)` this gives (5) exactly (2.3e-14).
Cross term: verified `W[[0,A],[A,0]]W* = PF_SPF_S+F_SPF_SP = PQ_S+Q_SP` for `W=(E,F_SE)`, `A=E*F_SE`
(exact block algebra); `W*f_ξ=(f_ξ|₍₀,₁₎, γ_S f_{−ξ}|₍₀,₁₎)` gives `2Re(γ_St_S)=ℓ_S`. (6) then follows from
(1)–(2) with `|v̂_h|²=W_h` (verified: `v̂_h=−2i sin(aξ/2)ĥ/√(2H)`, `‖v_h‖=1` since `2δ=0.101366<a=0.693147`).
`∫W_h=2π` re-derived from Plancherel + vanishing autocorrelation at `a`; diameter `a+2δ=0.794513<log3`.
Both moments of the exact `h₄` vanish numerically (2.8e-29). §3.1 (10) also re-derived (periodized `|ĥ|²≡aH`).

## 2. (7) and the planted failure — CORRECT

Own derivation with `w=e^{−iφ/2}u`, `X=Re w`, `Y=Im w`, `A` real symmetric: `⟨u,Zu⟩=⟨X,ZX⟩+⟨Y,ZY⟩`,
`Re γ⟨u,AZū⟩=⟨X,AZX⟩−⟨Y,AZY⟩`, hence `ℓ−d=2⟨X,(I−A)ZX⟩+2⟨Y,(I+A)ZY⟩=2⟨X,(I+A)⁻¹X⟩+2⟨Y,(I−A)⁻¹Y⟩`.
Numerics: 5 random 6×6 real symmetric contractions (α=0.9), (6)-of-parent vs (7) agree to 1e-10; both
square-root phase branches give the same value, as claimed.
Planted `A=2, c=i, u=2i, γ=1, t=−2`: `Z=−1/3`, `d=+4.000000`, `ℓ=−4.000000`, `d>ℓ` — exactly as stated.
(7) still holds as an identity there (`−8`), it is only its sign that fails. The judge's reading is right.

## 3. (12)–(13) and the 1-D non-uniformity — CORRECT

`α<1 ⇒ (1+α)⁻¹ ≤ (I±A)⁻¹ ≤ (1−α)⁻¹` and `‖X‖²+‖Y‖²=‖u‖²` give (12); numerics confirm the bracket in all
5 random trials. (13) follows from `𝔪−ℱ=∫W_h(ℓ₂−d₂)`, `W_h≥0`. `𝔪 ≥ ℱ+U` needs only `α₂≤1`. ✓
1-D counterexample `A=1−ε, γ=1, u=i`: `ℓ−d = 2/ε` exactly (checked at ε=1e−1,1e−3,1e−6) with `‖u‖=1`.
No uniform upper bound from `‖u‖` alone. ✓

## 4. Theorem 2 — (14)–(17) — CORRECT

(14) re-derived in Fourier: `B_S`↦`b_S(ξ)`, `B_S*`↦`b_S(−ξ)=conj b_S(ξ)`, `F_∞=C_{m_∞}R`,
`m_S=m_∞b_S(ξ)/b_S(−ξ)`; both sides get symbol `m_∞(ξ)b_S(ξ)f̂(−ξ)`. Exact circle-multiplier model
(N=4096, a=log2, 16 pts/shift, true `γ_∞=π^{−iξ}Γ(¼+iξ/2)/Γ(¼−iξ/2)`): relative error **9.0e-16**; `F_S`
unitary to 0, self-adjoint to 2.7e-4 (grid/Nyquist artifact). Both parent forms of `F_S` agree.
Cutoff invariance: `B_S*=∏(I−r_pU_{−a_p})` and `(B_S*)⁻¹=∏Σ_j r_p^jU_{−ja_p}` shift only left, so with
`P=1_{(−∞,0]}` I get `‖(I−P)B_S*P‖ = 0` and `‖(I−P)(B_S*)⁻¹P‖ = 0` exactly (truncated-shift model).
Norm bounds: symbol modulus `∈[b_−,b_+]=[0.292893,1.707107]` exactly.
Chain: `⟨f,(I−σA_S)f⟩=½‖F_Sf−σf‖²` verified on random self-adjoint-unitary data (err ≤7e-15, both σ);
`‖F_∞g−σg‖=‖B_S*(F_Sf−σf)‖≤b_+‖F_Sf−σf‖` and `‖g‖≥b_−‖f‖` ⇒ (15). For (16),
`(I−P)F_∞g=(I−P)B_S*(I−P)F_Sf` since `(I−P)B_S*P=0`, giving `(1−‖A_∞‖²)b_−²≤b_+²(1−‖A_S‖²)`. ✓
`κ_B²=((1+2^{−1/2})/(1−2^{−1/2}))² = 33.9705627485 = 17+12√2` (diff 7e-15). ✓
(17) follows from the same subspace comparison in both directions — accepted by derivation.
*Caveat (not an error):* no **non-degenerate** finite model meets all hypotheses at once (self-adjoint
unitary `F_S` forces `F_∞` to commute with `B_S*B_S`; in the periodic model `‖A_∞‖=1` exactly and the test
is vacuous). Verified step-by-step instead.

## 5. Theorem 3 — (18)–(22) — CORRECT

Exact finite Sonin model built from scratch (N=64 circle, unitary DFT, `B=I−rU`, random 25-dim `ℋ₀`):
`G=P₀B*BP₀` has spectrum in `[0.5211,2.5166]⊂[g₀,g₁]=[0.0858,2.9142]`; `S₂=BP₀G⁻¹P₀B*` is a genuine
projection (`‖S₂²−S₂‖=3e-15`, rank 25). At 6 frequencies `k₂(ξ)=⟨w^full,S₂w^full⟩` matches
`|1−re^{−iaξ}|²⟨w_ξ,G⁻¹w_ξ⟩` to **≤5.6e-17**; (19) holds every time. Own derivation: `V=BP₀G^{−1/2}` is an
isometry, `𝓕(Bf)=(1−re^{−iaξ})𝓕f`, `Σ_j|⟨G^{−1/2}w_ξ,b_j⟩|²=‖G^{−1/2}w_ξ‖²`.
(20): re-derived (vector error + `‖G⁻¹−Ĝ⁻¹‖≤ε_G/(g₀(g₀−ε_G))`) — stated form right. (21)/(22): completing
the square `⟨w,G⁻¹w⟩=E(y)+⟨z,G⁻¹z⟩` verified to 1e-10 on a 12-dim model, (22) exact there;
`‖FG²F−(FGF)²‖=1444.09≠0` on a rank-6 F — the excursion guard is real.
*Not verifiable here (external):* `𝖲₂=BP₀G⁻¹P₀B*` as the Sonin-space isomorphism (CCM23) and
`‖w_ξ‖²=k_∞` for the actual archimedean space. Marked UNVERIFIABLE-EXTERNAL, plausible and internally used
consistently.

## 6. §5.3 (24) — CORRECT

`ξ*=2π/log2=9.064720284 ∈ (5,16)`; `ξ*/2 = π/a = y = 4.532360142 < 5`. ✓
Partial fractions `Reψ(x+iy)−ψ(x)=Σ_{n≥0}y²/((n+x)((n+x)²+y²))` re-derived, checked (5.73818816878 both
sides). Bound `<4+½log(1+16y²)`: n=0 term `=4y²/(1/16+y²)<4`; rest `≤∫_x^∞y²ds/(s(s²+y²))=½log(1+16y²)`.
Numerically 5.7382 < 6.8991. ✓
`ψ(¼)=−γ−π/2−3log2` confirmed (−4.22745353338 both sides). `½log401=2.99698 < 7/2`. ✓
Numerics: **q_∞(ξ*)=+0.366004749552 < 3** ✓; `2a(1+√2)=3.346810648 > 16/5` ✓;
**q₂(ξ*)=−2.980805899 < −1/5** ✓ (identical via the series definition (3), diff <1e-20);
from `k₂≥0`: **d₂(ξ*) ≥ 0.4744099931 > 1/(10π)=0.03183** ✓. The paper chain is valid and very slack.

## 7. §6 (27)–(29) — CORRECT / one input UNVERIFIABLE

`δ_M = 2a(cosh(a/4)−1) = 0.0208661771221 > 0`. Given a *constant* shift, `inf 𝔪_♯ = inf 𝔪 − δ_M`, so the
two infima cannot both be 0 — the refutation of `P_PLANT_TEST_DEPENDENCE_EXPECTED` is valid.
**The value of δ_M itself I cannot check**: it depends on the plant/false-factor definition, which lives in
the request file I was told not to open. UNVERIFIABLE (not disputed).
(28) is complete. Moments of `h_T=(∂²−¼)(e^{iTx}η)` vanish because `(∂²−¼)e^{±x/2}=0` with no boundary
terms; `ĥ_T(ξ)=−(ξ²+¼)η̂(ξ−T)`; the domination constant is real
(`sup_{T≥1,|s|≤50}((T+s)²+¼)²/(T⁴(1+|s|)⁴)=1.5625`, lobe ≤2, `η̂` Schwartz, `d₂,ℓ₂` bounded and →0 by
parent (15)–(16)); `H_T/T⁴→‖η‖²` by the same domination. Nothing missing.

## 8. Theorem 4 (31) and (32)–(34) — CORRECT, bound verified with large margin

Three evaluators of `J(β,ξ)=∫₀¹(−log v)v^{−½−iξ}cos(βv)dv` built from scratch: power series
`Σ(−1)^mβ^{2m}/((2m)!(σ+2m)²)` at `dps=0.435β+60`; incomplete-gamma closed form
`−∂_s½[(∓iβ)^{−s}γ(s,∓iβ)]`; oscillation-subdivided quadrature. Series vs closed form agree to ≤2e-17
(quadrature fails at large ξ, as expected). Grid β∈{1,5,20,100,10³,10⁴,10⁶} × ξ∈{0,1,5,20,100,10³,3·10³}:

max over ξ of `|J|√β/(1+logβ)` per β = 3.9220 (β=1), 2.4722 (5), 2.0469 (20), 1.8198 (100),
1.6550 (10³), 1.5644 (10⁴), 1.4677 (10⁶). **Max over the grid = 3.922 at (β,ξ)=(1,0), ≤ 256.** ✓ The constant is conservative by ~65×.
A fine ξ-scan at β=1,2,5 (0…20 step 0.25) puts the max at ξ=0 each time. The internal proof constant
`4+(2+8/(1−2^{−1/2})+64√2)logβ = 4+119.82logβ` is indeed below `256(1+logβ)`; the `0<y<1` piece
`∫₀¹y^{−1/2}log(β/y)dy=2logβ+4` is exact.
(32): re-derived from (31) + `β_j^{−1/2}=(2π)^{−1/2}r^j` + `Σ_{k≥0}kr^k=r/(1−r)²`; my direct resummation of
the 256-majorant over j>55 equals the closed form (32) to 1e-25. **ε_55 = 8.957459307e-6**, hence
**4πε_55 = 1.1256e-4** (still below the diagnostic 0.0035, and below the 1/500 target).
(34): `T_* = 299.658877` (direct resummation identical), so `|ℓ₂| ≤ 2T_* = 599.32`. Conservative but valid.

## 9. §7.2 (35) — CORRECT

Symbolic expansion of `h₄=(1−z²)⁴''/δ² − (1−z²)⁴/4` gives exactly
`A=(−8δ⁻²−¼, 72δ⁻²+1, −120δ⁻²−3/2, 56δ⁻²+1, −¼)` — all five verified identically by sympy.
`H₄=2δΣA_iA_j/(2(i+j)+1)`: with `δ=0.0506831385135`, **H₄ = 301750.44686**, identical to direct quadrature.
Normalization: `∫η₄ = 0.0411901062205`, `N=1/∫η₄ = 24.2776747078`, and
**N²·H₄ = 1.77853369753e8 vs the evaluator's 1.7785336975e8 — ratio 1.00000000002.** (35) and the
evaluator's row are the same object up to the recorded `N₄` cancellation. ✓
Regularity statements right: zero-extended `η₄∈C³` so `h₄∈C¹` (and `∈H²`); `h₂` jumps at the endpoints so
`h₂∈H^s, s<½`; the bump's closed support `[−δ,δ]` is not compact in the open `I`.
(37) re-derived (`μ_X≤(2/H)X^{−2s}∫|ξ|^{2s}|ĥ|²=4π‖h^{(s)}‖²/(HX^{2s})`), BV variant likewise. (39)
re-derived and correct; `‖𝒯‖≤2π‖ℓ₂‖_∞` is right *because of* (2) (Rayleigh quotient `=−∫W_hℓ₂`,
`∫W_h=2π`), not the naive `4π` — the "by (2)" is load-bearing.

## 10. The two code criticisms — CORRECT, and one is stronger than stated

`prod_op.py:22` — `keep = np.abs(lam) < 1.0 - 1e-12`, `ndrop` stored in the `.npz`. Modes with
`|λ| ≥ 1−1e−12` are dropped. **Quote confirmed.**
`prod_t.py:21` — `"""(13): tail of the scalar series beyond J_U, with the shape constant set to 1."""`
**Quote confirmed.** Its formula is exactly parent (13) with `C=1`; I reproduced it: `tail_bound(2) =
3.499008e-08`, and `ε_55(C=256)/tail_bound(2) = 256.00` — the two differ by precisely the missing constant.
(i) Right: a retained-mode approximate correction is not a certified lower bound — with true `A=0,c=1,t=0`
the true correction is `0`, while `Â=û=ε` gives `2ε²/(1+ε)>0` for every ε>0 (ε=0.5,0.1,1e−3,1e−6).
(ii) The judge is right that the 3.5e−8 tail is not rigorous — **and my computation shows it is not even
numerically true.** At `β₅₆=4.5275e17` the ratio `|J|√β/(1+logβ)` is **1.3296 (ξ=0), 1.2289 (ξ=1),
1.1331 (ξ=20), 1.0308 (ξ=600)** — i.e. `C=1` is violated at the very scale the tail is taken. Summing the
actual terms `j=56…89`:

true `|t₂−t₂^{[55]}|` vs the stored "bound": ξ=0 → 4.6418e-8 vs 3.4990e-8 (**0.754×**);
ξ=2 → 1.0586e-8 vs 3.4990e-8 (3.31×); ξ=100 → 3.2707e-8 vs 3.1831e-8 (**0.973×**).

At ξ=0 and ξ=100 the stored "tail bound" is **smaller than the actual truncation error**. It is not a
majorant. The verdict's own hedge ("this is missing justification, not a claim that the literal numerical
tail necessarily exceeds that number", §7.1) is therefore *too weak*: the literal tail does exceed it.
Consequence for RESULT codes: `SETTING_UNSPECIFIED_TAIL_CONSTANT_TO_ONE_IS_A_CERTIFICATE: false` should be
strengthened — the constant is not merely unproved, it is false; `t₂` tables produced by `prod_t.py` carry an
undeclared error of order 5e-8 at low ξ. No RESULT code needs to change direction.

## 11. Rescoring of `P_PHASEPROOF_SOURCE_PACKET_MINUS_MARGIN_POSITIVE` (0.70)

The judge is right: the frozen event asserts a positive *source* packet margin, which only a two-sided
source-valid enclosure can resolve, and the supplied evidence is a diagnostic computed with dropped modes
(`prod_op.py:22`) and a tail constant that is now shown to be numerically false (`prod_t.py:21`), so the
event is neither confirmed nor refuted — UNRESOLVED is the correct fate.

## Verdict summary

| Item | Fate |
|---|---|
| 1 Theorem 1 (4)(5)(6) | CORRECT |
| 2 (7) + planted A=2 | CORRECT |
| 3 (12)(13) + 1-D non-uniformity | CORRECT |
| 4 Theorem 2 (14)–(17), κ_B²=17+12√2 | CORRECT (non-degenerate joint finite model impossible; steps verified) |
| 5 Theorem 3 (18)–(22), FG²F≠(FGF)² | CORRECT (Sonin isomorphism + ‖w‖²=k_∞ UNVERIFIABLE-EXTERNAL) |
| 6 §5.3 (24) | CORRECT |
| 7 §6 (27)–(29) | CORRECT; δ_M's *value* UNVERIFIABLE (needs the request) |
| 8 Theorem 4 (31)–(34) | CORRECT; grid max 3.922 ≤ 256; ε_55=8.96e-6, 4πε_55=1.13e-4, T_*=299.66 |
| 9 §7.2 (35) | CORRECT; H₄=301750.44686, N²H₄ matches the evaluator to 1e-10 |
| 10 code criticisms | CORRECT, and (ii) is stronger than the verdict states |
| 11 rescoring | CORRECT |

**No error found in the verdict. No RESULT code is invalidated.** The one substantive addition is item 10:
`prod_t.py`'s tail is not a majorant even numerically (0.75× the true error at ξ=0), which hardens
`SCALARFLOOR_EXPLICIT_UNIFORM_MELLIN_J_TAIL_MAJORANT` from "unjustified" to "refuted as written", and
makes any `t₂` table produced by that script unusable without redoing the tail with the proved constant 256.
