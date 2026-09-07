# PROFILESCHECK — independent check of PROSHKA_VERDICT_GOAL058_INDEPENDENT_PROFILES_RESERVOIR_2026-09-07

Method: own re-derivation of every step + independent numerics (mpmath dps=30 / numpy Gauss–Legendre panels).
Read: the verdict, SEMILOCAL l.100–103, GAUGE §1.2/§5.3. Scripts: `chk1..chk5.py` in this directory.

---

## 1. §1 (P2)–(P5) conventions — **CORRECT**

**Archimedean term — CORRECT, exactly.** Claim to check: `(1/2π)∫q_∞|f̂|² = 𝒟(f) − c_A‖f‖²`,
`q_∞ = Reψ(¼+iξ/2) − log π`. Since `‖U_tf−f‖² = (2π)^{-1}∫2(1−cos ξt)|f̂|²`, the claim is equivalent to
`W(ξ) := 2∫₀^∞A(t)(1−cos ξt)dt = q_∞(ξ)+c_A`. Expanding `A(t)=Σ_{k≥0}e^{−(2k+½)t}` and integrating termwise,
`W(ξ)=Σ_{k≥0}[1/(k+¼) − Re 1/(k+¼+iξ/2)] = Reψ(¼+iξ/2) − ψ(¼) = Reψ(¼+iξ/2)+γ+log8+π/2`.
Since `q_∞+c_A = Reψ − logπ + γ + log8π + π/2 = Reψ + γ + log8 + π/2`, the two agree **identically**.
Numeric confirmation (chk1): ξ=0 → 0 = 0; ξ=1 → 3.34703722612220 vs 3.34703722612220 (diff 3.9e-31);
ξ=3.7 → 4.83952692917926 both (diff −2.8e-22). (Large-ξ quadrature is oscillation-limited, not a discrepancy.)
This *is* the standard Weil archimedean digamma term in this normalization. `c_A = 5.3721834192256656` ✓.

**Pole term — CORRECT and consistent with the older `P₀₂`.** For `f = v*ṽ`, `f̂(±i/2)` continues to
`M_+conj(M_-)` and `conj(M_+)M_-`, so `f̂(i/2)+f̂(−i/2) = 2Re{M_+ conj(M_-)}` — the standard Weil pole
pair, with `+` sign, matching SEMILOCAL l.103 `P_02 = 2Re(A_+ conj(A_-))`. Reconciliation asked for:
with `M_± = C ± S`, `2Re{M_+conj(M_-)} = 2Re{(C+S)conj(C−S)} = 2(|C|²−|S|²) + 2Re{Sconj(C)−Cconj(S)}`
and the second bracket is `2Re{2i·Im(Sconj C)} = 0`. Hence **`2|C|²−2|S|² = 2Re{M_+conj(M_-)}` exactly** ✓.

**Prime term — CORRECT.** `f(−t)=conj(f(t))` gives `g(log n)+g(−log n) = 2C_v(log n)`, so
`−2Σ Λ(n)n^{−1/2}C_v(log n)`; with `Λ(2^j)/2^{j/2} = a r^j` this is SEMILOCAL's `−2Σ_j a2^{−j/2}C_v(ja)` ✓.

**Support claim — CORRECT.** `a+2δ = 0.7945134576 < log3 = 1.0986122887`; `log4 = 1.3863 > log3`. Only n=2.
Direct numeric test (chk5, non-pole-null random pair): `C_v(log2)=7.98482909426558e-03`,
`C_v(log3)=0`, `C_v(log4)=0` ✓.

**(P4) sign convention — CORRECT.** `U_sh(x)=h(x−s)` ⟹ `M_±(U_sh)=e^{±s/2}M_±(h)`, giving exactly
`e^{a/4}M_+(h₁)+e^{−a/4}M_+(h₂)=0`, `e^{−a/4}M_-(h₁)+e^{a/4}M_-(h₂)=0` ✓.

**(P5) factor — CORRECT, the cross term is picked up ONCE.** Of the four lag terms
`Γ_{ij}(a+x_i−x_j)` only `(i,j)=(2,1)` has lag 0 (the others have lags a, a, 2a, all > 2δ), so
`C_v(a)=Re⟨h₁,h₂⟩`, prime cost `−2w Re⟨h₁,h₂⟩`, `w=a/√2=0.4901290717`.
Numeric (chk5): `C_v(log2)=7.9848290942655820e-3`, `Re⟨h₁,h₂⟩=7.9848290942655872e-3` — identical;
the "twice" reading (1.597e-2) is excluded ✓.

## 2. §3.2 (P17) moment estimate — **CORRECT**

Reconstructed system: with `ε_i^± = ∫h_i(e^{±x/2}−1)`, `Vm = −e`,
`e₁ = e^{a/4}ε₁⁺+e^{−a/4}ε₂⁺`, `e₂ = e^{−a/4}ε₁⁻+e^{a/4}ε₂⁻` — matches the verdict.
`|ε_i^±| ≤ η_d√d‖h_i‖` (supp ⊂[−d/2,d/2], `|e^{±x/2}−1|≤η_d`). Then
`‖e‖² ≤ η_d²d[(Pu+Qz)²+(Qu+Pz)²] = η_d²d[(P²+Q²)H+4PQuz] ≤ η_d²d(P+Q)²H` ✓ (the AM–GM step is the
only slack and it is correct). `σ_min(V)=e^{a/4}−e^{−a/4}` ✓ (V symmetric, eigenvalues P±Q).
`coth(a/4) = (√2+1)/(√2−1) = 3+2√2 = 5.8284271247461901` ✓ (verified numerically to 20 digits).
`η_d = e^{d/4}−1 = 0.0263409485 ≤ (d/4)/(1−d/4) = 13/487 = 0.0266940452` ✓ (from `e^x ≤ 1/(1−x)`).
`6η_d ≤ 78/487 = 0.1580456908 < 1/5` ✓ ⟹ `‖m‖² < (d/25)H`, `d/25 = 0.00416`.
**Falsifier — CORRECT and load-bearing.** `h₁→1_I, h₂=0` gives `|m₁|²/‖h₁‖² → 2δ = 0.1013663 ≫ 0.00416`.
Quantitatively the constraints are *needed by this proof*: with `‖m‖²/H` at its unconstrained max 2δ the
last term of (P20) would be `−A(d)·2δ = −0.5125`, versus the total available margin 0.1606 — the bracket
would go negative. So (P17) is not decoration.
Numerics (chk3, 5 random constrained pairs): `‖m‖²/H ∈ {4.07e-5 … 1.56e-4}` ≪ 4.16e-3 ✓.

## 3. §3.3 (P18)–(P20) — **CORRECT**

`∫₀^d‖U_th−h‖²dt = 2d‖h‖² − 2∫₀^dC_h`; `C_h` real and even with supp ⊂[−2δ,2δ] ⊂ [−d,d], and
`∫_ℝ C_h = |∫h|²`, so `2∫₀^dC_h = |m|²`. **(P18) correct.** For `t ≥ 2δ` (a fortiori `t ≥ d`)
`‖U_th−h‖² = 2‖h‖²`, and `A` strictly decreasing gives (P19) ✓.
Cross bookkeeping re-derived: `𝒟(v) = Σ𝒟(h_i) − 2∫_{a−d}^{a+d}A(t)ReΓ₂₁(t−a)dt`, `|ReΓ₂₁| ≤ ‖h₁‖‖h₂‖`,
so cost `≤ 2J_d‖h₁‖‖h₂‖ ≤ J_dH`; prime cost `≤ wH` ✓. (P20) follows exactly as printed ✓.

## 4. §3.4 (P21)–(P25) rational ledger — **CORRECT** (all six signs, all six rationals)

| item | claim | exact value (mpmath, 20 digits) | verdict |
|---|---|---|---|
| `2dA(d)` | ≥ 1 | 1.0514792505852888869 | ✓ |
| `dA(d)` | < 3/5 | 0.52573962529264444347 | ✓ |
| `2∫_d^∞A` | closed form + lower bd | 5.1687037843903259393; bd `log(4/d)+π/2−d/2` = 5.1684550677555516258 | ✓ |
| `c_A` | γ+log8π+π/2 | 5.3721834192256655822 | ✓ |
| `J_d` | ≤ 2dA(a−d) < 23/100 | J_d = 0.19722937439048343209; 2dA(a−d) = 0.22382166438407769106; 102960/449589 = 0.229009 | ✓ |
| `w` | < 1/2 | 0.49012907173427359586 | ✓ |

(P22) derivation reproduced by `u=e^{−t/2}`: `2∫_d^∞A = 4∫₀^y du/(1−u⁴) = 2artanh y + 2arctan y`,
`y=e^{−d/2}`; closed form agrees with direct quadrature to 20 digits (2.5843518921951629696 both).
Lower bound: `(1+y)/(1−y)=coth(d/4)` and `tanh(d/4)≤d/4` ⟹ `≥ log(4/d)`; `d/dd[2arctan e^{−d/2}] =
−1/(2cosh(d/2)) ≥ −1/2` ⟹ `≥ π/2 − d/2` ✓.
`2∫_d^∞A − c_A ≥ log(4/d)+π/2−d/2 − γ − log8π − π/2 = −γ − log(2πd) − d/2` ✓ (identity, not inequality).
`2πd = 0.6534512719 < 2/3` ⟹ `−log(2πd) > log(3/2) > 152/375` ✓.
`γ = 0.5772156649 < 29/50`; the stated chain also closes: `γ < 25/12 − log(9/2) = 0.5792559366`, and
`log(9/2) = 2log2+log(9/8) > 2(842/1215)+2/17 = 1.5036552893 > 451/300 = 1.5033333` ✓ (checked; the margin
is only 3.2e-4, so this is the tightest rational step in the document, but it holds).
`log(3/2) ≤ 2/5+1/180 = 0.4055556 < 4d = 0.416` ⟹ `2δ < d` ✓; `2d = 0.208 < 2/3 < log2` ✓.
**(P25) fraction arithmetic:** `1 − 3/125 − 29/50 + 152/375 − 13/250 − 23/100 − 1/2 = 29/1500` — verified
exactly with `fractions.Fraction`; over 1500: `1500−36−870+608−78−345−750 = 29` ✓ > 1/100 ✓.
Each term's sign matches (P20) term-by-term (checked individually) ✓.
**EXACT bracket of (P20), 12+ digits:** `0.13961158461348643828`, i.e. 7.2× the certified 29/1500 and
14× the claimed 1/100. Ample.

## 5. §3.5 (P26) positive representation — **CORRECT (exact identity, verified twice)**

Symbolic expansion: `Term1 = Σ∫₀^dA‖·‖² − 2dA(d)H + A(d)‖m‖²`; `Term2 = J_dH + [𝒟(v)−Σ𝒟(h_i)]`;
`Term3 = wH − 2wRe⟨h₁,h₂⟩`; `Σ_i∫₀^dA‖·‖² − Σ𝒟(h_i) = −2H∫_d^∞A`; the `A(d)‖m‖²` of Term1 cancels
against Term5's; the constant bracket collapses to `−c_A` by the definition of `C₀`. Result:
`Σ terms = 𝒟(v) − c_AH − 2wRe⟨h₁,h₂⟩ = Q(v)` — **an exact identity, not an inequality**.
Numerics (chk3): 5 random pairs built by projecting complex coefficient vectors onto the null space of the
two (P4) functionals (constraint residuals 3e-19…6e-18). Q via (P5) vs Q via (P26):

| seed | Q (P5) | Q (P26) | diff | all terms ≥0 | Q/H |
|---|---|---|---|---|---|
| 1 | 0.00472147896677 | 0.00472147896677 | 8.7e-19 | yes | 2.397 |
| 2 | 0.01079126758789 | 0.01079126758789 | −1.2e-17 | yes | 2.221 |
| 3 | 0.02462109629267 | 0.02462109629267 | −3.5e-18 | yes | 2.427 |
| 11 | 0.01485802831976 | 0.01485802831976 | −1.7e-18 | yes | 2.532 |
| 42 | 0.00323529199414 | 0.00323529199414 | −1.3e-18 | yes | 2.441 |

In every case `Term4/H = 0.1396115846` = the exact (P20) bracket ✓. `M*M ⪯ βI` holds **on the constrained
subspace only**, which is what the text says ✓.

## 6. §2.2–2.3 (P11)–(P15) — **CORRECT**

`q₂ = q_∞ − 2aΣ_{j≥1}r^j cos(jaξ)` verified: `C_v(ja) = (2π)^{-1}∫|v̂|²cos(jaξ)dξ` and `Λ(2^j)/2^{j/2}=ar^j` ✓.
(P13): `ψ(¼+iξ/2) ~ log z − 1/(2z) − …`, `Re log z = log(|ξ|/2)+O(ξ^{−2})` and `Re(−1/2z) = −(1/8)/|z|² =
O(ξ^{−2})` (no `1/ξ` term because Re z = ¼ is real) ⟹ `q_∞ = log(|ξ|/2π)+O(ξ^{−2})` ✓.
(P11) verified entrywise: `(1,2)` entry `K_∞(t+a) = −A(a+t)`, `(2,1)` entry `−A(a−t)`, prime delta pairs to
`−2wRe⟨h₁,h₂⟩`, and `𝐊_Q(−t)=𝐊_Q(t)^*` holds ✓. Channel eigenvalues `log(|ξ|/2π) ∓ w` ✓.
**(P15) numerically confirmed** (chk4, `η=(1−(x/δ)²)⁴`, `h_T=(∂²−¼)(e^{iTx}η)`, pole moments 1e-13 or less):

| T | Q(v_{+,T}) | log(T/2π)−w | Q(v_{−,T}) | log(T/2π)+w | residual |
|---|---|---|---|---|---|
| 120 | 2.76364571 | 2.45948560 | 3.74390386 | 3.43974375 | 0.304160 |
| 240 | 3.25356818 | 3.15263279 | 4.23382632 | 4.13289093 | 0.100935 |
| 480 | 3.87352193 | 3.84577997 | 4.85378007 | 4.82603811 | 0.027742 |

Residual → 0 (×0.33, ×0.27 per doubling) ⟹ `Q(v_{±,T}) = log(T/2π) ∓ w + o(1)` ✓. The `∓w` prime constant
is exact: `Q(v_−)−Q(v_+) = 0.98025815 = 2w` at all three T ✓.
**Order-mismatch argument — SOUND.** Any representation `Q = pM + f̂`, `p ≍ 1/T`, `f ∈ W^{1,1}_c`, forces
`Q(v_{±,T}) → 0` (Riemann–Lebesgue), contradicting the observed log growth. Not a normalization quibble.

## 7. §5 (P31) — D1 dispute **SETTLED IN THE VERDICT'S FAVOUR**

(ii) verified exactly: `M_+(v_h) = (e^{a/4}−e^{−a/4})M_+(h)/(√2‖h‖)`,
`M_-(v_h) = −(e^{a/4}−e^{−a/4})M_-(h)/(√2‖h‖)` ⟹
`P₀₂(v_h) = −(e^{a/4}−e^{−a/4})²R_h/H = −4sinh²(a/4)R_h/H = −2cR_h/H` — this is GAUGE (G35) ✓, and
`2sinh²(a/4) = cosh(a/2)−1 = c = 0.0606601718` verified to 10 digits ✓.
(i) verified from (G2): `∬2αcosh((x−y)/2)conj(h)h = 2αRe{M_+conj(M_-)} = 2αR_h`; with `Q_F[h]=H𝓕(h)` this
is `𝓕_g(h) = 𝓕(h) + 2αR_h/H` ✓.
Substituting: `Q(v_h) = n₂ + 𝓕_g(h) + ‖T D₂‖² − 2αR_h/H − 2cR_h/H` ⟹ residual coefficient
**`−2(α+c)`** ✓ — exactly as printed in GAUGE. Gauging the *physical* kernel instead adds
`2αRe{M_+(v)conj(M_-(v))} = −2αcR_h/H`, leaving `−2c(1−α)`. The two agree only if `α(1+c)=0`.
With `α=519/1000`: `−2(α+c) = −1.15932034`, `−2c(1−α) = −0.05835509`, `−2c(1+α) = −0.18428560`.
**Прошка is right**: D1's `−2c(1±α)` is the coefficient of a *different* gauge object; at GAUGE's own
(G3) definition (gauge on the profile kernel R, i.e. on 𝓕) the printed `−2(α+c)` is correct.
Both formulas are individually correct for their own object — this is an object-identification error in D1,
not an arithmetic one, and the verdict says so.

## 8. §6 Lemma P2 (P32)–(P33) — **NO ERROR FOUND; complete at sketch level, with imports**

Checkable parts verified: frequency count below `e^{n+1}` is `#{(j,k): jlog2+klog3 ≤ n+1−log2π} = O((n+2)²)`
⟹ `O((n+2)⁴)` ordered pairs/shell ✓; the extra `(n+2)` in the `L¹` bound is the `(1+logβ)` factor of
`∫_U|L(β(t−τ))|dt ≤ C_U(1+logβ)/β`, and `1/β ≤ e^{−n}` ⟹ `(n+2)⁵e^{−n}` ✓ summable; the `W^{1,1}` bound
`(n+2)⁴e^{−n/2}` ✓ summable. The "roots outside U+" step is *correct with `max`* (not just the smaller
frequency): the original argument is `β_μe^t − β_ν`, and log-separation with `t∈U` bounded forces
`|β_μe^t−β_ν| ≳ max(β_ν,β_μ)` — the text's phrasing is right. Coefficients `c_{jk} → 1/3` do not decay, so
all summability rests on the kernel decay against the polynomial count; that works.
**Imported, unverifiable here (outside the read set):** SCH (3) (the `(1+logβ)/β` L¹ estimate) and
SCH (8) (the `Cβ^{−1/2}` W^{1,1} bound near the root) — the `e^{−n/2}` rate rests entirely on the latter.
**Asserted, not proved:** the identification of the limit with the tested source kernel ("finite sums first,
then the finite-Euler Mellin limit"). The verdict flags the sign gap itself as (P34) and claims no positivity.
Verdict: **UNVERIFIABLE in part** (two SCH imports), no gap found in what is checkable.

## 9. Overall

**Theorem P1 is CORRECT as a PAPER theorem.** Every step of §3 (P16)–(P26) was re-derived independently and
confirmed numerically; the exact bracket is `0.13961158461349`, so `Q(v) ≥ 0.1396‖v‖²` on the class — the
stated `1/100` is very conservative. The proof uses only: the geometric formula (P2) (which is the standard
Weil explicit formula in this normalization — verified exactly, not assumed), the disjointness of the two
lobes, `2δ < d`, the two total pole moments, and monotonicity of `A`. No gauge, no numerical certificate,
no reservoir sign. **No arithmetic or sign error found anywhere in §1 or §3.**

**RESULT codes justified**, with one nuance: `Q2: CERTIFICATE_RATIFIED` rests on a code audit only —
the header itself declares `INDEPENDENT_NUMERICAL_RERUN_BY_JUDGE: false` and
`ALL_RAW_CELLS_RESUMMED_BY_JUDGE: false`, and §5 says so in text. That is disclosed, not hidden, but
"ratified" is a stronger word than what was done. `Q1d PROVED_ON_CLASS`, `Q1b/Q1c PROVED_ON_CLASS`,
`Q1a/Q3 PARTIAL_WITH_PRECISE_REMAINDER`, `Q2_D1 ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE` — all accurate.

**First asserted-not-derived step in the document: (P7), §2.1** — `s₂(ξ) = 2⟨X,(I+A₂)^{-1}X⟩ +
2⟨Y,(I−A₂)^{-1}Y⟩ ≥ 0` is introduced with "Direct expansion gives"; the expansion is not shown, and its
nonnegativity additionally needs `‖A₂‖ ≤ 1`, which is nowhere stated in this document. It depends on
R (5)–(6), outside the authorized read set. (P8) right after it is imported from GAUGE (G34) at PAPER status.
**Inside Theorem P1 itself there is no asserted-not-derived step** — I reconstructed all of it.

**Scope caution the verdict states and I confirm:** the theorem is a narrow-support result — its margin is
`2dA(d)+2∫_d^∞A = 6.2202 > c_A = 5.3722`, i.e. it works because the lobes are narrow (`d = 0.104`). The moment
constraints add only `−0.021` of margin but are load-bearing (without them the bracket would be `≈ −0.35`).

**Tightest step in the ledger:** `log(9/2) > 451/300` via `2(842/1215)+2/17 = 1.5036553` versus `1.5033333` —
true, margin 3.2e-4. One more atanh term would make it comfortable; recommend widening it in the paper.
