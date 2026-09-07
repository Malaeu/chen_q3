# INVCHECK — independent check of PROSHKA_VERDICT_GOAL058_SIGNED_HEAD_INVARIANT_2026-09-07

Fresh checker, no access to the sibling REGIONAL_ENERGY document. Opened: the verdict, plus CHAIN
§1/§5 for conventions. Everything below was re-derived from scratch and recomputed; scripts in
`/home/chirurgie/.claude/jobs/4b35770d/tmp/invcheck/chk*.py` (mpmath dps 40, numpy/scipy).

## VERDICT

§3–§6 are **mathematically sound as written**. Every identity I derived independently came out
exactly as printed; every rational bound in the §2 ledger is true and most are conservative. Three
defects found, all of exposition, none load-bearing. RESULT codes justified; all three
`P_INVARIANT_*` registrations acceptable on content.

## 1. §3 (17)–(20) isolated prime star — DERIVED, CORRECT

* (17) A bordered matrix with one active row/column has norm `‖w‖ = (Σ log²p_j/p_j)^{1/2}`. The
  sign convention is forced by (C1): for `f = Σ z_i U_{x_i}η`, `−2w_p C_f(log p) = z*Nz` with
  `N_{ij}=N_{ji}=−w_p`. ✓
* Moment rows: (3) with a common profile gives `z_0+Σz_j√p_j = 0`, `z_0+Σz_j/√p_j = 0`. Putting
  `z_j = √p_j t_j` turns these into `z_0+Σp_jt_j = 0` and `z_0+Σt_j = 0`; the second is
  `z_0 = −Σt_j`, the difference is `Σ(p_j−1)t_j = 0`. Exactly (18). ✓
* (19) `z*M_⋆z = −2Re{z̄_0 Σw_{p_j}z_j}`, `w_{p_j}z_j = (log p_j)t_j`, `z̄_0 = −conj(L_0)`, hence
  `2Re{conj(L_0)L_log} = ½|L_0+L_log|² − ½|L_0−L_log|²`: rank ≤ 2, index₊ ≤ 1, index₋ ≤ 1, for every
  r. ✓ Radical on the constraint space has dim `(r−1)−2 = r−3` as claimed. ✓

## 2. §3 (21)–(24) four-lobe witness — EXACT, CORRECT

Rows vanish to 1e−40; `‖z⁽⁴⁾‖² = 86`. `z*M_⋆z = 2(4log2−4log3+log5) = −2log(81/80)`, per unit norm
`−log(81/80)/43 = −2.888958139199338e−4`, matching (24) to 40 digits and matching the t-route
(`t = (4,−4,1)`, `L_0 = 1`, `Σ(p_j−1)t_j = 0`, `L_log = −log(81/80)`). ✓

**Support guard (23) checked exhaustively**, not by the quoted pair: with `ℓ = log(3/2)/4 =
0.1013663` I scanned every ordered centre pair of {0,log2,log3,log5} against every prime power ≤ 200.
Only the three star edges 2, 3, 5 hit. The tightest non-star approach is `|log3−log(5/2)| = log(6/5)
= 0.18232`, then `log(5/4) = 0.22314` (the `log4`-vs-`log5` question), so `ℓ < min(log(6/5),
log(5/4))` is exactly the binding guard. ✓ Supports stay disjoint.

Signature (1,1): on the 2-dim constraint space `(L_0,L_log)` is `(1, log(4/3))` at `t=(2,−1,0)` and
`(3, log(16/5))` at `t=(4,0,−1)`; determinant 0.300 ≠ 0, so the functionals are independent and
`2Re{L̄_0L_log}` has signature (1,1). The zero-extended three-lobe vector is the positive direction
(`2log(4/3)`), `z⁽⁴⁾` the negative one. ✓

## 3. §3 (25) first non-star overlaps — CONFIRMED, LIST COMPLETE

`log(11/10) = 0.0953102 < ℓ`, `log(12/11) = 0.0870114 < ℓ`. ✓ Full enumeration for
{0,log2,log3,log5,log7,log11}, all prime powers ≤ 200: five star edges, plus exactly three offsets —
`(log5,log11)`/atom 2 at `+log(11/10)`, `(log3,log11)`/atom 4 at `−log(12/11)`, `(log2,log11)`/atom
5 at `+log(11/10)`. Nothing else. For centres up to log7 there are **none**; the closest miss is
`log(8/7) = 0.13353` (pair 0→log7 with atom 8, and (log2,log7) with atom 4), a 32 % margin over `ℓ`
— closer to failing than the text suggests, but the claim holds.

## 4. §2 ledger (8)–(16) — brief pass turned into a full one; EVERY CONSTANT HOLDS

| item | claimed | true | ok |
|---|---|---|---|
| `L P_n = 2H_n P_n`; (8) on random deg-6 f | — | eigenvalue verified n = 0..5 by direct quadrature; (8) holds with ~2× slack | ✓ |
| (9) `A ≥ 1/(2t)`; exterior potential | t ≤ d < 1; `≥ 2∫_{ℓ/2}^∞A‖f‖²` | `(1−t/2)(1+t) ≥ 1 ⟺ t ≤ 1`; convexity of `s↦∫_s^∞A` (`A′<0`) | ✓ |
| β (11) | `≥ 63/125 > 1/2` | true 0.54178; d-route 0.51542 | ✓ |
| `e^{1.11}<272/89<875/286<1/(πd)` | — | 3.03436 < 3.05618 < 3.05944 < 3.06067 | ✓ |
| `γ_E < H₁₆−log16−1/34 < 29/50` | — | 0.577216 < 0.578729 < 0.58; `H₁₆ = 3.3807290 < 3.381` | ✓ |
| `−A′` at `a−ℓ,b−ℓ,b−a−ℓ` | 11/4, 3/2, 8 | 1.4824, 0.5730, 5.4461 (Taylor bound at the rational points: 2.6811, 1.4115, 7.5963) | ✓ |
| η (12) | `≤ 7267/62500 < 1/8` | true ≤ 0.07119 | ✓ |
| `A(a),A(b),A(b−a)` | 21/20, 5/6, 25/16 | 0.94281, 0.64952, 1.46969 | ✓ |
| `‖ℓK‖ ≤ 3/10`, `‖M‖ ≤ 5/6`, `‖Me‖ ≤ 1/4` | — | 0.21106, 0.80159, 0.24585 | ✓ |
| `‖B‖ ≤ 17/15`, `‖Be‖ ≤ 11/20` | — | 0.98939, 0.28675 | ✓ |
| `e*Be > 0` (14) | — | **+0.195632**, closed form in (14) reproduces it exactly | ✓ |
| `VV* ≻ I/4` | det 5/48 | eig = {0.01423, 7.3191} | ✓ |
| (15) `2√(47/6)(e^{ℓ/4}−1)` | `< 78/487 < 1/6` | 0.143665 < 0.160164 < 0.166667 | ✓ |
| (16) `3/8−11/60−17/540` | `173/1080 > 3/20` | 0.1601852 > 0.15; with true β,η: **0.25578** | ✓ |

Structure behind the ledger also checks: the exact split of the prime term into `y*My +
⟨g,(M⊗I)g⟩`; the constant kernel `𝕋⁰` giving exactly `−ℓy*Ky` (it annihilates the `g`-parts, so
nothing is lost); `‖ΔT_{ij}‖ ≤ ℓ²sup(−A′)` by Hilbert–Schmidt plus block row sums for η;
`I₃+M ⪰ I₃/6` (true min eig 0.1984).

**Independent numerical channel (my own build).** I derived and confirmed the exact symbol:
`𝒟(f) − c_A‖f‖² = (2π)^{-1}∫|f̂|²[Re ψ(1/4+iξ/2) − log π]dξ` — i.e. **(C1)'s
`c_A = γ_E+log(8π)+π/2` is exactly the Weil archimedean normalisation** (8-digit agreement at
ξ = 0.3, 1, 5, 17). Assembling the three-lobe form in a Legendre basis with both total-pole moments
imposed gives a floor per unit `‖f‖²` of **0.96745** (10 dims) and **0.96635** (16 dims). The true
class floor is therefore ≈ 0.966: the paper bound 173/1080 is valid and ≈ 6× conservative, and there
is no conflict with the project's reported 9×9 value 1.01 (my subspace is strictly larger).

## 5. §4 transition audit — DERIVED, CORRECT

* **(28)** With `J` = zero extension of the same physical functions, `J*A_{n+1}J = A_n` (`Q` is one
  form on functions; new primes have `log m > 2n`, zero autocorrelation) and `J*G_{n+1}J = G_n`, so
  the increment is `G_n(1/(n+1)−1/n)+𝒦_n−J*𝒦_{n+1}J`. Exactly (28). ✓ It does need *declared* nested
  heads: canonical meshes are not nested and `T_n ⊄ T_{n+1}`, which is why no monotonicity exists.
* **(29)** `(B+ε′)^{-1}−(B+ε)^{-1} = (ε−ε′)(B+ε′)^{-1}(B+ε)^{-1}`, commuting positive resolvents,
  gives (29) and `⪯ −(ε−ε′)G`. Verified symbolically and numerically (residual 1.5e−15). ✓
  *Caveat:* this is the trivial monotonicity of `S(ε) = min_y[Q(v_z+y)+ε‖v_z+y‖²]` in ε. The scoped
  refutation `DECREASING_EPSILON_IS_A_PSD_INCREMENT_AT_FIXED_SPLIT` kills a claim nobody informed
  would make — honest, but near-zero kill-power.
* **(30)** Block identity verified exactly (residual 5e−15, Hermitian `D^{1/2}`); the `A=D=1, C=2 ⇒
  S=−3`, full form `−2` on `(1,−1)` detector is correct. ✓
* **§4.1 form core** Sound: `log(2+|η|/r) ≤ log(1/r)+log(2+|η|) ≤ C log(2+|η|)` gives uniform
  boundedness of dilation, strong continuity at `r=1` by density, mollification of radius `< n(1−r)`
  converges by dominated convergence on the Fourier side; head generators have `f̂ = O(1/|ξ|)`,
  `log(2+|ξ|)/|ξ| ∈ L²`. The one sketched piece — the digamma upper bound — is *immediate* from the
  exact symbol above: `Ω(ξ) = ½log(1/16+ξ²/4)+O(ξ^{-2})`, so `Ω+c_A ≍ log(2+|ξ|)` two-sidedly, no
  series splitting needed. The verdict makes this harder than it is.

## 6. §5 compensation — CORRECT WHERE DERIVABLE, ONE IMPORTED PREMISE

* **(31)** With `SP=PS=SQ=QS=0`, `R=P+Q`: `D+D² = (S−I+R)+(I−S+R²−2R) = R²−R = PQ+QP`. Verified
  symbolically and numerically (1e−15); no spectral assumption needed, as stated. ✓
* **(32) pole term** `M_± = M_c±M_s ⇒ 2Re{M₊conj(M₋)} = 2(|M_c|²−|M_s|²)` exactly (cross terms are
  purely imaginary). Consistent with (2)/(C1). ✓ **(32) as a whole is the first
  asserted-not-derived step** (see §8).
* **(33)** Setting `y = −(B+ε)^{-1}E_nz` in (C17) annihilates the square. Exact. ✓
* **(34)–(35)** `A⁻+B⁺ = Q(f)+ε‖f‖² = z*S_n(ε)z` by (33), `B⁺ ⪰ 0` by construction, and the lift is
  supported in `(−n,n)`, so every term of (34) is finite with no trace-extension theorem. The
  verdict's point that (34) is domain-safe where (32) is not is correct and is the better observation
  of §5. (35) is a valid sufficient scheme (`δ_n` is squeezed from both sides, so not vacuous), and
  the self-criticism about `X_n = S_n^{1/2}` circularity is right. ✓

## 7. §6 index package and zero mirror — CORRECT / PLAUSIBLE

* **(36)** If `J(a,a)>0`, `J(a,x)=0`, `J(x,x)>0`, then `a,x` are independent and
  `J(αa+βx,·) = |α|²J(a,a)+|β|²J(x,x) > 0`: a positive 2-plane, contradicting `ind₊=1`. Hence
  `J(Φz,Φz) ≤ 0` and `S_n = −Φ*JΦ+U*U ⪰ 0`. ✓ The `J = diag(1,−1)`, `Φ(1)=(1,0)` counterexample is
  correct: it shows the orthogonality hypothesis is not decorative (`J(a,Φ1) = 1 ≠ 0` there). ✓
* **(38)** `‖v_z+y‖² = ‖v_z‖²+‖y‖² ≥ z*G_nz` (`y ⊥ V_n`); with `Q ≥ 0`, `S_n(ε) ⪰ εG_n ≻ 0`. ✓
* **(39)** Structure verified: `Σ_j C(m,j)2^{-(m-j)}‖f^{(j)}‖₁` is exactly Leibniz for
  `(f·e^{x/2})^{(m)}`; `e^{R/2}` is the `|σ| ≤ 1/2` factor on `[−R,R]`; `|γ|^{-m}` is m-fold parts;
  the dyadic sum with the factor 2 for `±γ` is the right envelope and converges for polynomially
  bounded `B` once `m ≥ 2`. It does admit off-line zeros, since `|σ| ≤ 1/2` is assumed, not `σ=0`.
  Correctly caveated (needs proved `B(X)`, coverage below `T`, derivative enclosures, Gram
  conversion). Plausible. ✓

## 8. Defects

1. **First asserted-not-derived step: (32).** The trace representation imports an unpinned
   "source-tested trace identity"; `T_f, P, Q, S` are never defined here, and (31), which *is*
   proved, does not imply (32). Self-flagged (`[PAPER, with the identified source-trace theorem]`) —
   a labelled debt, not a concealed one, but the one place in §3–§6 taken on trust.
2. **(15) has no rational ledger.** `2√(47/6)(e^{ℓ/4}−1) < 78/487 < 1/6` is asserted as decimals in
   a section whose selling point is that "(11) is not an empirical decimal ledger". Both hold
   (0.143665 < 0.160164 < 0.166667, 11 % margin) but need rational upper bounds for `e^{ℓ/4}` and
   `√(47/6)` to match (11)–(13). Trivial repair.
3. **Lemma 1's approximation sentence is garbled.** "a Lipschitz error of size ε bounds its
   difference quotient by ε²|x−y|" conflates the square with the quotient; the correct statement is
   `|Δ(f−p)|²/(2(y−x)) ≤ ε²|x−y|/2`. One-line repair, but as printed it is not a proof of the limit.
4. **Cosmetic.** `(T_sf)(x) = ∫A(s+y−x)f(y)dy` in (5) is the transpose of the kernel the derivation
   from `𝒟` produces (`A(s+x−y)`); harmless since `𝕋_{ji} = 𝕋_{ij}*` and every bound used is
   transpose-invariant, but it should be said.

## 9. Consistency with the sibling three-lobe proof

No contradiction. `173/1080 = 0.16019` and `9579/40000 = 0.23948` are two *sufficient* estimates of
one quantity; both are valid lower bounds if both ledgers are sound, and both sit far below the true
floor ≈ 0.966 I measured. Neither can conflict with 1.744 / 1.01, upper-side facts about packets.

`ℓ` vs `d`: **in INVARIANT, `d = 13/125` is never an interval length.** `ℓ = 2δ` is the actual
support length and is the length in the regional gap `|∫h|²/ℓ` of (10); `d` enters only as a rational
*upper bound for* `ℓ` inside the exterior constant (11) and inside η (12), where monotonicity makes
the substitution safe (`2∫_{ℓ/2}^∞A ≥ 2∫_{d/2}^∞A`, `ℓ² ≤ d²`). If the sibling applies Lemma 1 on a
genuinely larger `J ⊃ I` of length `d`, that trade is legitimate — weaker mean penalty `1/d < 1/ℓ` —
**only if the exterior potential is then also cut at `∂J`, not at `∂I`**. Cutting the gap at `J`
while taking the baseline `2∫_{ℓ/2}^∞A` from `∂I` double-counts the strip `J∖I` and inflates the
constant. That is the specific item the sibling's checker should verify; it would explain a constant
1.5× larger. I cannot adjudicate it without opening that document.

## 10. RESULT codes, registrations, preflight critique

**Codes justified.** `OVERALL: PARTIAL_WITH_PRECISE_REMAINDER`, `Q1a/Q1b: PROVED_ON_CLASS`,
`Q1c/Q2b: PARTIAL`, `Q2a/Q2c: OBSTRUCTION_NAMED`, `Q2d/Q2e/Q3: COMPUTATION_SPECIFIED` all match what
is delivered. `THREE_LOBE_FLOOR_USES_NUMERICAL_PACKET: false` is accurate — §2 uses no packet
eigenvalue, only elementary bounds.

**Registrations, on content:** `P_INVARIANT_PRIME_STAR_RANK_REVIEW` (0.99) — **accept**, (19) and
(24) reproduced to 40 digits by two independent routes. `P_INVARIANT_THREE_LOBE_PAPER_REVIEW` (0.85)
— **accept** the `3/20` floor on the unchanged full complex class, conditional on repairs 2 and 3;
the margin is large (true β, η give 0.2558, the honest floor 0.966), so no repair threatens `3/20`.
`P_INVARIANT_OFFSET_MODEL_CHECK` (0.95) — **accept**; my scan says the six-centre assembly must
contain exactly three non-star blocks (5↔11 via 2, 3↔11 via 4, 2↔11 via 5) and no others, so the
discriminator is well posed.

**The preflight critique is fair.** "100 times the difference of two builds" is a convergence
*indicator*, not an enclosure: it presumes the two builds' errors are independent and comparable,
which is exactly what an a priori quadrature remainder would have to establish. 19 certified digits
need a proved remainder plus interval arithmetic on the assembled matrix. My independent build
reinforces this from a second direction: I get 0.96635 where the project reports 1.01, the gap
explained entirely by subspace size — so the "certified" number is a property of one chosen finite
packet, never the class floor.

**Next moves.** IF_A (repairs accepted): the cheapest advance is the six-centre full-width assembly
of §6.3 with the three offset blocks now pinned, not another packet. IF_B (someone disputes §2): the
dispute can only be defects 2–3 or the sibling's `d`-vs-`ℓ` cut, never the constants.
