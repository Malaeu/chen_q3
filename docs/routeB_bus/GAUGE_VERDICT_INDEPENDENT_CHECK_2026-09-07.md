# GAUGEVERDICTCHECK — independent check of PROSHKA_VERDICT_GOAL058_POLE_GAUGE_CLASS_CERTIFICATE_2026-09-07

Read: the verdict (708 lines); SCHUR §0–§4.2; GAUGE_POSITIVE_EXTENSION_CERTIFICATE_REPORT; `gauge/gauge_cert.py`,
`gauge_cert_core.py`, `out/gauge_cert_repaired_run.txt`; `hT_probe.py`; GAUGE_INDEPENDENT_CHECK,
SCHUR_INDEPENDENT_CHECK. Nothing else. Own scripts in `/home/chirurgie/.claude/jobs/4b35770d/tmp/gaugeverdictcheck/`
(`c1–c5.py j7.py orient.py plus.py`; mpmath dps=40 / python-flint prec=300 / sympy exact).
`hT_plus_probe_out.txt` did **not** exist — I ran my own plus-channel probe (`plus.py`).

**Verdict: sound.** Every derivation I could redo, I redid; every constant checked out. Two blemishes: an
arithmetic slip in a non-load-bearing aside (§5.3, LOW) and one §3.5 caution stronger than this run needs.
Nothing changes a RESULT code.

## 1. §1.3 Theorem G1 — CORRECT; (G5) is right

**Necessity.** `L=∂²−¼` maps `C_c^∞(I)→H₀₀` (`∫(φ''−φ/4)e^{±x/2}=0` after two integrations by parts, no
boundary terms). Vanishing on `H₀₀` gives `⟨L_xL_y k(x−y),φ⊗ψ̄⟩=0`. In `(t,u)=(x−y,(x+y)/2)`, `∂_x→∂_t`,
`∂_y→−∂_t`, and `(−∂_t)²=∂_t²`, so **both** factors become `∂_t²−¼`: `(∂_t²−¼)²k=0` on `I−I`. Tensor tests
separate ⇒ the ODE holds in `t` alone; `(∂²−¼)²=(∂−½)²(∂+½)²` ⇒ roots `±½` doubled ⇒ (G4), complex dim 4.
**Sufficiency.** `e^{t/2}↦M₊conj(M₋)`; `te^{t/2}=(xe^{x/2})(e^{−y/2})−(e^{x/2})(ye^{−y/2})` — each term carries a
bare `conj(M₋)` or `M₊`. Same for `e^{−t/2}`, `te^{−t/2}`. No density assumption needed. ✓
**(G5).** `k(−t)=k(t)` on (G4) forces `C=A, D=−B` ⇒ `2A cosh(t/2)+2B t sinh(t/2)`: **2 real dimensions,
correct**. Hermitian (`k(−t)=conj k(t)`) adds real-odd solutions in imaginary directions, `i sinh(t/2)`,
`i t cosh(t/2)` — as written. `P_e` rank 2 ⇒ rank`K ≤ 4` ⇒ (G6) ✓.

**Numerics (`c1.py`, 3001 nodes on `I`, both moments projected out, complex random draws), |form|:**
`cosh(t/2)` 6.6e−22 · `t sinh(t/2)` 2.9e−24 · `e^{t/2}+te^{−t/2}` 2.2e−21 (gauge) vs `cosh(t)` 8.0e−13 ·
`t²` 1.4e−12 · `cos(30t)` 8.0e−07 (non-gauge; control scale 4.7e−07). Gauge kernels vanish at the projection
floor, non-gauge ones do not (`cosh(t)`/`t²` sit at 1e−12 only because on a half-width-0.0507 interval `e^{±x}`
nearly lies in span`{e^{±x/2}}`; `cos(30t)` is the clean falsifier). **The report's §8 "only alpha is available"
is genuinely false**; `t sinh(t/2)` is an exact second real-even gauge, so
`Q1a_ONLY_TWO_DIFFERENCE_GAUGES: ATTEMPT_REFUTED…` is justified.

## 2. §2.1 (G8)–(G11) — CORRECT, all exact

Geometric summation of (G7) with `Σ2^{−j}=2`, `Σj2^{−j}=2` gives `p=(c/2)[2log(2π/|ξ|)+2a]=c(log(2π/|ξ|)+a)` ✓.
(G9): `β_j=Te^θ2^m` ⇒ `p(T)=cπ/(Te^θ)[2θ+2a]=2πc e^{−θ}(θ+a)/T` ✓. `min_{[0,a]}e^{−θ}(θ+a)=a`, attained at
**both** endpoints (`e^{−a}=½`); `θ=1−a` is the interior *maximum*. Series vs closed form agree to 12 digits at
`ξ=1e−3,0.5,3,2π` and `T=2π,20,100,480,1e5`; `T·p/c_* = 1.0000, 1.0580, 1.0023, 1.0412, 1.0121 ≥ 1` ✓.
`p(480)=5.730815e−4`. `p≥c_*/(2π+|ξ|)` follows on both branches ✓. (G11): `f_g` AC with compact support ⇒ no
boundary term ⇒ `|F_g|≤A`, `≤B/|ξ|` ✓. The remark that `A<ca` is the sharper split is right (factor 2).

## 3. §2.2 (G12)–(G15) — CORRECT; the rational chain holds, tightly

`√2>707/500` (1.4142136) ✓ · `log2>69/100` from 3 artanh terms (0.6930041) ✓ · `c>3(707/500)/4−1=121/2000=0.0605`
(true 0.0606602) ✓ · `c_*>2·3·(121/2000)(69/100)=25047/100000=0.25047>1/4` ✓ (margin 0.19 %) ·
`A ≤ 0.00346180882191+5.00e−15+1e−50 = 0.0034618 < 1/250` ✓ · `B ≤ 0.122854776540+1.50e−13+1e−50 = 0.1228548 <
1/8` ✓ (margin 1.7 %). High frequency needs `2B ≤ c_*`: rationally `2·(1/8)=0.25 < 25047/100000` ✓ (0.19 %
margin); truly `2B=0.245710 < 0.264185` (7 %). Low frequency needs `A ≤ p/2` with `p≥ca`: `(121/2000)(69/100)/2
= 0.0208725 > 1/250` ✓ (5.2× slack; true `ca/2 = 0.0210232`, and `121/2000 = 0.0605 < c = 0.0606602` ✓).
So **(G13) `p+F_g ≥ p/2` a.e. holds**, and (G14) follows. The two high-frequency rational margins are thin but
the inequalities are strict and every rounding is outward — valid.

**Theorem G2's closed-domain step — justified.** Density: `C_c^∞(I)` is dense in `L²(I)`; the 2×2 moment Gram of
two fixed smooth tests with independent moment vectors is invertible, so `h_n − Σc_ie_i ∈ H₀₀∩C_c^∞` converges.
Continuity: `∫_{|ξ|<1}p|ĥ|² ≤ 2δ‖h‖²∫_{|ξ|<1}p < ∞` (log locally integrable) and `∫_{|ξ|>1}p|ĥ|² ≤
(sup_{|ξ|>1}p)2π‖h‖²`; `|F_g|≤A`. Both sides bounded on `L²(I)` ✓. **`Q_F[h]>0` for `h≠0` — justified**: `p>0`
a.e. and `Q_F ≥ ½P`, so `Q_F=0 ⇒ ∫p|ĥ|²=0 ⇒ ĥ≡0` (`ĥ` entire) `⇒ h=0` ✓.

## 4. §3.1–§3.2 — CORRECT; orientation consistent; the Si(π) catch is real

**Orientation (G16) — confirmed numerically (`orient.py`).** With `γ(ξ)=∫f e^{+iξs}`, `t(ξ)=(2π)^{−1}∫u e^{−iξs}`,
the nonunitary inverse of `γt` equals `(2π)^{−1}∫f(s−τ)u(s)ds` — matched to 8 digits at `τ=0,0.35,−0.6,1.1`,
while `f(s+τ)` differs grossly (+0.019280 vs −0.109038 at τ=1.1). So (G16)'s `H_J(s−t)` is right and equals
`I_J(−t)/(2π)`; SCHUR's symmetrisation `[I_J(t)+I_J(−t)]/(2π)` is `t↦−t` invariant, so **the two documents agree
after symmetrisation**. No inconsistency.
**(G18)** re-derived: `L'=(sin z−Si z)/z²`, `L''=cos z/z²+(−3sin z+2Si z)/z³` ✓.
**(G19)** `max_{0<z≤200}|3sin z−2Si z| = 6.2475493` at `z=4.5675`, well below `20/3=6.6667` ✓. Case checks:
`Si(4)=1.7582 < 1.766979` (the 5-term alternating upper polynomial) `< 9/5` ✓; `π/2+2/(3π)=1.783003 < 9/5` ✓;
`3(4−π)+4 = 6.575 ≤ 6.58` ✓. **The judge's catch is correct**: `Si(π)=1.85193705198…`, so the report's
`1.851937` is *not* an upper bound and its `6.7038 = 3+2·1.851937` was never established (`3+2Si(π)=6.7038741`).
(G19) repairs it — `20/3 < 6.7038` — so the code's `(1+6.7038/|z|)/z²` stands.
**(G20)–(G22) all verified** (`c2.py`): `(1−e^{−d0})/d0 = 0.9181518 ≥ g=0.91813` ✓; `max|e^t−1−t|/t² = 0.5301770
≤ d=0.594604 (=e^{d0}/2)` ✓; `e^{d0/2}=1.0905077 ≤ 1.09051` ✓; `e^{3d0/2}=1.2968396 ≤ 1.29684` ✓;
`max|e^{3t/2}−1|/|t| = 1.712996 ≤ 1.8` ✓. (G21): `(1.8·1.189208+d)/9=0.303909<0.3231` ✓;
`1.09051/2+d/g²=1.250629<1.2507` ✓ (tight); `9/g²+7d/g³=16.054537<16.693` ✓; third bound `2·1.09051/g=2.37550
<13.917`, `3·1.29684/g²+3=7.61529<10.933` ✓. (G22): `2·1.09051/g+5d/g²=5.902373<5.91` ✓;
`4·1.09051/g=4.751005<4.76` ✓; `10(1.29684/g²+1)=25.384311<25.4` ✓. Every one is reconstructible, e.g.
`|q_β| ≤ |e^{t/2}−1||L(A)| + |A−B|sup|L'| ≤ 2e^{d0/2}/(gβ)+5d/(g²β)`. The `|L'|≤3/z²` used in (G21) is safe
(`|sin z−Si z| ≤ 1+Si(π) < 3`).

## 5. §3.3 (G23)–(G25) — CORRECT

`κ = ½e^{−d0}−¼ = e^{−a−d0}(1−e^{d0}/2)` — identical because `e^{−a}=½`; both `0.170448207626857` ✓ (= the code's
`kappa`). **Exhaustive minimisation** over `k∈{0,±1}`, `m∈[−30,30]\{k}`, `θ∈[−¼,¼]` (2001 points) of
`|2^m−2^{k+θ}|/2^{max(0,m)}` gives min `0.170448207627` attained **exactly at `(k,m,θ)=(−1,−2,−¼)`** — precisely
the case the verdict names (branch at `−a`, lower neighbour ratio `1/4`) ✓. Sum arguments bound below by
`e^{−a−d0}=0.42045 > κ` ✓ (conservative, as stated). (G24): I re-derived `C₀=2E/(π²κ)` from `|c_ic_j|≤¼`,
`|L|≤4/|z|`, 4 branches; and `C₁=E/(π²κ)+5EB_x/(2π²κ²)` from `|L'|≤5/z²` and chain factor `β_je^u ≤ β_max B_x`.
`E=1.5422108<1.542211` ✓, `B_x=2.3784142<2.378415` ✓, `κ>0.1704482` ✓, `C₀=1.8335027<1.834` ✓,
`C₁=32.897353<32.90` ✓ (0.008 % margin); with the verdict's own outward rationals `C₁=32.897384<32.90` ✓.
(G25) `Σ_{n>J}(2n+3)2^{−n}=(2J+7)2^{−J}` verified symbolically and at `J=0,3,24` ✓. The `Σ_s|w_s|=1+½+½=2`
factor and the deferred `2π` match the code (`NT` adds `2·tl`; `R_and_Rp` applies `−2πN`) ✓.

## 6. §3.4–§3.5 — the defect is real; the repair is sound; §3.5 is over-cautious for THIS run

**Region-I tail defect — confirmed by quote.** `gauge_cert.py:38–51`:
`def region1_Q(): tot = arb(0); for j in range(0, 400): … ; return tot` — no tail term for `j >= 400`.
It is the **only** unbounded truncation on the certificate path (`QQ`, `NT`, `_Lseries` each add explicit radii).
(G26): `(2048/√(2π))·2^{−200}/(1−2^{−1/2}) = 1.7359274e−57 < 2^{−188} = 2.5489471e−57` ✓; rational route
`2048/√6·4 = 3344.37 < 4096 = 2^{12}` ✓. The propagation `(c/2)ε_Q→V1`, `cε_Q→B_I`, `ct₂ε_Q→A_I` matches the
code's assembly exactly; contributions 1.05e−58 and 1.05e−61, both ≪ 1e−50 ✓.
**Constructor counterexample — reproduced exactly (`c3.py`, python-flint).** `tl=[0±0.1]`, `tr=[1±0.3]` ⇒
`arb(((tl+tr)/2).mid(),((tr−tl)/2).upper()) = [−0.2, 1.2]`, missing `tr.upper()=1.3`. GAUGECHECK's "provably
contains `[tl,tr]`" is indeed false **in general** ✓.
**But in this run the effect is exactly zero.** Rebuilding the grid at prec=300: 2579 cells; max node-ball
radius `7.41e−88 = 2^{−289.4}`; cell widths ≥ 2e−6. `tb` contains `[mid(tl),mid(tr)]` for **all 2579** cells, and
in fact contains the **full outer hull** `[tl.lower,tr.upper]` for all 2579 (worst shortfall 0). So the judge's
midpoint-partition interpretation is valid, and the stronger reading holds here too. The three analytic
endpoints have radii `t₂ 2^{−309.0}`, `2δ 2^{−300.4}`, `d₀ 2^{−301.8}`, all `< 2^{−290}` — the verdict's
"below 2^{−290}" refers to exactly those three and is true.
(G27)–(G29): `Σ_j[25.4/(β_js²)+4.76/(β_js)]` at `s=1/2000` = `3.234e7 < 4e7` ✓;
`2600·1e10·2^{−288} = 5.23e−74 < 1e−70` ✓; `1e−50` covers `1e−55` and `1e−70` ✓. (G28) quotes the **repaired**
run (`A ≤ 0.00346180882191`), not the report's pre-repair `…830291` — correct sourcing.

## 7. §4.1 (G30)–(G31) — CORRECT, and (G31) is non-vacuous on h4

(G30) is the standard Schur identity `inf_x⟨x+y,T(x+y)⟩ = ⟨y,(B−E*A^{−1}E)y⟩` at `x=−A^{−1}Ey`, then `≥ ½ inf_x
P[x+y] ≥ 0` by (G14). Strictness for `y≠0`: `V₈` is finite-dimensional hence `P`-closed, `y∉V₈`, `P` has no
nonzero null vector ⇒ `dist_P(y,V₈)>0` ✓ — and correctly *not* a `‖y‖₂²` floor.
(G31) re-derived: `dμ=|ĥ|²dξ/(2π‖h‖²)` is a probability measure (Plancherel); Jensen on the convex `1/(2π+t)`
gives `𝓕(h) ≥ (c_*/2)/(2π+∫|ξ|dμ)`; `∫|ξ|dμ ≤ (∫ξ²dμ)^{1/2} = ‖h'‖/‖h‖` by Cauchy–Schwarz + Plancherel ✓.
On `h₄=(∂²−¼)(1−(x/δ)²)⁴` (sympy, exact): `‖h₄‖² = 4096(7δ⁴+272δ²+7344)/(765765δ³) = 301750.446860` (matches
GAUGECHECK's 301750.4469 ✓), `‖h₄'‖² = 8192(δ⁴+108δ²+4680)/(45045δ⁵) = 2.5450566e9`, ratio `91.838496`.
Bound `= c_*/(2(2π+91.838496)) = 0.0013462136` **< certified 0.0035088** ✓ — 38 % of it: informative, not vacuous.

## 8. §5.1 (G32)–(G34) — the key new claim: CORRECT, confirmed by my own probe

**Re-derived from SCHUR §2.3 independently.** `Q_sc[v]=−∫ℓ₂|v̂|²` has spatial kernel `−2πK_ℓ`; for
`v=U_{a/2}h₊+U_{−a/2}h₋` the `(σ,τ)` block has kernel `−2πK_ℓ(t+(σ−τ)a/2)`. Diagonal `−2π·D(t)/(4π) → −2π·S/(2π)
= −1·S`; off-diagonal (displacement `±a`) `−2π(√2+r)/(4π) = −(√2+r)/2 = −C_a`. Hence (G32) ✓. Exactly
`(√2+2^{−1/2})/2 = 3/(2√2) = 1.0606601717798212866 = cosh((log2)/2)` ✓. Eigenvalues `C_a−1 = c = 0.0606601718`
(minus, matching `K_T=cS+R`) and `−(1+C_a) = −2.0606602` ✓ (G33). Normalisation `|v̂_±|²=(1±cos aξ)|ĥ|²/H` ⇒
`Q_sc[v_h]=𝓕(h)` and `Q_sc[v_{+,T}]=−((1+C_a)/c)p(T)+o(1/T)` with `(1+C_a)/c = 33.970563`. Lobes are disjoint
(`a/2=0.3466 > δ=0.0507`), so the `√2‖h‖` normalisation is exact ✓.
**My own float probe (`plus.py`, `hT_probe.py` with `(1−cos)→(1+cos)`, 2920 `ℓ₂` samples, R=250):**

| T | p(T) | minus `𝓕(h_T)/p` (⇒ 1) | plus `Q_sc[v_{+,T}]/p` (⇒ −33.9706) | plus absolute |
|---:|---|---:|---:|---|
| 120 | 2.292326e−3 | +0.7586 | −25.7693 | −5.907e−2 |
| 240 | 1.146163e−3 | +0.9201 | −31.2577 | −3.583e−2 |
| 480 | 5.730815e−4 | +0.9774 | −33.2018 | −1.903e−2 |

Both channels converge to their predicted multipliers with the **same** relative deficit at T=480 (2.26 % each):
the `o(1/T)` remainder behaves identically in the two channels, as (G34)'s proof asserts. `Q_sc[v_{+,480}] =
−0.01903` vs the predicted `−0.01947`. **(G34) corroborated; the plus channel is negative.** No invisible gauge
removes it: a shifted gauge kernel `k(t+a)` is again of the form (G4), so every block is gauge-invariant ✓.

## 9. §5.2–§5.3 — CORRECT (one arithmetic slip)

CF of `log3/log2 = 1.5849625007` is `[1;1,1,2,2,3,1,5,2,23,…]`; convergents give `2^8/3^5 = 1.0534979`,
`3^12/2^19 = 1.0136433` (both as printed), then `2^84/3^53 = 0.9979140`, `2^1054/3^665 = 0.99995635`,
`2^24727/3^15601 = 1.0000182`. Ratios `→1`, so no uniform `κ` for the two-prime lattice ✓; the dyadic constant
cannot be copied ✓. (G35): `M_±(U_ch)=e^{±c/2}M_±(h)` ⇒ `M₊(v_h)=2sinh(a/4)M₊(h)/(√2‖h‖)`,
`M₋(v_h)=−2sinh(a/4)M₋(h)/(√2‖h‖)` ⇒ `2Re{M₊(v_h)conj M₋(v_h)} = −(4sinh²(a/4)/‖h‖²)Re{M₊conj M₋}` — verified
numerically to 12 digits ✓; `2sinh²(a/4)=cosh(a/2)−1=c=0.0606601717798213` ✓.

**DEFECT D1 (LOW, non-load-bearing).** The follow-up sentence "Their combined residual pole coefficient is
`−2(α+c)Re(M₊conj M₋)/H`" does **not** follow from (G35). Per unit `Re(M₊conj M₋)/H`: Weil pole term `−2c =
−0.121320`; gauge form on `v_h` `= 2α·Re{M₊(v)conj M₋(v)} = −2αc = −0.062965`; pole∓gauge `= −2c(1∓α) = −0.058355`
or `−0.184286`. The printed `−2(α+c) = −1.159320` matches neither (it writes `α+c` for `c(1±α)`; factor 6–20 off).
The paragraph's conclusion ("no sign is obtained by calling this a harmless rank-two term") is unaffected —
nothing downstream uses the coefficient. Fix: `−2c(1+α)` (or `−2c(1−α)`), stating which side the gauge sits on.

## 10. RESULT codes and the four registrations

**Codes: accepted as written**, given the conditionals the header itself carries (`VERIFIER: PAPER`,
`LEAN_KERNEL_VERIFIED: false`, `INDEPENDENT_NUMERICAL_RERUN: false`, `COMPLETE_MACHINE_CHECKER…: not_run`,
`Q2_QUALIFICATION`). `Q1a_GAUGE: PROVED_ON_CLASS` ✓ (exact algebra, reproduced);
`Q1a_ONLY_TWO_DIFFERENCE_GAUGES: ATTEMPT_REFUTED…` ✓ (`t sinh(t/2)`); `Q1b/Q1c: PROVED_ON_CLASS` ✓ conditionally;
`Q2: CERTIFICATE_RATIFIED` with the region-I qualification ✓ (the defect is real, the repair arithmetic);
`Q3_FROZEN_NUMERICAL_EVENT: PARTIAL` ✓ (correct refusal to let a class theorem retire a frozen receipt);
`Q4_INDEPENDENT_PROFILES_SCALAR_SHORTCUT: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE` ✓ — noting it is an exact
*asymptotic family*, not a single exhibited witness, which the verdict itself labels `KILL_SCOPE: THEOREM_SHAPE`.

**All four new `P_GAUGE_*` registrations: I would accept.** `…FOUR_DIMENSIONAL…` (0.97) — verified end to end,
I would go higher. `…INDEPENDENT_PLUS_SCALAR_NEGATIVE` (0.93) — corroborated to 2.3 % at T=480 by an independent
probe; fair. `…TWO_PRIME_UNIFORM_NONRESONANT_KAPPA_FAILS` (0.98) — elementary and verified; fair.
`…COMPLETED_CLASS_HALF_PRINCIPAL_BOUND` (0.90) — fair, but the *rational* high-frequency margin is 0.19 %
(`2·(1/8)=0.25` vs `c_*>25047/100000`) and it rests on one unreplicated 2,579-cell arb run.

**First asserted-not-derived step.** Not in the new material — everything new I could reconstruct, including the
terse (G21)/(G22) constants. The first genuine gap is inherited and declared: §3.1's "gamma_J and t_J converge
uniformly in frequency by the source Euler and Mellin bounds" — the passage from the Abel-damped product to the
undamped distributional identity is asserted, not shown (the domination `C(−s)e^s` on the `s≤0` factor *is*).
It sits inside the stated SCH (5)–(8),(13) conditional. Second-closest: §5.1's "The remainder entries are
`W^{1,1}` on the short difference window" for the **off-diagonal** blocks — true by SCHUR's diagonal argument
with signs changed, but not written out, and exactly what `P_GAUGE_INDEPENDENT_PLUS_SCALAR_NEGATIVE` is graded on.

**What still has no second channel.** `A` and `B` come from a single run of `gauge_cert.py`; I did not re-sum the
2,579 rows either. Everything *above* those two scalars I verified independently; the scalars remain
single-channel, as the verdict states.
