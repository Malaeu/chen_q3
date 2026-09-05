# Independent audit — GOAL058 XIDEV verdict, four registered predictions

```yaml
REPORT_ID: AGENT_REPORT_2026-09-05_GOAL058_XIDEV_INDEPENDENT_AUDIT
AUDITED_DOCUMENT: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md
AUDITED_REQUEST: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.txt
METHOD: re-derivation from [C] arXiv:2511.22755 (3.1)-(3.11), (7.1)-(7.4) and [W] arXiv:2106.01715 (1.1)-(1.2), 2.1.1
        + independent float64/mpmath numerics; the verdict's own derivations were NOT used as premises
AUDITOR: Claude (Linux body), read-only except this file
LEAN_RUN: false      NUMERICAL_RUN: true (short, local)      COMMITS: none
NOT_ATTEMPTED: (DOM), (FM)   -- excluded by the audit task
VERDICTS:
  P_XIDEV_CANONICAL_SCALE_AND_RADICAL_SURVIVE: SURVIVES
  P_XIDEV_SIGNED_GROUND_STATE_IDENTITY_SURVIVES: SURVIVES
  P_XIDEV_LITERAL_DIAGONAL_BUDGET_SURVIVES: SURVIVES
  P_XIDEV_FINITE_PRIME_TAIL_SURVIVES: SURVIVES
NEW_DEFECT_FOUND: printed d_A = 1.372178 in [R] line 44 is wrong (true d_A = 1.3721834192);
                  the judge's decimal remark identifies the mismatch but assigns it to the wrong side
```

Scripts: `/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/audit/n1.py … n8.py`
(session-local scratch; all numbers below are reproducible from them).

---

## 0. What was re-derived before anything was believed

The geometric form (Q) was rebuilt from the source, not copied from the verdict.
Log transport `x = log u`, `F(x) = g(x)`, `f(u) = u^{-1/2}F(u)`, `h = f* * g` i.e.
`h(t) = R_{f,g}(t) = ∫ conj(f(x)) g(x+t) dx`. From [C] (3.10)–(3.11) `Ψ = W_{0,2} − W_R − Σ_p W_p`:

- **(3.11)** `W_{0,2}(F) = F̂(i/2)+F̂(−i/2) = ∫h(x)e^{x/2}dx + ∫h(x)e^{−x/2}dx = A_+(g)·conj(A_−(f)) + A_−(g)·conj(A_+(f))`,
  and for `f = g` this equals `2Re(A_+ conj(A_−)) = 2∫_0^∞ (e^{t/2}+e^{−t/2}) C_g(t) dt`.
  → the verdict's "pole contribution is `2∫_0^∞(e^{t/2}+e^{−t/2})C_g(t)dt`" is **confirmed**.
- **(3.7)** `Σ_p W_p(F) = Σ_{n≥2} w_n [h(log n)+h(−log n)] = 2 Σ_{n≥2} w_n C_g(log n)`, `w_n = Λ(n)/√n`.
- **(3.4)/(3.7)-line** the archimedean kernel is *literally* `a(t)`:
  `x^{1/2}/(x−x^{-1}) d*x = e^{−t/2}/(1−e^{−2t}) dt = a(t)dt`. Hence
  `−W_R = 𝒟(g) − H(g)[log 4π + γ + 2∫_0^∞(1−e^{−t/2})a(t)dt] = 𝒟(g) − c_A H(g)`.

So (Q) as printed in the verdict is exactly `Ψ(g* * g)` from [C]. No term is missing and no sign is flipped.
Numerically `∫_0^∞(1−e^{−t/2})a(t)dt = 1.13197175367742096` and `(1/2)log 2 + π/4 = 1.13197175367742096`
(agree to 20 digits, mpmath dps=30) — the archimedean constant reduction is correct.

**(EF) rederived.** `ĥ(z) = conj(Ff(z̄))·Fg(z)` by direct computation, and [C] (3.2) with
`f̃(ρ) = F̂(z)`, `ρ = 1/2+iz`, gives `B(f,g) = Σ_{Ξ(z)=0} conj(Ff(z̄)) Fg(z)`.
This is verbatim [W] (1.1) `QW(f,g) = Σ_{1/2+is∈Z} f̂(s̄) ĝ(s)` with [W] (1.2). Confirmed.

**(JS)/(S-GEOM) rederived.** `𝒟 = 𝒥 + ∫e^{−t/2}D_g = 𝒥 + 4H − 2∫e^{−t/2}C_g`, hence
`Q = 𝒥 − (c_A−4)H + 2∫_0^∞ e^{t/2}C_g dt − 2Σ w_n C_g(log n) = 𝒥 − d_A H + 𝒮`. The `−4` that makes
`d_A = c_A − 4` comes from `2∫_0^∞ e^{−t/2}·2H dt`. Confirmed.

---

## 1. P_XIDEV_CANONICAL_SCALE_AND_RADICAL_SURVIVE (0.88) — **SURVIVES**

### (i) Claim
The Mellin transform of the printed `E(h)` of [C] (7.1) is `ξ(s)/4`, so `Φ = 4E(h)(e^x)` has
`FΦ = Ξ`; `f_0 = Φ/‖Φ‖` is a **radical** vector: `B(f_0,v) = 0` for all `v ∈ X`.

### (ii) Independent derivation
The printed source reads (page 28 of the PDF, layout-preserved extraction)
`k(u) = E(h)(u), h(u) = (π/2) u²(2πu²−3) e^{−πu²}`, i.e. `h(u) = (π²u⁴ − (3/2)πu²)e^{−πu²}` —
identical to the verdict's `h`. Cross-check against (7.4): `3·2^{−17/4} h_0 = (3/16)e^{−πx²}` and
`√3·2^{−11/4} h_4 = (π²x⁴ − 3πx²/2 + 3/16)e^{−πx²}`; their difference is exactly `h`. Consistent.

With `∫_0^∞ u^{α}e^{−πu²}du = ½π^{−(α+1)/2}Γ((α+1)/2)`:

```
∫_0^∞ h(u)u^{w-1}du = ½π^{−w/2}Γ(w/2)[ (w/2)(w/2+1) − (3/2)(w/2) ] = (1/8) w(w−1) π^{−w/2} Γ(w/2)
```

which is `ξ(w)/(4ζ(w))`. Then `∫_0^∞ E(h)(u)u^{s−1}du = Σ_n n^{−(s+1/2)}∫h(v)v^{s−1/2}dv = ζ(s+½)·ξ(s+½)/(4ζ(s+½)) = ξ(s+½)/4`,
so with `F Φ(z) = 4∫_0^∞E(h)(u)u^{−iz}d*u = 4·ξ(1/2−iz)/4 = Ξ(z)` (functional equation, `Ξ` even).
**The factor 4 is real and it is a defect of the printed [C] Lemma 7.1, not of the verdict.**
`h` self-duality, `h(0)=∫h=0`, Poisson, and the resulting evenness `E(h)(u)=E(h)(1/u)` were checked
numerically (`Φ(x)=Φ(−x)` to 12 digits at x = 0.3, 0.7, 1.1).

Radical: `f_0` and its multiplicative form lie in the Weil class `W` of [C] p.5 / [W] §2.1.1
(`f(u)=u^{−1/2}f_0(log u) = O(u^δ)` at 0 and `O(u^{−1−δ})` at ∞ for every δ, by the super-exponential
envelope). The convolution `h = f_0^* * v` is likewise in `W`. `Ξ` is real entire ⇒
`conj(F f_0(z̄)) = Ξ(z)/A = 0` at every zero, so **every summand of (EF) vanishes identically**,
for any summation convention — the conditional convergence caveat of [C] p.5 is therefore inert here.
Extension from `C_c^∞` to `X` uses density + (CONT); I re-checked (CONT):
prime part `≤ 2W_gW_h Σ_{n≥2} log n·n^{−3/2} ≤ 2(1+4)W_gW_h = 10W_gW_h` (the summand decreases for
`x > e^{2/3}`, `∫_1^∞ log x·x^{−3/2}dx = 4`), pole part `≤ (8/3)W_gW_h` (`∫e^{±x−2|x|}dx = 4/3`),
energy part `≤ √(𝒟(g)𝒟(h))` ⇒ `C_X ≤ c_A + 12.67 ≤ |c_A|+14`. Correct.

### (iii) Verdict — SURVIVES
No factor, sign or domain defect found. Residual PAPER risk (named by the judge himself): the explicit
formula is an import, and [C] states it for the Weil class while *restricting itself* to
compactly-supported convolutions for absolute convergence. `f_0` satisfies the printed class conditions,
so the import is literal, not an extension.

### (iv) Numerics
| check | computed | reference |
|---|---|---|
| `∫ 4E(h)(e^x) dx` | 0.49712077818831 | `Ξ(0)=ξ(1/2)=0.49712077818831` |
| `F Φ(1), FΦ(2.5), FΦ(5)` | 0.48575742967098 / 0.42995853964681 / 0.2755499973442 | `Ξ(z)` identical to 14 digits |
| `∫Φ e^{±x/2}dx` | 0.499999999999992 | `ξ(0)=ξ(1)=1/2` ⇒ `A_± = 1/(2A)` |
| **`Q(f_0)` from (Q) directly** | **2.06e-14** | `(NULL)` — 0 |

`Q(f_0)` was assembled from independent pieces: `𝒟(f_0)=3.883667755637`, `c_A=5.3721834192`,
`2Re(A_+conj(A_−))=1.5637127963`, `2Σw_nC(log n)=0.0751971327`. This is an independent numerical
confirmation of (NULL) that neither the observer nor the judge produced (the judge ran no numerics).

---

## 2. P_XIDEV_SIGNED_GROUND_STATE_IDENTITY_SURVIVES (0.84) — **SURVIVES**

### (i) Claim
`Q(f_0 r) = ∫_0^∞ b(t)E_r(t)dt + Σ_{n≥2} w_n E_r(log n)`, `b = k − e^{t/2}`; and
`ν(I) ≤ −(43/168)log(8/7)` on `I = [log(7/5), log(8/5)]`.

### (ii) Independent derivation
Both polarization identities are exact — sympy residual **0** (not "small"):

```
|qz−pu|² − (q−p)(q|z|² − p|u|²) − pq|z−u|²   ≡ 0        (p,q real)
2pq Re(ū z) − pq(|u|²+|z|²) + pq|z−u|²      ≡ 0
```

With `v = f_0 r`, `w = f_0|r|²`, `p=f_0(x)`, `q=f_0(x+t)`, `u=r(x)`, `z=r(x+t)`, and `Re B(f_0,w)=0`:

- diagonal: `⟨f_0,w⟩ = ∫f_0²|r|² = ‖v‖²` ⇒ the `c_A` terms cancel exactly;
- translation energy: `D_v(t) − ⟨Δ_tf_0, Δ_tw⟩ = ∫[|qz−pu|² − (q−p)(q|z|²−p|u|²)]dx = E_r(t)` ⇒ `+a(t)E_r(t)`;
- correlations: `2C_v(t) − 2C_{f_0,w}(t) = ∫[2pqRe(ūz) − pq(|u|²+|z|²)]dx = −E_r(t)`, hence
  pole term `2∫(e^{t/2}+e^{−t/2})(C_v − C_{f_0,w}) = −∫(e^{t/2}+e^{−t/2})E_r`,
  prime term `−2Σw_n(C_v−C_{f_0,w}) = +Σ w_n E_r(log n)`;
- total density `a − e^{−t/2} − e^{t/2} = k − e^{t/2} = b`. **(GS) is reproduced exactly.**

`b(t) = √u(1/(u³−u) − 1)`, `u = e^t`: verified to 4e-16. On `I`, `u ∈ [1.4,1.6]`, `u³−u` is increasing with
`1.4³−1.4 = 1.344 = 168/125` exactly ⇒ `1/(u³−u) − 1 ≤ −43/168`, `√u > 1`, `|I| = log(8/7)`, and `[1.4,1.6]`
contains no integer ⇒ no prime-power atom. `(NEG-MEASURE)` follows, with room to spare.

### (iii) Verdict — SURVIVES
No sign or factor defect. `w = f_0|r|² ∈ X` for `r ∈ ℂ + C_c^∞` (bounded multiplier with bounded
derivative), so the subtraction of `Re B(f_0,w)` is licensed by L2, not circular.

### (iv) Numerics
- `∫_I b(t)dt = −0.07385378` vs claimed bound `−0.03417768` → holds (factor 2.2 of margin).
- **(GS) tested on a nontrivial complex `r(x) = e^{−x²}(1+ix) + 0.3`:**
  `Q(v)` via (Q) `= 6.0309103274e-05`; `Q(v)` via (GS) `= 6.0309103289e-05`; **difference −1.5e-14**.

---

## 3. P_XIDEV_LITERAL_DIAGONAL_BUDGET_SURVIVES (0.78) — **SURVIVES**

### (i) Claim
`‖Pf_0 − f_0‖_X ≤ B_L(ε_c+ε_t) + C_cut e^{−a√m} → 0` on the literal diagonal `N=m`, `L=log m`,
`R = L/4`, `B_L = √(mL+14(L+2))`.

### (ii) Independent derivation — every constant re-checked
- **(ENV) recursion.** `Φ^{(j)}(x) = e^{x/2}Σ_n p_j(πn²e^{2x})e^{−πn²e^{2x}}`, `p_0 = 4z²−6z`,
  `p_{j+1} = ½p_j + 2z(p_j' − p_j)`. Re-derived by the chain rule (`dz/dx = 2z`) and confirmed
  numerically: `p_1 = −8z³+30z²−15z` reproduces `Φ'` against central differences to 10 digits.
  Envelope: `e^{x/2}z^re^{−z} = π^{−1/4}n^{−1/2}z^{r+1/4}e^{−z/2}·e^{−z/2} ≤ π^{−1/4}(2(r+¼)/e)^{r+¼}e^{−z_1/2}e^{−(3π/2)(n−1)}`
  using `sup_z z^qe^{−z/2}=(2q/e)^q` and `n² ≥ 1+3(n−1)`; the geometric sum gives `(1−e^{−3π/2})^{−1}`.
  Constants exactly as printed. Numerically `A_0 = 23.9100`, `A_1 = 325.4253`; envelope holds with
  worst-case ratios 0.479 (j=0) and 0.288 (j=1) over `x∈[0,1.6]`.
- **`u_R` sits strictly inside `J_L`**: `L/4+1 < L/2 ⇔ L>4`, exactly the stated hypothesis ⇒ four
  integrations by parts have no boundary terms.
- **(RC)** my sharper computation gives `‖Pu_R−u_R‖_{∞,J_L} ≤ C_4L³/(24π⁴m³)` and
  `‖(Pu_R−u_R)'‖_∞ ≤ C_4L²/(8π³m²)`; the claimed `ε_c = C_4(L/m)²` dominates both. Generous, valid.
  `C_4 = Σ_j C(4,j)c_{4−j}‖f_0^{(j)}‖_1 ≥ ‖u_R^{(4)}‖_1` is the Leibniz rule with `c_0 = 1`; the `c_j`
  are R-independent because the cutoff profile is fixed and only translated.
- **(RB)** `TV(h) ≤ Lε + 2ε` (interior + two endpoint jumps of the zero extension);
  `D_h(t) ≤ min(2ε·t·TV(h), 4‖h‖²) = min(2(L+2)ε²t, 4Lε²)` ✔;
  `a(t) ≤ 4/(3t)` on `(0,1]` (max of `t·a(t)` there is 0.7014) and `a(t) ≤ (4/3)e^{−t/2}` for `t≥1`
  (`1/(1−e^{−2}) = 1.1565`) ✔; energy `≤ (8/3)(L+2)ε² + (32/3)e^{−1/2}Lε² ≈ (9.14L+5.33)ε² ≤ 14(L+2)ε²` ✔;
  weighted part `= ε²(e^L−1) = ε²(m−1) ≤ mLε²` ✔. So `B_L` is correct and loose.
- **Tail.** `‖r_R‖_1 ≤ 2A_0∫_R^∞e^{−ae^{2x}}dx ≤ A_0e^{−ae^{2R}}/(ae^{2R}) = T_R` ✔;
  `‖Pr_R‖_∞ ≤ (2m+1)T_R/L`, `‖(Pr_R)'‖_∞ ≤ (2πm/L)(2m+1)T_R/L` ✔ (coefficients `≤ L^{−1/2}T_R`).
- **`C_cut`.** My assembly gives `‖r_R‖_X² ≤ (E/2a)[(35/3)A_0² + (2/3)(A_1+c_1A_0)²]`; the printed
  `(4/3)(A_1²+c_1²A_0²) ≥ (2/3)(A_1+c_1A_0)²` by `2(α²+β²) ≥ (α+β)²`. The `35/3 = 1 + 32/3` matches
  term by term. Valid.
- **Limit.** `B_Lε_c ~ C_4L^{5/2}m^{−3/2} → 0`, `B_Lε_t ~ Cm^{3/2}L^{−3/2}e^{−a√m} → 0`,
  `e^{2R} = e^{L/2} = √m` ✔. `Pf_0 ∈ X` despite its two jumps because `∫_0 a(t)O(t)dt < ∞`.

### (iii) Verdict — SURVIVES
No arithmetic defect. Two scope caveats, both already flagged inside the verdict and **not** repaired here:
(a) the identification of "the literal full modes" with [F]'s `Fin (2*N+1)` carrier is an asserted
crosswalk, not verified by this audit; (b) the estimate says nothing about positivity of the finite
matrices, and the verdict does not claim it.

### (iv) Numerics
Not needed beyond the envelope check above: every step is an inequality whose two sides I recomputed
symbolically, and each printed constant dominates the sharp one.

---

## 4. P_XIDEV_FINITE_PRIME_TAIL_SURVIVES (0.88) — **SURVIVES**

### (i) Claim
(SP) Stieltjes cutoff with boundary term `2Δ(T)P^{−1/2}C_g(T)`; (TAIL-S); (CERT); (PCUT).

### (ii) Independent derivation
Write `F(t) = e^{−t/2}C_g(t)`, so `𝒮(g) = 2∫_0^∞ Δ dF`. Then
`2∫_0^T Δ dF = 2Δ(T)F(T) − 2∫_{(0,T]} F dΔ`, `Δ(0)=0`, `F` continuous, `dΔ = dψ(e^t) − e^t dt` ⇒

```
2∫_0^T Δ dF = 2∫_0^T e^{t/2}C_g dt − 2Σ_{2≤n≤P} (Λ(n)/√n) C_g(log n) + 2Δ(T)P^{-1/2}C_g(T) = S_P(g)
```

exactly (SP), boundary sign `+`, atom at `n=P` included. Hence `𝒮 − S_P = 2∫_T^∞ Δ dF`.

- **(CORR)**: `e^{2|x|}+e^{2|x+t|} ≥ e^{−2x}+e^{2(x+t)} = 2e^t cosh(2x+t)` (exact),
  `cosh 2y ≥ 1+2y²` ⇒ `∫e^{−a(e^{2|x|}+e^{2|x+t|})}dx ≤ (√π/2√a)e^{−t/2}e^{−2ae^t}`; multiply by
  `A_0A_1` and `A_0²/2`. `M_g` as printed.
- **(TAIL-S)**: `|Δ(t)| ≤ e^t(1+t)` from `0 ≤ ψ(x) ≤ x log x`; integrand `≤ 2M_g(1+t)e^{−2ae^t}`;
  `x = e^t` ⇒ `2M_g∫_P^∞ (1+log x)x^{−1}e^{−2ax}dx ≤ (M_g/a)((1+log P)/P)e^{−2aP}`. As printed.
- **(TAIL-J)**: `k(t) ≤ e^{−5t/2}/(1−P^{−2})` for `t ≥ log P`, `D_g ≤ 4H`, `∫_{log P}^∞e^{−5t/2}dt = (2/5)P^{−5/2}`
  ⇒ `E_J = (8H/5)P^{−5/2}/(1−P^{−2})`. As printed.
- **(CERT)**: `Q − 𝒜_P = (𝒥−J_P) + (𝒮−S_P) ∈ [0,E_J] + [−E_S,E_S]` ⇒ the printed two-sided enclosure,
  with the asymmetry (`E_J` only on the upper side) correct.
- **(PCUT)**: `(1+log P)/P ≤ 1` and `(1−P^{−2})^{−1} ≤ 4/3` for `P ≥ 2`;
  `E_J ≤ (32H/15)P^{−5/2} ≤ ε/2 ⇔ P ≥ (64H/15ε)^{2/5}` ✔;
  `E_S ≤ (M/a)e^{−2aP} ≤ ε/2 ⇔ P ≥ (1/2a)log(2M/aε)`, and the printed `log(1+2M/aε)` is larger. ✔

### (iii) Verdict — SURVIVES
No sign, factor, or endpoint defect. The endpoint term is genuinely load-bearing (see numerics).

### (iv) Numerics — the endpoint identity tested directly
`𝒮(f_0) = 0.8015418577652628` computed independently from (S-GEOM).

| P | `S_P` (with endpoint) | `𝒮 − S_P` | `2∫_T^∞ Δ dF` | match |
|---:|---|---|---|---|
| 2 | +0.7456283884 | +5.5913e-02 | +5.5913e-02 | −9.1e-15 |
| 3 | +0.8011278144 | +4.1404e-04 | +4.1404e-04 | −7.3e-15 |
| 11 | +0.8015418578 | ~2e-15 | — | — |

(SP) is therefore an **exact identity**, endpoint term included, to quadrature precision.
Warning for later use: at `P = 2,3` dropping the endpoint term happens to give a *smaller*
apparent error (−2.3e-2 / −2.0e-4) — accidental cancellation against the tail, not evidence that the
term is optional. Anyone tuning a cutoff numerically will be misled by this if they test only P≤3.

(CORR) checked against the true correlation with the judge's own `M_{f_0} = 5704`:
`t=0.5`: `1.587e0 ≤ 2.501e1`; `t=1.0`: `4.43e-2 ≤ 6.77e-1`; `t=2.0`: `1.86e-12 ≤ 1.74e-7`. Holds, loose.
`E_S(f_0, 59) = 9.9e-79` — consistent with the verdict's "contains `e^{−59π}`".

---

## 5. The decimal remark — the judge is half right, and the defect is in the request

```
c_A = γ + log(8π) + π/2 = 5.3721834192256655822
d_A = c_A − 4          = 1.3721834192256655822          →  10 digits: 1.372183419
```

- **Request [R] line 44 prints `d_A = ... = 1.372178`. That number is wrong**, by `+5.42e-6`.
  It is not a rounding of `1.3721834192` at any precision.
- The judge writes: "the displayed numbers give `0.5706416+0.801542 = 1.3721836`, whereas the displayed
  `d_A` is `1.372178`". The arithmetic observation is correct, but the mismatch comes **entirely from the
  printed `d_A`**, not from the pair `(J_inf, S_inf)`.
- My independent values: `𝒥(f_0) = 0.5706415614603715` (rounds to **0.5706416** ✔),
  `𝒮(f_0) = 0.8015418577652628` (rounds to **0.801542** ✔), and
  `𝒥+𝒮 = 1.3721834192256859` vs `d_A = 1.3721834192256655` — agreement `2.0e-14`.
- So `0.5706416 + 0.801542 = 1.3721836` **is consistent with the true `d_A` at the printed precision**:
  the printed inputs carry `±5e-7`, and `d_A − 1.3721836 = −1.8e-7`, inside that.
- The observer's claimed full-precision residual `−5.5e-11` is **not confirmed and not refuted** here:
  my float64 pipeline gives `+2.1e-14` with its own quadrature error of order `1e-13`, so both numbers
  are consistent with the exact identity (CAN-EQ). The judge's stricter point stands: printed decimals
  do not certify a residual; only interval arithmetic would.

**Net:** the judge's "decimal boundary" paragraph should be re-aimed. The item to fix is the request's
`d_A = 1.372178`; the observer's `J_inf`/`S_inf` decimals are correct as printed.

---

## 6. Summary

| Prediction | p | Audit verdict | Basis |
|---|---:|---|---|
| `P_XIDEV_CANONICAL_SCALE_AND_RADICAL_SURVIVE` | 0.88 | **SURVIVES** | Mellin `= ξ(s+½)/4` re-derived; `FΦ = Ξ` to 14 digits at 4 points; (EF) rebuilt from [C](3.10)-(3.11) = [W](1.1); `Q(f_0) = 2e-14` |
| `P_XIDEV_SIGNED_GROUND_STATE_IDENTITY_SURVIVES` | 0.84 | **SURVIVES** | both polarizations exact (sympy 0); (GS) rebuilt independently; numeric test on complex `r` matches to 1.5e-14; `∫_I b = −0.0739 ≤ −0.0342` |
| `P_XIDEV_LITERAL_DIAGONAL_BUDGET_SURVIVES` | 0.78 | **SURVIVES** | every constant recomputed; each printed bound dominates the sharp one; `35/3 = 1+32/3` reproduces exactly; (ENV) constants verified numerically |
| `P_XIDEV_FINITE_PRIME_TAIL_SURVIVES` | 0.88 | **SURVIVES** | (SP) verified as an exact identity at P=2,3 to 1e-14 incl. endpoint; (CORR)/(TAIL-S)/(TAIL-J)/(CERT)/(PCUT) re-derived |

Not attempted, by instruction: **(DOM)** and **(FM)** — the two open inequalities. Nothing in this audit
touches the open status of `W`; all four confirmed items remain PAPER-level, none is kernel-verified.

**Falsification attempts that failed** (i.e. the verdict withstood them): forcing a factor mismatch in
`FΦ` at four independent `z`; forcing a sign error in (GS) with a complex, non-symmetric `r` with a
nonzero constant at infinity; forcing an endpoint-convention error in (SP) at the smallest cutoffs where
the boundary term is largest; forcing an envelope-constant error by evaluating (ENV)/(CORR) against the
true `f_0`.
