# H4 scalar-floor certificate — inverse-free interval for 𝓕(h₄)

**RESULT CODE (v1 §9): `SCALARFLOOR_H4_SOURCE_LOWER_CERTIFIED`.**

```
L_F = 0.0034393623002774739205      U_F = 0.0035782034198665259817
1/500 = 0.002                        L_F >= 1/500 : TRUE
```

The interval is a **numerical certificate** (ball arithmetic, python-flint 0.8 / arb),
CONDITIONAL on the paper theorems named in §7. Everything else in this report that is
not the interval itself is **DIAGNOSTIC_NEVER_A_PROOF**.

Certified statement: for the exact zero-extended polynomial test h₄ of §1,
𝓕(h₄) = −∫_ℝ W_{h₄} ℓ₂ dξ ∈ [L_F, U_F] ⊂ (0, ∞). Via SCALARFLOOR Theorem 1 (6) this
gives 𝔪(h₄) ≥ L_F ≥ 1/500 **with no semilocal inverse and no dropped mode**. It certifies
that test's genuine-source positivity only — not plant survival, not the frozen eta event,
not the whole class.

## 1. The frozen test

h₄(x) = Σ_{j=0..4} A_j (x/δ)^{2j} on |x| < δ, zero outside; **N₄ = 1** (the normalized
functional is invariant under a nonzero scalar, v1 §7.2).

* δ = (log3 − log2)/8 = 0.050683138513520547747…, support = closed [−δ, δ], 2δ < log 3.
* (A₀,…,A₄) = (−8δ^{−2} − 1/4, 72δ^{−2} + 1, −120δ^{−2} − 3/2, 56δ^{−2} + 1, −1/4)   [v1 (35)]
* **H₄ = ‖h₄‖₂² = 2δ Σ_{i,j} A_iA_j/(2(i+j)+1) = 301750.44686019244778** [v1 (35)] — matches
  the target 301750.44686 to all printed digits.
* h₄ = η₄″ − η₄/4 with η₄ = (1−(x/δ)²)⁴. Regularity of the zero extension: h₄ ∈ C¹(ℝ),
  h₄″ ∈ L^∞ with a jump at ±δ, so h₄ ∈ H²(ℝ) and **not** H³. This is a valid approximation
  profile, not a literal member of C_c^∞(I) (v1 §7.2).
* **Both pole moments vanish exactly, as an algebraic identity, not a quadrature result:**
  ∫h₄e^{±x/2}dx = ∫(η₄″ − η₄/4)e^{±x/2}dx = ∫η₄((e^{±x/2})″ − e^{±x/2}/4)dx = 0, because
  η₄ and η₄′ vanish at ±δ (two integrations by parts, no boundary term) and (e^{±x/2})″ = e^{±x/2}/4.
  Numerical confirmation in arb: |∫h₄e^{±x/2}dx| ≤ 6.0e−116 (requested tolerance was 1e−25).

## 2. Conventions, each with its source equation

| object | definition | source |
|---|---|---|
| a, r, δ | log 2, 2^{−1/2}, (log3−log2)/8 | v1 §1 |
| ĥ(ξ) | ∫h(x)e^{−iξx}dx (nonunitary) | v1 §1 |
| W_h(ξ) | (1 − cos aξ)|ĥ(ξ)|²/H, ∫_ℝ W_h = 2π | v1 (1),(2) |
| γ₂(ξ) | π^{−iξ}·Γ(¼+iξ/2)/Γ(¼−iξ/2)·b(−ξ)/b(ξ), b(ξ)=1−re^{−iaξ}; \|γ₂\|=1 on ℝ | RESONANCE (2) |
| J(β,η) | ∫₀¹(−log v)v^{−1/2+iη}cos(βv)dv | RESONANCE §2.2 |
| t₂(ξ) | (1/2π)[Σ_{j≥0}J(2π2^j, −ξ) − J(π, −ξ)] | RESONANCE (10) with p=2, c₋₁=−½, c_j=½; restated v2 §3.2 |
| ℓ₂ | 2 Re(γ₂ t₂) | v1 §1 (3) |
| 𝓕(h) | −∫_ℝ W_h ℓ₂ dξ | v1 (3) |

Reconciliation check performed: RESONANCE (10) is t_p = (1/π)Σ_{j≥−1}c_jJ(β_j,−ξ) with
β₋₁=2π/p, c₋₁=−1/p, β_j=2πp^j, c_j=1−1/p. For p=2 this is exactly the v2 §3.2 form used here,
and it is the same convention as `mellin_d2/dens.py::t_S` (verified numerically, §6 V3).

## 3. What is computed rigorously, and how

Splitting (no double counting):

    𝓕 = [−∫_{|ξ|≤X} W ℓ₂^{[J₀]}]  −  ∫_{|ξ|≤X} W (ℓ₂ − ℓ₂^{[J₀]})  −  ∫_{|ξ|>X} W ℓ₂
        └── compact CC quadrature ──┘  └──── ≤ 4π ε_{J₀}, v1 (33) ────┘  └── ≤ 2T μ_X ──┘

with X = 2000, J₀ = 90 (Euler sum kept through j = J₀).

**(a) ĥ₄ — exact.** ĥ₄(ξ) = 2δ Σ_j A_j ∫₀¹ z^{2j}cos(δξz)dz, each factor by its entire power
series Σ_n(−1)^n c^{2n}/((2n)!(2j+2n+1)), c = δξ, with an enclosed alternating tail. No division
by a removable zero anywhere; the formula is entire in ξ, which is what the quadrature bound needs.

**(b) γ₂ — arb, ball.** log-Γ form; on real nodes the returned ball has |γ₂| = 1 ± 1e−12. The
modulus/evaluation error of v1 (36) is **not** budgeted separately: it is inside the ball, since
every operation is ball arithmetic. HARD rule obeyed — no arb→float conversion on the certificate path.

**(c) J(β,−ξ) — two representations, agreeing on an overlap band.**
1. *Series* (small β): J = Σ_n(−1)^nβ^{2n}/((2n)!(s+2n)²), s = ½ − iξ, at working precision
   1.4427·β + 460 + O(log β) bits (the sum cancels by e^β), with the geometric tail enclosed.
   The node ξ must be a ball of radius ≪ 2^{−working prec}: it is built at 12000 bits.
   *(This was a real trap: at 400-bit nodes the e^β amplification of the node radius produced
   enclosures of width 1e+43 — caught by the ball arithmetic, not by a plausibility check.)*
2. *Large β* — derived here, elementary:
   J(β,ξ) = β^{−s}Γ(s)[(log β − ψ(s))cos(πs/2) + (π/2)sin(πs/2)] + R_β(s),
   R_β(s) = ∫₁^∞(log v)v^{s−1}cos(βv)dv = −Σ_{m=2..k}(−1)^{m−1}Q_{m−1}(s)β^{−m}sin(β−(m−1)π/2) + E_k,
   |E_k| ≤ β^{−k}[|P_k|/(k−½)² + |Q_k|/(k−½)],  P_m = Π_{i<m}(s−1−i), Q_{m+1} = (s−1−m)Q_m + P_m, Q₀ = 0.
   Derivation: ∫₀^∞v^{s−1}cos(βv)dv = β^{−s}Γ(s)cos(πs/2) for 0 < Re s < 1; subtract ∫₁^∞;
   differentiate in s; k-fold integration by parts of ∫₁^∞ with g(v) = (log v)v^{s−1}, g(1) = 0,
   g^{(m)}(v) = v^{s−1−m}(P_m log v + Q_m), ∫₁^∞v^{−½−k}dv = 1/(k−½), ∫₁^∞v^{−½−k}log v = 1/(k−½)².
   E_k enters the returned ball; the branch is taken only when E_k ≤ 1e−28. Agreement verified (§6 V2).

**(d) Euler-sum truncation.** |t₂ − t₂^{[J₀]}| ≤ ε_{J₀}, v1 (32) with the **proved uniform**
constant C = 256 of v1 Theorem 4 (31). Since |γ₂| = 1 and ∫W = 2π, the floor cost is 4πε_{J₀}
(v1 (33)). At J₀ = 90 this is 9.47e−10 — the v2 (14) alternative is not needed at this J₀.

**(e) Compact-frequency quadrature.** Composite **Clenshaw–Curtis**, panel width 0.5 on [0,2000]
(4000 panels), degree n = 32 (33 nodes/panel), doubled by evenness of W_hℓ₂. CC nodes cos(kπ/n)
and the closed-form CC weights are computed exactly in arb (checked: Σw = 2, ∫x², ∫x⁴ exact).
Rigorous error: I_n(f) = ∫p_n with p_n the degree-n interpolant, so |I − I_n| ≤ 2‖f−p_n‖_∞ ≤
**8Mρ^{−n}/(ρ−1)** for f analytic in the Bernstein ellipse E_ρ with |f| ≤ M there
(Trefethen, *ATAP* Thm 8.2). With ρ = 3, the ellipse for a panel lies in the disc of radius
(w/4)(ρ+1/ρ) = 0.4167 with |Im ξ| ≤ (w/4)(ρ−1/ρ) = 0.3333.
*Analyticity, verified piece by piece:* ĥ, 1−cos aξ entire; J(β,−ξ) analytic for Im ξ > −½ and
J(β,ξ) for Im ξ < ½; γ₂(ξ) has its nearest singularities (pole of Γ(¼+iξ/2), zero of b(ξ)) exactly
at Im ξ = +½ and γ₂(−ξ) at Im ξ = −½. So f is analytic on the strip |Im ξ| < ½ ⊃ every ellipse used.
*M per panel, rigorously enclosed:* |1−cos aξ|·(‖h‖₁e^{δR})²/H·2·max(|γ₂(±ξ)|)·T_b with
‖h‖₁ ≤ √(2δH) = 174.892 (Cauchy–Schwarz), |ĥ(ξ)| ≤ ‖h‖₁e^{δ|Im ξ|}, T_b = (J₀+2)/(½−R)²/2π from
the elementary |J(β,·)| ≤ ∫₀¹(−log v)v^{−½+|Im ξ|}dv = (½−R)^{−2}, and |γ₂| bounded through the
**entire** reciprocal gamma (acb `lgamma`/`gamma` return nan on wide balls near the origin; the
shifted-argument form Γ(z) = Γ(z+3)/(z(z+1)(z+2)) is used as a fallback). Σ_panels M = 1.6185e10.

**(f) Frequency tail.** Two proved ingredients, both stronger than the ones offered in the verdicts.
1. *Uniform scalar bound.* |t₂(ξ)| ≤ T := (1/2π)[4 + Σ_{j≥0} min(4, 256β_j^{−1/2}(1+log β_j))]
   = **13.9371046604** for every real ξ, hence |ℓ₂| ≤ 2T = 27.874. The `4` is elementary
   (∫₀¹(−log v)v^{−1/2}dv = 4); the second entry is v1 Theorem 4 (31). This is 21× smaller than
   the verdict's T_* of (34) = 299.6, which is what makes X = 2000 rather than X ≈ 14000 affordable.
2. *Transform tail.* Since h₄, h₄′ are continuous and vanish at ±δ, h₄″ is even and h₄‴ is odd,
   two/three integrations by parts give
   |ĥ₄(ξ)| ≤ B₃/|ξ|³ + B₄/ξ⁴, B₃ = 2|h₄″(δ)| = 1.16387735517e8,
   B₄ = 2|h₄‴(δ)| + ‖h₄⁗‖_{L¹(−δ,δ)} = 8.03769798335e10, whence
   μ_X = ∫_{|ξ|>X}W_h ≤ (4/H)[B₃²/(5X⁵) + 2B₃B₄/(6X⁶) + B₄²/(7X⁷)] = **1.8638e−6** at X = 2000.
   (v1 (37) with s = 2 gives only ξ^{−4} decay and would have required X ≈ 1.4e4.)
   Floor cost 2Tμ_X ≤ 5.195e−5.

## 4. Ledger

| term | bound (arb string) | how proved |
|---|---|---|
| compact −∫_{\|ξ\|≤2000} W ℓ₂^{[90]} | `[0.0035087828600720 +/- 3.49e-17]` | composite CC, all inputs ball-enclosed; 132 000 node evaluations |
| E_quadrature | ≤ `1.746903620e-5` | Bernstein-ellipse bound, ρ=3, n=32, ΣM = 1.6185e10 |
| E_scalar (γ₂, J, ĥ, H evaluation) | absorbed | ball arithmetic on every operation — v1 (36) needs no separate line |
| 4π ε_{J₀}, J₀ = 90 | ≤ `9.472692064e-10` | v1 (32)–(33) with C = 256 of v1 Thm 4 (31) |
| 2T μ_X, X = 2000 | ≤ `5.195057632e-5` | §3(f); T = `13.93710466`, μ_X = `1.8637507e-6` |
| **L_F** | `0.0034393623002774739205` | (38) |
| **U_F** | `0.0035782034198665259817` | (38) |

No double counting: the Euler tail beyond J₀ appears only in the 4πε_{J₀} row (the quadrature
integrand is ℓ₂^{[J₀]}, not ℓ₂); the frequency tail appears only in the 2Tμ_X row.

## 5. STEP 0 (diagnostic) reproduction

The same arb chain on |ξ| ≤ 600 gives **0.0035087763099604**, against the shelf's diagnostic
`floor +0.003509` for h₄ (`mellin_d2/PROGRESS.md`, 02:40 entry). The band [600, 2000] adds
6.6e−9 — consistent with W_{h₄} ~ ξ^{−6}. DIAGNOSTIC_NEVER_A_PROOF.

## 6. Independent checks (different channels, per the owner's verification axiom)

* **V1 — mass.** ∫_{|ξ|≤2000}W_{h₄}dξ = `6.2831850208109340049`; 2π = `6.2831853071795864769`;
  deficit `2.8637e-7`, which must and does lie in [0, μ_X = 1.8638e−6]. This exercises ĥ₄, H₄,
  the CC rule and the transform-tail bound simultaneously, through an integrand that contains no J at all.
* **V2 — two J representations.** Series vs large-β expansion at ξ ∈ {0, 50, 250, 900, 1999} and
  β = 2π2^{9..12}: **20/20 balls overlap**; E_asym between 5.6e−37 and 0.
* **V3 — foreign evaluator.** ℓ₂ from this arb chain vs `mellin_d2/dens.py` + `core.py::J_closed`
  (mpmath incomplete gamma + `mp.diff`, scipy `loggamma` for γ₂ — a wholly different code path,
  and truncated at J_U = 55): agreement 3e−9 … 3.5e−8 at ξ ∈ {1, 17.5, 60, 123.25, 400, 600},
  consistent with that evaluator's own ε₅₅ ≈ 9e−6 headroom.
* **V4 — moments.** |∫h₄e^{±x/2}dx| ≤ 6.0e−116 in arb (and 0 as an algebraic identity, §1).
* **CC rule.** Σw = 2, ∫x² = 2/3, ∫x⁴ = 2/5 exactly for n = 8, 20, 32.
* **V5 — second quadrature**, entirely different node set (w = 0.4, n = 24, ρ = 2.8, 5000 panels,
  125 000 nodes, 1011 s): compact value `[0.0035087828600720 +/- 3.56e-17]` — **identical to the
  main run in every printed digit**. Its own certified E_quad is 1.9e−2 (degree 24 is too low to
  certify), so it enters the report only as a value cross-check, not into L_F.

## 7. What remains unproved — CONDITIONALs

The interval is a certificate for the scalar 𝓕(h₄) **given** the following, none of which this
report proves:

1. **RESONANCE Lemma 2 (6)** — that ℓ_S = 2Re(γ_S t_S) is the leading part of the true continuous
   angle density d_S, and in particular the analytic domain of that source identity and the
   trace-class justification of its generalized-wave calculation. This is the load-bearing
   dependency: the certificate certifies a *number attached to that identity*.
2. **SCALARFLOOR Theorem 1 (5)–(6)** — 𝔪(h) = 𝓕(h) + ‖T_{v_h}D₂‖²_{HS} ≥ 𝓕(h). Without it, L_F > 0
   says nothing about 𝔪(h₄).
3. **SCALARFLOOR Theorem 4 (31)**, |J(β,ξ)| ≤ 256β^{−1/2}(1+log β) for β ≥ 1, uniformly in real ξ.
   Used twice (Euler tail ε_{J₀}, uniform T). Its proof is in v1 §7.1 and was **not** independently
   re-derived here. If (31) fails, both tail rows must be replaced; the compact row is unaffected.
4. **Trefethen ATAP Thm 8.2** (Bernstein/Chebyshev interpolation bound) for E_quadrature.
5. RESONANCE (2) for γ₂ and (10) for t₂ as the correct source objects at cutoff λ = 1.

Not certified by this document: plant survival, the frozen PHASEPROOF eta event, 𝓕 ≥ 0 on the
phase class, the near-unit-angle count, anything about the operator part of d₂ (the certificate is
inverse-free by construction — no A₂ diagonalization, no dropped mode, no fitted constant).

## 8. Runtime, files, reproduction

Main run: 4000 panels × 33 nodes = 132 000 rigorous node evaluations, 22 processes,
**1081.8 s wall** (≈ 6.6 core-hours), `systemd-run --user --unit=h4cert_main`.
Budget/verification scripts: seconds to ~10 min each.

Scripts (repo, none of the surrounding tree touched, nothing committed):
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/h4_cert/`
— `h4arb.py` (profile, ĥ, γ₂, J series + large-β, |γ₂| ellipse bound), `evalf.py` (node
integrand, J₀, method switch), `cert.py` (CC rule, panels, E_quad), `budget.py` (ε_J, T,
B₃/B₄, μ_X), `assemble.py` ((38)), `verify.py` (V1–V4), `sanity.py` (float STEP 0).
Reproduce: `budget.py`; `cert.py 2000 0.5 32 3.0 22 out.txt`; `assemble.py out.txt 2000 90`;
`verify.py all` (with `.venv/bin/python`).
Logs and raw outputs: `/home/chirurgie/.claude/jobs/4b35770d/tmp/h4_cert/` (`main.txt`,
`main.log`, `xcheck.txt`).

## 9. Honest gaps in *this* work

* The certificate rests on (31) as an imported theorem (§7.3). A self-contained ξ-uniform
  β-decay bound for J was not derived here; v2 (13) is ξ-dependent and diverges as |ξ| grows,
  so it cannot replace (31) in the frequency-tail row.
* The M-bound feeding E_quadrature is deliberately crude (ΣM = 1.6e10 against actual |f| ≲ 1e−3).
  It costs nothing because ρ^{−32} = 5.4e−16, but it is not a sharp statement about the integrand.
* `E_quadrature` = 1.75e−5 and `2Tμ_X` = 5.20e−5 dominate the error. Both shrink cheaply
  (n = 40, or X = 3000 → 5.9e−6) if a tighter interval is ever wanted; 1/500 is met with
  a factor-1.7 margin as it stands.
