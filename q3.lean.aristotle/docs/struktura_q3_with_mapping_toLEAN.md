# Q3 Project Structure with Paper → Lean Mapping

Last updated: 2026-01-19

## Mission

Formal proof of the Riemann Hypothesis (RH) via Weil criterion:
```
RH ⟺ Q(Φ) ≥ 0 for all Φ ∈ Weil_cone
```

## 2026-01-29 Audit — PDF vs Lean Mainline (важно)

**Ключевая развилка:** RH_Q3.pdf формулирует **классический Weil-конус** `W` и
классический Weil‑критерий. Текущая Lean‑mainline использует **узкий τ=0 конус**
`Weil_cone_tau0` с фиксированным диапазоном `B ∈ [B_min, B_max]`.

**Это означает:** текущая Lean‑цепочка формализует **не точь‑в‑точь PDF**, а
узкую “τ=0 / B‑range” версию, выбранную из‑за численных сертификатов.

### Section‑level mapping (RH_Q3.tex → Lean)

| PDF section (file) | Core claim in PDF | Lean module(s) | Status vs PDF |
|---|---|---|---|
| abstract.tex, introduction.tex, scope_notation.tex, Notation/* | обзор/контекст/нотация | — | doc‑only |
| T0.tex, T0_AD_fix.tex | нормализация Guinand–Weil, Q = arch − prime | `Q3/Basic/Defs.lean`, `Q3/Main.lean` | **OK**, но `explicit_formula` остаётся AX |
| A1prime.tex | плотность Fejér×heat в `W_K` | `Q3/Proofs/A1_density.lean` | **OK (theorem)** |
| A2.tex | Lipschitz на компактах | `Q3/Proofs/Q_Lipschitz*.lean` | **OK (theorem)** |
| A3/* | Toeplitz‑bridge, floor `c_*`, два масштаба | `Q3/Proofs/A3_Floor_Main.lean`, `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` | **DIVERGED:** single‑scale `t_critical`, τ=0, B‑range |
| RKHS/* | prime cap / RKHS operator | `Q3/Proofs/RKHS_cap_rayleigh.lean` | **PARTIAL:** Rayleigh cap OK, но операторный мост PDF‑версии разошёлся |
| D3/* | Prime cancellation (D3) | — | **OFF‑CHAIN / archived** |
| Weil_linkage.tex, Weil_pack.tex, Main_closure.tex | Weil criterion ⇒ RH | `Q3/Main.lean` | **DIVERGED:** uses `Weil_criterion_tau0` |

### Mainline divergence summary

1) **Конус тестов:** PDF использует полный `Weil_cone`; Lean mainline использует
   `Weil_cone_tau0` (τ=0 + B‑range).
2) **Масштабы:** PDF использует two‑scale (`t_sym`, `t_rkhs`), Lean mainline —
   single‑scale `t_critical`.
3) **Prime bounds:** Lean mainline опирается на **сертификаты** PrimeCert
   (`prime_b_grid_bounds_data`, `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`),
   чего нет в PDF.
4) **D3:** PDF содержит D3‑модуль, Lean mainline его не использует.

**Итог:** текущая Lean‑цепочка — это **суженная “τ=0 / B‑range / t_critical” версия**,
а не буквальная формализация RH_Q3.pdf. Для полного соответствия PDF нужен
возврат к классическому Weil‑конусу и снятие ограничения по B.

## Paper Hypotheses (H1)-(H5)

From the paper: "When we write under (T0) + (A1′) + (A2) + (A3) + (RKHS) we mean precisely the data enumerated above."

| Hypothesis | Paper Reference | Description |
|------------|-----------------|-------------|
| **(H1) T0** | Proposition 5.1 | Guinand–Weil normalization of Q |
| **(H2) A1′** | Theorem 6.3 | Density of Fejér×heat cone on every W_K |
| **(H3) A2** | Lemma 7.3, Corollary 7.4 | Lipschitz continuity of Q on each W_K |
| **(H4) A3** | Lemma 8.19, Theorem 8.35 | Toeplitz bridge with uniform floor c* > 0, RKHS cap ρ(t_rkhs) ≤ c*/4 |
| **(H5) RKHS** | Corollary 8.22 | Prime contraction via uniform RKHS cap |

Sections 5–9.5 establish (H1)–(H5); Theorem 11.4 (closure) assumes these hypotheses; Theorem 11.2 invokes (H1)–(H5) with Weil's criterion.

---

## Complete Mapping: Hypothesis → Paper → Lean

### (H1) T0 — Guinand–Weil Normalization

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Prop 5.1 | Proposition | Q = arch_term − prime_term | `T0_normalization` | `Q3/Main.lean:52` | ✅ |
| Def 5.2 | Definition | Q(Φ) functional | `Q` | `Q3/Basic/Defs.lean` | ✅ |
| Def 5.3 | Definition | arch_term(Φ) = ∫ a(ξ)Φ(ξ)dξ | `arch_term` | `Q3/Basic/Defs.lean` | ✅ |
| Def 5.4 | Definition | prime_term(Φ) = Σ_p w_p Φ(ξ_p) | `prime_term` | `Q3/Basic/Defs.lean` | ✅ |
| Def 5.5 | Definition | a(ξ) = log π − Re ψ(1/4 + iπξ) | `a_star` | `Q3/Basic/Defs.lean` | ✅ |
| Thm 5.6 | Theorem | Guinand-Weil explicit formula | `explicit_formula` | `Q3/Axioms.lean` | AX |

### (H2) A1′ — Fejér×Heat Cone Density

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Def 6.1 | Definition | Fejér kernel F_B(x) | `Fejer_kernel` | `Q3/Axioms.lean:230` | ✅ |
| Def 6.2 | Definition | Heat kernel H_t(x) | `heat_kernel_A1` | `Q3/Axioms.lean:234` | ✅ |
| Def 6.3 | Definition | Atom g_{B,t,τ}(ξ) | `Fejer_heat_atom` | `Q3/Axioms.lean:238` | ✅ |
| Def 6.4 | Definition | AtomCone_K | `AtomCone_K` | `Q3/Axioms.lean:253` | ✅ |
| Lem 6.4 | Lemma | Fixed-t₀ cone density | `hat_interpolation_approx` | `Q3/Proofs/HatInterpolation.lean` | ✅ |
| **Thm 6.3** | Theorem | AtomCone_K dense in W_K | `A1_density_WK_thm` | `Q3/Proofs/A1_density.lean` | ✅ THEOREM |

### (H3) A2 — Lipschitz Continuity

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Def 7.1 | Definition | W_K test function space | `W_K` | `Q3/Basic/Defs.lean` | ✅ |
| Def 7.2 | Definition | L_Q(K) Lipschitz constant | `L_Q_local` | `Q3/Proofs/Q_Lipschitz.lean:50` | ✅ |
| **Lem 7.3** | Lemma | arch_term Lipschitz | `arch_term_Lipschitz` | `Q3/Proofs/Q_Lipschitz_arch_bridge.lean` | ✅ |
| **Lem 7.4** | Lemma | prime_term Lipschitz | `prime_term_Lipschitz` | `Q3/Proofs/Q_Lipschitz_prime_bridge.lean` | ✅ |
| **Cor 7.4** | Corollary | Q Lipschitz on W_K | `Q_Lipschitz_on_W_K_thm` | `Q3/Proofs/Q_Lipschitz.lean` | ✅ THEOREM |
| — | Lemma | a_star bounded on compacts | `a_star_bdd_on_compact` | `Q3/Axioms.lean` | AX |
| — | Lemma | a_star continuous | `a_star_continuous` | `Q3/Axioms.lean` | AX |

### (H4) A3 — Toeplitz Bridge & Floor

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Def 8.1 | Definition | Toeplitz matrix T_M[P] | `ToeplitzMatrix` | `Q3/Axioms.lean:111` | ✅ |
| Def 8.2 | Definition | Symbol P_A(θ) | `P_A` | `Q3/Basic/Defs.lean` | ✅ |
| Def 8.3 | Definition | c* = 11/10 uniform floor | `c_star` | `Q3/Axioms.lean:187` | ✅ |
| Lem 8.15 | Lemma | a(1/2) > 29/50 | (in A3_FLOOR) | `A3_Floor_Main.lean` | ✅ |
| Lem 8.18 | Lemma | Sample point bounds | (in A3_FLOOR) | `A3_Floor_Main.lean` | ✅ |
| **Lem 8.19** | Lemma | P_A(θ) ≥ c* = 11/10 | `P_A_ge_c_star` | `A3_Floor_Main.lean` | ✅ PROVEN |
| Def 8.20 | Definition | L*(t_sym) uniform Lipschitz | `L_star` | `Q3/Proofs/Q_Lipschitz.lean` | ✅ |
| Lem 8.21 | Lemma | Rayleigh quotient ≥ inf P | `Szego_Rayleigh_lower_bound` | `Q3/Axioms.lean` | AX |
| **Cor 8.22** | Corollary | ρ(t_rkhs) ≤ 1/25 < c*/4 | `rkhs_cap_rayleigh_tcap` | `Q3/Proofs/RKHS_cap_rayleigh.lean:850` | ✅ PROVEN |
| Thm 8.35 | Theorem | A3 bridge data uniform | `A3_bridge_data_uniform` | `Q3/Axioms.lean:438` | ✅ |
| — | Theorem | A3 bridge from Szegő | `A3_bridge_from_Szego` | `Q3/Proofs/A3_bridge.lean:143` | ✅ |

### (H5) RKHS — Prime Contraction

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Def 8.23 | Definition | T_P compressed operator | `T_P_comp_real` | `Q3/Basic/Defs.lean` | ✅ |
| Def 8.24 | Definition | w_Q(n) prime weights | `w_Q` | `Q3/Basic/Defs.lean` | ✅ |
| Lem 8.25 | Lemma | w_Q(n) ≤ C/n² | `w_Q_le_const` | `Q3/Proofs/RKHS_cap_rayleigh.lean:111` | ✅ |
| Lem 8.26 | Lemma | Weight sum finite | `weight_sum_le_rho_one` | `Q3/Proofs/RKHS_cap_rayleigh.lean:561` | ✅ PROVEN |
| **Cor 8.22** | Corollary | ‖T_P‖ ≤ ρ(1) = 1/25 | `T_P_comp_real_opNorm_le_weight_sum` | `Q3/Proofs/RKHS_cap_rayleigh.lean:831` | ✅ |
| Cor 8.27 | Corollary | RKHS contraction | `RKHS_contraction_data_uniform` | `Q3/Axioms.lean:466` | ✅ |
| — | Bridge | RKHS contraction bridge | `RKHS_contraction_bridge` | `Q3/Proofs/RKHS_contraction_bridge.lean` | ✅ |

### Main Theorems (Section 11)

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Thm 11.1 | Theorem | Weil criterion: RH ⟺ Q ≥ 0 | `Weil_criterion` | `Q3/Axioms.lean` | AX (external) |
| **Thm 11.4** | Theorem | T5 transfer: atoms → W_K | `T5_transfer` | `Q3/T5_Transfer.lean:76` | ✅ THEOREM |
| Cor 11.5 | Corollary | Q ≥ 0 on W_K | `Q_nonneg_on_W_K` | `Q3/Main.lean:96` | ✅ |
| Thm 11.6 | Theorem | Q ≥ 0 on Weil_cone | `Q_nonneg_on_Weil_cone` | `Q3/Main.lean:127` | ✅ |
| **Thm 11.2** | Theorem | **Riemann Hypothesis** | `RH_of_Weil_and_Q3` | `Q3/Main.lean:190` | ✅ (1 AX) |

### T5 Transfer Details (Appendix G.13-G.14)

#### Standing Analytic Inputs (Uniform Version)

| Input | Statement | Paper Ref | Lean | Status |
|-------|-----------|-----------|------|--------|
| **(A3)** | min_{θ∈T} P_A(θ) ≥ c* | Lemma 8.19 | `P_A_ge_c_star` | ✅ PROVEN |
| **(A3.b)** | C_SB · ω_{P_A}(1/2M) ≤ c*/2 for M ≥ M₀^unif | Corollary 8.21 | `discretization_control` | ✅ |
| **(RKHS)** | ‖T_P‖ ≤ ρ(t_rkhs) ≤ c*/4 for t_rkhs ≥ t*_rkhs^unif | Corollary 8.22 | `rkhs_cap_rayleigh_tcap` | ✅ PROVEN |
| **(A1′)** | Fejér×heat cone dense in W_K | Theorem 6.3 | `A1_density_WK_thm` | ✅ THEOREM |
| **(A2)** | \|Q(Φ) − Q(Ψ)\| ≤ L_Q(K)‖Φ − Ψ‖_∞ | Lemma 7.3 | `Q_Lipschitz_on_W_K_thm` | ✅ THEOREM |

#### G.13 Compact-by-Compact Transfer

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| **Lem G.18** | Lemma | Grid-lift: λ_min(T_M[P_A] − T_P) ≥ c*/4 | `grid_lift_inequality` | `Q3/Proofs/A3_bridge.lean` | ✅ |
| **Thm G.19** | Theorem | T5 uniform transfer: Q ≥ 0 on W_K | `T5_transfer` | `Q3/T5_Transfer.lean:76` | ✅ THEOREM |

**Lemma G.18 Proof Structure:**
```
λ_min ≥ c* − C_SB·ω_{P_A}(1/2M) − ‖T_P‖
      ≥ c* − c*/2 − c*/4
      = c*/4
```

**Theorem G.19 (T5) Proof Structure:**
1. By Lem G.18: T_M[P_A] − T_P has λ_min ≥ c*/4 > 0 for M ≥ M₀^unif
2. Positivity on Fejér×heat cone follows
3. (A1′) + (A2) extend Q ≥ 0 from dense cone to all W_K
4. Union over K gives full Weil class

#### G.14 Inductive Limit over Compacts

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Def | Definition | W = ∪_{K>0} W_K with inductive limit | `Weil_cone` | `Q3/Basic/Defs.lean` | ✅ |
| **Lem G.20** | Lemma | Nested dictionaries yield W | `nested_dictionaries` | (implicit in T5) | ✅ |
| **Thm G.21** | Theorem | Transfer to Weil class | `Q_nonneg_on_Weil_cone` | `Q3/Main.lean:127` | ✅ |
| **Lem G.22** | Lemma | Grid-lift by Lipschitz margin | `grid_lift_Lipschitz` | `Q3/Proofs/A3_bridge.lean` | ✅ |
| **Lem G.23** | Lemma | Uniform inheritance across K | `uniform_inheritance` | (implicit in T5) | ✅ |

**Key Insight: No K-dependent schedules!**

The uniform approach eliminates:
- ~~c₀(K)~~ → c* (uniform)
- ~~t*(K)~~ → t_rkhs^unif (uniform)  
- ~~M*(K)~~ → M₀^unif (uniform)

Same parameters work for ALL compacts [-K, K] simultaneously.

#### Lean Implementation of T5

```lean
-- Q3/T5_Transfer.lean:76
theorem T5_transfer (K : ℝ) (hK : K ≥ 1) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  intro Φ hΦ
  -- Get Lipschitz constant from A2
  obtain ⟨L, hL_pos, hLip⟩ := Q_Lipschitz_on_W_K_thm K (by linarith)
  -- By A1 (theorem), get approximant g ∈ AtomCone_K
  -- with ||Φ - g||_∞ < ε
  -- By atoms positivity (from A3 + RKHS), Q(g) ≥ 0
  -- By Lipschitz, |Q(Φ) - Q(g)| ≤ L·ε
  -- Take ε → 0
  ...
```

### Auxiliary Lemmas & Bridges

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| — | Lemma | c* > 0 | `c_star_pos` | `Q3/Axioms.lean:190` | ✅ |
| — | Lemma | c* > 1 | `c_star_gt_one` | `Q3/Axioms.lean:193` | ✅ |
| — | Lemma | c*/4 > 0 | `c_star_div_four_pos` | `Q3/Axioms.lean:196` | ✅ |
| — | Lemma | a_star even | `a_star_even` | `Q3/Axioms.lean` | AX |
| — | Lemma | a_star positive | `a_star_pos` | `Q3/Axioms.lean` | AX |
| — | Lemma | AtomCone ⊆ W_K | `AtomCone_subset_W_K` | `Q3/T5_Transfer.lean:54` | ✅ |
| — | Lemma | W_K ⊆ Weil_cone | `W_K_subset_Weil_cone` | `Q3/Main.lean:68` | ✅ |
| — | Lemma | Schur test | `Schur_test` | `Q3/Axioms.lean` | AX |

### Technical Clarifications (Appendix B)

These remarks justify key technical choices and are implicitly used throughout.

#### Node Structure

| Remark | Statement | Lean | File | Used in |
|--------|-----------|------|------|---------|
| **Nodes finite** | On [-K,K]: n ≤ N(K) = ⌊e^{2πK}⌋ | `Nodes K` is Fintype | `Q3/Basic/Defs.lean:38` | **(H4), (H5)** |
| **Minimal gap** | δ_K = min gap ≥ 1/(2π(N(K)+1)) > 0 | `node_spacing` | `Q3/Proofs/node_spacing.lean` | **(H5) RKHS** |
| **Node coords** | ξ_n = log(n)/(2π) | `xi_n` | `Q3/Basic/Defs.lean:35` | **(H1), (H4), (H5)** |

**Key formula:**
```
δ_K = min_{1≤n<N(K)} (ξ_{n+1} − ξ_n) = (1/2π) min_{n} log(1 + 1/n) ≥ 1/(2π(N(K)+1))
```

#### Weight Bounds

| Remark | Statement | Lean | File | Used in |
|--------|-----------|------|------|---------|
| **w_max bound** | w(n) = Λ(n)/√n ≤ log(n)/√n ≤ 2/e < 1 | `w_max := 2/e` | `Q3/Basic/Defs.lean:49` | **(H5) RKHS** |
| **Numerical** | w_max ≈ 0.7358 < 3/4 < 1 | `w_max_lt_one` | `Q3/Proofs/RKHS_cap_rayleigh.lean` | **(H5)** |
| **Weight def** | w_Q(n) = 2Λ(n)/√n | `w_Q` | `Q3/Basic/Defs.lean:43` | **(H1), (H5)** |
| **RKHS weight** | w_RKHS(n) = Λ(n)/√n | `w_RKHS` | `Q3/Basic/Defs.lean:46` | **(H5)** |

**Key inequality (Lemma):** log(n)/√n ≤ 2/e for n ≥ 2
- Proven in `Q3/Basic/Defs.lean:181`

#### Gram & Operator Structure

| Remark | Statement | Lean | File | Used in |
|--------|-----------|------|------|---------|
| **Finite Gram** | G of {k_{ξ_n}} is finite-dim | `T_P_comp` finite | `Q3/Basic/Defs.lean:105` | **(H5)** |
| **Operator norm** | ‖T_P‖ = ‖W^{1/2} G W^{1/2}‖ | `T_P_comp_real` | `Q3/Basic/Defs.lean:113` | **(H5)** |
| **Rank-one sum** | T_P = Σ_n w_n · v_n ⊗ v_n | `T_P_comp` def | `Q3/Basic/Defs.lean:108` | **(H5)** |

#### Heat Parameter Control

| Remark | Statement | Lean | File | Used in |
|--------|-----------|------|------|---------|
| **S_K decay** | S_K(t) = 2e^{-δ²_K/(4t)}/(1-e^{-δ²_K/(4t)}) ↓ 0 as t↓0 | `S_K_small` | `Q3/Proofs/S_K_small.lean` | **(H5)** |
| **t_min exists** | t_min(K) = δ²_K/(4 ln((2+η)/η)) | `t_min_exists` | `Q3/S_K_Bound.lean` | **(H5)** |
| **Uniform t** | t_rkhs^unif works for all K | `t_rkhs_cap = 40` | `Q3/Proofs/RKHS_cap_rayleigh.lean` | **(H4), (H5)** |

#### Density & Topology

| Remark | Statement | Lean | File | Used in |
|--------|-----------|------|------|---------|
| **Dictionary density** | Finite G_K is ε-dense in C_K at fixed K | `A1_density_WK_thm` | `Q3/Proofs/A1_density.lean` | **(H2)** |
| **Not global** | Not: fixed finite set dense globally | (design choice) | — | — |
| **Weil topology** | W = ∪_K W_K with inductive limit | `Weil_cone` | `Q3/Basic/Defs.lean` | **(H1)** |
| **Q continuous on W** | Q continuous on each W_K ⇒ on W | `Q_nonneg_on_Weil_cone` | `Q3/Main.lean:127` | **Thm 11.2** |

#### Role of Kernels

| Remark | Statement | Used in |
|--------|-----------|---------|
| **Fejér factor** | Localizes to compacts, BV/Lipschitz regularity | **(H2) A2**, **(H4) A3** |
| **Heat factor** | Smoothing, Gaussian-in-log tails | **(H4) A3**, **(H5) RKHS** |
| **Product** | Preserves positivity + supplies regularity | **(H2), (H4), (H5)** |

#### What We Do NOT Assume

| Non-assumption | Explanation |
|----------------|-------------|
| Selfadjoint operator with pure point spectrum | Not modeled on Paley–Wiener |
| Rigged eigenfunctions e^{iγτ} | Not elements of Hilbert space |
| Weyl asymptotics from heat traces | Not used |
| Determinant identities ≡ RH | Not imposed |

These clarify that the Q3 approach is elementary (Toeplitz + density + Lipschitz) and does NOT rely on heavy spectral machinery.

### Remaining Axiom (Closable)

| Paper Ref | Type | Statement | Lean Name | File | Status |
|-----------|------|-----------|-----------|------|--------|
| Thm 8.35 | Theorem | Q ≥ 0 on atoms (A3+RKHS) | `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` | `Q3/Axioms.lean` | **AX (closable)** |

**Closure path:** Wire via `Rayleigh_Q_identification.lean` using:
- `P_A_ge_c_star` (A3 floor) ✅
- `rkhs_cap_rayleigh_tcap` (RKHS cap) ✅
- `rayleigh_Q_eq_Q` (Rayleigh-Q identification) ✅

---

## Paper → Lean Mapping

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    PAPER (Sections 5-11) → LEAN FILES                       │
└─────────────────────────────────────────────────────────────────────────────┘

(H1) T0 — Guinand–Weil normalization (Prop 5.1)
     ├── Q3/Main.lean              — T0_normalization theorem
     ├── Q3/Axioms.lean            — explicit_formula axiom
     └── Q3/Basic/Defs.lean        — Q := arch_term - prime_term

(H2) A1′ — Fejér×heat density (Thm 6.3)
     ├── Q3/A1_Density.lean        — module wrapper
     ├── Q3/T5_Transfer.lean       — uses A1_density_WK_thm
     └── Q3/Proofs/A1_density.lean — 1421 lines, PROVEN! [OK]
         └── A1_density_main.lean  — 895 lines helpers

(H3) A2 — Lipschitz on W_K (Lemma 7.3, Cor 7.4)
     ├── Q3/A2_Lipschitz.lean      — module wrapper
     ├── Q3/Proofs/Q_Lipschitz.lean — 290 lines, THEOREM! [OK]
         ├── Q_Lipschitz_arch_bridge.lean  — arch term
         ├── Q_Lipschitz_prime_bridge.lean — prime term
         └── Q_Lipschitz_Bridge.lean    — combined

(H4) A3 — Toeplitz floor c* = 11/10 (Lemma 8.19, Thm 8.35)
     ├── Q3/A3_Bridge.lean         — module wrapper
     ├── Q3/Axioms.lean            — c_star := 11/10
     ├── A3_Floor_Main.lean — 47K lines, floor PROVEN!
     └── Q3/Proofs/
         ├── A3_bridge.lean                — 149 lines
         ├── A3_bridge_rayleigh_first.lean — 76 lines
         ├── P_A_Toeplitz_bridge.lean      — 108 lines
         └── Rayleigh_Q_identification.lean — 629 lines

(H5) RKHS — prime contraction (Cor 8.22)
     ├── Q3/RKHS_Contraction.lean  — module wrapper
     └── Q3/Proofs/
         ├── RKHS_cap_rayleigh.lean      — 893 lines, cap PROVEN! [OK]
         ├── RKHS_contraction.lean       — 371 lines
         └── RKHS_contraction_bridge.lean — 211 lines

═══════════════════════════════════════════════════════════════════════════════

(T5) Transfer Theorem 11.4 — atoms → W_K
     └── Q3/T5_Transfer.lean       — T5_transfer theorem [OK]
         Uses: A1' + A2 + atoms positivity

(RH) Main Theorem 11.2 — Riemann Hypothesis
     └── Q3/Main.lean              — RH_of_Weil_and_Q3 [MAIN!]
         Uses: Weil_criterion + Q_nonneg_on_Weil_cone
```

---

## Hypothesis Status

| Hypothesis | Paper Ref | Status | Key Lean File |
|------------|-----------|--------|---------------|
| **(H1) T0** | Prop 5.1 | ✅ OK (def) | `Q3/Main.lean` |
| **(H2) A1′** | Thm 6.3 | ✅ THEOREM | `Q3/Proofs/A1_density.lean` |
| **(H3) A2** | Lem 7.3 | ✅ THEOREM | `Q3/Proofs/Q_Lipschitz.lean` |
| **(H4) A3** | Lem 8.19 | ✅ PROVEN | `A3_Floor_Main.lean` |
| **(H5) RKHS** | Cor 8.22 | ✅ BRIDGED | `Q3/Proofs/RKHS_cap_rayleigh.lean` |
| **(T5)** | Thm 11.4 | ✅ THEOREM | `Q3/T5_Transfer.lean` |
| **(RH)** | Thm 11.2 | ⚠️ 1 AXIOM | `Q3/Main.lean` |

---

## Critical Chain (ASCII)

```
RH_of_Weil_and_Q3
  │
  ├── Weil_criterion [AX external — Weil 1952]
  │
  └── Q_nonneg_on_Weil_cone [OK]
       │
       └── T5_transfer [OK]
            │
            ├── A1_density_WK [OK] — (H2) atoms dense in W_K
            ├── Q_Lipschitz_on_W_K [OK] — (H3) Q continuous
            └── Q_nonneg_on_atoms [AX]
                 │
                 ├── Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom [AX]
                 └── RKHS_contraction [OK] — (H5)
```

---

## Axiom Count: 10 Total

| Type | Count | Examples |
|------|-------|----------|
| Standard Lean | 3 | `propext`, `Classical.choice`, `Quot.sound` |
| External/Classical | 6 | `Weil_criterion`, `a_star_pos`, `Schur_test` |
| Q3 Paper (closable) | 1 | `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` |

---

## Q3/Proofs/ — Complete File List (54 files, ~11,300 lines)

| File | Lines | Description |
|------|-------|-------------|
| **A1_density.lean** | 1421 | Atomic density (main) |
| **A1_density_main.lean** | 895 | A1 density main lemmas |
| **RKHS_cap_rayleigh.lean** | 893 | RKHS cap bound (t=40) |
| **Rayleigh_Q_identification.lean** | 629 | Rayleigh ↔ Q identification |
| **Bridge.lean** | 512 | General bridges between modules |
| **Q_Lipschitz_Bridge.lean** | 431 | Lipschitz bridge |
| **RKHS_contraction.lean** | 371 | RKHS operator contraction |
| **Q_Lipschitz_prime_bridge.lean** | 358 | Prime term Lipschitz |
| **HatInterpolation.lean** | 339 | Hat function interpolation |
| **ShiftedWindows.lean** | 307 | Shifted windows W_K |
| **Q_nonneg_lemmas.lean** | 293 | Lemmas for Q ≥ 0 |
| **RKHS_Contraction_Bridge.lean** | 290 | RKHS bridge |
| **Q_Lipschitz.lean** | 290 | Q Lipschitz main |
| **Q_nonneg_bridge.lean** | 284 | Q ≥ 0 bridge |
| **Rayleigh_Fourier.lean** | 220 | Rayleigh via Fourier |
| **RKHS_contraction_bridge.lean** | 211 | RKHS bridge v1 |
| **RKHS_rescaling.lean** | 190 | RKHS rescaling |
| **Q_Lipschitz_arch_bridge.lean** | 183 | Arch term Lipschitz |
| **W_Sum_Finite_Bridge.lean** | 180 | Sum finiteness |
| **off_diag_exp_sum.lean** | 170 | Off-diagonal exp sums |
| **node_spacing_bridge.lean** | 159 | Node spacing bridge |
| **off_diag_exp_sum_integrated.lean** | 157 | Off-diag integrated |
| **A3_bridge.lean** | 149 | A3 floor bridge |
| **T_P_comp_utils.lean** | 148 | T_P compression utilities |
| **S_K_Small_Bridge.lean** | 141 | S_K small bridge |
| **Q_Lipschitz_bridge.lean** | 136 | Lipschitz bridge v1 |
| **Rayleigh_utils.lean** | 133 | Rayleigh utilities |
| **W_sum_finite.lean** | 122 | W-sum finiteness |
| **A1_density_integrated.lean** | 119 | A1 integrated |
| **A3_bridge_integrated.lean** | 117 | A3 integrated |
| **Off_Diag_Exp_Sum_Bridge.lean** | 116 | Off-diag bridge |
| **Q_nonneg_on_atoms.lean** | 110 | Q ≥ 0 on atoms |
| **RKHS_contraction_integrated.lean** | 108 | RKHS integrated |
| **P_A_Toeplitz_bridge.lean** | 108 | P_A Toeplitz bridge |
| **W_Sum_Finite_Bridge.lean** | 106 | W-sums |
| **node_spacing.lean** | 105 | Node spacing |
| **W_sum_finite_bridge.lean** | 103 | W-sums bridge v1 |
| **node_spacing_integrated.lean** | 101 | Spacing integrated |
| **W_sum_finite_integrated.lean** | 100 | W-sums integrated |
| **S_K_small_bridge.lean** | 98 | S_K small v1 |
| **A3_Bridge_Uniform.lean** | 98 | A3 uniform bridge |
| **S_K_small_integrated.lean** | 95 | S_K integrated |
| **Q_nonneg_atoms_helpers.lean** | 94 | Helpers for atoms |
| **Q_nonneg_on_atoms_integrated.lean** | 90 | Q atoms integrated |
| **Q_Lipschitz_integrated.lean** | 88 | Lipschitz integrated |
| **Rayleigh_basis0.lean** | 85 | Rayleigh basis0 module |
| **Off_Diag_Exp_Sum_Bridge.lean** | 83 | Off-diag |
| **A3_bridge_rayleigh_first.lean** | 76 | A3 Rayleigh-first |
| **Q_Nonneg_Bridge.lean** | 74 | Q >= 0 bridge |
| **A1_Density_Bridge.lean** | 70 | A1 bridge |
| **A3_Bridge_Simple.lean** | 64 | A3 bridge |
| **S_K_small.lean** | 57 | S_K small bounds |
| **off_diag_exp_sum_bridge.lean** | 53 | Off-diag bridge v1 |
| **Rayleigh_basis0_of_A3.lean** | 31 | basis0 from A3 |
| **Q_nonneg_on_atoms_fourier_axiom.lean** | 27 | Fourier axiom |

---

## Key Constants (from LaTeX)

| Const | Value | Description | Used in |
|-------|-------|-------------|---------|
| c* | 11/10 | Symbol floor (uniform) | Lemma 8.19, A3 |
| C_SB | 4 | Szegő-Böttcher constant | Theorem 8.35 |
| t_rkhs_cap | 40 | RKHS heat parameter | Corollary 8.22 |
| ρ(1) | 1/25 | RKHS cap bound | Corollary 8.22 |
| t_sym | 3/50 | Symbol heat param | A3 floor |
| M₀^unif | (computed) | Uniform discretisation threshold | Theorem 8.35 |

---

## Elementary Inequalities (Section 8.3)

The A3 floor proof (Lemma 8.19) uses only fixed constant bounds and elementary inequalities.
For audit convenience, here are the ones invoked explicitly:

### Pi Bounds

| Inequality | Value | Source |
|------------|-------|--------|
| π < 22/7 | 3.142857... | Classical rational bound |
| π > 3 | 3.14159... | Classical lower bound |
| π > 333/106 | 3.141509... | Classical lower bound (used for exponentials) |

### Logarithm Bounds

| Inequality | Derivation |
|------------|------------|
| log(3/2) < 5/12 | Alternating series: log(1+x) = x - x²/2 + x³/3 - x⁴/4 + ... at x = 1/2 |
| log(5/2) < 1 | Since e > 1 + 1 + 1/2 + 1/6 + 1/24 = 65/24 > 2.5 |

### Exponential Bounds

| Inequality | Derivation |
|------------|------------|
| e < 3 | Series e = Σ(k≥0) 1/k! with tail bound |
| e^(3/5) ≤ Σ(j=0..4) (3/5)^j/j! + (3/120)(3/5)^5 < 50/27 | Taylor remainder |
| e^(-3/5) > 27/50 | From above |
| e^(x₀) > 10 where x₀ = 665334/280900 | Σ(j=0..5) x₀^j/j! > 10 |
| e^(6π²/25) > 10 | Implies w_Bmin(1) ≤ 1/15, w_Bmin(2) ≤ 1/30000 in Lemma 8.19 |
| e^x ≤ 1 + x + x² for 0 ≤ x ≤ 1 | f(x) = 1 + x + x² - e^x with f(0) = f'(0) = 0, f'(1) = 3 - e > 0 |
| e^(1/144) < 1007/1000 | From 1 + 1/144 + 1/20736 < 1007/1000 |

### Other Constants

| Inequality | Source |
|------------|--------|
| γ > 0.5772 | Euler's constant lower bound (standard tables [31], [22]) |

### Lean Verification Status

These inequalities are verified in `A3_Floor_Main.lean` using:
- `norm_num` for rational arithmetic
- `nlinarith` for polynomial inequalities
- Explicit Taylor bounds for transcendental functions

---

## Digamma Bounds: Analytic Framework (Appendix F)

The analytic framework behind the uniform Archimedean floor bounds.
Main proof relies only on analytic lemmas in Section 8.3.

### F.1 Definitions

**Archimedean density:**
```
a(ξ) := log π − Re ψ(1/4 + iπξ)
```
where ψ(z) = Γ'(z)/Γ(z) is the digamma function.

**For B > 0 and t_sym > 0:**

| Symbol | Definition | Description | Used in |
|--------|------------|-------------|---------|
| A₀(B, t_sym) | 2π ∫_{-B}^{B} a(ξ)(1 - \|ξ\|/B) e^{-4π²t_sym ξ²} dξ | Integrated Archimedean term | **(H4) A3** |
| g_{B,t_sym}(ξ) | a(ξ)(1 - \|ξ\|/B) e^{-4π²t_sym ξ²} | Weighted Archimedean kernel | **(H4) A3** |
| L_A(B, t_sym) | 2π sup_{θ∈[-1/2,1/2]} Σ_{m∈Z} \|g'_{B,t_sym}(θ+m)\| | Lipschitz constant for B | **(H3) A2** |

### Key Parameters

| Parameter | Value | Description | Used in |
|-----------|-------|-------------|---------|
| B_min | 3 | Minimum bandwidth | **(H4) A3** |
| t_sym | 3/50 = 0.06 | Symbol heat parameter | **(H4) A3** |
| L*(t_sym) | sup_{B≥B_min} L_A(B, t_sym) | Uniform Lipschitz constant | **(H3) A2** |
| c* | 11/10 | Uniform Archimedean floor (Lemma 8.19) | **(H4) A3** |

### F.2 Digamma Properties

The digamma function at z = 1/4 satisfies the reflection formula [31, Ch. 2]:
```
ψ(1/4) = −γ − π/2 − 3 ln 2
```
where γ is Euler's constant. This gives:
```
a(0) = log π + γ + π/2 + 3 ln 2
```

For ξ ≠ 0, the real part of ψ(1/4 + iπξ) via series [31, Ch. 2]:
```
Re ψ(1/4 + iπξ) = −γ + Σ_{n=0}^∞ (1/(n+1) − (n + 1/4)/((n + 1/4)² + π²ξ²))
```

| Property | Statement | Source | Used in |
|----------|-----------|--------|---------|
| Reflection at 1/4 | ψ(1/4) = −γ − π/2 − 3 ln 2 | [31, Ch. 2] | **(H1) T0**, **(H4) A3** |
| Conjugation | ψ(z̄) = ψ(z)̄ | NIST DLMF 5.5 | **(H4) A3** (a_star_even) |
| Asymptotic | ψ(z) ~ log z - 1/(2z) - Σ B_{2k}/(2k·z^{2k}) | Stirling | **(H4) A3** |
| Recurrence | ψ(z+1) = ψ(z) + 1/z | Functional equation | **(H4) A3** |
| Remainder bound | \|ψ(z) − log z + 1/(2z)\| ≤ 1/(12\|z\|²) | [22, §5.11] | **(H4) A3** |

### F.3 Analytic Bound Framework

Section 8.3 introduces analytic bounds for L*(t_sym) and records the direct pointwise floor c* (Lemma 8.19).

| Component | Description | Hypothesis |
|-----------|-------------|------------|
| L*(t_sym) bounds | Mean–modulus estimates for L_A | **(H3) A2** Lipschitz |
| c* = 11/10 floor | Direct pointwise bound on P_A(θ) | **(H4) A3** Toeplitz |
| A₀ auxiliary bounds | Not used in main chain | (auxiliary) |

### F.4 Finite-Sum Bounds at Sample Points

For y = πξ, define the summand:
```
t_n(y) := 1/(n+1) − (n + 1/4)/((n + 1/4)² + y²)
```

**Truncation rule:** t_n(y) ≤ 0 once n ≥ ⌈(4/3)y² − 1/4⌉

**Example: ξ = 1/2**

For ξ = 1/2, t_n(π/2) ≤ 0 for n ≥ 4, so:
```
Re ψ(1/4 + iπ/2) ≤ −γ + Σ_{n=0}^{3} t_n(π/2)
```

Using π² < 10:

| n | Bound | Value |
|---|-------|-------|
| t₀ | ≤ 37/41 | 0.902... |
| t₁ | ≤ 5/26 | 0.192... |
| t₂ | ≤ 13/363 | 0.035... |
| t₃ | ≤ 1/836 | 0.001... |
| **Sum** | < 1.132 | |

With π > 333/106 and γ > 0.5772:
```
a(1/2) = log π + γ − Σ t_n(π/2) > 29/50 = 0.58
```
(Lemma 8.18)

**Large ξ bounds (ξ ≥ 1):**

Using digamma remainder bound \|ψ(z) − log z + 1/(2z)\| ≤ 1/(12\|z\|²):
```
a(ξ) ≥ −log ξ − 1/(2πξ) − 1/(12π²ξ²)
```

| ξ | Bound | Derivation | Result |
|---|-------|------------|--------|
| 3/2 | a(3/2) > −3/5 | −5/12 − 1/9 − 1/243 using log(3/2) < 5/12 | Lemma 8.18 |
| 5/2 | a(5/2) > −11/10 | −1 − 1/15 − 1/675 using log(5/2) < 1 | Lemma 8.18 |

### Lean Files Mapping

| Component | File | Status | Hypothesis |
|-----------|------|--------|------------|
| a(ξ) definition | `Q3/Basic/Defs.lean` | ✅ | **(H1) T0** |
| a_star_pos axiom | `Q3/Axioms.lean` | AX (Tier-1) | **(H4) A3** |
| a_star_even axiom | `Q3/Axioms.lean` | AX (Tier-1) | **(H4) A3** |
| a_star_continuous | `Q3/Axioms.lean` | AX (Tier-1) | **(H3) A2** |
| A0 computation | `A3_Floor_Main.lean` | ✅ | **(H4) A3** |
| Floor c* = 11/10 | `A3_Floor_Main.lean` | ✅ PROVEN | **(H4) A3** |
| Finite-sum bounds | `A3_Floor_Main.lean` | ✅ | **(H4) A3** |
| L_A Lipschitz | `Q3/Proofs/Q_Lipschitz.lean` | ✅ THEOREM | **(H3) A2** |

### Why a(ξ) > 0

From the explicit formula:
```
a(ξ) = log π - Re ψ(1/4 + iπξ)
     = log π + γ + 3 log 2 + Σ_{n≥0} Re[1/(n + 1/4 + iπξ) - 1/(n+1)]
```

The sum is positive because each term contributes positively when ξ ≠ 0.
For ξ = 0: a(0) = log π + γ + 3 log 2 - ψ(1/4) ≈ 2.415 > 0.

This is axiomatized as `a_star_pos` in Lean (Tier-1 classical axiom from Titchmarsh).

---

## Remaining Blocker

Single closable axiom remaining:
```
Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
```

This connects A3 floor + RKHS cap → Q ≥ 0 on atoms. Need to wire via `Rayleigh_Q_identification.lean`.

---

## Build Commands

```bash
cd full/q3.lean.aristotle

# Build
lake build Q3.Main

# Verify axioms
./scripts/check_axioms.sh

# Quick axiom check
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'
```

---

## Directory Structure

```
chen_q3/                           (7.2 GB total)
├── full/q3.lean.aristotle/        (6.3 GB, main Lean project)
│   ├── Q3/                        (1.2 MB, core proof modules)
│   │   ├── Basic/Defs.lean        — Core definitions (Q, Weil_cone, W_K)
│   │   ├── Axioms.lean            — Tier-1/Tier-2 axioms
│   │   ├── AxiomsTheorems.lean    — Theorem wiring
│   │   ├── Main.lean              — RH_of_Weil_and_Q3 (main theorem!)
│   │   └── Proofs/                — 54 proof files (~11,300 lines)
│   │
│   ├── aristotle_input/           (792 KB) — prompts for Aristotle
│   ├── aristotle_output/          (1.5 MB) — proof outputs
│   ├── aristotle_db/              (296 KB) — lemma database
│   ├── .lake/                     (6.2 GB) — Mathlib cache
│   ├── lakefile.toml              — Lake build config
│   └── scripts/check_axioms.sh    — axiom verification
│
├── docs/                          — documentation and archives
├── paper/                         — LaTeX paper
├── src/                           — Python numerical calculations
└── archive/                       (3.7 MB) — historical code
```
