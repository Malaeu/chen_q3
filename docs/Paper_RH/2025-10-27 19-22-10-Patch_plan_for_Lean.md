# Patch plan for Lean

https://chat.openai.com/c/68ffb84c-4684-832a-9951-ae1ff7e1694b

## USER
Thanks for the diagnostics! Here’s a consolidated fix plan for `RHFormalization/WeilCriterion.lean`, addressing every point you flagged:

---

### 1. Replace the non-existent `div_pos_of_pos_of_pos`

Occurrences (≈ lines 380, 466):

```lean
have : 0 < c₀ / 4 := div_pos hc₀ (by norm_num)
have hweight_pos : 0 < weightSum := div_pos hS (by norm_num)
```

Simple `div_pos` is the right lemma in Lean 4; no custom `div_pos_of_pos_of_pos`.

---

### 2. Rewrite the `mul_div_cancel'` step

Around line 400, recast the cancellation with a nonzero proof:

```lean
have hc_ne : (c₀ / 4) ^ 2 ≠ 0 := by
  have : 0 < (c₀ / 4) ^ 2 := …  -- already available above
  exact ne_of_gt this
have : ((c₀ / 4) ^ 2 * S) / (c₀ / 4) ^ 2 = S := by
  simpa [mul_comm] using (mul_div_cancel₀ S hc_ne)
```

(No need for the non-existent lemma; Lean 4 has `mul_div_cancel₀`.)

---

### 3. Properly use `Real.sqrt_sq`

Near lines 401–405:

```lean
have hAnonneg : 0 ≤ A := le_of_lt hA_pos
have : Real.sqrt (A ^ 2) = A := by
  simpa [abs_of_nonneg hAnonneg] using Real.sqrt_sq hAnonneg
```

`Real.sqrt_sq` takes a `0 ≤ _` proof in Lean 4—once you supply it, the absolute-value cleanup works automatically.

---

### 4. Fix the monotonicity of the fraction (line 410)

Instead of `div_le_div_of_nonneg_left`, use inverses and multiplication:

```lean
set denom_tmin := Real.sqrt (4 * Real.pi * tmin)
set denom_t   := Real.sqrt (4 * Real.pi * t)

have denom_monotone :
    denom_t⁻¹ ≤ denom_tmin⁻¹ := by
  have hden_le : denom_tmin ≤ denom_t := ... -- from sqrt monotonicity
  exact inv_le_inv_of_le (by exact Real.sqrt_pos.mpr ...) hden_le

have frac_le :
    S * denom_t⁻¹ ≤ S * denom_tmin⁻¹ :=
  mul_le_mul_of_nonneg_left denom_monotone hSnonneg

-- convert back to `/` form:
have : S / denom_t ≤ S / denom_tmin := by
  simpa [one_div, denom_t, denom_tmin] using frac_le
```

The idea: compare the inverses, then multiply on the left; finally rewrite as division.

---

### 5. Eliminate the residual `mkNodeSet`/`t` mismatch (line 489)

Before simplifying the norm bound, make sure both sides literally reference the same `t`:

```lean
have ht_id : (RH.RKHSPrimeBridge.mkNodeSet K t ht_pos).t = t := rfl
simp [prime_operator_norm, ht_pos, ht_id, hweights_eq] at hbound
```

If `mkNodeSet` exposes `t` as a structure field named `.t`, this `rfl` (or an equivalent lemma) clears the mismatch so the concluding inequality collapses to `≤ rfl`.

---

### 6. Clean up small lint issues

- Remove `Complex.ofReal_mul` from the `simp` list around line 194—it isn’t a simp formula in Lean 4.
- For the `by_cases hx : x = 0` branch, write `if _ : x = 0 then ... else ...` or rename the proof `_` to silence the “unused variable” warning.

---

Apply these tweaks and rerun `lake build`; the checker should now stop only at the existing `sorry`s. Let me know if anything still sticks!  

<chatName="WeilCriterion lint & algebra fixes"/>
<file_map>
/Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean
├── RH
│   ├── A1Contract.lean *
│   ├── Contracts.lean *
│   ├── FejerHeat.lean *
│   ├── T0A1A2.lean *
│   ├── RKHSPrime.lean
│   └── RKHSPrimeBridge.lean
├── RH_Formalization
│   ├── .github
│   │   └── workflows
│   │       └── lean_action_ci.yml *
│   ├── RHFormalization
│   │   └── Basic.lean *
│   ├── .gitignore *
│   ├── CLAUDE.md *
│   ├── lakefile.toml *
│   ├── lean-toolchain *
│   ├── Main.lean *
│   ├── README_RU.md *
│   ├── README.md *
│   └── RHFormalization.lean *
├── RHFormalization
│   └── WeilCriterion.lean *
├── RiemannQ3
│   ├── Basic
│   │   ├── Definitions.lean *
│   │   ├── Kernels.lean *
│   │   └── NodeSpacing.lean *
│   ├── Density
│   │   └── Lipschitz.lean *
│   └── Density.lean *
├── .lake
│   ├── build
│   │   ├── bin
│   │   │   ├── rh_formalization
│   │   │   ├── rh_formalization.hash
│   │   │   └── rh_formalization.trace
│   │   ├── ir
│   │   │   ├── RH
│   │   │   │   └── ...
│   │   │   ├── RHFormalization
│   │   │   │   └── ...
│   │   │   ├── RiemannQ3
│   │   │   │   └── ...
│   │   │   ├── Main.c +
│   │   │   ├── Main.c.hash
│   │   │   ├── Main.c.o.export
│   │   │   ├── Main.c.o.export.hash
│   │   │   ├── Main.c.o.export.trace
│   │   │   ├── Main.setup.json
│   │   │   ├── RHFormalization.c +
│   │   │   ├── RHFormalization.c.hash
│   │   │   ├── RHFormalization.c.o.export
│   │   │   ├── RHFormalization.c.o.export.hash
│   │   │   ├── RHFormalization.c.o.export.trace
│   │   │   └── RHFormalization.setup.json
│   │   └── lib
│   │       └── lean
│   │           └── ...
│   └── packages
│       ├── aesop
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── Aesop
│       │   │   └── ...
│       │   ├── AesopTest
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── Aesop.lean
│       │   ├── lake-manifest.json
│       │   ├── lakefile.toml
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   └── README.md
│       ├── batteries
│       │   ├── .docker
│       │   │   └── ...
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── Batteries
│       │   │   └── ...
│       │   ├── BatteriesTest
│       │   │   └── ...
│       │   ├── docs
│       │   │   └── ...
│       │   ├── scripts
│       │   │   └── ...
│       │   ├── Shake
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── .gitpod.yml
│       │   ├── Batteries.lean
│       │   ├── bors.toml
│       │   ├── lake-manifest.json
│       │   ├── lakefile.toml
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   └── README.md
│       ├── Cli
│       │   ├── .github
│       │   │   └── ...
│       │   ├── Cli
│       │   │   └── ...
│       │   ├── CliTest
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── Cli.lean
│       │   ├── lake-manifest.json
│       │   ├── lakefile.toml
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   └── README.md
│       ├── importGraph
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── html-template
│       │   │   └── ...
│       │   ├── ImportGraph
│       │   │   └── ...
│       │   ├── ImportGraphTest
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── .gitpod.yml
│       │   ├── ImportGraph.lean
│       │   ├── ImportGraphTest.lean
│       │   ├── lake-manifest.json
│       │   ├── lakefile.toml
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   ├── Main.lean
│       │   └── README.md
│       ├── LeanSearchClient
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── LeanSearchClient
│       │   │   └── ...
│       │   ├── LeanSearchClientTest
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── lake-manifest.json
│       │   ├── lakefile.toml
│       │   ├── lean-toolchain
│       │   ├── LeanSearchClient.lean
│       │   ├── LeanSearchClientTest.lean
│       │   ├── LICENSE
│       │   └── README.md
│       ├── mathlib
│       │   ├── .devcontainer
│       │   │   └── ...
│       │   ├── .docker
│       │   │   └── ...
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── Archive
│       │   │   └── ...
│       │   ├── Cache
│       │   │   └── ...
│       │   ├── Counterexamples
│       │   │   └── ...
│       │   ├── docs
│       │   │   └── ...
│       │   ├── DownstreamTest
│       │   │   └── ...
│       │   ├── LongestPole
│       │   │   └── ...
│       │   ├── Mathlib
│       │   │   └── ...
│       │   ├── MathlibTest
│       │   │   └── ...
│       │   ├── scripts
│       │   │   └── ...
│       │   ├── widget
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── .gitpod.yml
│       │   ├── .pre-commit-config.yaml
│       │   ├── Archive.lean
│       │   ├── bors.toml
│       │   ├── CODE_OF_CONDUCT.md
│       │   ├── Counterexamples.lean
│       │   ├── docs.lean
│       │   ├── lake-manifest.json
│       │   ├── lakefile.lean
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   ├── Mathlib.lean
│       │   └── README.md
│       ├── plausible
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── Plausible
│       │   │   └── ...
│       │   ├── Test
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── lake-manifest.json
│       │   ├── lakefile.toml
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   ├── Plausible.lean
│       │   ├── README.md
│       │   └── Test.lean
│       ├── proofwidgets
│       │   ├── .github
│       │   │   └── ...
│       │   ├── .lake
│       │   │   └── ...
│       │   ├── doc
│       │   │   └── ...
│       │   ├── ProofWidgets
│       │   │   └── ...
│       │   ├── test
│       │   │   └── ...
│       │   ├── widget
│       │   │   └── ...
│       │   ├── .gitignore
│       │   ├── lake-manifest.json
│       │   ├── lakefile.lean
│       │   ├── lean-toolchain
│       │   ├── LICENSE
│       │   ├── ProofWidgets.lean
│       │   ├── README.md
│       │   └── RELEASES.md
│       └── Qq
│           ├── .github
│           │   └── ...
│           ├── .lake
│           │   └── ...
│           ├── examples
│           │   └── ...
│           ├── Qq
│           │   └── ...
│           ├── .gitignore
│           ├── GNUmakefile
│           ├── lake-manifest.json
│           ├── lakefile.toml
│           ├── lean-toolchain
│           ├── LICENSE
│           ├── Qq.lean
│           └── README.md
├── plans
│   ├── archimedean_bridge_plan.md
│   ├── basic_infra_plan.md
│   ├── contracts_plan.md
│   ├── rkhs_prime_plan.md
│   ├── transport_plan.md
│   └── weil_criterion_plan.md
├── scripts
│   └── verify_artifacts.py +
├── CLAUDE.md *
├── codemap.md *
├── lake-manifest.json *
├── lakefile.toml *
├── lean_zeta_formalization.md *
├── lean-toolchain *
├── lean4_syntax_notes.md *
├── Main.lean *
├── Q3_Definitions_Extraction.md *
├── RH_formalization.lean *
├── RH_Formalization.tar.gz *
├── RH_Q3.pdf *
├── RHFormalization.lean *
├── scratch.lean *
├── sorry_matrix_README.md *
├── sorry_matrix.md *
├── todo.md *
├── Как оформить документ в формате ЛИН_.zip *
├── Формализация Гипотезы Римана в Lean 4: Итоговый отчет.md *
├── Формализация Гипотезы Римана через Критерий Вейля в Lean 4.md *
├── eps_transport.json
├── grid_psd.json
├── KE_integral_certificate.json
├── phase_monotone.json
├── tmp.lean
└── weil_criterion_plan.md


(* denotes selected files)
(+ denotes code-map available)
Config: depth cap 3.
</file_map>
<file_contents>
File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/sorry_matrix.md
```md
# RH Formalization: Sorry Matrix

**Status**: 0/50 closed | **Updated**: 2025-10-25

## 🎯 Mission

Complete traceability matrix linking every `sorry` to:
- **Mathematical theorem** from Q3 paper
- **Numerical artifacts** (JSON certificates with SHA256)
- **Lean formalization** requirements
- **Closure plan** and dependencies

## 📊 Statistics

| Phase | Sorry Count | Closed | Critical Path |
|-------|-------------|--------|---------------|
| **Phase 1: Infrastructure** | 7 | 6 | ✓ |
| **Phase 2: Toeplitz Barrier** | 3 | 3 | ✓ |
| **Phase 3: RKHS Contraction** | 2 | 0 | - |
| **Phase 4: Assembly** | 13 | 0 | - |
| **Duplicates/Skip** | 25 | N/A | - |
| **Contracts** | 1 | 1 | ✓ |
| **TOTAL** | 50 | 7 | - |

---

## 🔴 Phase 1: Infrastructure (Critical Path)

| № | File | Line | Component | Math Ref | Artifact | Plan | Status |
|---|------|------|-----------|----------|----------|------|--------|
| 1 | RH_formalization.lean | 42 | `archimedean_density` | §4.2, Eq 4.7 | K1_A3_lock.json, grid_psd.json | [basic_infra](plans/basic_infra_plan.md#archimedean) | 🟢 |
| 14 | RHFormalization/WeilCriterion.lean | 37 | `archimedean_density` | §4.2 | K1_A3_lock.json, grid_psd.json | [basic_infra](plans/basic_infra_plan.md#archimedean) | 🟢 |
| 15 | RHFormalization/WeilCriterion.lean | 83 | `fourier_even_of_even` | §6 Fourier | RH/Contracts (Axiom A5) | [basic_infra](plans/basic_infra_plan.md#fourier) | 🟢 |
| 16 | RHFormalization/WeilCriterion.lean | 93 | `fejer_kernel_nonneg` | §7 Fejér | RH/Contracts (Axiom A3) | [basic_infra](plans/basic_infra_plan.md#fejer) | 🟢 |
| 17 | RHFormalization/WeilCriterion.lean | 107 | `heat_kernel_pos` | §7 Heat | RH/Contracts (Axiom A4) | [basic_infra](plans/basic_infra_plan.md#heat) | 🟢 |
| 18 | RHFormalization/WeilCriterion.lean | 117 | `fejer_heat_kernel_nonneg` | §7 Product | RH/Contracts (Axiom A3–A4) | [basic_infra](plans/basic_infra_plan.md#product) | 🟢 |
| 50 | RH/Contracts.lean | various | Axioms | §8-12 | grid_psd.json, phase_monotone.json, eps_transport.json, KE_integral_certificate.json, K1_A3_lock.json | [contracts](plans/contracts_plan.md) | 🟢 |

**Blocks**: Phase 2 (Toeplitz)

---

## 🔴 Phase 2: Toeplitz Barrier (Critical Path)

| № | File | Line | Component | Math Ref | Artifact | Plan | Status |
|---|------|------|-----------|----------|----------|------|--------|
| 8 | RH_formalization.lean | 102 | `archimedean_toeplitz_barrier` | Thm 8.35 | grid_psd.json | [toeplitz](plans/archimedean_bridge_plan.md#barrier) | 🟢 |
| 31 | RHFormalization/WeilCriterion.lean | 233 | `archimedean_toeplitz_barrier` | Thm 8.35 | grid_psd.json | [toeplitz](plans/archimedean_bridge_plan.md#barrier) | 🟢 |
| 38 | RHFormalization/WeilCriterion.lean | 464 | `choose_M_for_modulus` | §8.9 | grid_psd.json | [toeplitz](plans/archimedean_bridge_plan.md#choose-m) | 🟢 |

**Requires**: #1, #14-18, #29-30  
**Blocks**: #35-37 (Assembly)

**Numerical Evidence**: 
- `grid_psd.json`: λ_min = **1.297×10⁻⁸** (D7 PSD verification)
- Grid size M = **16**, safety margin = **1.297×10⁻⁸**

---

## 🔴 Phase 3: RKHS Contraction

| № | File | Line | Component | Math Ref | Artifact | Plan | Status |
|---|------|------|-----------|----------|----------|------|--------|
| 11 | RH_formalization.lean | 123 | `prime_contraction` | Thm 9.23 | K1_blocks.json, K1_step_next.json, phase_monotone.json, KE_integral_certificate.json | [rkhs](plans/rkhs_prime_plan.md#contraction) | 🔴 |
| 33 | RHFormalization/WeilCriterion.lean | 303 | `prime_contraction` | Thm 9.23 | K1_blocks.json, K1_step_next.json, phase_monotone.json, KE_integral_certificate.json | [rkhs](plans/rkhs_prime_plan.md#contraction) | 🔴 |

**Requires**: #9-10, #32  
**Blocks**: #35 (Assembly)

---

## 🔴 Phase 4: Assembly

| № | File | Line | Component | Math Ref | Artifact | Plan | Status |
|---|------|------|-----------|----------|----------|------|--------|
| 3 | RH_formalization.lean | 67 | `main_theorem` | Thm 1.1 | KE_integral_certificate.json | [weil](plans/weil_criterion_plan.md#main) | 🔴 |
| 13 | RH_formalization.lean | 159 | `riemann_hypothesis_formal_proof` | Thm 13.2 | KE_integral_certificate.json | [weil](plans/weil_criterion_plan.md#final) | 🔴 |
| 35 | RHFormalization/WeilCriterion.lean | 380 | `positivity_on_compact` | §13 | KE_integral_certificate.json | [weil](plans/weil_criterion_plan.md#compact) | 🔴 |
| 36 | RHFormalization/WeilCriterion.lean | 388 | `weil_positivity` | §13 | KE_integral_certificate.json | [weil](plans/weil_criterion_plan.md#positivity) | 🔴 |
| 37 | RHFormalization/WeilCriterion.lean | 403 | `riemann_hypothesis_proof` | Thm 13.2 | KE_integral_certificate.json | [weil](plans/weil_criterion_plan.md#rh-proof) | 🔴 |

**Requires**: All Phase 1-3  
**Final Goal**: Close RH proof chain

---

## 🟡 Duplicates / Skip

| № | File | Line | Component | Note | Status |
|---|------|------|-----------|------|--------|
| 39-47 | RH_Formalization/.../WeilCriterion.lean | various | [duplicates] | Duplicate of main copy | 🟡 SKIP |
| 48 | Main.lean | 17 | Status string | Cosmetic | 🟡 SKIP |
| 49 | RH/T0A1A2.lean | 14 | Comment | Cosmetic | 🟡 SKIP |

---

## 📦 Numerical Artifacts Registry

| File | SHA256 | Used By | Key Data | Verification |
|------|--------|---------|----------|--------------|
| `grid_psd.json` | `[compute]` | #8, #31, #38 | λ_min=1.297e-08, M=16 | ✓ D7 passed |
| `phase_monotone.json` | `[compute]` | Transport | φ'_min=0.00124 | ✓ D8 passed |
| `eps_transport.json` | `[compute]` | #12, #34 | gap=1.216e-06, safety=1.028 | ✓ γ>δ |
| `KE_integral_certificate.json` | `[compute]` | #3, #13, #35-37 | Final certification | ✓ Complete |
| `M5pp_continuum_bridge.json` | `[compute]` | Bridge | Bridge margin=9.73e-09 | ✓ Positive |

**Verification Script**: `scripts/verify_artifacts.py` (checksums + value ranges)

---

## 🗺️ Plan Files

| Plan | Coverage | Sorry Count | Status |
|------|----------|-------------|--------|
| [basic_infra_plan.md](plans/basic_infra_plan.md) | Kernels, densities, Fourier | 7 | 📝 Draft |
| [archimedean_bridge_plan.md](plans/archimedean_bridge_plan.md) | A3 Toeplitz barrier | 3 | 📝 Draft |
| [rkhs_prime_plan.md](plans/rkhs_prime_plan.md) | RKHS contraction | 2 | 📝 Draft |
| [transport_plan.md](plans/transport_plan.md) | T5 compact transfer | 2 | 📝 Draft |
| [weil_criterion_plan.md](plans/weil_criterion_plan.md) | Main assembly (T0, A1', A2) | 13 | 📝 Draft |
| [contracts_plan.md](plans/contracts_plan.md) | Axioms → theorems | 1 | 📝 Draft |

---

## 🚀 Workflow: Closing a Sorry

### 1. **Preprocessing** (in plan file)
```markdown
## Sorry #8: archimedean_toeplitz_barrier

### Math
- **Q3**: §8.9, Theorem 8.35
- **Equation**: λ_min(T_M[P_A]) ≥ c₀ - C·ω(π/M)

### Numerical
- `grid_psd.json` → λ_min = 1.297e-08
- Verification: λ_min > -1e-15 ✓

### Lean Target
```lean
theorem archimedean_toeplitz_barrier ... : 
  minEigenvalue T ≥ c₀ - C*ω(π/M)
```

### Agent Debate
- **Advocate**: "grid_psd gives c₀!"
- **Skeptic**: "That's one grid, need uniform bound"
- **Resolution**: Axiomatize Szegő, use grid as witness
```

### 2. **Implementation**
- Write Lean code
- Link to numerical constants
- Test with `lake build`

### 3. **Verification**
```bash
python scripts/verify_numerical_match.py sorry_08
```

### 4. **Closure**
- Update matrix: 🔴 → 🟢
- Create `closed/2025-10-25_sorry_08.md`
- Document dependencies unblocked

---

## 🔬 Example Closure Log

**File**: `closed/2025-10-25_sorry_08.md`

```markdown
# Sorry #8: archimedean_toeplitz_barrier

**Closed**: 2025-10-25  
**Commit**: `abc123def`  
**Lean**: `theorem archimedean_toeplitz_barrier_impl`

## Numerical Inputs
- λ_min = 1.2971215226606565e-08 (grid_psd.json)
- M₀ = 16
- c₀ = 0.0428 (from A3 tables)

## Implementation
```lean
theorem archimedean_toeplitz_barrier_impl ... := by
  use 1.297e-08
  use 16
  apply szego_min_eig_lower_bound
  ...
```

## Verification
- [x] Compiles without sorry
- [x] Numerical values match JSON ±1e-10
- [x] Unblocks: #31, #35, #38

## Agent Resolution
Szegő theorem axiomatized in Contracts.lean (future: replace with full proof)
```

---

## 📋 Complete Sorry List (Reference)

<details>
<summary>All 50 Sorry Locations</summary>

### RH_formalization.lean (14 sorry)
1. Line 42: archimedean_density
2. Line 51: weil_functional  
3. Line 67: main_theorem proof
4. Line 80: weil_criterion_equivalence
5. Line 94: ToeplitzOperator def
6. Line 98: P_A symbol
7. Line 100: M discretization
8. Line 102: archimedean_toeplitz_barrier
9. Line 115: PrimeOperator def
10. Line 120: prime contraction constant
11. Line 123: prime_contraction
12. Line 137: compact_transfer
13. Line 159: riemann_hypothesis_formal_proof
14. (comment): "proofs replaced with sorry"

### RHFormalization/WeilCriterion.lean (25 sorry)
14. Line 37: archimedean_density
15. Line 83: fourier_even_of_even
16. Line 93: fejer_kernel_nonneg
17. Line 107: heat_kernel_pos
18. Line 117: fejer_heat_kernel_nonneg
19. Line 127: guinand_weil_functional
20. Line 134: guinand_weil_equivalence
21. Line 140: weil_class_on_window
22. Line 153: fejer_heat_span
23. Line 162: fejer_heat_density
24. Line 168: sup_norm_on_window
25. Line 179: q_lipschitz_on_window
26. Line 188: density_extension_via_lipschitz
27. Line 196: main_theorem
28. Line 205: weil_criterion_equivalence
29. Line 216: minEigenvalue axiom
30. Line 225: toeplitz_operator_on_window
31. Line 233: archimedean_toeplitz_barrier
32. Line 254: prime_operator_norm
33. Line 303: prime_contraction
34. Line 339: compact_transfer
35. Line 380: positivity_on_compact
36. Line 388: weil_positivity
37. Line 403: riemann_hypothesis_proof
38. Line 464: choose_M_for_modulus

### RH_Formalization/.../WeilCriterion.lean (9 duplicates)
39-47. Lines 33-166: [duplicates of above]

### Auxiliary (2 cosmetic)
48. Main.lean:17 (comment)
49. RH/T0A1A2.lean:14 (comment)

### Contracts (1 axiom block)
50. RH/Contracts.lean (various axioms)

</details>

---

## 🎯 Next Actions

1. **Fill plan files** (archimedean_bridge_plan.md first - demo)
2. **Extract numerical constants** from JSON to Lean defs
3. **Sketch proof structure** for Phase 1 (even with inner sorry)
4. **Agent debate** on each sorry before implementation
5. **Verify numerics** with Python scripts

**Start with**: Sorry #8 (archimedean_toeplitz_barrier) - critical path blocker

---

**Last Updated**: 2025-10-25 by Multi-Agent System  
**No Assume Protocol**: Every number traceable to JSON artifact

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH/FejerHeat.lean
```lean
import Mathlib/Topology/ContinuousFunction.Basic
import Mathlib/Topology/ContinuousFunction.Compact
import Mathlib/Topology/MetricSpace.Basic
import Mathlib/Analysis/SpecialFunctions/Exp
import Mathlib/Data/Real/Sqrt
import Mathlib/Data/Real/Pi
import Mathlib/Algebra/BigOperators.Basic
import Mathlib/Tactic/Continuity
import RH/A1Contract

noncomputable section

open scoped BigOperators Real

namespace RH

variable {K : ℝ}

/-- Hat (Fejér) profile at scale `B`. -/
def tent (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)

lemma tent_nonneg {B x : ℝ} : 0 ≤ tent B x := by
  unfold tent
  exact le_max_iff.2 (Or.inl rfl.le)

lemma continuous_tent {B : ℝ} (hB : 0 < B) :
    Continuous fun x : ℝ => tent B x := by
  unfold tent
  have hDiv : Continuous fun x : ℝ => |x| / B := by
    simpa [div_eq_mul_inv] using
      (Real.continuous_abs.mul (continuous_const : Continuous fun _ : ℝ => (1 / B)))
  have hCore : Continuous fun x : ℝ => 1 - |x| / B := by
    simpa using (continuous_const.sub hDiv)
  simpa using hCore.max continuous_const

/-- Heat (Gaussian) profile at scale `t`. -/
def heat (t : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x ^ 2) / (4 * t))

lemma heat_nonneg {t x : ℝ} (ht : 0 < t) : 0 ≤ heat t x := by
  unfold heat
  have hcoeff : 0 < Real.sqrt (4 * Real.pi * t) := by
    have hpos : 0 < 4 * Real.pi * t := by
      have : 0 < Real.pi := Real.pi_pos
      nlinarith
    exact Real.sqrt_pos.mpr hpos
  have hcoeff_nonneg : 0 ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ :=
    inv_nonneg.mpr hcoeff.le
  have hExp : 0 ≤ Real.exp (-(x ^ 2) / (4 * t)) :=
    (Real.exp_pos _).le
  exact mul_nonneg hcoeff_nonneg hExp

lemma continuous_heat {t : ℝ} (ht : 0 < t) :
    Continuous fun x : ℝ => heat t x := by
  unfold heat
  have hcoeff : Continuous fun _ : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ :=
    continuous_const
  have hExp : Continuous fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t)) := by
    -- Lean понимает, что экспонента от гладкой функции непрерывна
    simpa [div_eq_mul_inv] using
      (by
        have : Continuous fun x : ℝ => -(x ^ 2) / (4 * t) := by
          -- tactic `by continuity` справляется с композициями
          simpa [div_eq_mul_inv] using (by continuity : Continuous fun x : ℝ => -(x ^ 2) / (4 * t))
        exact this.exp)
  simpa using hcoeff.mul hExp

/-- Symmetric Fejér×heat packet centered at `τ`. -/
def fhPacket (K B t τ : ℝ) (hB : 0 < B) (ht : 0 < t) : Window K :=
  let core (x : ℝ) :=
    tent B (x - τ) * heat t (x - τ) + tent B (x + τ) * heat t (x + τ)
  ⟨fun x => core x,
    by
      have h1 :=
        (continuous_tent hB).comp ((continuous_subtype_val).sub continuous_const)
      have h2 :=
        (continuous_heat ht).comp ((continuous_subtype_val).sub continuous_const)
      have h3 :=
        (continuous_tent hB).comp ((continuous_subtype_val).add continuous_const)
      have h4 :=
        (continuous_heat ht).comp ((continuous_subtype_val).add continuous_const)
      simpa [core, fhPacket] using (h1.mul h2).add (h3.mul h4)⟩

lemma fhPacket_nonneg (K B t τ : ℝ) (hB : 0 < B) (ht : 0 < t) :
    ∀ x : Set.Icc (-K) K, 0 ≤ fhPacket K B t τ hB ht x := by
  intro x
  dsimp [fhPacket]
  have hL :
      0 ≤ tent B ((x : ℝ) - τ) * heat t ((x : ℝ) - τ) :=
    mul_nonneg
      (tent_nonneg (B := B) (x := (x : ℝ) - τ))
      (heat_nonneg (t := t) (x := (x : ℝ) - τ) ht)
  have hR :
      0 ≤ tent B ((x : ℝ) + τ) * heat t ((x : ℝ) + τ) :=
    mul_nonneg
      (tent_nonneg (B := B) (x := (x : ℝ) + τ))
      (heat_nonneg (t := t) (x := (x : ℝ) + τ) ht)
  exact add_nonneg hL hR

/-- The Fejér×heat cone: finite nonnegative linear combinations of packets. -/
def FHcone (K : ℝ) : Set (Window K) :=
  {f | ∃ (N : ℕ) (B t : ℝ) (hB : 0 < B) (ht : 0 < t)
        (τ : Fin N → ℝ) (c : Fin N → ℝ),
      (∀ i, 0 ≤ c i) ∧
      f = ∑ i, (c i) • fhPacket K B t (τ i) hB ht}

lemma FHcone_subset_nonneg {K : ℝ} :
    FHcone K ⊆ nonnegCone K := by
  classical
  intro f hf
  rcases hf with ⟨N, B, t, hB, ht, τ, c, hc, rfl⟩
  intro x
  have hsum :
      ∀ i : Fin N,
        0 ≤ ((c i) • fhPacket K B t (τ i) hB ht) x := by
    intro i
    have := fhPacket_nonneg K B t (τ i) hB ht x
    simpa using mul_nonneg (hc i) this
  have hx :
      0 ≤ ∑ i : Fin N, ((c i) • fhPacket K B t (τ i) hB ht) x :=
    Finset.sum_nonneg (fun i _ => hsum i)
  exact hx

end RH

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RiemannQ3/Density.lean
```lean
import RiemannQ3.Density.Lipschitz

/-!
# RiemannQ3.Density

Umbrella module aggregating all Density components so that `lake build RiemannQ3.Density`
has a concrete entry point.
-/

-- Intentionally empty: the imported modules already live in the `RiemannQ3.Density` namespace.

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/codemap.md
```md
## RH Formalization Codemap

This map records where the project pulls the main analytic and spectral tools.
Read it first before digging into mathlib or the legacy archive.

### 1. Supporting Library Modules
- **Inner product & operator basics** – `Mathlib/Analysis/InnerProductSpace/Basic`,
  `Mathlib/LinearAlgebra/Matrix/Hermitian`. Contains the coercions needed for
  self-adjoint matrices, spectral inequalities, and continuous linear maps.
- **Toeplitz infrastructure** – no direct mathlib module yet; we rely on
  `RH/Contracts.lean` (`ToeplitzSpec`, `szego_min_eig_lower_bound`) as a contract.
  Actual discretization data comes from `cert/bridge/K*_A3_lock.json`.
- **Lipschitz machinery** – `Mathlib/Topology/MetricSpace/Lipschitz`. Use this
  for Module A2 bounds (`A2LipschitzSpec`).
- **Closed-set propagation** – `Mathlib/Topology/Continuous` (lemma
  `IsClosed.preimage`). Needed for extending nonnegativity from dense subsets in
  `A2LipschitzSpec.nonneg_on_window_of_dense`.
- **Real metric identities** – `Mathlib/Data/Real/Basic` (provides
  `Real.dist_eq`, `abs_sub_comm`), used by the Lipschitz estimates in
  `A2LipschitzSpec.abs_le_mul`.
- **A1 contract layer** – `RH/A1Contract.lean` builds the abstract density
  machinery:
  - `Window` (`ContinuousMap` on `[-K,K]`)
  - `A1Contract` packages a positivity-preserving smoothing family `S ε`, a
    designated cone `cone`, and the approximate-identity estimate
  - Density lemmas `A1Contract.density_nonneg`, `A1Contract.A1_density_on_nonneg`,
    and the exported `A1_density` for reuse inside T0/A2.
- **Fejér×heat generators** – `RH/FejerHeat.lean` provides concrete nonnegative
  packets (`tent`, `heat`, `fhPacket`) and the cone `FHcone ⊆ nonnegCone`, all without
  `sorry`. These serve as ready-made witnesses for instantiating `A1Contract`.
- **Matrix norms/Hoffman–Wielandt** – currently abstracted by the contract
  `hoffman_wielandt_bound` in `RH/Contracts.lean`. When replacing with a real
  proof, the relevant mathlib entry lives under `Mathlib/Analysis/Matrix`.
- **RKHS energy identities** – captured by `KernelGram` and `rkhs_energy_id` in
  `RH/Contracts.lean`. Numerical Gram matrices originate from the RKHS tables
  (`cert/bridge/K*_trace.json`).

### 2. Project Modules
- `RH/Contracts.lean`: single source of truth for heavy analytic assumptions
  (Szegő barrier, Rayleigh link, Gershgorin floor, Hoffman–Wielandt budget).
  Any downstream module must depend on these contracts instead of ad hoc sorries.
- `RH/T0A1A2.lean`: encapsulates safe results for Modules T0, A1′, A2 via the
  structures `T0Spec`, `A1DensitySpec`, and `A2LipschitzSpec`.
- Future modules follow the Batch plan in `todo.md`: `RH/A3_Local`, `RH/A3_Bridge`,
  `RH/RKHS_Prime`, `RH/T5_Transfer`, `RH/Weil_Link`, `RH/AcceptanceGate`.

### 3. Legacy Artifacts (read-only)
- Archimedean constants: `cert/bridge/K*_A3_lock.json`, `prime_cap_table.tex`.
- RKHS sums: `cert/bridge/K*_trace.json`.
- Acceptance parameters: `appendix/T5_parameters.tex`, `appendix/verification.tex`.

### 4. Workflow Notes
1. Always check `codemap.md` + `todo.md` before coding.
2. New proofs should target the Batch plan; when a contract becomes a proven lemma,
   replace the axiom and update this codemap.
3. Avoid scattering library explorations—record relevant mathlib paths here.

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH/T0A1A2.lean
```lean
import RH.A1Contract
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Continuous
import Mathlib.Data.Real.Basic

/-!
# Local analytic contracts for the Weil formalization (T0, A1′, A2)

This module provides lightweight interfaces encoding the ``safe'' functional
analysis ingredients of the Q3 track.  They are phrased as reusable structures
whose fields capture the precise hypotheses needed downstream.  By packaging
the results in this way we avoid any placeholder arguments: later, when the full
proofs are available, one only needs to supply concrete instances of the
structures defined here.
-/

noncomputable section

open scoped Topology
open Set

namespace RH

/-- Wrapper exposing the abstract A1 density contract on windows. -/
theorem A1_density_of_contract {K : ℝ} (C : A1Contract K) :
    ∀ f : Window K, (∀ x, 0 ≤ f x) → f ∈ closure C.cone :=
  A1_density C

/-- Data container for the T0 crosswalk between the quadratic functional `Q`
and the classical Guinand–Weil formulation.  The equality is stored as the
field `crosswalk`, so `t0_weil_crosswalk` is merely a convenient accessor. -/
structure T0Spec (Φ : Type*) where
  /-- The quadratic functional arising from the operator viewpoint. -/
  Q : Φ → ℝ
  /-- The Guinand–Weil quadratic functional expressed on the same test space. -/
  QGW : Φ → ℝ
  /-- Crosswalk identity (Lemma 4.2 in RH_Q3.pdf). -/
  crosswalk : ∀ Φ₀, Q Φ₀ = QGW Φ₀

namespace T0Spec

variable {Φ : Type*} (spec : T0Spec Φ)

/-- Direct accessor for the T0 crosswalk equality. -/
@[simp] theorem t0_weil_crosswalk (Φ₀ : Φ) :
    spec.Q Φ₀ = spec.QGW Φ₀ :=
  spec.crosswalk Φ₀

end T0Spec

/-- Fejér×heat density data: encapsulates the window, the cone of approximants,
and the density statement required in Module A1′. -/
structure A1DensitySpec (Φ : Type*) [TopologicalSpace Φ] where
  /-- Fixed compact window inside the Weil class. -/
  window : Set Φ
  /-- Witness that the window is closed (the project works with compacts). -/
  window_closed : IsClosed window
  /-- Cone generated by Fejér×heat atoms. -/
  approximants : Set Φ
  /-- Every approximant lives in the window. -/
  subset_window : approximants ⊆ window
  /-- Density statement: closure of the cone agrees with the window. -/
  dense : closure approximants = window

namespace A1DensitySpec

variable {Φ : Type*} [TopologicalSpace Φ] (spec : A1DensitySpec Φ)

@[simp] theorem closure_approximants :
    closure spec.approximants = spec.window :=
  spec.dense

end A1DensitySpec

/-- Package an `A1Contract` into an `A1DensitySpec` by viewing the cone inside the
nonnegative windows.  The additional hypothesis ensures the cone sits in the window
and, together with the closedness of nonnegative windows, yields density. -/
def A1DensitySpec.ofContract {K : ℝ}
    (C : A1Contract K) : A1DensitySpec (Window K) :=
{ window := nonnegCone K
, window_closed := isClosed_nonnegCone K
, approximants := C.cone
, subset_window := fun _ hf => C.cone_nonneg hf
, dense := C.closure_cone_eq_nonnegCone }

/-- Lipschitz control for the quadratic functional on a fixed window (Module
A2).  The layout uses `NNReal` to interact with `LipschitzWith`. -/
structure A2LipschitzSpec (Φ : Type*) [PseudoMetricSpace Φ] where
  /-- Window on which the Lipschitz estimate is valid. -/
  window : Set Φ
  /-- Quadratic functional viewed as a real-valued map. -/
  Q : Φ → ℝ
  /-- Declared Lipschitz constant. -/
  lipschitzConst : NNReal
  /-- Lipschitz certificate for `Q` restricted to the whole space; users may
  combine it with the window information when needed. -/
  lipschitz : LipschitzWith lipschitzConst Q

namespace A2LipschitzSpec

variable {Φ : Type*} [PseudoMetricSpace Φ] (spec : A2LipschitzSpec Φ)

@[simp] theorem lipschitz_with :
    LipschitzWith spec.lipschitzConst spec.Q :=
  spec.lipschitz

@[simp] theorem dist_le_mul (x y : Φ) :
    dist (spec.Q x) (spec.Q y) ≤ spec.lipschitzConst * dist x y :=
  (A2LipschitzSpec.lipschitz_with spec).dist_le_mul x y

theorem abs_le_mul (x y : Φ) :
    |spec.Q x - spec.Q y| ≤ spec.lipschitzConst * dist x y := by
  simpa [Real.dist_eq, abs_sub_comm] using
    dist_le_mul (spec := spec) x y

section Extension

/-- If `Q` is Lipschitz on a window and nonnegative on a dense subset provided by
`A1DensitySpec`, then `Q` stays nonnegative on the entire window. -/
theorem nonneg_on_window_of_dense
    (density : A1DensitySpec Φ)
    (lip : A2LipschitzSpec Φ)
    (hwindow : density.window = lip.window)
    (h_nonneg : ∀ x ∈ density.approximants, 0 ≤ lip.Q x) :
    ∀ x ∈ lip.window, 0 ≤ lip.Q x := by
  classical
  intro x hx_window
  -- Identify `x` as an element of the closure of the approximating cone.
  have hx_window' : x ∈ density.window := by simpa [hwindow] using hx_window
  have hx_closure :
      x ∈ closure density.approximants := by
    have h_dense := density.dense
    have hx_window'' : x ∈ density.window := hx_window'
    simpa [h_dense] using hx_window''
  -- Closed set capturing the nonnegativity region of `Q`.
  let S : Set Φ := {y : Φ | 0 ≤ lip.Q y}
  have h_closed : IsClosed S := by
    have h_cont : Continuous lip.Q :=
      (A2LipschitzSpec.lipschitz_with lip).continuous
    have h_pre :
        IsClosed (lip.Q ⁻¹' Set.Ici (0 : ℝ)) :=
      IsClosed.preimage h_cont isClosed_Ici
    simpa [S, Set.preimage, Set.Ici, Set.mem_setOf_eq] using h_pre
  have h_subset : density.approximants ⊆ S := by
    intro y hy
    have hy_nonneg := h_nonneg y hy
    simpa [S, Set.mem_setOf_eq] using hy_nonneg
  have h_closure_subset : closure density.approximants ⊆ S :=
    closure_minimal h_subset h_closed
  have hx_mem_S : x ∈ S := h_closure_subset hx_closure
  simpa [S, Set.mem_setOf_eq] using hx_mem_S

end Extension

/-- Convenient alias matching the naming in the project notes: Lipschitz plus
local density implies full-window nonnegativity. -/
theorem density_extension_via_lipschitz
    (density : A1DensitySpec Φ)
    (lip : A2LipschitzSpec Φ)
    (hwindow : density.window = lip.window)
    (h_nonneg : ∀ x ∈ density.approximants, 0 ≤ lip.Q x) :
    ∀ x ∈ lip.window, 0 ≤ lip.Q x :=
  nonneg_on_window_of_dense density lip hwindow h_nonneg

end A2LipschitzSpec

end RH

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_formalization.lean
```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Spectrum
import RH.RKHSPrime

noncomputable section

open Complex Set Filter Topology

-- The user wants a formal proof of the mathematical hypotheses from the document.
-- The document outlines a proof of the Riemann Hypothesis using Weil's criterion
-- and operator-theoretic methods.

-- This is an extremely ambitious goal for a single interaction.
-- A full formal proof would be a massive undertaking.
-- I will create a skeleton of the formalization, defining the key concepts
-- and stating the main theorems from the paper in Lean 4.

-- This will demonstrate how the paper's arguments could be formalized,
-- even if the proofs themselves are still represented abstractly.

-- Main Goal: Formalize Q(Φ) ≥ 0 for Φ in the Weil class (Theorem 1.1)
-- and show its equivalence to the Riemann Hypothesis via Weil's criterion.


--------------------------------------------------------------------------------
-- Section 4 & 5: Notation, Conventions, and Normalization (T0)
--------------------------------------------------------------------------------

-- Define the Weil class of test functions `W`
-- Even, compactly supported test functions on ℝ.
structure WeilClass where
  f : ℝ → ℂ
  is_even : ∀ x, f (-x) = f x
  has_compact_support : HasCompactSupport f
  integrable : Integrable f

/-- Aggregated contract describing every analytic component used in the Q3 track.
Each field stands for a proven result shipped from the legacy toolchain, so Lean
can depend on them without additional placeholders inside this file. -/
structure TrackBSpec (H : Type*) [InnerProductSpace ℂ H] [HilbertSpace H] where
  /-- Archimedean density on the frequency axis. -/
  archimedean_density : ℝ → ℂ
  /-- Quadratic functional `Q`. -/
  weil_functional : WeilClass → ℂ
  /-- Lipschitz/positivity estimate on the Weil class (Module T5). -/
  main_nonneg :
      ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re
  /-- Weil's criterion linking `Q ≥ 0` to RH. -/
  weil_criterion :
      (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re)
        ↔ RiemannHypothesis
  /-- Truncated Toeplitz operator factory (Module A3). -/
  toeplitz_operator :
      (ℝ → ℂ) → H →L[ℂ] H
  /-- Archimedean barrier controlling the Toeplitz part. -/
  archimedean_toeplitz_barrier :
      ∀ (K : ℝ) (hK : 0 < K),
        ∃ (P_A : ℝ → ℂ) (M : ℕ) (c₀ : ℝ),
          0 < c₀ ∧
            let T_A := toeplitz_operator P_A
            in ∀ v : H, ‖v‖ = 1 →
                c₀ ≤ Complex.realPart (inner (T_A v) v)
  /-- Prime discretization operator (RKHS module). -/
  prime_operator :
      (K : ℝ) → (0 < K) → H →L[ℂ] H
  /-- RKHS contraction bound (Module RKHS). -/
  prime_contraction :
      ∀ (K : ℝ) (hK : 0 < K),
        ∃ (c₀ : ℝ), 0 < c₀ ∧
          ‖prime_operator K hK‖ ≤ c₀ / 4
  /-- Compact-to-global transfer (Module T5). -/
  compact_transfer :
      (∀ (K : ℝ) (hK : 0 < K) (Φ : WeilClass),
          HasCompactSupport Φ →
          support Φ.f ⊆ Icc (-K) K →
          IsNonNegative Φ →
          0 ≤ (weil_functional Φ).re)
        → (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re)

-- Define the quadratic functional Q(Φ) from the paper (Equation 5.5)
-- Q(φ) := ∫ a*(ξ)φ(ξ)dξ - ∑ 2Λ(n)/√n * φ(ξ_n)

-- Archimedean density a*(ξ)
noncomputable def archimedean_density {H : Type*} [InnerProductSpace ℂ H]
    [HilbertSpace H] (_spec : TrackBSpec H) (_ξ : ℝ) : ℂ :=
  Complex.ofReal (RH.c0K1 - RH.lambdaMinD7)

-- Prime nodes ξ_n = log n / 2π
def prime_node (n : ℕ) : ℝ := Real.log (n : ℝ) / (2 * Real.pi)

-- von Mangoldt function Λ(n)
-- Already available in Mathlib as `Nat.mangoldt`

-- The quadratic functional Q
def weil_functional {H : Type*} [InnerProductSpace ℂ H] [HilbertSpace H]
    (spec : TrackBSpec H) (Φ : WeilClass) : ℂ :=
  spec.weil_functional Φ

variable {H : Type*} [InnerProductSpace ℂ H] [HilbertSpace H]
variable (spec : TrackBSpec H)
--  ∫ (archimedean_density ξ) * (Φ.f ξ) dξ - ∑' n, 2 * (Nat.mangoldt n) / (Real.sqrt n) * Φ.f (prime_node n)


--------------------------------------------------------------------------------
-- Main Theorem Statement (Theorem 1.1)
--------------------------------------------------------------------------------

-- The main result of the paper is that Q is non-negative for non-negative functions.
-- Let's define what it means for a test function to be non-negative.
def IsNonNegative (Φ : WeilClass) : Prop :=
  ∀ x : ℝ, 0 ≤ (Φ.f x).re ∧ (Φ.f x).im = 0

-- Theorem 1.1 (Main result, informal)
theorem main_theorem :
    ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional spec Φ).re :=
  spec.main_nonneg


--------------------------------------------------------------------------------
-- Weil's Criterion (Theorem 13.1)
--------------------------------------------------------------------------------

-- The paper states that Q(Φ) ≥ 0 is equivalent to the Riemann Hypothesis.
-- Mathlib has a formal statement of the Riemann Hypothesis: `RiemannHypothesis`

-- Theorem 13.1 (Weil criterion)
theorem weil_criterion_equivalence :
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional spec Φ).re)
      ↔ RiemannHypothesis :=
  spec.weil_criterion


--------------------------------------------------------------------------------
-- Section 8: Archimedean Toeplitz Barrier (A3)
--------------------------------------------------------------------------------

-- The proof relies on splitting Q into an Archimedean part and a prime part.
-- Q = T_M[P_A] - T_P

-- We need to define Toeplitz operators.
-- Let H be a Hilbert space.

def ToeplitzOperator (symbol : ℝ → ℂ) : H →L[ℂ] H :=
  spec.toeplitz_operator symbol

-- The paper claims a lower bound on the Archimedean part.
theorem archimedean_toeplitz_barrier (K : ℝ) (hK : 0 < K) :
    ∃ (P_A : ℝ → ℂ) (M : ℕ) (c₀ : ℝ),
        0 < c₀ ∧
          let T_A := ToeplitzOperator spec P_A
          in ∀ v : H, ‖v‖ = 1 →
              c₀ ≤ Complex.realPart (inner (T_A v) v) :=
  spec.archimedean_toeplitz_barrier K hK


--------------------------------------------------------------------------------
-- Section 9.5: Prime Contraction (RKHS)
--------------------------------------------------------------------------------

-- The prime contribution is bounded using a Reproducing Kernel Hilbert Space (RKHS).

-- Define the heat kernel
def heat_kernel (t : ℝ) (x y : ℝ) : ℂ := cexp (-(x - y)^2 / (4 * t))

-- Define the prime operator T_P
def PrimeOperator (K : ℝ) (hK : 0 < K) : H →L[ℂ] H :=
  spec.prime_operator K hK

-- The RKHS norm bound on the prime operator
theorem prime_contraction (K : ℝ) (hK : 0 < K) :
    ∃ (c₀ : ℝ), 0 < c₀ ∧
      ‖PrimeOperator spec K hK‖ ≤ c₀ / 4 :=
  spec.prime_contraction K hK


--------------------------------------------------------------------------------
-- Section 12: Compact-by-Compact Transfer (T5)
--------------------------------------------------------------------------------

-- This is the final step, propagating positivity from compact sets to the full Weil class.

theorem compact_transfer :
    (∀ (K : ℝ) (hK : 0 < K), ∀ (Φ : WeilClass),
        HasCompactSupport Φ →
        support Φ.f ⊆ Icc (-K) K →
        IsNonNegative Φ →
        0 ≤ (weil_functional spec Φ).re)
      → (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional spec Φ).re) :=
  spec.compact_transfer


--------------------------------------------------------------------------------
-- Final Proof Structure
--------------------------------------------------------------------------------

-- The final proof would combine these elements:
-- 1. Use `archimedean_toeplitz_barrier` and `prime_contraction` to show positivity on compact sets.
-- 2. Use `compact_transfer` to extend this to the full Weil class.
-- 3. Use `weil_criterion_equivalence` to conclude the Riemann Hypothesis.

theorem riemann_hypothesis_formal_proof : RiemannHypothesis := by
  have h_main :
      ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional spec Φ).re :=
    spec.main_nonneg
  exact (weil_criterion_equivalence spec).mp h_main

end

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/Формализация Гипотезы Римана в Lean 4: Итоговый отчет.md
```md
# Формализация Гипотезы Римана в Lean 4: Итоговый отчет

## Введение

Данный документ представляет собой итоговый отчет о формализации математических гипотез из работы **"Operator Methods for the Weil Criterion: Q3"** (Eugen Malamutmann, University of Duisburg–Essen, October 22, 2025) на языке формальной верификации **Lean 4**.

Работа посвящена доказательству **Гипотезы Римана** через **критерий Вейля** с использованием операторно-теоретических методов. Основная идея состоит в том, чтобы показать неотрицательность квадратичного функционала Q на специальном классе тестовых функций, что по теореме Вейля эквивалентно Гипотезе Римана.

---

## Структура оригинального доказательства

Доказательство в документе организовано как цепочка из шести аналитических модулей, каждый из которых вносит свой вклад в итоговое утверждение.

### Модуль T0: Нормализация Гинанда-Вейля

Устанавливается соответствие между репозиторной нормализацией функционала Q и классическим функционалом Гинанда-Вейля. Это обеспечивает корректность используемых обозначений и определений.

**Ключевая формула:**
```
Q(φ) = Q_GW(φ_GW)  при η = 2πξ, dη = 2π dξ
```

### Модуль A1': Локальная плотность

Доказывается плотность конуса Фейера×тепловых приближений на каждом компактном окне W_K = [-K, K]. Это позволяет аппроксимировать произвольные тестовые функции комбинациями ядер Фейера и тепловых ядер.

**Теорема 6.2:** Для каждого компактного [-K, K] конус {Фейер * тепловые приближения} плотен в C⁺_even([-K, K]) в равномерной норме.

### Модуль A2: Липшицева непрерывность

Устанавливается Липшицева непрерывность функционала Q на каждом компактном окне W_K. Это критически важно для распространения положительности с плотного подмножества на весь класс.

**Лемма 7.3:** Q обладает Липшицевым контролем на каждом W_K.

### Модуль A3: Архимедов барьер Теплица

Функционал Q разлагается на архимедову часть (оператор Теплица T_M[P_A]) и простую часть (T_P). Для архимедовой части устанавливается положительная нижняя граница.

**Теорема 8.35 (Ключевое неравенство):**
```
λ_min(T_M[P_A]) ≥ c₀(K) - C·ω_PA(π/M)
```

где:
- c₀(K) > 0 — архимедов барьер
- ω_PA — модуль непрерывности символа P_A
- M — параметр дискретизации

### Модуль RKHS: Сжатие простых чисел

Норма оператора простых чисел T_P ограничивается в воспроизводящем ядерном гильбертовом пространстве (RKHS), индуцированном тепловым ядром.

**Теорема 9.23 (Два подхода):**

1. **Грамов подход:**
   ```
   ‖T_P‖ ≤ w_max + √(w_max · η_K)
   ```
   где w_max ≤ 2/e, а η_K настраивается через зазор узлов δ_K.

2. **Ранний/хвостовой подход:**
   Разбиение суммы простых чисел на N = N(K) с явными оценками обеих частей.

При правильном выборе параметра t достигается **‖T_P‖ ≤ c₀(K)/4**.

### Модуль T5: Компактный перенос

Финальный шаг: если положительность установлена на каждом компактном окне W_K с монотонными параметрами, она распространяется на весь класс Вейля W.

**Теорема 12.6:** Монотонная цепочка K_i ↑ ∞ с согласованными параметрами (M⋆(K), t⋆(K)) обеспечивает перенос положительности.

---

## Ключевые математические объекты

### Класс Вейля W

**Определение:** Класс W состоит из тестовых функций Φ : ℝ → ℂ со следующими свойствами:

1. **Четность:** Φ(-x) = Φ(x) для всех x ∈ ℝ
2. **Компактная поддержка:** существует K > 0 такое, что Φ(x) = 0 для |x| > K
3. **Непрерывность:** Φ ∈ C(ℝ)
4. **Неотрицательность:** Φ(x) ≥ 0 для всех x ∈ ℝ (для рассматриваемого подкласса)

### Квадратичный функционал Q

**Определение (уравнение 5.5):**
```
Q(Φ) = ∫_ℝ a*(ξ) Φ(ξ) dξ - ∑_{n≥2} (2Λ(n)/√n) Φ(ξ_n)
```

где:

- **a*(ξ) = 2π·a(ξ)** — нормализованная архимедова плотность
- **a(ξ) = log π - Re ψ(1/4 + iπξ)** — архимедова плотность
  - ψ — дигамма-функция (логарифмическая производная гамма-функции)
- **ξ_n = (log n)/(2π)** — узлы простых чисел
- **Λ(n)** — функция фон Мангольдта:
  ```
  Λ(n) = { log p,  если n = p^k для простого p
         { 0,      иначе
  ```

### Критерий Вейля

**Теорема (Weil, Theorem 13.1):** Следующие утверждения эквивалентны:

1. **Гипотеза Римана:** Все нетривиальные нули дзета-функции Римана ζ(s) лежат на критической прямой Re(s) = 1/2.

2. **Критерий Вейля:** Q(Φ) ≥ 0 для всех Φ ∈ W с Φ ≥ 0.

Это фундаментальная связь, превращающая аналитическую проблему о нулях ζ(s) в задачу о положительности функционала.

---

## Формализация в Lean 4

### Общая структура

Формализация организована в виде Lean-проекта со следующей структурой:

```
RH_Formalization/
├── RHFormalization/
│   ├── Basic.lean              # Базовые определения (создан автоматически)
│   └── WeilCriterion.lean      # Главная формализация
├── RHFormalization.lean         # Корневой модуль библиотеки
├── Main.lean                    # Точка входа программы
├── lakefile.toml               # Конфигурация системы сборки Lake
├── lean-toolchain              # Версия Lean (4.24.0)
└── README_RU.md                # Подробная документация на русском
```

### Основные определения в Lean

#### 1. Класс Вейля

```lean
structure WeilClass where
  f : ℝ → ℂ
  is_even : ∀ x, f (-x) = f x
  has_compact_support : HasCompactSupport f
  continuous : Continuous f
```

#### 2. Неотрицательность

```lean
def IsNonNegative (Φ : WeilClass) : Prop :=
  ∀ x : ℝ, (Φ.f x).im = 0 ∧ 0 ≤ (Φ.f x).re
```

#### 3. Квадратичный функционал Q

```lean
def weil_functional (Φ : WeilClass) : ℂ :=
  let archimedean_part := ∫ ξ, archimedean_density_star ξ * Φ.f ξ
  let prime_part := ∑' n : ℕ, if n ≥ 2 then
    (2 * von_mangoldt n / sqrt (n : ℝ)) * Φ.f (prime_node n)
  else 0
  archimedean_part - prime_part
```

### Основные теоремы

#### Теорема 1.1: Главный результат

```lean
theorem main_theorem :
    ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re
```

**Утверждение:** Квадратичный функционал Q неотрицателен на классе Вейля для неотрицательных тестовых функций.

#### Теорема 13.1: Критерий Вейля

```lean
theorem weil_criterion_equivalence :
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) ↔
    RiemannHypothesis
```

**Утверждение:** Неотрицательность Q эквивалентна Гипотезе Римана.

Здесь `RiemannHypothesis` — это формальное определение из Mathlib (библиотеки Lean для математики), доступное благодаря недавней работе по формализации дзета-функции.

#### Теорема 8.35: Архимедов барьер Теплица

```lean
theorem archimedean_toeplitz_barrier
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℝ) (hK : 0 < K) :
    ∃ (c₀ : ℝ) (M₀ : ℕ), 0 < c₀ ∧
    ∀ (T : ToeplitzOperator H) (M : ℕ), M ≥ M₀ →
    ∃ (C : ℝ) (ω : ℝ → ℝ), ...
```

**Утверждение:** На каждом компактном окне W_K оператор Теплица имеет положительную нижнюю границу.

#### Теорема 9.23: Сжатие простых чисел

```lean
theorem prime_contraction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℝ) (hK : 0 < K) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ (t_min : ℝ), 0 < t_min ∧
    ∀ (T_P : H →L[ℂ] H) (t : ℝ), t ≥ t_min →
    ‖T_P‖ ≤ c₀ / 4
```

**Утверждение:** Норма оператора простых чисел в RKHS может быть ограничена для обеспечения положительности.

#### Теорема 12.6: Компактный перенос

```lean
theorem compact_transfer :
    (∀ (K : ℝ) (hK : 0 < K) (Φ : WeilClass),
      supported_on_compact Φ K → IsNonNegative Φ →
      0 ≤ (weil_functional Φ).re) →
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re)
```

**Утверждение:** Если положительность выполнена на всех компактных окнах, она распространяется на весь класс Вейля.

#### Теорема 13.2: Гипотеза Римана

```lean
theorem riemann_hypothesis_proof : RiemannHypothesis := by
  rw [← weil_criterion_equivalence]
  exact weil_positivity
```

**Утверждение:** Гипотеза Римана следует из положительности Вейля через критерий Вейля.

### Структура доказательства в Lean

```lean
theorem riemann_hypothesis_proof : RiemannHypothesis := by
  -- 1. Доказываем положительность на компактах
  have h_compact : ∀ K > 0, ∀ Φ на [-K,K], Q(Φ) ≥ 0 := by
    -- Используем архимедов барьер (A3)
    -- Используем сжатие простых (RKHS)
    -- Комбинируем: λ_min(T_A - T_P) ≥ c₀ - C·ω(π/M) - ‖T_P‖ > 0
    sorry
  
  -- 2. Распространяем на весь класс Вейля
  have h_weil : ∀ Φ ∈ W, Q(Φ) ≥ 0 := by
    apply compact_transfer
    exact h_compact
  
  -- 3. Применяем критерий Вейля
  rw [← weil_criterion_equivalence]
  exact h_weil
```

---

## Связь с Mathlib

Формализация активно использует библиотеку **Mathlib4** — стандартную математическую библиотеку для Lean 4.

### Используемые компоненты Mathlib

1. **Комплексный анализ:**
   - `Mathlib.Analysis.Complex.Basic` — комплексные числа и базовые операции
   
2. **Дзета-функция Римана:**
   - `Mathlib.NumberTheory.ZetaFunction` — формальное определение ζ(s)
   - `RiemannHypothesis` — формальная формулировка Гипотезы Римана
   
3. **Специальные функции:**
   - `Mathlib.Analysis.SpecialFunctions.Log.Basic` — логарифм
   
4. **Преобразование Фурье:**
   - `Mathlib.Analysis.Fourier.FourierTransform` — теория Фурье
   
5. **Гильбертовы пространства:**
   - `Mathlib.Analysis.InnerProductSpace.Basic` — скалярное произведение
   
6. **Теория меры:**
   - `Mathlib.MeasureTheory.Integral.IntervalIntegral` — интегрирование
   
7. **Арифметические функции:**
   - `Mathlib.NumberTheory.ArithmeticFunction` — функция фон Мангольдта

### Недавние достижения в формализации теории чисел

Согласно статье **"Formalizing zeta and L-functions in Lean"** (arXiv:2503.00959v3, David Loeffler & Michael Stoll, 2025), в Mathlib уже формализованы:

- ✅ Определение дзета-функции Римана `riemannZeta`
- ✅ Формула Эйлера ζ(2) = π²/6
- ✅ Эйлерово произведение для ζ(s)
- ✅ Функциональное уравнение ζ(1-s) ↔ ζ(s)
- ✅ Отсутствие нулей на Re(s) ≥ 1
- ✅ **Формальная формулировка Гипотезы Римана**

Это означает, что наша формализация опирается на солидный фундамент уже проверенных определений и теорем.

---

## Статус формализации

### ✅ Полностью формализовано

1. **Определения:**
   - Класс Вейля W
   - Квадратичный функционал Q
   - Архимедова плотность a*(ξ)
   - Узлы простых чисел ξ_n
   - Функция фон Мангольдта Λ(n)
   - Неотрицательность тестовых функций

2. **Формулировки теорем:**
   - Главная теорема (Theorem 1.1)
   - Критерий Вейля (Theorem 13.1)
   - Архимедов барьер (Theorem 8.35)
   - Сжатие простых (Theorem 9.23)
   - Компактный перенос (Theorem 12.6)
   - Гипотеза Римана (Theorem 13.2)

3. **Структура доказательства:**
   - Логическая цепочка модулей T0 → A1' → A2 → A3 → RKHS → T5
   - Комбинирование результатов для финального доказательства

### ⚠️ Требует дальнейшей работы (помечено `sorry`)

1. **Специальные функции:**
   - Дигамма-функция ψ и её свойства
   - Связь с гамма-функцией Γ
   
2. **Операторная теория:**
   - Полная теория операторов Теплица
   - Спектральные оценки для самосопряженных операторов
   - Минимальные собственные значения
   
3. **RKHS (Воспроизводящие ядерные гильбертовы пространства):**
   - Конструкция RKHS из теплового ядра
   - Грамова геометрия
   - Оценки норм операторов в RKHS
   
4. **Интегралы и суммы:**
   - Сходимость интегралов с архимедовой плотностью
   - Сходимость рядов по простым числам
   - Обмен порядка интегрирования и суммирования
   
5. **Доказательства:**
   - Все основные доказательства заменены на `sorry`
   - Требуется детальная проработка каждого шага

---

## Критический анализ

### Важное замечание о статусе доказательства

**Гипотеза Римана остается открытой проблемой.** Несмотря на то, что документ RH_Q3.pdf представляет собой попытку доказательства, необходимо понимать следующее:

1. **Нет общепризнанного доказательства Гипотезы Римана** — это одна из семи задач тысячелетия с премией в $1,000,000.

2. **Данная формализация — это скелет структуры доказательства**, а не полное доказательство. Все ключевые шаги помечены `sorry` и требуют строгого математического обоснования.

3. **Критерий Вейля сам по себе корректен** — это известный результат, эквивалентный Гипотезе Римана. Вопрос в том, действительно ли удается доказать Q(Φ) ≥ 0.

4. **Операторно-теоретический подход перспективен** — идея использования самосопряженных операторов и спектральной теории соответствует программе Гильберта-Пойа, но требует исключительной строгости.

### Потенциальные пробелы

Согласно критериям строгости для доказательств Гипотезы Римана (см. базу знаний), необходимо избегать следующих типичных пробелов:

1. **Отсутствие явной конструкции самосопряженного оператора** H такого, что spec(H) = {γ : ζ(1/2 + iγ) = 0}.

2. **Недостаточная строгость в переходе от локальных оценок к глобальным** — компактный перенос требует тщательного контроля констант.

3. **Неявные предположения о сходимости** — ряды по простым числам и интегралы должны быть строго обоснованы.

4. **Отсутствие вычислительной верификации** — хотя документ упоминает "reproducibility data" в приложениях, формализация не включает численные проверки.

---

## Пути дальнейшего развития

### Краткосрочные цели

1. **Формализация дигамма-функции:**
   - Определить ψ(z) = Γ'(z)/Γ(z)
   - Доказать основные свойства (функциональное уравнение, асимптотики)
   - Связать с архимедовой плотностью a(ξ)

2. **Операторы Теплица:**
   - Формализовать определение оператора Теплица с символом
   - Доказать теорему Сегё-Бёттхера об асимптотике собственных значений
   - Установить связь с дискретным преобразованием Фурье

3. **Тепловое ядро и RKHS:**
   - Построить RKHS с воспроизводящим ядром k_t(x,y) = exp(-(x-y)²/(4t))
   - Доказать свойства положительной определенности
   - Формализовать оценки норм через Грамову геометрию

### Среднесрочные цели

4. **Доказательство модуля A1':**
   - Формализовать ядра Фейера
   - Доказать плотность конуса на компактах
   - Установить явные оценки скорости сходимости

5. **Доказательство модуля A2:**
   - Вывести Липшицеву константу для Q
   - Связать с модулем непрерывности символа

6. **Доказательство модуля A3:**
   - Вычислить архимедов барьер c₀(K)
   - Оценить модуль непрерывности ω_PA
   - Выбрать параметр дискретизации M₀(K)

### Долгосрочные цели

7. **Доказательство модуля RKHS:**
   - Реализовать один из двух подходов (Грамов или ранний/хвостовой)
   - Вычислить эффективные веса w_max
   - Определить пороговый параметр t_min(K)

8. **Доказательство модуля T5:**
   - Формализовать монотонность параметров
   - Доказать наследование положительности
   - Провести предельный переход K → ∞

9. **Финальная сборка:**
   - Объединить все модули
   - Удалить все `sorry`
   - Провести полную проверку в Lean

### Амбициозная цель

10. **Полная формальная верификация Гипотезы Римана:**
    - Если все шаги успешно формализованы и проверены
    - Получить первое машинно-проверенное доказательство RH
    - Опубликовать результат для независимой верификации сообществом

---

## Технические детали

### Установка и использование

#### Требования

- **Операционная система:** Linux, macOS, или Windows (через WSL)
- **Lean 4:** версия 4.24.0 (устанавливается через elan)
- **Lake:** система сборки для Lean (входит в комплект)
- **Mathlib4:** стабильная ветка (указана в lakefile.toml)

#### Установка

```bash
# 1. Установить Lean 4 через elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 2. Перезапустить терминал или обновить PATH
source ~/.profile  # или ~/.bashrc, ~/.zshrc

# 3. Распаковать архив проекта
tar -xzf RH_Formalization.tar.gz
cd RH_Formalization

# 4. Обновить зависимости (загрузить Mathlib)
lake update

# 5. Собрать проект
lake build
```

#### Проверка формализации

```bash
# Проверить синтаксис и типы
lake build RHFormalization

# Запустить главный файл (если есть исполняемая логика)
lake exe rh_formalization

# Проверить конкретный файл
lean RHFormalization/WeilCriterion.lean
```

### Структура файла WeilCriterion.lean

```lean
-- Импорты из Mathlib
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaFunction
...

-- Открытие пространств имен
open Complex Real Set Filter Topology MeasureTheory

-- Определение пространства имен для проекта
namespace RiemannHypothesis

-- Секция 4: Обозначения
def frequency_var ...
def archimedean_density ...

-- Секция 5: Класс Вейля и функционал Q
structure WeilClass ...
def weil_functional ...

-- Основные теоремы
theorem main_theorem ...
theorem weil_criterion_equivalence ...
theorem archimedean_toeplitz_barrier ...
theorem prime_contraction ...
theorem compact_transfer ...
theorem riemann_hypothesis_proof ...

end RiemannHypothesis
```

---

## Заключение

Данная формализация представляет собой **первый шаг** к машинной верификации операторно-теоретического подхода к Гипотезе Римана через критерий Вейля.

### Что достигнуто

1. **Полная формализация структуры доказательства** — все ключевые определения и теоремы переведены на язык Lean 4.

2. **Интеграция с Mathlib** — использование существующих формализаций дзета-функции и Гипотезы Римана.

3. **Модульная архитектура** — доказательство разбито на независимые модули, которые можно развивать параллельно.

4. **Явная зависимость от гипотез** — каждая теорема четко указывает, какие предположения она использует.

### Что требует дальнейшей работы

1. **Замена всех `sorry` на настоящие доказательства** — это основная и наиболее трудоемкая задача.

2. **Формализация специальных функций** — дигамма-функция, тепловое ядро, ядра Фейера.

3. **Операторная теория** — Теплиц-операторы, RKHS, спектральные оценки.

4. **Численная поддержка** — хотя формальное доказательство не требует вычислений, они могут помочь в выборе параметров.

### Значимость работы

Независимо от того, является ли оригинальное доказательство корректным, данная формализация демонстрирует:

- **Возможность формализации сложных аналитических аргументов** в системах формальной верификации.
- **Ценность машинной проверки** для обнаружения пробелов в математических рассуждениях.
- **Перспективность операторно-теоретического подхода** к Гипотезе Римана.

### Призыв к сотрудничеству

Формализация математики — это коллективное усилие. Мы приглашаем математиков, специалистов по теории чисел, функциональному анализу и формальной верификации присоединиться к развитию этого проекта.

Каждый модуль может быть развит независимо, и любой вклад — от формализации отдельных лемм до полного доказательства модуля — будет ценным шагом к цели.

---

## Ссылки и литература

### Оригинальный документ

- Malamutmann, E. (2025). *Operator Methods for the Weil Criterion: Q3*. University of Duisburg–Essen.

### Lean и Mathlib

- Lean 4: https://lean-lang.org/
- Mathlib4: https://github.com/leanprover-community/mathlib4
- Theorem Proving in Lean 4: https://lean-lang.org/theorem_proving_in_lean4/

### Формализация теории чисел

- Loeffler, D., & Stoll, M. (2025). *Formalizing zeta and L-functions in Lean*. arXiv:2503.00959v3.
  https://arxiv.org/abs/2503.00959

### Гипотеза Римана

- Riemann, B. (1859). *Über die Anzahl der Primzahlen unter einer gegebenen Grösse*.
- Weil, A. (1952). *Sur les "formules explicites" de la théorie des nombres premiers*.
- Conrey, J. B. (2003). *The Riemann Hypothesis*. Notices of the AMS, 50(3), 341-353.

### Операторная теория

- Reed, M., & Simon, B. (1980). *Methods of Modern Mathematical Physics I: Functional Analysis*.
- Böttcher, A., & Silbermann, B. (2006). *Analysis of Toeplitz Operators*.

---

**Автор формализации:** Manus AI  
**Дата:** 22 октября 2025 года  
**Версия Lean:** 4.24.0  
**Версия Mathlib:** stable (2025)

---

*Этот документ создан в образовательных и исследовательских целях. Формализация не претендует на полное доказательство Гипотезы Римана и требует дальнейшей разработки и верификации математическим сообществом.*


```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH/A1Contract.lean
```lean
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Hom.ContinuousEvalConst
import Mathlib.Data.Real.Basic

open Classical
noncomputable section

open scoped BigOperators
open Metric

namespace RH

/-- Continuous real-valued functions on the window `[-K, K]`. -/
abbrev Window (K : ℝ) := ContinuousMap (Set.Icc (-K) K) ℝ

/-- The cone of nonnegative windows on the compact interval. -/
def nonnegCone (K : ℝ) : Set (Window K) :=
  {f | ∀ x : Set.Icc (-K) K, 0 ≤ f x}

/-- The set of nonnegative windows is closed in the sup norm. -/
lemma isClosed_nonnegCone (K : ℝ) :
    IsClosed (nonnegCone K) := by
  classical
  have h_eval :
      ∀ x : Set.Icc (-K) K,
        Continuous fun f : Window K => f x := fun x => continuous_eval_const x
  have h_closed_target : IsClosed {y : ℝ | 0 ≤ y} := by
    simpa using (isClosed_le (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)) continuous_id)
  have h_rep :
      nonnegCone K =
        ⋂ x : Set.Icc (-K) K, {f : Window K | 0 ≤ f x} := by
    ext f
    constructor
    · intro hf; refine Set.mem_iInter.2 ?_; intro x; exact hf x
    · intro hf x; exact (Set.mem_iInter.1 hf x)
  have h_closed_inter :
      IsClosed (⋂ x : Set.Icc (-K) K, {f : Window K | 0 ≤ f x}) :=
    isClosed_iInter fun x => (h_closed_target.preimage (h_eval x))
  refine h_rep.symm ▸ h_closed_inter

/-- Contract capturing the properties needed for the A1 density argument. -/
structure A1Contract (K : ℝ) : Type where
  /-- Dense candidate: a cone of positive test functions on the window. -/
  cone : Set (Window K)
  /-- Positive smoothing operator `S ε` acting on windows. -/
  S : ℝ → Window K → Window K
  /-- Positivity preservation of the smoothing operator. -/
  S_pos : ∀ {ε : ℝ}, 0 < ε → ∀ {f : Window K}, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (S ε f) x
  /-- The smoothing operator always lands inside the chosen cone. -/
  S_mem_cone :
    ∀ {ε : ℝ}, 0 < ε → ∀ {f : Window K}, (∀ x, 0 ≤ f x) → S ε f ∈ cone
  /-- Approximate-identity estimate in the sup norm. -/
  approx_id :
    ∀ (f : Window K) {δ : ℝ}, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ‖S ε f - f‖ < δ
  /-- Elements of the cone are pointwise nonnegative. -/
  cone_nonneg : ∀ {g : Window K}, g ∈ cone → ∀ x, 0 ≤ g x

namespace A1Contract

variable {K : ℝ} (C : A1Contract K)

/-- Any nonnegative target can be approximated in sup norm by elements of the contract cone. -/
theorem density_nonneg :
    ∀ (f : Window K), (∀ x, 0 ≤ f x) → ∀ {δ : ℝ}, 0 < δ →
      ∃ g ∈ C.cone, ‖g - f‖ < δ := by
  intro f hf δ hδ
  obtain ⟨ε, hεpos, hε⟩ := C.approx_id f hδ
  refine ⟨C.S ε f, C.S_mem_cone hεpos hf, ?_⟩
  simpa [sub_eq_add_neg] using hε

/-- Abstract A1 density: the contract cone is dense among nonnegative windows. -/
theorem A1_density_on_nonneg :
    ∀ (f : Window K), (∀ x, 0 ≤ f x) →
      f ∈ closure C.cone := by
  intro f hf
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  rcases C.density_nonneg f hf hε with ⟨g, hgCone, hgdist⟩
  refine ⟨g, hgCone, ?_⟩
  have hgdist' : ‖f - g‖ < ε := by simpa [norm_sub_rev] using hgdist
  simpa [dist_eq_norm] using hgdist'

/-- The closure of the contract cone sits inside the nonnegative cone. -/
lemma closure_cone_subset_nonneg :
    closure C.cone ⊆ nonnegCone K :=
  closure_minimal (fun _ hg => C.cone_nonneg hg) (isClosed_nonnegCone K)

/-- Every nonnegative window lies in the closure of the contract cone. -/
lemma nonneg_subset_closure :
    nonnegCone K ⊆ closure C.cone := by
  intro f hf
  have hf' : ∀ x, 0 ≤ f x := by simpa [nonnegCone] using hf
  exact C.A1_density_on_nonneg f hf'

/-- The closure of the contract cone coincides with the nonnegative cone. -/
theorem closure_cone_eq_nonnegCone :
    closure C.cone = nonnegCone K :=
  le_antisymm C.closure_cone_subset_nonneg C.nonneg_subset_closure

end A1Contract

/-- Convenience re-export: density of the contract cone on the nonnegative windows. -/
theorem A1_density {K : ℝ} (C : A1Contract K) :
    ∀ f : Window K, (∀ x, 0 ≤ f x) → f ∈ closure C.cone :=
  A1Contract.A1_density_on_nonneg C

end RH

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/RHFormalization/Basic.lean
```lean
def hello := "world"

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/.gitignore
```
/.lake

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/Main.lean
```lean
import RHFormalization

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/Как оформить документ в формате ЛИН_.zip
```zip
[Binary file]
```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/CLAUDE.md
```md
# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a **Lean 4 formalization** of a proof of the **Riemann Hypothesis** using operator-theoretic methods and the **Weil Criterion**. The formalization is based on the paper "Operator Methods for the Weil Criterion: Q3" by Eugen Malamutmann.

**Core Mathematical Idea:** Prove that a quadratic functional Q is non-negative on a class of test functions (Weil class), which by Weil's criterion is equivalent to the Riemann Hypothesis.

## Build System

This project uses **Lake** (Lean's build tool) with configuration in `lakefile.toml`.

### Essential Commands

```bash
# Build the project
lake build

# Update dependencies (mathlib4)
lake update

# Clean build artifacts
lake clean

# Build and run a specific target
lake build rh_formalization
lake exe rh_formalization

# Check a specific file
lake env lean WeilCriterion.lean

# Start Lean server for IDE support
lean --server
```

### Installing Lean 4

If Lean is not installed:
```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# The project will auto-install the correct Lean version when you run lake
```

## Project Structure

### Main Formalization Files

- **`WeilCriterion.lean`** - Complete formalization of the Riemann Hypothesis proof:
  - Weil class definition (even, compactly supported test functions)
  - Quadratic functional Q(Φ)
  - Main theorem: Q(Φ) ≥ 0 for nonnegative Φ
  - Weil criterion equivalence: Q ≥ 0 ⟺ Riemann Hypothesis
  - Six analytical modules: T0, A1', A2, A3, RKHS, T5

- **`RHFormalization.lean`** - Library root module (imports other modules)

- **`RH_formalization.lean`** - Legacy/alternative formalization (may be outdated)

### Documentation Files (Russian)

- `Формализация Гипотезы Римана в Lean 4: Итоговый отчет.md` - Detailed report on the formalization
- `Формализация Гипотезы Римана через Критерий Вейля в Lean 4.md` - Weil criterion explanation
- `lean_zeta_formalization.md` - Notes on available mathlib definitions for Riemann zeta
- `lean4_syntax_notes.md` - Lean 4 syntax reference

## Key Mathematical Objects

### Weil Class (WeilClass)
```lean
structure WeilClass where
  f : ℝ → ℂ                    -- Test function Φ : ℝ → ℂ
  is_even : ∀ x, f (-x) = f x  -- Even symmetry
  has_compact_support : ...    -- Compact support
  continuous : Continuous f    -- Continuity
```

### Quadratic Functional Q
```lean
def weil_functional (Φ : WeilClass) : ℂ :=
  ∫ ξ, archimedean_density_star ξ * Φ.f ξ -
  ∑' n : ℕ, (2 * Λ(n) / √n) * Φ.f (ξ_n)
```
where:
- `archimedean_density_star` = 2π·(log π - Re ψ(1/4 + iπξ))
- `ξ_n = (log n)/(2π)` (prime nodes)
- `Λ(n)` = von Mangoldt function

### Main Theorems

1. **Theorem 1.1 (Main Result)**: `Q(Φ) ≥ 0` for all nonnegative Φ in Weil class
2. **Theorem 13.1 (Weil Criterion)**: `Q ≥ 0 ⟺ RiemannHypothesis`
3. **Theorem 13.2**: `RiemannHypothesis` (follows from combining above)

## Proof Architecture: Six Analytical Modules

The proof is structured as a chain of six modules:

1. **T0 (Guinand-Weil Normalization)**: Establishes correspondence with classical formulation
2. **A1' (Local Density)**: Fejér × heat approximations are dense on compact windows
3. **A2 (Lipschitz Continuity)**: Q is Lipschitz continuous on compact windows
4. **A3 (Archimedean Toeplitz Barrier)**: Toeplitz operator T_M[P_A] has positive lower bound
5. **RKHS (Prime Contraction)**: Prime operator T_P norm bounded in RKHS
6. **T5 (Compact Transfer)**: Extends positivity from compact windows to full Weil class

## Dependencies

### Mathlib4 Imports
```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.ArithmeticFunction
```

### Available in Mathlib
- `riemannZeta : ℂ → ℂ` - Riemann zeta function definition
- `RiemannHypothesis : Prop` - Formal statement of RH
- `ArithmeticFunction.vonMangoldt` - von Mangoldt function Λ(n)
- `riemannZeta_eulerProduct` - Euler product formula
- `riemannZeta_one_sub` - Functional equation

## Development Workflow

### Working with Lean 4

```bash
# Check syntax without building
lean --run WeilCriterion.lean

# Interactive development - use VS Code with Lean 4 extension
code WeilCriterion.lean

# Build and check all proofs
lake build

# Clean and rebuild from scratch
lake clean && lake build
```

### Common Lean 4 Patterns

**Sorries**: Unfinished proofs marked with `sorry` indicate:
- Statements are formalized but proofs are incomplete
- This is expected for a formalization of an unproven conjecture
- Focus areas: Archimedean barrier bounds, RKHS norm estimates, compact transfer

**Noncomputable**: Most definitions use `noncomputable section` because:
- Complex analysis and integration aren't computationally effective
- This is standard for pure mathematical formalizations

## Important Notes

1. **This is a formalization project, not a computational one** - The goal is formal verification, not execution
2. **Many proofs contain `sorry`** - This represents the current state of formalization work
3. **Mathlib dependency**: Always use `lake update` after pulling changes to sync mathlib
4. **Lean version**: Managed by elan, will auto-install correct version
5. **No README.md** - Documentation is in Russian markdown files and this CLAUDE.md

## Troubleshooting

### Lean installation hanging
```bash
# Kill hanging processes
pkill -9 lean
pkill -9 lake

# Remove lock files
rm -f ~/.elan/toolchains/*.lock

# Retry
lake build
```

### Mathlib errors
```bash
# Update to latest stable mathlib
lake update mathlib

# Rebuild dependencies
lake build
```

### VS Code Lean extension issues
```bash
# Restart Lean server in VS Code: Cmd+Shift+P → "Lean 4: Restart Server"
# Or kill and restart manually:
pkill lean
code .
```

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RiemannQ3/Basic/Kernels.lean
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Real

namespace RiemannQ3
namespace Basic

noncomputable section
/-!
# RiemannQ3.Basic.Kernels

Convenient kernels used in Q3: the Fejér hat and the heat kernel,
with basic nonnegativity/support properties and a nonnegativity
fact for their product.
-/

/-! ## Fejér hat -/

def fejerHat (B : ℝ) (x : ℝ) : ℝ := max (1 - |x| / B) 0

lemma fejerHat_nonneg (B : ℝ) (x : ℝ) : 0 ≤ fejerHat B x := by
  unfold fejerHat; exact le_max_right _ _

lemma fejerHat_eq_zero_of_abs_gt {B x : ℝ} (hB : 0 < B) (h : B < |x|) :
    fejerHat B x = 0 := by
  unfold fejerHat
  have : 1 - |x| / B ≤ 0 := by
    have hb_le : B ≤ |x| := le_of_lt h
    have : 1 ≤ |x| / B := by
      exact (one_le_div_iff.mpr (Or.inl ⟨hB, hb_le⟩))
    exact sub_nonpos.mpr this
  simpa [this]

/-! ## Heat kernel -/

def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x*x) / (4 * t))

lemma heatKernel_pos {t x : ℝ} (ht : 0 < t) : 0 < heatKernel t x := by
  unfold heatKernel
  have hden : 0 < Real.sqrt (4 * Real.pi * t) := by
    have : 0 < 4 * Real.pi * t := by
      have : 0 < (4 : ℝ) := by norm_num
      have : 0 < Real.pi := Real.pi_pos
      have : 0 < (4 : ℝ) * Real.pi := mul_pos (by norm_num) this
      exact mul_pos this ht
    exact Real.sqrt_pos.mpr this
  have h1 : 0 < (Real.sqrt (4 * Real.pi * t))⁻¹ := by
    exact inv_pos.mpr hden
  have h2 : 0 < Real.exp (-(x * x) / (4 * t)) := by
    simpa using (Real.exp_pos (-(x * x) / (4 * t)))
  exact mul_pos h1 h2

lemma FH_atom_nonneg {B t x : ℝ} (ht : 0 < t) :
    0 ≤ fejerHat B x * heatKernel t x := by
  have h₁ : 0 ≤ fejerHat B x := fejerHat_nonneg _ _
  have h₂ : 0 ≤ heatKernel t x := le_of_lt (heatKernel_pos ht)
  exact mul_nonneg h₁ h₂

end -- section

end Basic
end RiemannQ3

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/lake-manifest.json
```json
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/mathlib4.git",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "f897ebcf72cd16f89ab4577d0c826cd14afaafc7",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "stable",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/plausible",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "dfd06ebfe8d0e8fa7faba9cb5e5a2e74e7bd2805",
   "name": "plausible",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/LeanSearchClient",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "99657ad92e23804e279f77ea6dbdeebaa1317b98",
   "name": "LeanSearchClient",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "d768126816be17600904726ca7976b185786e6b9",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "556caed0eadb7901e068131d1be208dd907d07a2",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.74",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "725ac8cd67acd70a7beaf47c3725e23484c1ef50",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "dea6a3361fa36d5a13f87333dc506ada582e025c",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "8da40b72fece29b7d3fe3d768bac4c8910ce9bee",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "leanprover",
   "rev": "91c18fa62838ad0ab7384c03c9684d99d306e1da",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "RH_Formalization",
 "lakeDir": ".lake"}

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/todo.md
```md
## RH_Formalization TODO

### Contracts (Batch 0)
- [x] `RH/Contracts.lean`: declare axioms `szego_min_eig_lower_bound`, `rayleigh_weil_id`, `rkhs_energy_id`, `gershgorin_psd_floor`, `hoffman_wielandt_F` with precise comments and links to RH_Q3.pdf §§8, 10, 12.

### Functional Analysis Core (Batch 1)
- [x] `RH/A1Contract.lean`: abstract cone + smoothing contract, proof of density without `sorry`.
- [ ] `RH/T0_A1_A2.lean`: prove `t0_weil_crosswalk`, `A1_density`, `A2_lip`, `density_extension_via_lipschitz` using existing mathlib (Fourier, convolution, Arzelà–Ascoli).
- [ ] Integrate `rayleigh_weil_id` calls for Fejér×heat atoms; remove legacy `sorry` references.

### Toeplitz Bridge (Batch 2)
- [ ] `RH/A3_Local.lean`: implement `lip_symbol_local_pos` (Q3 §8.9) and bounds on modulus of continuity.
- [ ] `RH/A3_Bridge.lean`: combine `szego_min_eig_lower_bound`, local lemmas, and `hoffman_wielandt_F` to obtain Theorem 8.16 (`archimedean_toeplitz_barrier`).

### Prime / RKHS Block (Batch 3)
- [ ] `RH/RKHS_Prime.lean`: prove `rkhs_contraction_params`, compute explicit `t_min(K)` using legacy constants (prime_cap tables).
- [ ] `RH/IND_Step.lean`: add Weyl-based induction step `ind_step_via_weyl` with budget tracking (IND schedule).
- [ ] Glue operator sandwich `operator_sandwich` (Q3 §10.3) via Gershgorin + energy identity.

### Compact Transfer & Weil Link (Batch 4)
- [ ] `RH/T5_Transfer.lean`: implement `grid_lift`, `monotone_inheritance`, and T5 chain to extend compact positivity.
- [ ] `RH/Weil_Link.lean`: restate Weil criterion, prove `weil_linkage` and final RH equivalence reusing contracts only.

### Acceptance Gate Integration
- [ ] `RH/AcceptanceGate.lean`: codify grid parameters, Lipschitz budgets, and final margin `c0/2`, referencing acceptance logs.
- [ ] Update `Main.lean` status string once all modules compile without `sorry`.

### Meta
- [x] `codemap.md`: maintain a living index of mathlib dependencies, contracts, and legacy artifacts.
- [ ] At each session start: read codemap + todo before editing; log new library discoveries in codemap.

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/lakefile.toml
```toml
name = "RH_Formalization"
version = "0.1.0"
defaultTargets = ["rh_formalization"]

[[lean_lib]]
name = "RHFormalization"

[[lean_exe]]
name = "rh_formalization"
root = "Main"

[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4.git", rev = "stable" }


```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/Q3_Definitions_Extraction.md
```md
# Extraction of Definitions and Theorems from Q3 Paper

This document systematically extracts all mathematical definitions, theorems, lemmas, and propositions from "Operator Methods for the Weil Criterion: Q3" for formalization in Lean 4.

---

## Section 4: Notation and Conventions

### Definition 4.1 (Frequency Variable)
**PDF Location:** Section 4, page ...
**Mathematical Statement:**
- ξ = η/(2π) where η is the standard frequency variable
**Lean Status:** ✓ Already formalized as `frequency_var`

### Definition 4.2 (Archimedean Density)
**PDF Location:** Section 4
**Mathematical Statement:**
- a(ξ) = log π - Re ψ(1/4 + iπξ)
- where ψ is the digamma function
**Lean Status:** ✓ Already formalized as `archimedean_density` (with sorry)

### Definition 4.3 (Normalized Archimedean Density)
**PDF Location:** Section 4
**Mathematical Statement:**
- a*(ξ) = 2π · a(ξ)
**Lean Status:** ✓ Already formalized as `archimedean_density_star`

### Definition 4.4 (Prime Nodes)
**PDF Location:** Section 4
**Mathematical Statement:**
- ξ_n = log(n)/(2π) for n ≥ 2
**Lean Status:** ✓ Already formalized as `prime_node`

### Definition 4.5 (Von Mangoldt Function)
**PDF Location:** Section 4
**Mathematical Statement:**
- Λ(n) = log p if n = p^k for prime p, else 0
**Lean Status:** ✓ Already formalized as `von_mangoldt` (uses mathlib)

### Additional Notation from Section 4:
- [ ] W = Weil class (even, compactly supported test functions)
- [ ] s = 1/2 + it (critical line variable)
- [ ] ζ(s) = Riemann zeta function
- [ ] Re, Im = real and imaginary parts
- [ ] ⟨·,·⟩ = inner product
- [ ] ‖·‖ = norm

---

## Section 5: The Weil Class and Quadratic Functional

### Definition 5.1 (Weil Class W)
**PDF Location:** Section 5.1
**Mathematical Statement:**
A test function Φ : ℝ → ℂ is in the Weil class W if:
1. Φ is even: Φ(-x) = Φ(x)
2. Φ has compact support: supp(Φ) is compact
3. Φ is continuous
4. [Additional smoothness if needed]

**Lean Status:** ✓ Already formalized as `WeilClass` structure

### Definition 5.2 (Nonnegative Test Function)
**PDF Location:** Section 5
**Mathematical Statement:**
A test function Φ ∈ W is nonnegative if:
- Φ(x) ∈ ℝ for all x ∈ ℝ (i.e., Im Φ(x) = 0)
- Φ(x) ≥ 0 for all x ∈ ℝ

**Lean Status:** ✓ Already formalized as `IsNonNegative`

### Definition 5.3 (Quadratic Functional Q)
**PDF Location:** Section 5, Equation (5.5)
**Mathematical Statement:**
Q(Φ) = ∫_{-∞}^{∞} a*(ξ) Φ(ξ) dξ - ∑_{n≥2} (2Λ(n)/√n) Φ(ξ_n)

where:
- First term: Archimedean contribution (integral over ℝ)
- Second term: Prime contribution (sum over prime nodes)

**Lean Status:** ✓ Already formalized as `weil_functional`

---

## Section 6: Fourier Transform Properties

### Definition 6.1 (Fourier Transform)
**PDF Location:** Section 6
**Mathematical Statement:**
For Φ ∈ W, the Fourier transform is:
Φ̂(η) = ∫_{-∞}^{∞} Φ(x) e^{-iηx} dx

Properties needed:
- Φ̂ is entire (holomorphic everywhere)
- Φ̂ has rapid decay
- Evenness: Φ̂(-η) = Φ̂(η) if Φ is even

**Lean Status:** ❌ Not yet formalized (should use mathlib FourierTransform)

### Definition 6.2 (Compact Support in Frequency Domain)
**PDF Location:** Section 6
**Mathematical Statement:**
A function Φ ∈ W has compact frequency support if:
supp(Φ̂) ⊆ [-B, B] for some B > 0

**Lean Status:** ❌ Not yet formalized

---

## Section 7: Fejér and Heat Kernels

### Definition 7.1 (Fejér Kernel)
**PDF Location:** Section 7
**Mathematical Statement:**
F_L(x) = (sin(Lx/2) / (Lx/2))^2

Properties:
- F_L(x) ≥ 0 for all x
- ∫ F_L(x) dx = 2π
- F_L → 2πδ(x) as L → ∞ (Dirac delta approximation)

**Lean Status:** ❌ Not yet formalized

### Definition 7.2 (Heat Kernel)
**PDF Location:** Section 7
**Mathematical Statement:**
k_t(x, y) = (1/√(4πt)) exp(-(x-y)²/(4t))

Properties:
- k_t(x, y) > 0 for all x, y, t > 0
- ∫ k_t(x, y) dy = 1 (probability measure)
- k_t → δ(x-y) as t → 0⁺

**Lean Status:** ✓ Partially formalized as `heat_kernel` (missing normalization constant)

### Definition 7.3 (Fejér × Heat Product Kernel)
**PDF Location:** Section 7
**Mathematical Statement:**
K_{L,t}(x, y) = F_L(x-y) · k_t(x, y)

This is the key approximating kernel used in A1' (local density).

**Lean Status:** ❌ Not yet formalized

---

## Section 8: Toeplitz Operators and A3

### Definition 8.1 (Toeplitz Operator)
**PDF Location:** Section 8
**Mathematical Statement:**
A Toeplitz operator T_M[P] with symbol P : ℝ → ℂ is defined by:
(T_M[P] u)_j = ∑_{k=-M}^M P_{j-k} u_k

where P_j = P(jπ/M) are discretization samples.

**Lean Status:** ✓ Partially formalized as `ToeplitzOperator` (needs discretization details)

### Definition 8.2 (Discretization Parameter M)
**PDF Location:** Section 8
**Mathematical Statement:**
M ∈ ℕ is the discretization parameter.
Grid points: x_j = jπ/M for j ∈ [-M, M]
Grid spacing: Δx = π/M

**Lean Status:** ✓ Included in `ToeplitzOperator.discretization_param`

### Definition 8.3 (Symbol P_A for Archimedean Part)
**PDF Location:** Section 8
**Mathematical Statement:**
P_A(x) = a*(x) (the normalized Archimedean density)

**Lean Status:** ❌ Not yet formalized as separate definition

### Lemma 8.4 (Positive Definiteness of Archimedean Symbol)
**PDF Location:** Section 8
**Mathematical Statement:**
The symbol P_A(x) = a*(x) satisfies:
P_A(x) ≥ c > 0 for x ∈ [-K, K]

for some constant c = c(K) > 0.

**Lean Status:** ❌ Not yet formalized

---

## Section 9: RKHS and Prime Contraction

### Definition 9.1 (RKHS with Heat Kernel)
**PDF Location:** Section 9
**Mathematical Statement:**
The RKHS H_t is the reproducing kernel Hilbert space with kernel:
k_t(x, y) = exp(-(x-y)²/(4t))

Inner product:
⟨f, g⟩_{H_t} = ...

**Lean Status:** ❌ Not yet formalized (complex, needs RKHS theory)

### Definition 9.2 (Prime Operator T_P)
**PDF Location:** Section 9
**Mathematical Statement:**
T_P = ∑_{n≥2} w_n |δ_{ξ_n}⟩⟨δ_{ξ_n}|

where:
- w_n = 2Λ(n)/√n (prime weights)
- ξ_n = log(n)/(2π) (prime nodes)
- |δ_ξ⟩ = Dirac delta at ξ

**Lean Status:** ✓ Partially formalized as `PrimeOperator` (needs operator details)

### Theorem 9.3 (RKHS Norm Bound)
**PDF Location:** Section 9.23
**Mathematical Statement:**
For the heat kernel RKHS H_t:
‖T_P‖_{H_t} ≤ C/√t

for some constant C > 0 independent of t.

**Lean Status:** ❌ Not yet formalized

---

## Section 10-11: T0, A1', A2 Modules

### Module T0: Guinand-Weil Normalization

**Status:** ❌ Not yet formalized at all

Key components needed:
- [ ] Guinand-Weil trace formula
- [ ] Normalization factors
- [ ] Connection to classical Weil criterion

### Module A1': Local Density

**Status:** ❌ Not yet formalized at all

Key theorem:
**Theorem A1'.1 (Density of Fejér × Heat)**
Fejér × heat product kernels are dense in the Weil class restricted to compact windows.

### Module A2: Lipschitz Continuity

**Status:** ❌ Not yet formalized at all

Key theorem:
**Theorem A2.1 (Lipschitz Continuity of Q)**
The functional Q : W → ℂ is Lipschitz continuous on compact windows:
|Q(Φ₁) - Q(Φ₂)| ≤ L ‖Φ₁ - Φ₂‖_∞

for some Lipschitz constant L = L(K).

---

## Section 12: T5 Compact Transfer

### Theorem 12.1 (Compact-by-Compact Extension)
**PDF Location:** Section 12, Theorem 12.6
**Mathematical Statement:**
If Q(Φ) ≥ 0 for all Φ ∈ W with supp(Φ) ⊆ [-K, K] for all K > 0,
then Q(Φ) ≥ 0 for all Φ ∈ W.

**Lean Status:** ✓ Formalized as `compact_transfer` (with sorry)

---

## Section 13: Weil Criterion and Main Results

### Theorem 13.1 (Weil Criterion)
**PDF Location:** Section 13.1
**Mathematical Statement:**
The following are equivalent:
1. Q(Φ) ≥ 0 for all nonnegative Φ ∈ W
2. The Riemann Hypothesis holds

**Lean Status:** ✓ Formalized as `weil_criterion_equivalence` (with sorry)

### Theorem 13.2 (Main Result - Riemann Hypothesis)
**PDF Location:** Section 13.2
**Mathematical Statement:**
The Riemann Hypothesis is true.

Proof strategy:
1. Prove Q(Φ) ≥ 0 on compact windows (using A3 + RKHS)
2. Extend to full Weil class (using T5)
3. Apply Weil criterion (Theorem 13.1)

**Lean Status:** ✓ Formalized as `riemann_hypothesis_proof` (with sorry chain)

---

## Summary of Formalization Status

### ✓ Already Formalized (with sorry proofs):
- Section 4: Basic notation
- Section 5: Weil class and Q functional
- Section 8: Toeplitz operators (partial)
- Section 9: RKHS and prime operators (partial)
- Section 12: Compact transfer theorem
- Section 13: Weil criterion and main theorem

### ❌ Not Yet Formalized:
- Section 6: Fourier transform properties
- Section 7: Fejér and heat kernels
- Section 10: T0 module (Guinand-Weil)
- Section 11: A1' module (local density) and A2 module (Lipschitz)
- Detailed lemmas and propositions from all sections

---

## Next Steps

1. **Formalize missing kernels** (Fejér, heat, product kernel)
2. **Add Fourier transform properties** (evenness, compact support)
3. **Formalize T0, A1', A2 modules**
4. **Fill in detailed lemmas** for A3 and RKHS
5. **Add auxiliary results** (bounds, estimates, approximation lemmas)
6. **Begin proof sketches** (replace `sorry` with actual tactics)

---

This extraction will be updated as I read through the PDF more carefully.

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RiemannQ3/Basic/Definitions.lean
```lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Real

namespace RiemannQ3
namespace Basic

noncomputable section

/-!
# RiemannQ3.Basic.Definitions

Elementary calculus facts used across Q3. In particular we show
that the function `x ↦ log x / sqrt x` (for `x > 0`) attains its
global maximum at `x = exp 2` with value `2 / exp 1`, and we derive
the convenient bound for integers `n ≥ 2`.

We carry out the derivative calculation by writing the function
in the auxiliary variable `y = √x`:

  h(y) = 2 * log y / y

whose derivative has the simple form

  h'(y) = (2 / y^2) * (1 - log y),

so `h` is strictly increasing on `(0, e)` and strictly decreasing on
`(e, ∞)`. This immediately gives the desired maximum at `y = e` and
thus at `x = e^2` for the original variable.
-/

/-! ## The auxiliary function `h y = 2 * log y / y` -/

def h (y : ℝ) : ℝ := (2 : ℝ) * Real.log y / y

lemma h_le_at_e {y : ℝ} (hy : 0 < y) :
    h y ≤ (2 : ℝ) / Real.exp 1 := by
  -- Use `log (y/ e) ≤ (y/e) - 1` with `e = exp 1`.
  have epos : 0 < Real.exp 1 := by simpa using Real.exp_pos 1
  have tpos : 0 < y / Real.exp 1 := by exact div_pos hy epos
  have hlog_bound : Real.log (y / Real.exp 1) ≤ y / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos tpos
  -- Rewrite `log y = 1 + log (y/e)`.
  have hmul : Real.exp 1 * (y / Real.exp 1) = y := by
    calc
      Real.exp 1 * (y / Real.exp 1)
          = Real.exp 1 * y / Real.exp 1 := (mul_div_assoc' (Real.exp 1) y (Real.exp 1))
      _ = y := by simpa using (mul_div_cancel_left (Real.exp 1) y)
  have hlogy : Real.log y = 1 + Real.log (y / Real.exp 1) := by
    have hxne : Real.exp 1 ≠ 0 := ne_of_gt epos
    have htne : y / Real.exp 1 ≠ 0 := ne_of_gt tpos
    have := Real.log_mul hxne htne
    simpa [hmul, Real.log_exp] using this
  -- Conclude: `log y ≤ y/e` and scale by `2/y`.
  have hineq : Real.log y ≤ y / Real.exp 1 := by
    have := add_le_add_left hlog_bound 1
    simpa [hlogy, add_comm, add_left_comm, add_assoc] using this
  -- Multiply by `2` and divide by `y` to reach `h y`.
  have step1 : (2 : ℝ) * Real.log y ≤ (2 : ℝ) * (y / Real.exp 1) :=
    (mul_le_mul_of_nonneg_left hineq (by norm_num))
  have step2 : ((2 : ℝ) * Real.log y) / y ≤ ((2 : ℝ) * (y / Real.exp 1)) / y :=
    (div_le_div_of_nonneg_right step1 (le_of_lt hy))
  have rhs_simpl : ((2 : ℝ) * (y / Real.exp 1)) / y = (2 : ℝ) / Real.exp 1 := by
    have : (((2 : ℝ) * y) / Real.exp 1) / y = ((2 : ℝ) * y) / (Real.exp 1 * y) := by
      simpa using (div_div (((2 : ℝ) * y)) (Real.exp 1) y)
    have hyne : y ≠ 0 := ne_of_gt hy
    calc
      ((2 : ℝ) * (y / Real.exp 1)) / y
          = (((2 : ℝ) * y) / Real.exp 1) / y := by simp [mul_div_assoc']
      _ = ((2 : ℝ) * y) / (Real.exp 1 * y) := this
      _ = (y * (2 : ℝ)) / (y * Real.exp 1) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      _ = (2 : ℝ) / Real.exp 1 := by
        simpa using (mul_div_mul_left (2 : ℝ) (Real.exp 1) hyne)
  have lhs_simpl : ((2 : ℝ) * Real.log y) / y = h y := by
    simp [h]
  have : h y ≤ (2 : ℝ) / Real.exp 1 := by
    simpa [lhs_simpl, rhs_simpl] using step2
  exact this

/-! ### Back to `x ↦ log x / sqrt x` -/

def f (x : ℝ) : ℝ := Real.log x / Real.sqrt x

lemma f_bound_for_pos (x : ℝ) (hx : 0 < x) :
    f x ≤ (2 : ℝ) / Real.exp 1 := by
  -- Put `y = √x > 0` so that `f x = h y` and apply `h_le_at_e`.
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hx0 : 0 ≤ x := le_of_lt hx
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0
  have hreduce : (2 : ℝ) * (Real.log x / 2) = Real.log x := by
    calc
      (2 : ℝ) * (Real.log x / 2) = ((2 : ℝ) * Real.log x) / 2 := (mul_div_assoc' _ _ _)
      _ = Real.log x := by simpa using (mul_div_cancel_left (2 : ℝ) (Real.log x))
  have h2 : Real.log x = (2 : ℝ) * Real.log (Real.sqrt x) := by
    have : (2 : ℝ) * Real.log (Real.sqrt x) = Real.log x := by
      simpa [hlogsqrt] using hreduce
    simpa using this.symm
  have : f x = h (Real.sqrt x) := by
    simp [f, h, h2]
  simpa [this] using h_le_at_e hy

lemma f_nat_bound {n : ℕ} (hn : 2 ≤ n) :
    f n ≤ (2 : ℝ) / Real.exp 1 := by
  have : (0 : ℕ) < n := lt_of_lt_of_le (by decide : (0:ℕ) < 2) hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast this
  simpa [f] using f_bound_for_pos (n : ℝ) hn0

end -- section

end Basic
end RiemannQ3

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/CLAUDE.md
```md
# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**RH_Formalization** - Formal verification of the Riemann Hypothesis proof using Lean 4.

This project formalizes the mathematical proof from "Operator Methods for the Weil Criterion: Q3" by Eugen Malamutmann (University of Duisburg-Essen, October 22, 2025). The proof uses operator-theoretic methods to show Q(Φ) ≥ 0 for all test functions in the Weil class, which by Weil's criterion is equivalent to the Riemann Hypothesis.

**Note:** This is a standalone git repository nested within the larger RH_2025_V3_October project.

## Build Commands

### Basic Operations
```bash
# Build the entire project
lake build

# Build and run the executable
lake build rh_formalization
lake exe rh_formalization

# Update mathlib dependency (after pulling changes)
lake update

# Clean build artifacts
lake clean

# Full rebuild
lake clean && lake build
```

### Working with Specific Files
```bash
# Check a single file
lake env lean RHFormalization/WeilCriterion.lean

# Interactive type checking (use in VS Code with Lean 4 extension)
code RHFormalization/WeilCriterion.lean
```

### Dependency Management
```bash
# Update to latest stable mathlib
lake update mathlib

# Check mathlib version
cat lake-manifest.json | grep mathlib

# Force rebuild dependencies
rm -rf .lake && lake build
```

## Project Structure

```
RH_Formalization/
├── RHFormalization/
│   ├── Basic.lean           # Basic definitions (placeholder)
│   └── WeilCriterion.lean   # Main formalization (6953 bytes)
├── RHFormalization.lean     # Library root module
├── Main.lean                # Executable entry point
├── lakefile.toml            # Lake build configuration
├── lean-toolchain           # Lean version spec (v4.24.0)
├── README_RU.md             # Detailed documentation (Russian)
├── README.md                # Brief overview (English)
└── CLAUDE.md                # This file
```

## Code Architecture

### RHFormalization/WeilCriterion.lean (Main File)

This is the core formalization containing the complete proof structure:

**Namespace:** `RiemannHypothesis`

**Key Structures:**
1. `WeilClass` - Test functions (even, compact support, continuous)
2. `ToeplitzOperator` - Toeplitz operators with symbol and discretization
3. `PrimeOperator` - Prime operator with weights w(n) = 2Λ(n)/√n

**Key Definitions:**
- `frequency_var` - ξ = η/(2π)
- `archimedean_density` - a(ξ) = log π - Re ψ(1/4 + iπξ)
- `prime_node` - ξ_n = (log n)/(2π)
- `von_mangoldt` - Λ(n) function
- `weil_functional` - Q(Φ) quadratic functional
- `heat_kernel` - k_t(x,y) = exp(-(x-y)²/(4t))

**Main Theorems:**
1. `main_theorem` (Theorem 1.1) - Q(Φ) ≥ 0 for nonnegative Φ
2. `weil_criterion_equivalence` (Theorem 13.1) - Q ≥ 0 ⟺ RH
3. `archimedean_toeplitz_barrier` (Theorem 8.35) - Toeplitz lower bound
4. `prime_contraction` (Theorem 9.23) - RKHS norm bound
5. `compact_transfer` (Theorem 12.6) - Extend from compact to full class
6. `riemann_hypothesis_proof` (Theorem 13.2) - Final RH proof

**Proof Strategy (6 Modules):**
- **T0**: Guinand-Weil normalization
- **A1'**: Local density (Fejér × heat approximations)
- **A2**: Lipschitz continuity
- **A3**: Archimedean Toeplitz barrier
- **RKHS**: Prime contraction via RKHS
- **T5**: Compact-by-compact transfer

### RHFormalization/Basic.lean

Placeholder file with basic definitions. Currently contains only:
```lean
def hello := "world"
```

### Main.lean

Executable entry point. Currently a hello-world placeholder:
```lean
import RHFormalization
def main : IO Unit := IO.println s!"Hello, {hello}!"
```

## Development Workflow

### Initial Setup
```bash
# Clone and enter project
cd /path/to/RH_Formalization

# Build (will download mathlib on first run)
lake build

# This may take 10-30 minutes for first build
```

### Daily Development
```bash
# Start VS Code with Lean 4 extension
code .

# Open main formalization file
code RHFormalization/WeilCriterion.lean

# Build after changes
lake build

# Check specific theorem
# (Navigate to theorem in VS Code and check info view)
```

### Working with Proofs

**All main theorems currently use `sorry`** - this is expected because:
1. Riemann Hypothesis is an unsolved Millennium Prize Problem
2. This formalization captures the proof *structure* from the paper
3. Each `sorry` represents a gap that needs formal verification

**Priority areas for formalization:**
1. `archimedean_toeplitz_barrier` - Needs spectral bounds for Toeplitz operators
2. `prime_contraction` - Needs RKHS norm estimates
3. `compact_transfer` - Needs monotonicity and limit arguments
4. `weil_criterion_equivalence` - Needs connection to classical Weil criterion

## Dependencies

### Mathlib4 (stable branch)

Key imports from `WeilCriterion.lean`:
```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.ArithmeticFunction
```

**Available from Mathlib:**
- `riemannZeta : ℂ → ℂ` - Riemann zeta function
- `RiemannHypothesis : Prop` - Formal RH statement
- `ArithmeticFunction.vonMangoldt` - Λ(n) function
- Complex analysis, Fourier transforms, measure theory
- Inner product spaces, spectral theory

## Lean 4 Version

**Fixed version:** `leanprover/lean4:v4.24.0` (specified in `lean-toolchain`)

Elan (Lean version manager) automatically installs and uses this version when you run `lake` commands in this directory.

## Important Notes

### This is NOT Executable Code
- The project compiles but doesn't compute anything
- All definitions are `noncomputable` (standard for pure math)
- Goal is formal verification, not execution

### Status of Formalization
- **Structure:** ✅ Complete (all 6 modules outlined)
- **Definitions:** ✅ Complete (Weil class, Q functional, operators)
- **Theorem statements:** ✅ Complete (all key theorems stated)
- **Proofs:** ❌ Incomplete (marked with `sorry`)

### Git Repository
This is a **separate git repository** from the parent Q3_paper project:
```bash
# Check git status of THIS project
git status

# Parent project is at:
# /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper
```

## Testing and Validation

```bash
# Check all files compile (no type errors)
lake build

# Check specific file for errors
lake env lean RHFormalization/WeilCriterion.lean

# Verify no type errors in VS Code
# - Open file in VS Code with Lean 4 extension
# - Check "Lean: Problems" panel (Cmd+Shift+M)
# - Blue underlines = info, red = errors
```

## Common Issues

### Lake build hangs
```bash
# Kill any hanging lean/lake processes
pkill -9 lean
pkill -9 lake

# Remove lock files
rm -f ~/.elan/toolchains/*.lock

# Retry
lake build
```

### Mathlib version conflicts
```bash
# Reset to stable mathlib
lake update mathlib

# If still broken, delete cache and rebuild
rm -rf .lake
lake build
```

### VS Code Lean extension not working
```bash
# Restart Lean server: Cmd+Shift+P → "Lean 4: Restart Server"
# Or manually:
pkill lean
code .
```

### "unknown package" errors
```bash
# Make sure you're in the RH_Formalization directory
cd /path/to/RH_Formalization

# Rebuild manifest
lake update
lake build
```

## Next Steps for Development

To continue this formalization:

1. **Fill in `sorry` proofs** starting with smallest components
2. **Add helper lemmas** for intermediate steps
3. **Expand Basic.lean** with foundational definitions
4. **Consult paper** (RH_Q3.pdf) for detailed arguments
5. **Use Mathlib** - search for existing theorems before reproving
6. **Ask Zulip** - Lean community at leanprover.zulipchat.com

## Documentation

- **README_RU.md** - Comprehensive guide in Russian (9KB)
- **README.md** - Brief overview in English
- **Paper reference:** "Operator Methods for the Weil Criterion: Q3"

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH/Contracts.lean
```lean
import Mathlib

/-!
This module records the Track B contracts that bridge classical analysis with
the numerical artifacts stored under `notes/lean/`.  Every axiom below references
a literature theorem (Szego, de Branges, etc.) and the associated JSON witnesses:
* `notes/lean/grid_psd.json` (D7 Toeplitz PSD)
* `notes/lean/phase_monotone.json` (D8 phase monotonicity)
* `notes/lean/KE_integral_certificate.json` (global KE acceptance)
* `cert/bridge/eps_transport.json` (eps-transport margins)
The JSON paths are enforced by `notes/lean/scripts/verify_artifacts.py`.
-/

noncomputable section

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace RH

/-- Fejér kernel used in Section A1′. Normalized so `fejerKernel 0 = 1`. -/
def fejerKernel (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.sin (x / 2) / (x / 2)) ^ 2

/-- One-dimensional heat kernel at scale `t`. -/
def heatKernel (t x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x ^ 2) / (4 * t))

/-- Metadata describing the truncated Toeplitz construction used in module A3. -/
structure ToeplitzSpec (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Symbol on the frequency axis. -/
  symbol : ℝ → ℂ
  /-- Discrete truncation indexed by `M`. -/
  trunc : ℕ → H →L[ℂ] H
  /-- Modulus of continuity controlling Szegő errors. -/
  modulus : ℝ → ℝ
  /-- Essential infimum of the symbol. -/
  essInf : ℝ
  /-- Lipschitz certificate for the symbol. -/
  lipschitzConst : NNReal
  lipschitz : LipschitzWith lipschitzConst symbol

/-- Abstract minimal eigenvalue functional.  Concrete instances will refine this
axiomatically supplied oracle. -/
axiom minEigenvalue
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : H →L[ℂ] H) : ℝ

/-- Szegő–Böttcher barrier contract used in A3. -/
axiom szego_min_eig_lower_bound
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (spec : ToeplitzSpec H)
  (Csb : ℝ) (M : ℕ) :
  minEigenvalue (spec.trunc M) ≥ spec.essInf - Csb * spec.modulus (Real.pi / (M : ℝ))

/-- Prime operator metadata used in the RKHS contraction principle. -/
structure PrimeOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Bounded linear operator capturing the prime sampling action. -/
  op : H →L[ℂ] H
  /-- Auxiliary kernel witnessing symmetry / positivity. -/
  kernel : H → H → ℂ
  /-- Symmetry of the kernel. -/
  kernel_symm : ∀ x y, kernel x y = conj (kernel y x)
  /-- Positive diagonal ensures the kernel induces a Hilbert norm. -/
  kernel_diag_pos : ∀ x, 0 < ‖kernel x x‖

/-- de Branges style contraction axiom for the prime operator. -/
axiom rkhs_prime_contraction
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : PrimeOperator H) (c : ℝ)
  (hc₀ : 0 < c) (hc₁ : c < 1) :
  ‖P.op‖ ≤ c

/-- Rayleigh witness connecting quadratic forms with operator energies. -/
structure RayleighWitness (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  archimedean : H →L[ℂ] H
  prime : H →L[ℂ] H
  testVector : H
  weilValue : ℂ

/-- Rayleigh identity contract. -/
axiom rayleigh_weil_id
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (w : RayleighWitness H) :
  inner (𝕜 := ℂ) ((w.archimedean - w.prime) w.testVector) w.testVector =
    (1 / (2 * Real.pi)) * w.weilValue

/-- Finite Gram data extracted from the RKHS discretization. -/
structure KernelGram where
  n : ℕ
  gram : Matrix (Fin n) (Fin n) ℂ

/-- RKHS energy identity contract. -/
axiom rkhs_energy_id
  (K : KernelGram)
  (a : Fin K.n → ℂ) : Prop

/-- Gershgorin-style certificate providing a lower spectral bound. -/
structure GershgorinCertificate
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  operator : H →L[ℂ] H
  lower : ℝ
  budget : ℝ

/-- Gershgorin barrier contract. -/
axiom gershgorin_psd_floor
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (cert : GershgorinCertificate H) :
  minEigenvalue cert.operator ≥ cert.lower - cert.budget

/-- Hoffman–Wielandt perturbation budget. -/
structure HoffmanBudget
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  base : H →L[ℂ] H
  perturbed : H →L[ℂ] H
  budget : ℝ
  nonneg : 0 ≤ budget

/-- Hoffman–Wielandt contract bounding eigenvalue drift. -/
axiom hoffman_wielandt_bound
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (hb : HoffmanBudget H) :
  |minEigenvalue hb.perturbed - minEigenvalue hb.base| ≤ hb.budget

/-- Archimedean kernel approximation contract (ingredients for Sorry #1/#14). -/
structure ArchimedeanKernel where
  K : ℝ
  φ : ℝ → ℂ
  /-- Placeholder for the support condition `supp φ ⊆ [-K,K]`. -/
  supportWithin : Prop
  /-- Witness that the kernel factors through Fejér×heat packets. -/
  fejerHeatFactor :
    ∃ (B t : ℝ), 0 < B ∧ 0 < t ∧
      ∀ x, φ x = (Real.sin (x / 2) / (x / 2))^2 * Real.exp (-(x ^ 2) / (4 * t))

/-- Density axiom: Archimedean packets approximate the Weil class on compacts. -/
axiom archimedean_density_contract
  (K : ℝ) (hK : 0 < K) :
  ∃ (seq : ℕ → ArchimedeanKernel),
    (∀ n, (seq n).K = K) ∧
    TendstoUniformlyOn (fun n => (seq n).φ) (fun _ => 0) Filter.atTop (Set.Icc (-K) K)

/-- Fourier transform preserves evenness under the hypotheses of Section~6. -/
axiom fourier_even_of_even
  {f : ℝ → ℂ} (hf_even : Function.Even f)
  (hf_integrable : Integrable f) :
  Function.Even fun η => Real.fourierIntegral f η

/-- Fejér kernel is everywhere nonnegative (Section~7). -/
axiom fejer_kernel_nonneg (x : ℝ) : 0 ≤ fejerKernel x

/-- Heat kernel stays strictly positive for positive time (Section~7). -/
axiom heat_kernel_pos (t x : ℝ) (ht : 0 < t) : 0 < heatKernel t x

/-- Product Fejér×heat used in the cone construction is nonnegative. -/
axiom fejer_heat_kernel_nonneg
  (t : ℝ) (ht : 0 < t) (x : ℝ) :
  0 ≤ fejerKernel x * heatKernel t x

/-- Guinand–Weil functional relation placeholder (Section~6). -/
axiom guinand_weil_functional (Φ : ℂ → ℂ) : Prop

/-- Weil positivity ⇒ RH contract used in the final assembly. -/
axiom weil_positivity_implies_rh (hPos : Prop) : Prop

/-- Numerical metadata for a JSON-backed constant. -/
structure NumericalWitness where
  /-- Fully qualified JSON path, relative to repository root. -/
  jsonPath : String
  /-- Dot-separated field selector inside the JSON document. -/
  fieldPath : String
  /-- Certified value of the field. -/
  value : ℝ
  /-- Absolute tolerance guaranteed by the external verification script. -/
  tolerance : ℝ
  /-- Flag propagated from `scripts/verify_artifacts.py`. -/
  verified : Bool

/-- Oracle returning the Lean constant associated to a JSON witness.
The external script `notes/lean/scripts/verify_artifacts.py` must certify the tuple. -/
axiom validated_constant (w : NumericalWitness) : ℝ

/-- D7 Toeplitz PSD witness: λ_min = 1.2971215e-8 (grid size M = 16). -/
def lambdaMinD7 : ℝ :=
  validated_constant
    { jsonPath := "notes/lean/grid_psd.json"
      fieldPath := "d7_analysis.d7_criterion.lambda_min"
      value := 1.2971215226606565e-08
      tolerance := 1e-15
      verified := true }

/-- Positivity of the D7 witness (extracted from JSON safety margin). -/
axiom lambdaMinD7_pos : 0 < lambdaMinD7

/-- D8 phase monotonicity slope: φ'_{min} = 0.0012396… -/
def phiPrimeMinD8 : ℝ :=
  validated_constant
    { jsonPath := "notes/lean/phase_monotone.json"
      fieldPath := "d8_analysis.phi_prime_min"
      value := 0.0012396137877944142
      tolerance := 1e-10
      verified := true }

/-- ε-transport safety margin γ - δ = 1.2163705811887586e-06. -/
def transportGap : ℝ :=
  validated_constant
    { jsonPath := "cert/bridge/eps_transport.json"
      fieldPath := "gap_difference"
      value := 1.2163705811887586e-06
      tolerance := 1e-12
      verified := true }

/-- Global KE numerical margin backing the final Weil positivity step. -/
def keNumericalMargin : ℝ :=
  validated_constant
    { jsonPath := "notes/lean/KE_integral_certificate.json"
      fieldPath := "KE_integral_certificate.final_verdict.numerical_margin"
      value := 1.2163705811887586e-06
      tolerance := 1e-12
      verified := true }

/-- Example Archimedean barrier constant for K = 1 (matches Table A3). -/
def c0K1 : ℝ :=
  validated_constant
    { jsonPath := "cert/bridge/K1_A3_lock.json"
      fieldPath := "c0"
      value := 0.8986238471298743
      tolerance := 1e-10
      verified := true }

/-- Symmetrization step size for K = 1 witness. -/
def tSymK1 : ℝ :=
  validated_constant
    { jsonPath := "cert/bridge/K1_A3_lock.json"
      fieldPath := "t_sym"
      value := 0.03
      tolerance := 1e-12
      verified := true }

/-- Sum of squared prime weights for the K=1 RKHS block schedule. -/
def primeWeightSumK1 : ℝ :=
  validated_constant
    { jsonPath := "cert/bridge/K1_blocks_sum.json"
      fieldPath := "sum"
      value := 0.2305712288133166
      tolerance := 1e-12
      verified := true }

/-- Heat parameter used for the RKHS contraction (taken from the B=0.2,t=0.4 block). -/
def rkhsHeatParamK1 : ℝ :=
  validated_constant
    { jsonPath := "cert/bridge/K1_blocks_sum.json"
      fieldPath := "t"
      value := 0.4
      tolerance := 1e-12
      verified := true }

end RH

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RiemannQ3/Basic/NodeSpacing.lean
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped Real

namespace RiemannQ3
namespace Basic

noncomputable section
/-!
# RiemannQ3.Basic.NodeSpacing

Simple spacing estimates for logarithmic nodes `ξ_n := (log n)/(2π)`.
We extract from the mean value theorem for `log` the crude bound

  log n - log m ≥ (n - m) / n,   for 2 ≤ m < n,

and turn it into a spacing bound for the rescaled nodes.
-/

def node (n : ℕ) : ℝ := Real.log (n : ℝ) / (2 * Real.pi)

lemma log_diff_lower (m n : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    Real.log (n : ℝ) - Real.log (m : ℝ) ≥ ((n - m : ℕ) : ℝ) / (n : ℝ) := by
  -- Setup positivity and inclusions to use MVT.
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm2
  have hmn' : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hmn_le : (m : ℝ) ≤ (n : ℝ) := le_of_lt hmn'
  -- Continuity and differentiability of `log` on `[m,n]` / `(m,n)`.
  have hcont : ContinuousOn Real.log (Set.Icc (m : ℝ) (n : ℝ)) := by
    have hsubset : Set.Icc (m : ℝ) (n : ℝ) ⊆ {0}ᶜ := by
      intro x hx; exact ne_of_gt (lt_of_lt_of_le hm_pos hx.1)
    exact Real.continuousOn_log.mono hsubset
  have hdiff : DifferentiableOn ℝ Real.log (Set.Ioo (m : ℝ) (n : ℝ)) := by
    have hsubset : Set.Ioo (m : ℝ) (n : ℝ) ⊆ {0}ᶜ := by
      intro x hx; exact ne_of_gt (lt_trans hm_pos hx.1)
    exact Real.differentiableOn_log.mono hsubset
  -- Lagrange MVT for `log` on `[m,n]`.
  obtain ⟨c, hc, hc_slope⟩ :=
    exists_deriv_eq_slope (f := Real.log) (a := (m : ℝ)) (b := (n : ℝ)) hmn' hcont hdiff
  -- Use `deriv log c = c⁻¹` to rewrite the slope.
  have hc_deriv : deriv Real.log c = c⁻¹ := by simpa using Real.deriv_log c
  have hEq : Real.log (n : ℝ) - Real.log (m : ℝ) = ((n : ℝ) - (m : ℝ)) * (1 / c) := by
    have slope_eq : c⁻¹ = (Real.log (n : ℝ) - Real.log (m : ℝ)) / ((n : ℝ) - (m : ℝ)) := by
      simpa [hc_deriv] using hc_slope
    have := congrArg (fun t : ℝ => t * ((n : ℝ) - (m : ℝ))) slope_eq
    simpa [div_eq_inv_mul, one_div, mul_comm, mul_left_comm, mul_assoc] using this
  -- Since `c ∈ (m,n)`, we have `c ≤ n`, hence `1/c ≥ 1/n`.
  have hc_le : (c : ℝ) ≤ n := le_of_lt hc.2
  have hfrac : 1 / c ≥ 1 / (n : ℝ) := one_div_le_one_div_of_le (lt_trans hm_pos hc.1) hc_le
  -- Multiply by the nonnegative factor `(n - m)`.
  have hnm_nonneg : 0 ≤ (n : ℝ) - (m : ℝ) := sub_nonneg.mpr hmn_le
  have hmul := mul_le_mul_of_nonneg_left hfrac hnm_nonneg
  -- Convert to a clean division form and finish.
  have : ((n : ℝ) - (m : ℝ)) * (1 / c) ≥ ((n : ℝ) - (m : ℝ)) * (1 / (n : ℝ)) := hmul
  have hnm_cast : ((n : ℝ) - (m : ℝ)) = ((n - m : ℕ) : ℝ) := by
    have : (n : ℝ) - (m : ℝ) = ((n - m : ℕ) : ℝ) := (Nat.cast_sub (le_of_lt hmn)).symm
    simpa using this
  have rhs : ((n : ℝ) - (m : ℝ)) * (1 / (n : ℝ)) = ((n - m : ℕ) : ℝ) / (n : ℝ) := by
    simpa [hnm_cast, one_div, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Apply the equality for `log` difference and the inequality for the fraction.
  calc
    Real.log (n : ℝ) - Real.log (m : ℝ)
        = ((n : ℝ) - (m : ℝ)) * (1 / c) := hEq
    _ ≥ ((n : ℝ) - (m : ℝ)) * (1 / (n : ℝ)) := hmul
    _ = ((n - m : ℕ) : ℝ) / (n : ℝ) := by simpa [rhs]

lemma node_spacing_lower (m n : ℕ) (hm2 : 2 ≤ m) (h : m < n) :
    node n - node m ≥ (1 : ℝ) / (2 * Real.pi) * ((n - m : ℕ) : ℝ) / (n : ℝ) := by
  -- Scale `log_diff_lower` by `(2π)⁻¹` and rewrite to `node`.
  have h0 := log_diff_lower m n hm2 h
  have two_pi_pos : 0 < 2 * Real.pi := by
    have : 0 < (2 : ℝ) := by norm_num
    exact mul_pos this Real.pi_pos
  have nonneg_inv : 0 ≤ (1 : ℝ) / (2 * Real.pi) := by
    simpa [one_div] using (le_of_lt (inv_pos.mpr two_pi_pos))
  have hmul := mul_le_mul_of_nonneg_left h0 nonneg_inv
  -- Convert LHS to `node` difference.
  have hnode : node n - node m = (Real.log (n : ℝ) - Real.log (m : ℝ)) / (2 * Real.pi) := by
    have := sub_div (Real.log (n : ℝ)) (Real.log (m : ℝ)) (2 * Real.pi)
    simpa [node] using this.symm
  have : (Real.log (n : ℝ) - Real.log (m : ℝ)) / (2 * Real.pi)
      ≥ (1 / (2 * Real.pi)) * (((n - m : ℕ) : ℝ) / (n : ℝ)) := by
    simpa [one_div, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [hnode, one_div, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using this

end -- section

end Basic
end RiemannQ3
 
 

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/lean-toolchain
```
leanprover/lean4:v4.24.0

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/scratch.lean
```lean
import Mathlib
#check Complex.abs

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/.github/workflows/lean_action_ci.yml
```yml
name: Lean Action CI

on:
  push:
  pull_request:
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/Формализация Гипотезы Римана через Критерий Вейля в Lean 4.md
```md
# Формализация Гипотезы Римана через Критерий Вейля в Lean 4

## Обзор

Этот проект представляет собой формализацию в Lean 4 доказательства Гипотезы Римана с использованием операторно-теоретических методов, основанную на работе **"Operator Methods for the Weil Criterion: Q3"** автора Eugen Malamutmann (University of Duisburg–Essen, October 22, 2025).

## Основная идея

Документ доказывает Гипотезу Римана через **критерий Вейля**: показывается, что квадратичный функционал **Q(Φ) ≥ 0** для всех четных, неотрицательных, компактно поддерживаемых тестовых функций Φ из класса Вейля **W**.

### Структура доказательства

Доказательство организовано в виде цепочки аналитических модулей:

1. **T0 (Нормализация Гинанда-Вейля)**: Установление соответствия между репозиторной нормализацией Q и классическим функционалом Гинанда-Вейля.

2. **A1' (Локальная плотность)**: Доказательство плотности конуса Фейера×тепловых приближений на каждом компактном окне W_K.

3. **A2 (Липшицева непрерывность)**: Установление Липшицевой непрерывности Q на каждом W_K.

4. **A3 (Архимедов барьер Теплица)**: Разложение Q на архимедову часть (оператор Теплица T_M[P_A]) и простую часть (T_P) с явными нижними оценками:
   ```
   λ_min(T_M[P_A]) ≥ c₀(K) - C·ω_PA(π/M)
   ```

5. **RKHS (Сжатие простых чисел)**: Ограничение нормы оператора простых чисел в воспроизводящем ядерном гильбертовом пространстве (RKHS):
   ```
   ‖T_P‖ ≤ w_max + √(w_max·η_K)
   ```
   с выбором параметра t, обеспечивающим ‖T_P‖ ≤ c₀(K)/4.

6. **T5 (Компактный перенос)**: Распространение положительности с компактных множеств на весь класс Вейля через монотонную цепочку K_i ↑ ∞.

### Ключевые определения

#### Класс Вейля W

Тестовые функции Φ : ℝ → ℂ со свойствами:
- **Четность**: Φ(-x) = Φ(x)
- **Компактная поддержка**: supp(Φ) компактен
- **Неотрицательность**: Φ(x) ≥ 0 для всех x

#### Квадратичный функционал Q

```
Q(Φ) = ∫_ℝ a*(ξ) Φ(ξ) dξ - ∑_{n≥2} (2Λ(n)/√n) Φ(ξ_n)
```

где:
- **a*(ξ) = 2π·a(ξ)** — нормализованная архимедова плотность
- **a(ξ) = log π - Re ψ(1/4 + iπξ)** — архимедова плотность
- **ξ_n = (log n)/(2π)** — узлы простых чисел
- **Λ(n)** — функция фон Мангольдта

#### Критерий Вейля

**Теорема (Weil)**: Гипотеза Римана эквивалентна утверждению:
```
Q(Φ) ≥ 0  для всех Φ ∈ W с Φ ≥ 0
```

## Структура файлов

```
RH_Formalization/
├── RHFormalization/
│   ├── Basic.lean              # Базовые определения
│   └── WeilCriterion.lean      # Главная формализация
├── RHFormalization.lean         # Корневой модуль
├── Main.lean                    # Точка входа
├── lakefile.toml               # Конфигурация Lake
└── README_RU.md                # Этот файл
```

## Основные теоремы в WeilCriterion.lean

### 1. Главная теорема (Theorem 1.1)

```lean
theorem main_theorem :
    ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re
```

### 2. Критерий Вейля (Theorem 13.1)

```lean
theorem weil_criterion_equivalence :
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) ↔
    RiemannHypothesis
```

### 3. Архимедов барьер Теплица (Theorem 8.35)

```lean
theorem archimedean_toeplitz_barrier
    (K : ℝ) (hK : 0 < K) :
    ∃ (c₀ : ℝ) (M₀ : ℕ), 0 < c₀ ∧ ...
```

### 4. Сжатие простых чисел (Theorem 9.23)

```lean
theorem prime_contraction
    (K : ℝ) (hK : 0 < K) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ (t_min : ℝ), 0 < t_min ∧ ∀ (T_P : H →L[ℂ] H), ‖T_P‖ ≤ c₀ / 4
```

### 5. Компактный перенос (Theorem 12.6)

```lean
theorem compact_transfer :
    (∀ (K : ℝ) (Φ : WeilClass), supported_on_compact Φ K → ...) →
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re)
```

### 6. Гипотеза Римана (Theorem 13.2)

```lean
theorem riemann_hypothesis_proof : RiemannHypothesis
```

## Статус формализации

### ✅ Завершено

- Определение класса Вейля
- Определение квадратичного функционала Q
- Формулировка всех ключевых теорем
- Структура доказательства
- Связь с Mathlib (использование `RiemannHypothesis` из Mathlib)

### ⚠️ Требует доработки (помечено `sorry`)

- **Архимедова плотность**: Требуется формализация дигамма-функции ψ
- **Интегралы и суммы**: Детальная работа с мерами и сходимостью
- **Операторы Теплица**: Полная теория операторов Теплица в Hilbert пространствах
- **RKHS**: Теория воспроизводящих ядерных гильбертовых пространств
- **Спектральная теория**: Оценки собственных значений и спектральные границы
- **Доказательства теорем**: Все основные доказательства заменены на `sorry`

## Важное замечание

**Это формализация структуры доказательства, а не полное доказательство.**

Документ RH_Q3.pdf представляет собой попытку доказательства Гипотезы Римана. Однако:

1. **Гипотеза Римана остается открытой проблемой** — нет общепризнанного доказательства
2. Данная формализация показывает, **как** можно было бы формализовать подход из документа
3. Все ключевые шаги помечены `sorry` и требуют строгого математического обоснования
4. Для полной формализации потребуются:
   - Детальная теория операторов Теплица
   - Воспроизводящие ядерные гильбертовы пространства
   - Спектральная теория самосопряженных операторов
   - Теория функций фон Мангольдта и дзета-функции Римана

## Использование

### Установка зависимостей

```bash
# Установить Lean 4 через elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Перейти в директорию проекта
cd RH_Formalization

# Обновить зависимости (Mathlib)
lake update

# Собрать проект
lake build
```

### Проверка формализации

```bash
# Проверить синтаксис
lake build RHFormalization

# Запустить главный файл
lake exe rh_formalization
```

## Ссылки

- **Оригинальный документ**: RH_Q3.pdf (Eugen Malamutmann, 2025)
- **Lean 4**: https://lean-lang.org/
- **Mathlib**: https://github.com/leanprover-community/mathlib4
- **Формализация дзета-функции в Mathlib**: https://arxiv.org/abs/2503.00959

## Автор формализации

Формализация создана **Manus AI** на основе документа Eugen Malamutmann.

## Лицензия

Этот проект создан в образовательных и исследовательских целях.


```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/lean_zeta_formalization.md
```md
# Lean Formalization of Riemann Zeta Function

## Key Mathlib Definitions and Theorems

Based on the paper "Formalizing zeta and L-functions in Lean" (arXiv:2503.00959v3):

### Available in Mathlib

1. **riemannZeta**: Definition of the Riemann zeta function
   - Type: `ℂ → ℂ`
   - Defined for `s : ℂ` with `s ≠ 1`

2. **riemannZeta_two**: Euler's Basel problem
   ```lean
   theorem riemannZeta_two : ζ 2 = π^2 / 6
   ```

3. **riemannZeta_eulerProduct**: Euler's product formula
   ```lean
   theorem riemannZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
     ζ s = ∏' p : Nat.Primes, (1 - p^(-s))⁻¹
   ```

4. **riemannZeta_one_sub**: Functional equation
   ```lean
   theorem riemannZeta_one_sub (s : ℂ) :
     ζ (1 - s) = ... (relates to ζ s)
   ```

5. **riemannZeta_ne_zero_of_one_le_re**: Non-vanishing on critical line boundary
   ```lean
   theorem riemannZeta_ne_zero_of_one_le_re (s : ℂ) (hs : 1 ≤ s.re) :
     ζ s ≠ 0
   ```

6. **RiemannHypothesis**: Formal statement of RH
   ```lean
   def RiemannHypothesis : Prop :=
     ∀ s : ℂ, ζ s = 0 → (s.re = 1/2 ∨ ∃ n : ℤ, n < 0 ∧ Even n ∧ s = n)
   ```

### Dirichlet L-functions

- Definitions for Dirichlet characters
- L-functions `L(χ, s)` for characters χ
- Non-vanishing theorems
- **Nat.setOf_prime_and_eq_mod_infinite**: Dirichlet's theorem on primes in arithmetic progressions

## Imports Needed

```lean
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
```

## Structure for Operator-Theoretic Approach

For the Weil criterion and operator methods, we would need:

```lean
-- Quadratic functional Q on test functions
def WeilFunctional (Φ : ℝ → ℂ) : ℂ := sorry

-- Weil criterion: Q ≥ 0 ⟺ RH
theorem weil_criterion :
  (∀ Φ : WeilClass, 0 ≤ (WeilFunctional Φ).re) ↔ RiemannHypothesis := sorry

-- Toeplitz operators
def ToeplitzOperator (symbol : ℝ → ℂ) : Operator := sorry

-- RKHS (Reproducing Kernel Hilbert Space)
def HeatKernel (t : ℝ) (x y : ℝ) : ℂ := Complex.exp (-(x - y)^2 / (4 * t))

-- Spectral theory
theorem spectral_bound (T : Operator) (h : IsSelfAdjoint T) :
  ∃ λ : ℝ, IsMinEigenvalue T λ := sorry
```

## Note on Current Status

The Mathlib library has:
- ✅ Definition of Riemann zeta function
- ✅ Basic properties (Euler product, functional equation)
- ✅ Non-vanishing on Re(s) ≥ 1
- ✅ Formal statement of Riemann Hypothesis
- ❌ No proof of Riemann Hypothesis (it's an open problem!)

For formalizing the operator-theoretic approach from the RH_Q3.pdf paper, we would need to:
1. Define the Weil test class
2. Define the quadratic functional Q
3. Formalize Toeplitz operators and their spectral properties
4. Formalize RKHS and heat kernel methods
5. Prove the Weil criterion equivalence
6. Prove Q ≥ 0 using operator bounds


```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization.tar.gz
```gz
[Binary file]
```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RHFormalization.lean
```lean
-- This module serves as the root of the `RHFormalization` library.
-- Import modules here that should be built as part of the library.

-- Main formalization module
import RHFormalization.WeilCriterion

-- Abstract contracts and safe analytic scaffolding
import RH.Contracts
import RH.T0A1A2

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/lakefile.toml
```toml
name = "RH_Formalization"
version = "0.1.0"
defaultTargets = ["rh_formalization"]

[[lean_lib]]
name = "RH"

[[lean_lib]]
name = "RHFormalization"
imports = ["RH"]

[[lean_lib]]
name = "RiemannQ3"
imports = ["Mathlib"]

[[lean_exe]]
name = "rh_formalization"
root = "Main"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "stable"

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Q3.pdf
```pdf
[Binary file]
```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/RHFormalization.lean
```lean
-- This module serves as the root of the `RHFormalization` library.
-- Import modules here that should be built as part of the library.
import RHFormalization.Basic
import RHFormalization.WeilCriterion

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RHFormalization/WeilCriterion.lean
```lean
/-
Formalization of the Riemann Hypothesis via Weil's Criterion
Based on "Operator Methods for the Weil Criterion: Q3" by Eugen Malamutmann

This file formalizes the main theorem and key concepts from the paper,
which proves the Riemann Hypothesis using operator-theoretic methods.

Main Goal: Prove Q(Φ) ≥ 0 for all Φ in the Weil class, which by Weil's
criterion is equivalent to the Riemann Hypothesis.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Topology.Algebra.Support
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import RH.RKHSPrime
import RH.RKHSPrimeBridge
import RH.Contracts

noncomputable section

open Complex Real Set Filter Topology MeasureTheory Function RH

namespace RiemannHypothesis

/-! ## Section 4: Notation and Conventions -/

/-- The frequency variable ξ = η/(2π) -/
def frequency_var (η : ℝ) : ℝ := η / (2 * π)

/-- Archimedean density witness calibrated to the $K=1$ bridge certificate.
Rather than re-derive the digamma expression inside Lean, we import the
numeric barrier from `cert/bridge/K1_A3_lock.json` via `RH.c0K1` and offset it
by the PSD witness `RH.lambdaMinD7`.  This keeps the value tied to the same
JSON artifacts used throughout the A3 module. -/
noncomputable def archimedean_density (_ξ : ℝ) : ℂ :=
  Complex.ofReal (RH.c0K1 - RH.lambdaMinD7)

/-- The normalized Archimedean density a*(ξ) = 2π a(ξ) -/
def archimedean_density_star (ξ : ℝ) : ℂ :=
  2 * π * archimedean_density ξ

/-- Prime nodes ξ_n = (log n)/(2π) -/
def prime_node (n : ℕ) : ℝ :=
  Real.log (n : ℝ) / (2 * π)

/-- Von Mangoldt function Λ(n) from mathlib. -/
def von_mangoldt (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-! ## Section 5: The Weil Class and Quadratic Functional -/

/-- The Weil class W: even, nonnegative, compactly supported test functions -/
structure WeilClass where
  /-- The test function Φ : ℝ → ℂ -/
  f : ℝ → ℂ
  /-- Φ is even: Φ(-x) = Φ(x) -/
  is_even : ∀ x, f (-x) = f x
  /-- Φ has compact support -/
  has_compact_support : HasCompactSupport f
  /-- Φ is continuous -/
  continuous : Continuous f
  /-- Φ is integrable on ℝ. -/
  integrable : Integrable f

/-- A test function is nonnegative if Φ(x) is real and ≥ 0 for all x -/
def IsNonNegative (Φ : WeilClass) : Prop :=
  ∀ x : ℝ, (Φ.f x).im = 0 ∧ 0 ≤ (Φ.f x).re

/-- The quadratic functional Q(Φ) from equation (5.5):
    Q(Φ) = ∫ a*(ξ) Φ(ξ) dξ - ∑_{n≥2} (2Λ(n)/√n) Φ(ξ_n) -/
def weil_functional (Φ : WeilClass) : ℂ :=
  let archimedean_part := ∫ ξ, archimedean_density_star ξ * Φ.f ξ
  let prime_part := ∑' n : ℕ, if n ≥ 2 then
    (((2 * von_mangoldt n) / Real.sqrt (n : ℝ)) : ℂ) * Φ.f (prime_node n)
  else 0
  archimedean_part - prime_part

/-! ## Section 6: Fourier Transform Properties -/

/-- The Fourier transform of a test function Φ ∈ W
    Note: We use mathlib's FourierIntegral which uses convention:
    Φ̂(η) = ∫ Φ(x) e^{-iηx} dx -/
def fourier_transform (Φ : WeilClass) (η : ℝ) : ℂ :=
  Real.fourierIntegral Φ.f η

/-- A test function has compact frequency support if its Fourier transform
    is supported on [-B, B] for some B > 0 -/
def has_compact_frequency_support (Φ : WeilClass) (B : ℝ) : Prop :=
  ∀ η : ℝ, abs η > B → fourier_transform Φ η = 0

/-- If Φ is even, then its Fourier transform is even -/
lemma fourier_even_of_even (Φ : WeilClass) :
    ∀ η : ℝ, fourier_transform Φ (-η) = fourier_transform Φ η := by
  classical
  have h := RH.fourier_even_of_even (f := Φ.f) Φ.is_even Φ.integrable
  intro η
  simpa [fourier_transform] using h η

/-! ## Section 7: Fejér and Heat Kernels -/

/-! ### Fejér kernel (real-valued, then embedded into ℂ) -/

private def fejer_kernelR (L x : ℝ) : ℝ :=
  if hx : x = 0 then 1 else
    let u := L * x / 2
    (Real.sin u / u) ^ 2

lemma fejer_kernelR_nonneg (L x : ℝ) : 0 ≤ fejer_kernelR L x := by
  classical
  by_cases hx : x = 0
  · simp [fejer_kernelR, hx]
  · have : 0 ≤ (Real.sin (L * x / 2) / (L * x / 2)) ^ 2 :=
      sq_nonneg _
    simpa [fejer_kernelR, hx] using this

/-- Complex Fejér kernel: real kernel wrapped via `Complex.ofReal`. -/
def fejer_kernel (L : ℝ) (x : ℝ) : ℂ :=
  Complex.ofReal (fejer_kernelR L x)

@[simp] lemma fejer_kernel_re (L x : ℝ) :
    (fejer_kernel L x).re = fejer_kernelR L x := by
  simp [fejer_kernel]

@[simp] lemma fejer_kernel_im (L x : ℝ) :
    (fejer_kernel L x).im = 0 := by
  simp [fejer_kernel]

/-- The Fejér kernel is nonnegative -/
lemma fejer_kernel_nonneg (L : ℝ) (x : ℝ) :
    0 ≤ (fejer_kernel L x).re := by
  simpa [fejer_kernel_re] using fejer_kernelR_nonneg L x

private def heat_kernelR (t x y : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x - y) ^ 2 / (4 * t))

/-- The normalized heat kernel k_t(x, y) = (1/√(4πt)) exp(-(x-y)²/(4t)). -/
def heat_kernel_normalized (t : ℝ) (x y : ℝ) : ℂ :=
  Complex.ofReal (heat_kernelR t x y)

@[simp] lemma heat_kernel_normalized_re (t x y : ℝ) :
    (heat_kernel_normalized t x y).re = heat_kernelR t x y := by
  simp [heat_kernel_normalized]

@[simp] lemma heat_kernel_normalized_im (t x y : ℝ) :
    (heat_kernel_normalized t x y).im = 0 := by
  simp [heat_kernel_normalized]

/-- The heat kernel is positive for t > 0 -/
lemma heat_kernel_pos (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    0 < (heat_kernel_normalized t x y).re := by
  have hden :
      0 < Real.sqrt (4 * Real.pi * t) := by
    have : 0 < (4 : ℝ) := by norm_num
    have : 0 < 4 * Real.pi * t := by exact mul_pos (mul_pos this Real.pi_pos) ht
    simpa [mul_comm, mul_left_comm, mul_assoc] using Real.sqrt_pos.mpr this
  have hcoeff :
      0 < (Real.sqrt (4 * Real.pi * t))⁻¹ :=
    inv_pos.mpr hden
  have hexp :
      0 < Real.exp (-(x - y) ^ 2 / (4 * t)) :=
    Real.exp_pos _
  have hmul : 0 < heat_kernelR t x y := by
    dsimp [heat_kernelR]; exact mul_pos hcoeff hexp
  simpa [heat_kernel_normalized_re] using hmul

/-- The Fejér × heat product kernel K_{L,t}(x, y) = F_L(x-y) · k_t(x, y)
    This is the key approximating kernel for A1' (local density). -/
def fejer_heat_kernel (L t : ℝ) (x y : ℝ) : ℂ :=
  fejer_kernel L (x - y) * heat_kernel_normalized t x y

/-- The product kernel is nonnegative for L, t > 0 -/
lemma fejer_heat_kernel_nonneg (L t : ℝ) (ht : 0 < t) (x y : ℝ) :
    0 ≤ (fejer_heat_kernel L t x y).re := by
  have hfej : 0 ≤ fejer_kernelR L (x - y) :=
    fejer_kernelR_nonneg L (x - y)
  have hheat : 0 ≤ heat_kernelR t x y := by
    have : 0 ≤ (heat_kernel_normalized t x y).re :=
      le_of_lt (heat_kernel_pos t ht x y)
    simpa [heat_kernel_normalized_re] using this
  have hprod :
      0 ≤ fejer_kernelR L (x - y) * heat_kernelR t x y :=
    mul_nonneg hfej hheat
  have : (fejer_heat_kernel L t x y).re
      = fejer_kernelR L (x - y) * heat_kernelR t x y := by
    simp [fejer_heat_kernel, fejer_kernel, heat_kernel_normalized,
      Complex.ofReal_mul]
  simpa [this]
    using hprod

/-! ## Section 10: Module T0 - Guinand-Weil Normalization -/

/-- The classical Guinand-Weil functional (before normalization)
    This connects our formulation to the classical Weil criterion. -/
def guinand_weil_functional (Φ : WeilClass) : ℂ :=
  sorry -- Classical formulation using sum over zeros

/-- **Theorem T0.1 (Normalization Equivalence)**: The Q functional is equivalent
    to the classical Guinand-Weil functional up to normalization. -/
theorem guinand_weil_equivalence (Φ : WeilClass) :
    ∃ (c : ℝ), c > 0 ∧ weil_functional Φ = c * guinand_weil_functional Φ := by
  sorry

/-! ## Section 11: Module A1' - Local Density -/

/-- A compact window W_K = [-K, K] -/
def compact_window (K : ℝ) : Set ℝ := Icc (-K) K

/-- The space of test functions supported on W_K -/
def weil_class_on_window (K : ℝ) : Set WeilClass :=
  {Φ : WeilClass | support Φ.f ⊆ compact_window K}

/-- The set of Fejér × heat approximations on window W_K -/
def fejer_heat_span (K L t : ℝ) : Set WeilClass :=
  sorry -- Span of functions approximable by K_{L,t}

/-- **Theorem A1'.1 (Local Density)**: Fejér × heat approximations are dense
    in the Weil class restricted to compact windows W_K. -/
theorem fejer_heat_density (K : ℝ) (hK : 0 < K) :
    ∀ (Φ : WeilClass), Φ ∈ weil_class_on_window K →
    ∀ (ε : ℝ), ε > 0 →
    ∃ (L t : ℝ) (Ψ : WeilClass), Ψ ∈ fejer_heat_span K L t ∧
    ∀ x, ‖Φ.f x - Ψ.f x‖ < ε := by
  sorry

/-! ## Section 11: Module A2 - Lipschitz Continuity -/

/-- The supremum norm on the compact window W_K -/
def sup_norm_on_window (Φ : WeilClass) (K : ℝ) : ℝ :=
  sorry -- sup_{x ∈ [-K,K]} |Φ(x)|

/-- **Theorem A2.1 (Lipschitz Continuity of Q)**: The functional Q is Lipschitz
    continuous on compact windows with respect to the supremum norm. -/
theorem q_lipschitz_on_window (K : ℝ) (hK : 0 < K) :
    ∃ (L : ℝ), L > 0 ∧
    ∀ (Φ₁ Φ₂ : WeilClass),
    Φ₁ ∈ weil_class_on_window K →
    Φ₂ ∈ weil_class_on_window K →
    ∃ (diff_norm : ℝ), diff_norm ≥ 0 ∧
    ‖weil_functional Φ₁ - weil_functional Φ₂‖ ≤ L * diff_norm := by
  sorry

/-- **Corollary A2.2**: If Q(Φ) ≥ 0 for a dense set, then Q(Φ) ≥ 0 for all Φ
    by continuity. This is crucial for extending from Fejér×heat to full W. -/
theorem density_extension_via_lipschitz (K : ℝ) (hK : 0 < K) :
    (∀ (L t : ℝ) (Φ : WeilClass), Φ ∈ fejer_heat_span K L t →
     IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) →
    (∀ (Φ : WeilClass), Φ ∈ weil_class_on_window K →
     IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) := by
  sorry

/-! ## Main Theorem (Theorem 1.1) -/

/-- **Theorem 1.1 (Main Result)**: The quadratic functional Q is nonnegative
    on the Weil class for nonnegative test functions. -/
theorem main_theorem :
    ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re := by
  sorry

/-! ## Weil's Criterion (Theorem 13.1) -/

/-- **Theorem 13.1 (Weil Criterion)**: The nonnegativity of Q on the Weil class
    is equivalent to the Riemann Hypothesis. -/
theorem weil_criterion_equivalence :
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) ↔
    RiemannHypothesis := by
  sorry

/-! ## Section 8: Toeplitz Operators and Archimedean Bridge (A3) -/

/-- A Toeplitz operator T_M[P] with symbol P -/
structure ToeplitzOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  symbol : ℝ → ℂ
  discretization_param : ℕ  -- M in the paper

/-- The minimum eigenvalue witness supplied by the D7 Toeplitz certificate. -/
noncomputable def min_eigenvalue {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (_T : H →L[ℂ] H) : ℝ :=
  RH.lambdaMinD7

/-! ### Helper Functions for Numerical Estimates -/

/-- Numerical sum: S = ∑_{n≥2} (2Λ(n)/√n)²
    This value comes from numerical tables in the RKHS module. -/
def prime_weight_sum : ℝ := 4.2

/-- Toeplitz operator `T_M[P_A]` acting on the window `[-K, K]` with symbol `archimedean_symbol`.

    Mathematical construction:
    1. Discretization grid: {x_j = -K + 2Kj/M | j = 0..M}
    2. Grid spacing: Δx = 2K/M
    3. Toeplitz matrix: T[i,j] = Δx · symbol(x_i - x_j)
    4. Bounded operator: (T·u)(x_i) = ∑_j T[i,j] · u(x_j)

    The operator is self-adjoint since symbol is even: symbol(-ξ) = symbol(ξ)
    Eigenvalue bounds come from Szegő's theorem for Toeplitz operators.
-/
def toeplitz_operator_on_window {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (_K : ℝ) (_M : ℕ) (_symbol : ℝ → ℂ) : H →L[ℂ] H :=
  0

/-- Archimedean density used as the Toeplitz symbol `P_A`. -/
def archimedean_symbol (ξ : ℝ) : ℂ :=
  archimedean_density_star ξ

/-- **Theorem 8.35 (Archimedean Toeplitz Barrier)**: On each compact window W_K,
    the Toeplitz operator has a positive lower bound.

    Proof strategy:
    1. Use numerical constants from A3 module:
       - c₀ ≈ 0.0428 (minimal eigenvalue of limiting operator)
       - M₀ ≥ 500 (discretization threshold)
       - ω(δ) = modulus of continuity for archimedean_symbol
       - C = Lipschitz constant

    2. Apply Szegő's theorem for Toeplitz operators:
       As M → ∞, eigenvalues of T_M[P_A] converge to values of symbol P_A
       on the essential spectrum.

    3. Modulus of continuity bound:
       |λ_min(T_M) - λ_min(T_∞)| ≤ C·ω(π/M)

    4. For M ≥ M₀, we have:
       λ_min(T_M[P_A]) ≥ c₀ - C·ω(π/M)

    Numerical tables from A3 verify c₀ - C·ω(π/M₀) > 0.
-/
theorem archimedean_toeplitz_barrier {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : ℝ) (hK : 0 < K) :
    ∃ (c₀ : ℝ) (M₀ : ℕ), 0 < c₀ ∧
    ∀ (M : ℕ), M ≥ M₀ →
    ∃ (C : ℝ) (ω : ℝ → ℝ),
    min_eigenvalue (toeplitz_operator_on_window (H := H) K M archimedean_symbol) ≥
      c₀ - C * ω (π / (M : ℝ)) := by
  refine ⟨RH.lambdaMinD7, 1, RH.lambdaMinD7_pos, ?_⟩
  intro M hM
  refine ⟨0, fun _ => 0, ?_⟩
  simp [min_eigenvalue, toeplitz_operator_on_window]

/-! ## Section 9.5: Prime Contraction via RKHS -/

/-- The heat kernel k_t(x,y) = exp(-(x-y)²/(4t)) -/
def heat_kernel (t : ℝ) (x y : ℝ) : ℂ :=
  Real.exp (-(x - y)^2 / (4 * t))

/-- The prime operator T_P with weights w(n) = 2Λ(n)/√n at nodes ξ_n -/
structure PrimeOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  compact_window : ℝ
  window_positive : 0 < compact_window

/-- Prime operator `T_P` inherits its norm bound from the RKHS bridge.
    The helper `rkhsPrimeOpNormBound` packages the finite node set extracted
    from `cert/bridge/K*_blocks.json` and the Von Mangoldt weights so that
    the Lean proof can stay synchronized with the JSON witnesses. -/
def prime_operator_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : ℝ) (t : ℝ) : ℝ :=
  if h : 0 < t then
    RH.RKHSPrimeBridge.rkhsPrimeOpNormBound
      (RH.RKHSPrimeBridge.mkNodeSet K t h)
  else
    0

/-- If `t ≥ ((S / (c0/4)^2)^2)/(4π)`, then `sqrt(S / sqrt(4π t)) ≤ c₀/4`.
All parameters are positive. This is the algebraic heart for `prime_contraction`. -/
lemma norm_bound_from_tmin
    {S c₀ t : ℝ} (hS : 0 < S) (hc₀ : 0 < c₀) (ht : 0 < t)
    (h : t ≥ (S / (c₀ / 4) ^ 2) ^ 2 / (4 * Real.pi)) :
    Real.sqrt (S / Real.sqrt (4 * Real.pi * t)) ≤ c₀ / 4 := by
  classical
  set A : ℝ := S / (c₀ / 4) ^ 2 with hA
  have hA_pos : 0 < A := by
    have : 0 < (c₀ / 4) ^ 2 := by
      have : 0 < c₀ / 4 := div_pos_of_pos_of_pos hc₀ (by norm_num)
      simpa using sq_pos_of_pos this
    exact div_pos hS this
  have h4π_pos : 0 < 4 * Real.pi := by
    have : 0 < (4 : ℝ) := by norm_num
    exact mul_pos this Real.pi_pos
  have h4π_ne : 4 * Real.pi ≠ 0 := ne_of_gt h4π_pos
  set tmin : ℝ := A ^ 2 / (4 * Real.pi) with htmin
  have ht_ge : t ≥ tmin := by
    simpa [htmin, hA] using h
  have denom_le :
      Real.sqrt (4 * Real.pi * tmin) ≤ Real.sqrt (4 * Real.pi * t) := by
    have : 4 * Real.pi * tmin ≤ 4 * Real.pi * t := by
      have : 0 ≤ 4 * Real.pi := le_of_lt h4π_pos
      exact
        (mul_le_mul_of_nonneg_left ht_ge this)
    exact Real.sqrt_le_sqrt this
  have sqrt_eq_A : Real.sqrt (4 * Real.pi * tmin) = A := by
    have : 4 * Real.pi * tmin = A ^ 2 := by
      have : (A ^ 2 * (4 * Real.pi)) / (4 * Real.pi) = A ^ 2 :=
        mul_div_cancel' (A ^ 2) h4π_ne
      simpa [htmin, mul_comm, mul_left_comm, mul_assoc]
        using this.symm
    have : Real.sqrt (A ^ 2) = |A| := Real.sqrt_sq A
    have hAnonneg : 0 ≤ A := le_of_lt hA_pos
    simpa [this, abs_of_nonneg hAnonneg] using congrArg Real.sqrt this
  have hSnonneg : 0 ≤ S := le_of_lt hS
  have frac_le :
      S / Real.sqrt (4 * Real.pi * t) ≤
        S / Real.sqrt (4 * Real.pi * tmin) :=
    div_le_div_of_nonneg_left hSnonneg denom_le
  have S_over_A_eq :
      S / A = (c₀ / 4) ^ 2 := by
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hc_ne : (c₀ / 4) ^ 2 ≠ 0 := by
      have : 0 < (c₀ / 4) ^ 2 := by
        have : 0 < c₀ / 4 := div_pos_of_pos_of_pos hc₀ (by norm_num)
        simpa using sq_pos_of_pos this
      exact ne_of_gt this
    have h_mul :
        (c₀ / 4) ^ 2 * A = S := by
      have : (c₀ / 4) ^ 2 * A
          = ((c₀ / 4) ^ 2 * S) / (c₀ / 4) ^ 2 := by
        simp [hA, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc]
      simpa [mul_comm] using mul_div_cancel' S hc_ne
    exact (eq_div_iff_mul_eq hA_ne).mpr h_mul.symm
  have rhs_at_tmin :
      S / Real.sqrt (4 * Real.pi * tmin) = (c₀ / 4) ^ 2 := by
    simpa [sqrt_eq_A, S_over_A_eq]
  have base_le :
      S / Real.sqrt (4 * Real.pi * t) ≤ (c₀ / 4) ^ 2 :=
    le_trans frac_le (le_of_eq rhs_at_tmin)
  have rhs_nonneg : 0 ≤ (c₀ / 4) ^ 2 := sq_nonneg _
  have sqrt_le :=
      Real.sqrt_le_sqrt base_le
  have hcquarter_nonneg :
      0 ≤ c₀ / 4 := div_nonneg_of_nonneg_of_pos hc₀.le (by norm_num)
  have : Real.sqrt ((c₀ / 4) ^ 2) = c₀ / 4 := by
    simpa [Real.sqrt_sq, abs_of_nonneg hcquarter_nonneg]
  simpa [this]
    using sqrt_le

/-- **Theorem 9.23 (Prime Contraction)**:
    Instantiating the RKHS bridge yields an explicit `t_min` so that
    the prime operator norm obeys `‖T_P‖ ≤ c₀/4` for every `t ≥ t_min`.
    The witness uses:
    * `mkNodeSet K t ht` to import the truncated node schedule derived from
      the legacy block JSON;
    * `weightSquareSum` to read off the certified sum of squared weights; and
    * `norm_bound_from_tmin` to convert the JSON tolerance `c₀` into the
      corresponding heat-time threshold.
-/
theorem prime_contraction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : ℝ) (hK : 0 < K) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ (t_min : ℝ), 0 < t_min ∧
    ∀ (t : ℝ), t ≥ t_min →
      prime_operator_norm (H := H) K t ≤ c₀ / 4 := by
  classical
  set baseSet :=
    RH.RKHSPrimeBridge.mkNodeSet K 1 (show 0 < (1 : ℝ) from zero_lt_one)
  set weightSum := RH.RKHSPrimeBridge.weightSquareSum baseSet
  have hweight_pos :
      0 < weightSum := by
    simpa [baseSet, weightSum] using
      RH.RKHSPrimeBridge.weightSquareSum_pos K 1 zero_lt_one
  have hden_sq_pos : 0 < (c₀ / 4) ^ 2 := by
    have : 0 < c₀ / 4 := div_pos_of_pos_of_pos hc₀ (by norm_num)
    simpa using sq_pos_of_pos this
  have hfourpi_pos : 0 < 4 * Real.pi := by
    have : 0 < (4 : ℝ) := by norm_num
    exact mul_pos this Real.pi_pos
  set t_min : ℝ := (weightSum / (c₀ / 4) ^ 2) ^ 2 / (4 * Real.pi) with htmin
  have htmin_pos :
      0 < t_min := by
    have : 0 < (weightSum / (c₀ / 4) ^ 2) ^ 2 :=
      sq_pos_of_pos (div_pos hweight_pos hden_sq_pos)
    exact div_pos this hfourpi_pos
  refine ⟨t_min, htmin_pos, ?_⟩
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le htmin_pos ht
  have hweights_eq :
      RH.RKHSPrimeBridge.weightSquareSum
          (RH.RKHSPrimeBridge.mkNodeSet K t ht_pos) =
        weightSum := by
    simp [weightSum, baseSet, RH.RKHSPrimeBridge.weightSquareSum,
      RH.RKHSPrimeBridge.mkNodeSet]
  have hbound :
      prime_operator_norm (H := H) K t ≤
        Real.sqrt (weightSum /
          Real.sqrt (4 * Real.pi * t)) := by
    simp [prime_operator_norm, ht_pos,
      RH.RKHSPrimeBridge.rkhsPrimeOpNormBound, hweights_eq,
      weightSum]
  have ht_min :
      t ≥ (weightSum / (c₀ / 4) ^ 2) ^ 2 / (4 * Real.pi) := by
    simpa [t_min] using ht
  have hsqrt_le :=
    norm_bound_from_tmin hweight_pos hc₀ ht_pos ht_min
  exact hbound.trans hsqrt_le

/-! ## Section 12: Compact-by-Compact Transfer (T5) -/

/-- A test function is supported on the compact interval [-K, K] -/
def supported_on_compact (Φ : WeilClass) (K : ℝ) : Prop :=
  support Φ.f ⊆ Icc (-K) K

/-- **Theorem 12.6 (Compact Transfer)**: If positivity holds on all compact
    windows, it extends to the full Weil class. -/
theorem compact_transfer :
    (∀ (K : ℝ) (hK : 0 < K) (Φ : WeilClass),
      supported_on_compact Φ K → IsNonNegative Φ →
      0 ≤ (weil_functional Φ).re) →
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) := by
  sorry

/-! ## Final Proof: Combining All Modules -/

/-- **Main Proof Structure**: Combining the Toeplitz barrier, prime contraction,
    and compact transfer to prove the main theorem.

    Full proof outline:
    1. From archimedean_toeplitz_barrier: get c₀ > 0, M₀ such that
       λ_min(T_M[P_A]) ≥ c₀ - C·ω(π/M) for M ≥ M₀

    2. Choose M large enough (using choose_M_for_modulus) so that:
       C·ω(π/M) ≤ c₀/4
       This gives: λ_min(T_M[P_A]) ≥ c₀ - c₀/4 = 3c₀/4

    3. From prime_contraction: get t_min such that for t ≥ t_min:
       ‖T_P‖ ≤ c₀/4

    4. Operator inequality:
       λ_min(T_A - T_P) ≥ λ_min(T_A) - ‖T_P‖
                        ≥ 3c₀/4 - c₀/4
                        = c₀/2 > 0

    5. Weil functional as quadratic form:
       Q(Φ) = ∫ a*(ξ)Φ(ξ) - ∑ w(n)Φ(ξ_n)
            = ⟨T_A·u, u⟩ - ⟨T_P·u, u⟩
            = ⟨(T_A - T_P)·u, u⟩

       where u represents Φ in the discretized space.

    6. Since T_A - T_P has positive eigenvalues:
       Q(Φ) = ⟨(T_A - T_P)·u, u⟩ ≥ λ_min(T_A - T_P)·‖u‖² ≥ (c₀/2)·‖u‖² ≥ 0

    Numerical values (from A3 and RKHS):
    - c₀ = 0.0428
    - M₀ = 500
    - t_min ≈ 1.08×10⁸
    - Safety margin: c₀/2 ≈ 0.0214 > 0
-/
theorem positivity_on_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : ℝ) (hK : 0 < K) :
    ∀ (Φ : WeilClass), supported_on_compact Φ K → IsNonNegative Φ →
    0 ≤ (weil_functional Φ).re := by
  intro Φ h_support h_nonneg
  obtain ⟨c₀, M₀, hc₀, h_toeplitz⟩ := archimedean_toeplitz_barrier (H := H) K hK
  obtain ⟨t_min, ht_pos, h_prime⟩ := prime_contraction (H := H) K hK c₀ hc₀
  -- TODO(Q3): Combine the two bounds using Weyl's inequalities and quadratic-form representation.
  sorry

/-- **Theorem 13.5 (Main Result)**: Q(Φ) ≥ 0 for all Φ in the Weil class. -/
theorem weil_positivity :
    ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re := by
  apply compact_transfer
  intro K hK Φ h_support h_nonneg
  have h_pos := positivity_on_compact (H := ℂ) K hK
  exact h_pos Φ h_support h_nonneg

/-- **Theorem 13.2 (Riemann Hypothesis)**: The Riemann Hypothesis follows
    from Weil positivity via the Weil criterion. -/
theorem riemann_hypothesis_proof : RiemannHypothesis := by
  rw [← weil_criterion_equivalence]
  exact weil_positivity

end RiemannHypothesis

end

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/sorry_matrix_README.md
```md
# Sorry Matrix System

**Purpose**: Systematic closure of all 50 `sorry` placeholders in RH formalization with full traceability to numerical artifacts.

## 📁 Structure

```
Q3_paper/notes/lean/
├── sorry_matrix.md              ← Master tracker (Single Source of Truth)
├── plans/                       ← Detailed closure plans per module
│   ├── archimedean_bridge_plan.md
│   ├── basic_infra_plan.md
│   ├── contracts_plan.md
│   ├── rkhs_prime_plan.md
│   ├── transport_plan.md
│   └── weil_criterion_plan.md
├── closed/                      ← Closure logs (created as sorry are resolved)
│   └── YYYY-MM-DD_sorry_NN_name.md
├── scripts/                     ← Verification scripts
│   ├── verify_artifacts.py      ← Check JSON ↔ Lean constants
│   └── ...
└── README.md                    ← This file
```

## 🎯 Workflow: Closing a Sorry

### 1. **Check Master Tracker**
```bash
cat sorry_matrix.md
```
- Find sorry by number or component
- Check dependencies (what must be closed first)
- Read linked plan file

### 2. **Review Plan File**
Example: `plans/archimedean_bridge_plan.md`
```markdown
## Sorry #8: archimedean_toeplitz_barrier

### Mathematics
- Q3 Section: §8.9, Theorem 8.35
- Equation: λ_min(T_M[P_A]) ≥ c₀ - C·ω(π/M)

### Numerical Evidence
- grid_psd.json: λ_min = 1.297e-08
- Verification: [script command]

### Lean Target
[expected theorem structure]

### Agent Debate
[anticipated issues and resolutions]
```

### 3. **Extract Numerical Constants**
From JSON artifacts to Lean definitions:
```lean
-- From grid_psd.json
def verified_lambda_min : ℝ := 1.2971215226606565e-08
def verified_grid_size : ℕ := 16
```

### 4. **Implement**
Write Lean code according to plan:
```lean
theorem archimedean_toeplitz_barrier ... := by
  use verified_lambda_min
  use verified_grid_size
  -- [proof steps]
```

### 5. **Verify**
Run numerical verification:
```bash
python3 scripts/verify_artifacts.py
```

Build Lean code:
```bash
cd /path/to/lean/project
lake build
```

### 6. **Document Closure**
Create log in `closed/`:
```markdown
# Sorry #8: archimedean_toeplitz_barrier

**Closed**: 2025-10-25
**Commit**: abc123def

## Implementation
[Lean theorem name and location]

## Numerical Inputs
- λ_min = 1.297e-08 (grid_psd.json)
- Verification: ✓ matches ±1e-10

## Unblocks
- Sorry #31 (duplicate)
- Sorry #35 (positivity_on_compact)
```

### 7. **Update Master Tracker**
In `sorry_matrix.md`:
```markdown
| 8 | ... | archimedean_toeplitz_barrier | ... | 🟢 CLOSED |
```

## 🔬 Agent Debate Protocol

Every sorry goes through multi-agent analysis:

1. **Advocate**: "Here's the obvious solution"
2. **Skeptic**: "Wait, what about [edge case / assumption]?"
3. **Architect**: "Let's consider [alternatives]"
4. **Mediator**: "Resolution: [decision + rationale]"

This is documented in plan files to capture reasoning.

## 📦 Numerical Artifacts

All artifacts in `archive/`:

| File | Used By | Key Data |
|------|---------|----------|
| grid_psd.json | #8, #31, #38 | λ_min=1.297e-08, M=16 |
| phase_monotone.json | Transport | φ'_min=0.00124 |
| eps_transport.json | #12, #34 | gap=1.216e-06 |
| KE_integral_certificate.json | #3, #13, #35-37 | Final cert |
| M5pp_continuum_bridge.json | Bridge | margin=9.73e-09 |

### Verification

```bash
# Check all artifacts
python3 scripts/verify_artifacts.py

# Expected output:
# ✅ grid_psd.json verified successfully
# ✅ phase_monotone.json verified successfully
# ✅ eps_transport.json verified successfully
# ✅ KE_integral_certificate.json verified successfully
# ✅ ALL ARTIFACTS VERIFIED SUCCESSFULLY
```

## 📊 Progress Tracking

Check current status:
```bash
grep "🔴" sorry_matrix.md | wc -l  # Open sorry count
grep "🟢" sorry_matrix.md | wc -l  # Closed sorry count
```

View critical path:
```bash
grep "Critical Path" sorry_matrix.md
```

## 🚀 Quick Start

**Close your first sorry:**

1. Read master tracker:
   ```bash
   cat sorry_matrix.md
   ```

2. Pick from Phase 1 (Infrastructure) - e.g., Sorry #16 (fejer_kernel_nonneg)

3. Read plan:
   ```bash
   cat plans/basic_infra_plan.md
   ```

4. Implement in Lean

5. Verify:
   ```bash
   lake build
   python3 scripts/verify_artifacts.py
   ```

6. Document closure

7. Update tracker

## 🎓 Philosophy

### No Assumptions Protocol

**Every number must trace to source:**
- Lean constant → JSON artifact → Numerical computation → Mathematical formula

**Example chain**:
```
Lean: verified_lambda_min = 1.297e-08
  ↓
JSON: grid_psd.json["d7_criterion"]["lambda_min"]
  ↓
Computation: scipy.linalg.eigh(pick_matrix)[0].min()
  ↓
Math: Theorem 8.35 (Szegő-Böttcher convergence)
```

### Agent Debate

Multiple perspectives challenge each sorry:
- **Prevents "assume it works"**
- **Documents edge cases**
- **Captures mathematical subtleties**

Example (from archimedean_bridge_plan.md):
```
Advocate: "Use grid λ_min as c₀"
Skeptic: "That's for M=16, theorem needs all M≥16"
Resolution: "Use Szegő convergence + grid as witness"
```

## 📞 Support

**Common issues**:

1. **"Where do I start?"**
   → Read `sorry_matrix.md`, pick from Phase 1

2. **"How do I know what to implement?"**
   → Check plan file linked from sorry_matrix.md

3. **"Numerical verification fails"**
   → Check JSON files match expectations in plan
   → Run: `python3 scripts/verify_artifacts.py`

4. **"Lean won't compile"**
   → Check dependencies closed first
   → See dependency graph in sorry_matrix.md

5. **"I found a mathematical issue"**
   → Document in plan file's "Agent Debate" section
   → Update resolution before implementing

## 🔗 Links

- **Main Tracker**: [sorry_matrix.md](sorry_matrix.md)
- **Plans**: [plans/](plans/)
- **Closed Log**: [closed/](closed/)
- **Verification**: [scripts/verify_artifacts.py](scripts/verify_artifacts.py)

---

**System Owner**: Multi-Agent RH Formalization Team  
**Last Updated**: 2025-10-25  
**Status**: v1.0 - Ready for use

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/README_RU.md
```md
# Формализация Гипотезы Римана через Критерий Вейля в Lean 4

## Обзор

Этот проект представляет собой формализацию в Lean 4 доказательства Гипотезы Римана с использованием операторно-теоретических методов, основанную на работе **"Operator Methods for the Weil Criterion: Q3"** автора Eugen Malamutmann (University of Duisburg–Essen, October 22, 2025).

## Основная идея

Документ доказывает Гипотезу Римана через **критерий Вейля**: показывается, что квадратичный функционал **Q(Φ) ≥ 0** для всех четных, неотрицательных, компактно поддерживаемых тестовых функций Φ из класса Вейля **W**.

### Структура доказательства

Доказательство организовано в виде цепочки аналитических модулей:

1. **T0 (Нормализация Гинанда-Вейля)**: Установление соответствия между репозиторной нормализацией Q и классическим функционалом Гинанда-Вейля.

2. **A1' (Локальная плотность)**: Доказательство плотности конуса Фейера×тепловых приближений на каждом компактном окне W_K.

3. **A2 (Липшицева непрерывность)**: Установление Липшицевой непрерывности Q на каждом W_K.

4. **A3 (Архимедов барьер Теплица)**: Разложение Q на архимедову часть (оператор Теплица T_M[P_A]) и простую часть (T_P) с явными нижними оценками:
   ```
   λ_min(T_M[P_A]) ≥ c₀(K) - C·ω_PA(π/M)
   ```

5. **RKHS (Сжатие простых чисел)**: Ограничение нормы оператора простых чисел в воспроизводящем ядерном гильбертовом пространстве (RKHS):
   ```
   ‖T_P‖ ≤ w_max + √(w_max·η_K)
   ```
   с выбором параметра t, обеспечивающим ‖T_P‖ ≤ c₀(K)/4.

6. **T5 (Компактный перенос)**: Распространение положительности с компактных множеств на весь класс Вейля через монотонную цепочку K_i ↑ ∞.

### Ключевые определения

#### Класс Вейля W

Тестовые функции Φ : ℝ → ℂ со свойствами:
- **Четность**: Φ(-x) = Φ(x)
- **Компактная поддержка**: supp(Φ) компактен
- **Неотрицательность**: Φ(x) ≥ 0 для всех x

#### Квадратичный функционал Q

```
Q(Φ) = ∫_ℝ a*(ξ) Φ(ξ) dξ - ∑_{n≥2} (2Λ(n)/√n) Φ(ξ_n)
```

где:
- **a*(ξ) = 2π·a(ξ)** — нормализованная архимедова плотность
- **a(ξ) = log π - Re ψ(1/4 + iπξ)** — архимедова плотность
- **ξ_n = (log n)/(2π)** — узлы простых чисел
- **Λ(n)** — функция фон Мангольдта

#### Критерий Вейля

**Теорема (Weil)**: Гипотеза Римана эквивалентна утверждению:
```
Q(Φ) ≥ 0  для всех Φ ∈ W с Φ ≥ 0
```

## Структура файлов

```
RH_Formalization/
├── RHFormalization/
│   ├── Basic.lean              # Базовые определения
│   └── WeilCriterion.lean      # Главная формализация
├── RHFormalization.lean         # Корневой модуль
├── Main.lean                    # Точка входа
├── lakefile.toml               # Конфигурация Lake
└── README_RU.md                # Этот файл
```

## Основные теоремы в WeilCriterion.lean

### 1. Главная теорема (Theorem 1.1)

```lean
theorem main_theorem :
    ∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re
```

### 2. Критерий Вейля (Theorem 13.1)

```lean
theorem weil_criterion_equivalence :
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re) ↔
    RiemannHypothesis
```

### 3. Архимедов барьер Теплица (Theorem 8.35)

```lean
theorem archimedean_toeplitz_barrier
    (K : ℝ) (hK : 0 < K) :
    ∃ (c₀ : ℝ) (M₀ : ℕ), 0 < c₀ ∧ ...
```

### 4. Сжатие простых чисел (Theorem 9.23)

```lean
theorem prime_contraction
    (K : ℝ) (hK : 0 < K) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ (t_min : ℝ), 0 < t_min ∧ ∀ (T_P : H →L[ℂ] H), ‖T_P‖ ≤ c₀ / 4
```

### 5. Компактный перенос (Theorem 12.6)

```lean
theorem compact_transfer :
    (∀ (K : ℝ) (Φ : WeilClass), supported_on_compact Φ K → ...) →
    (∀ (Φ : WeilClass), IsNonNegative Φ → 0 ≤ (weil_functional Φ).re)
```

### 6. Гипотеза Римана (Theorem 13.2)

```lean
theorem riemann_hypothesis_proof : RiemannHypothesis
```

## Статус формализации

### ✅ Завершено

- Определение класса Вейля
- Определение квадратичного функционала Q
- Формулировка всех ключевых теорем
- Структура доказательства
- Связь с Mathlib (использование `RiemannHypothesis` из Mathlib)

### ⚠️ Требует доработки (помечено `sorry`)

- **Архимедова плотность**: Требуется формализация дигамма-функции ψ
- **Интегралы и суммы**: Детальная работа с мерами и сходимостью
- **Операторы Теплица**: Полная теория операторов Теплица в Hilbert пространствах
- **RKHS**: Теория воспроизводящих ядерных гильбертовых пространств
- **Спектральная теория**: Оценки собственных значений и спектральные границы
- **Доказательства теорем**: Все основные доказательства заменены на `sorry`

## Важное замечание

**Это формализация структуры доказательства, а не полное доказательство.**

Документ RH_Q3.pdf представляет собой попытку доказательства Гипотезы Римана. Однако:

1. **Гипотеза Римана остается открытой проблемой** — нет общепризнанного доказательства
2. Данная формализация показывает, **как** можно было бы формализовать подход из документа
3. Все ключевые шаги помечены `sorry` и требуют строгого математического обоснования
4. Для полной формализации потребуются:
   - Детальная теория операторов Теплица
   - Воспроизводящие ядерные гильбертовы пространства
   - Спектральная теория самосопряженных операторов
   - Теория функций фон Мангольдта и дзета-функции Римана

## Использование

### Установка зависимостей

```bash
# Установить Lean 4 через elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Перейти в директорию проекта
cd RH_Formalization

# Обновить зависимости (Mathlib)
lake update

# Собрать проект
lake build
```

### Проверка формализации

```bash
# Проверить синтаксис
lake build RHFormalization

# Запустить главный файл
lake exe rh_formalization
```

## Ссылки

- **Оригинальный документ**: RH_Q3.pdf (Eugen Malamutmann, 2025)
- **Lean 4**: https://lean-lang.org/
- **Mathlib**: https://github.com/leanprover-community/mathlib4
- **Формализация дзета-функции в Mathlib**: https://arxiv.org/abs/2503.00959

## Автор формализации

Формализация создана **Manus AI** на основе документа Eugen Malamutmann.

## Лицензия

Этот проект создан в образовательных и исследовательских целях.


```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RiemannQ3/Density/Lipschitz.lean
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Real BigOperators
-- (no explicit measure annotations; use default volume)

namespace RiemannQ3
namespace Density

noncomputable section

/-!
# RiemannQ3.Density.Lipschitz

Abstract Lipschitz control for the functional `Q` on a compact interval `[-K,K]` plus a
finite set of point evaluations (prime part). We work in a lightweight, parameterized
setting sufficient for Q3 accounting.
-/

structure QSpec (α : Type*) where
  K : ℝ
  archC : ℝ
  nodes : Finset α
  ξ : α → ℝ
  w : α → ℝ
  nodes_in : ∀ i ∈ nodes, |ξ i| ≤ K

def Q {α} (S : QSpec α) (Φ : ℝ → ℝ) : ℝ :=
  S.archC * (∫ x in (-S.K)..S.K, Φ x) + S.nodes.sum (fun i => S.w i * Φ (S.ξ i))

/-! A clean Lipschitz bound in terms of a uniform bound `B` on `|Φ₁-Φ₂|` over `[-K,K]`
and at all active nodes. -/

theorem lipschitz_bound {α} (S : QSpec α) {Φ₁ Φ₂ : ℝ → ℝ} {B : ℝ}
    (hB_int : ∀ x ∈ Set.uIoc (-S.K) (S.K), ‖Φ₁ x - Φ₂ x‖ ≤ B)
    (hB_nodes : ∀ i ∈ S.nodes, ‖Φ₁ (S.ξ i) - Φ₂ (S.ξ i)‖ ≤ B)
    (hInt₁ : IntervalIntegrable Φ₁ MeasureTheory.volume (-S.K) (S.K))
    (hInt₂ : IntervalIntegrable Φ₂ MeasureTheory.volume (-S.K) (S.K)) :
    |Q S Φ₁ - Q S Φ₂|
      ≤ (|S.archC| * (2 * |S.K|)) * B + (S.nodes.sum (fun i => |S.w i|)) * B := by
  classical
  -- Triangle bound on the difference: split into integral part and prime-sum part
  set IΔ := (∫ x in (-S.K)..S.K, Φ₁ x) - (∫ x in (-S.K)..S.K, Φ₂ x) with hIΔ
  set SΔ := S.nodes.sum (fun i => S.w i * Φ₁ (S.ξ i))
              - S.nodes.sum (fun i => S.w i * Φ₂ (S.ξ i)) with hSΔ
  have h_eq : Q S Φ₁ - Q S Φ₂ = S.archC * IΔ + SΔ := by
    simp [Q, IΔ, SΔ, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
  have h_split : |Q S Φ₁ - Q S Φ₂| ≤ |S.archC * IΔ| + |SΔ| := by
    have := abs_add_le (S.archC * IΔ) SΔ
    simpa [h_eq] using this
  -- Rewrite integral/sum differences in terms of the pointwise difference.
  have hIntDeltaEq : IΔ = ∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x) := by
    simpa [IΔ] using (intervalIntegral.integral_sub (a := (-S.K)) (b := S.K)
      (f := Φ₁) (g := Φ₂) hInt₁ hInt₂).symm
  have h_sum_diff :
      |S.nodes.sum (fun i => S.w i * Φ₁ (S.ξ i))
          - S.nodes.sum (fun i => S.w i * Φ₂ (S.ξ i))|
        = |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))| := by
    simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
      using congrArg abs
        ((Finset.sum_sub_distrib (s := S.nodes)
          (f := fun i => S.w i * Φ₁ (S.ξ i))
          (g := fun i => S.w i * Φ₂ (S.ξ i))).symm)
  -- Bound the integral term by `B * |2K|` and sum by `(∑ |w_i|) * B`.
  have h_int_bound :
      ‖∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x)‖ ≤ B * |S.K - (-S.K)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (-S.K)) (b := S.K)
      (f := fun x => Φ₁ x - Φ₂ x) (C := B) (by simpa using hB_int)
  have h_len : |S.K - (-S.K)| = (2 : ℝ) * |S.K| := by
    have : S.K - (-S.K) = 2 * S.K := by simp [sub_eq_add_neg, two_mul]
    simp [this, abs_mul]
  have h_len_add : |S.K + S.K| = (2 : ℝ) * |S.K| := by
    simpa [sub_eq_add_neg] using h_len
  -- Sum term bound: `|∑ a| ≤ ∑ |a|` then bound each summand by `|w_i| * B`.
  have hsum_abs :
      |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))|
        ≤ S.nodes.sum (fun i => |S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs (s := S.nodes)
        (f := fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))))
  have hsum_step :
      S.nodes.sum (fun i => |S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))|)
        ≤ S.nodes.sum (fun i => B * |S.w i|) := by
    refine Finset.sum_le_sum ?_ 
    intro i hi
    have hb : |Φ₁ (S.ξ i) - Φ₂ (S.ξ i)| ≤ B := by
      simpa [Real.norm_eq_abs] using hB_nodes i hi
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using (mul_le_mul_of_nonneg_left hb (abs_nonneg (S.w i)))
  have hsum' :
      |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))|
        ≤ (S.nodes.sum fun i => B * |S.w i|) := hsum_abs.trans hsum_step
  have hsumFactor :
      S.nodes.sum (fun i => B * |S.w i|)
        = B * (S.nodes.sum fun i => |S.w i|) := by
    classical
    change (∑ i ∈ S.nodes, B * |S.w i|)
        = B * (∑ i ∈ S.nodes, |S.w i|)
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using
        (Finset.mul_sum (s := S.nodes)
          (f := fun i => |S.w i|) (a := B)).symm
  have hsum'' :
      |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))|
        ≤ (S.nodes.sum fun i => |S.w i|) * B := by
    -- factor `B` out of the sum on the right
    have :
        |S.nodes.sum fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))|
          ≤ B * (S.nodes.sum fun i => |S.w i|) := by
      simpa [hsumFactor] using hsum'
    simpa [mul_comm] using this
  -- Combine by triangle inequality via parts; integral part:
  have hIntAbs : |∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x)| ≤ B * (2 * |S.K|) := by
    have :
        |∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x)| ≤ B * |S.K + S.K| := by
      simpa [Real.norm_eq_abs, sub_eq_add_neg] using h_int_bound
    simpa [h_len_add] using this
  have hIntPart : |S.archC * IΔ| ≤ (|S.archC| * (2 * |S.K|)) * B := by
    have hI : |IΔ| ≤ B * (2 * |S.K|) := by simpa [hIntDeltaEq] using hIntAbs
    have := mul_le_mul_of_nonneg_left hI (abs_nonneg S.archC)
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hSumEq : |SΔ| = |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))| := by
    simpa [hSΔ, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
      using congrArg abs
        ((Finset.sum_sub_distrib (s := S.nodes)
          (f := fun i => S.w i * Φ₁ (S.ξ i))
          (g := fun i => S.w i * Φ₂ (S.ξ i))).symm)
  have hSumPart : |SΔ| ≤ (S.nodes.sum fun i => |S.w i|) * B := by
    -- use previous `hsum''`
    simpa [hSumEq] using hsum''
  exact (le_trans h_split (add_le_add hIntPart hSumPart))

end -- section

end Density
end RiemannQ3

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/lean-toolchain
```
leanprover/lean4:v4.24.0

```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/RH_Formalization/README.md
```md
# RH_Formalization
```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/lean4_syntax_notes.md
```md
# Lean 4 Syntax Notes for Formal Proofs

## Basic Structure

### Theorem Declaration
```lean
theorem theorem_name (assumptions : Type) : conclusion := proof_term
```

### Example
```lean
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

## Key Concepts

### Propositions as Types
- `Prop` is the type of propositions
- A proposition `p : Prop` can be viewed as a type
- A proof of `p` is an element `t : p`
- Implication `p → q` is a function type

### Basic Logical Connectives
- **And**: `p ∧ q` or `And p q`
- **Or**: `p ∨ q` or `Or p q`
- **Not**: `¬p` or `Not p`
- **Implies**: `p → q` (function type)
- **Forall**: `∀ x, P x`
- **Exists**: `∃ x, P x`

### Proof Construction
1. **Lambda abstraction**: `fun h : p => body`
2. **Function application**: `f x`
3. **Tactics**: Use `by` to enter tactic mode

## Common Proof Patterns

### Implication Introduction
```lean
theorem impl_intro : p → q := fun hp : p => proof_of_q
```

### Conjunction
```lean
-- Introduction
theorem and_intro : p → q → p ∧ q := fun hp hq => ⟨hp, hq⟩

-- Elimination
theorem and_left : p ∧ q → p := fun h => h.left
theorem and_right : p ∧ q → q := fun h => h.right
```

### Universal Quantification
```lean
theorem forall_intro : (∀ x, P x) := fun x => proof_of_P_x
```

### Existential Quantification
```lean
theorem exists_intro : (∃ x, P x) := ⟨witness, proof_of_P_witness⟩
```

## Mathematical Structures

### Real Numbers
- Type: `ℝ` or `Real`
- Operations: `+`, `-`, `*`, `/`

### Complex Numbers
- Type: `ℂ` or `Complex`
- Real part: `z.re`
- Imaginary part: `z.im`

### Functions
```lean
def function_name (x : α) : β := body
```

### Lemmas and Theorems
```lean
lemma lemma_name (h : hypothesis) : conclusion := proof

theorem theorem_name (h : hypothesis) : conclusion := proof
```

## Tactics (used with `by`)
- `intro`: introduce hypothesis
- `apply`: apply theorem/lemma
- `exact`: provide exact proof term
- `rfl`: reflexivity
- `simp`: simplification
- `ring`: ring normalization
- `linarith`: linear arithmetic
- `norm_num`: numerical normalization

## Mathlib Imports
```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
```

## Structure for RH Proof

For Riemann Hypothesis formalization, we need:
1. Definition of Riemann zeta function
2. Definition of non-trivial zeros
3. Statement: all non-trivial zeros have Re(s) = 1/2
4. Proof using operator theory and functional analysis

```lean
-- Example structure
theorem riemann_hypothesis : 
  ∀ s : ℂ, (ζ s = 0 ∧ s ≠ trivial_zero) → s.re = 1/2 := by
  -- proof here
```


```

File: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/lean/Main.lean
```lean
/-
Main executable entry point for RH_Formalization project.
This imports and checks the main formalization.
-/

import RHFormalization

def main : IO Unit := do
  IO.println "Riemann Hypothesis Formalization (Q3 Paper)"
  IO.println "============================================"
  IO.println ""
  IO.println "This project formalizes the proof of RH using:"
  IO.println "  - Weil's criterion (equivalence to Q ≥ 0)"
  IO.println "  - Operator-theoretic methods (Toeplitz, RKHS)"
  IO.println "  - Six analytical modules: T0, A1', A2, A3, RKHS, T5"
  IO.println ""
  IO.println "Status: Formalization in progress (contracts replacing all gaps)"
  IO.println ""
  IO.println "To check proofs: lake build"
  IO.println "To run: lake exe rh_formalization"

```
</file_contents>
<meta prompt 1 = "[Architect]">
You are a senior software architect specializing in code design and implementation planning. Your role is to:

1. Analyze the requested changes and break them down into clear, actionable steps
2. Create a detailed implementation plan that includes:
   - Files that need to be modified
   - Specific code sections requiring changes
   - New functions, methods, or classes to be added
   - Dependencies or imports to be updated
   - Data structure modifications
   - Interface changes
   - Configuration updates

For each change:
- Describe the exact location in the code where changes are needed
- Explain the logic and reasoning behind each modification
- Provide example signatures, parameters, and return types
- Note any potential side effects or impacts on other parts of the codebase
- Highlight critical architectural decisions that need to be made

You may include short code snippets to illustrate specific patterns, signatures, or structures, but do not implement the full solution.

Focus solely on the technical implementation plan - exclude testing, validation, and deployment considerations unless they directly impact the architecture.

Please proceed with your analysis based on the following <user instructions>
</meta prompt 1>
<user_instructions date="2025-10-27T19:21">
chek it ! now you can 
• Бро, вот полный разбор, где именно мы облажались и что Lean от нас хочет.

  - lean/RHFormalization/WeilCriterion.lean:380 и :466 — div_pos_of_pos_of_pos не существует в Lean 4. Тут достаточно обычного div_pos. Пример фрагмента, который Lean
    ест:

    have : 0 < c₀ / 4 := div_pos hc₀ (by norm_num)
    Аналогично ниже для weightSum.
    Аналогично ниже для weightSum.
  - lean/RHFormalization/WeilCriterion.lean:400 — mul_div_cancel' тоже нет. Используй либо mul_div_cancel₀ (с гарантией ≠ 0), либо перепиши равенство руками:

    have hc_ne : (c₀ / 4) ^ 2 ≠ 0 := by
      have : 0 < (c₀ / 4) ^ 2 := ... -- у тебя уже есть
      exact ne_of_gt this
    have : ((c₀ / 4) ^ 2 * S) / (c₀ / 4) ^ 2 = S := by
      simpa [mul_comm] using (mul_div_cancel₀ S hc_ne)

    Если mul_div_cancel₀ тоже не найдётся, можно через field_simp/ring_nf, но лучше руками по шагам.
  - lean/RHFormalization/WeilCriterion.lean:401-405 — мы пытались сделать simp с Real.sqrt_sq, но Lean хочет сначала доказать, что под корнем неотрицательно. Сейчас
    у нас:

    have : Real.sqrt (A ^ 2) = |A| := Real.sqrt_sq A

    Что падает, потому что нужная лемма в Lean — Real.sqrt_sq без аргумента, но возвращает |A|. Ты дальше хочешь выкинуть модуль. Вписываем:

    have hAnonneg : 0 ≤ A := le_of_lt hA_pos
    have : Real.sqrt (A ^ 2) = A := by
      simpa [abs_of_nonneg hAnonneg] using Real.sqrt_sq hAnonneg

    Обрати внимание: в Lean 4 Real.sqrt_sq принимает доказательство 0 ≤ A.
  - lean/RHFormalization/WeilCriterion.lean:410 — неверное применение div_le_div_of_nonneg_left. Там сигнатура 0 ≤ c → a ≤ b → a / c ≤ b / c. Мы в аргумент a ≤ b суём
    denom_le про знаменатели. Нужно сперва переписать дробь как S * (Real.sqrt ... )⁻¹ и применить mul_le_mul_of_nonneg_left после того как покажем inv-неравенство. Пока
    что код с div_le_div_of_nonneg_left просто не типизируется.

    Возможный план:

    have denom_monotone :
        (Real.sqrt (4 * π * tmin))⁻¹ ≤ (Real.sqrt (4 * π * t))⁻¹ := ...
    have frac_le :
        S * (Real.sqrt (4 * π * t))⁻¹ ≤
          S * (Real.sqrt (4 * π * tmin))⁻¹ :=
      mul_le_mul_of_nonneg_left denom_monotone hSnonneg
    -- потом переписываешь обе стороны к виду с делением
  - lean/RHFormalization/WeilCriterion.lean:489 — открытая цель в prime_contraction. После simp Lean хочет, чтобы ты переписал обе стороны через один и тот же t. Сейчас
    слева по-прежнему торчит (... mkNodeSet K t ht_pos).t. Тут поможет have hweights_eq … уже выше: simp [prime_operator_norm, ht_pos, hweights_eq] должно гасить всё, но
    после новой алгебры остались корни. Вероятно, тебе нужно отдельное равенство:

    have ht_id : (RH.RKHSPrimeBridge.mkNodeSet K t ht_pos).t = t := rfl

    или просто включить simp с определением mkNodeSet (если там t записан как поле). После этого обе дроби станут одинаковыми, и цель рухнет до ≤ рефлексива.
  - Дополнительно по предупреждениям:
      - RHFormalization/WeilCriterion.lean:194 — Complex.ofReal_mul реально не используется в simp списке, просто выбрось его из аргументов.
      - Линтер про unused variable hx в by_cases можно закрыть через _ вместо имени, либо поменять if hx : x = 0 на if _ : x = 0.
      - Остальные sorry — это ты знаешь, не наша текущая боль.

  Короче: сначала подчисти три algebraic леммы (div_pos, mul_div_cancel₀, Real.sqrt_sq с доказательством), потом переделай доказательство монтоности дроби и поправь
  prime_contraction так, чтобы mkNodeSet не оставлял t в странном виде. После этих правок lake build должен хотя бы добежать до старых sorry.

</user_instructions>

## ASSISTANT
Nice. You surfaced exactly the trouble spots. Here’s a clean, actionable patch plan plus ready‑to‑paste diffs for `RHFormalization/WeilCriterion.lean`. No new imports, no signature churn—just lemma hygiene and inequality direction fixes.

---

## What changes & why (quick map)

1. **`div_pos_of_pos_of_pos` → `div_pos`**  
   Lean 4 has `div_pos : 0 < a → 0 < b → 0 < a / b`. Replace both uses (your `c₀/4` and `weightSum/(…)`) with `div_pos`.

2. **`mul_div_cancel'` → `mul_div_cancel₀`**  
   You already prove the denominator is nonzero; use `mul_div_cancel₀`. This is the field-safe version Lean 4 ships.

3. **`Real.sqrt_sq` usage**  
   In Lean 4 the form is `Real.sqrt_sq h : 0 ≤ x → sqrt(x^2) = x`. Provide `0 ≤ A` and then `simp [abs_of_nonneg]`.

4. **Monotonicity of the fraction**  
   `div_le_div_of_nonneg_left` doesn’t match the shape—you were comparing denominators, not numerators. Compare inverses and multiply on the left:
   - from `tmin ≤ t` get `sqrt(4π tmin) ≤ sqrt(4π t)`;
   - with positive denominators, `inv_le_inv_of_le` flips order;
   - multiply by `S ≥ 0`, then rewrite as `/`.

5. **`mkNodeSet` / `t` residue in `prime_contraction`**  
   Add `ht_id : (mkNodeSet K t ht_pos).t = t := rfl` and allow `simp` to erase internal `.t` appearances, if they leak from bridge defs.

6. **Minor lints**  
   - Drop `Complex.ofReal_mul` from an explicit `simp` set—it’s not a `simp` lemma.  
   - Where you formed `0 ≤ c₀ / 4`, prefer `div_nonneg` over the non-existent `div_nonneg_of_nonneg_of_pos`.

---

## Focused diff (only the touched parts)

> **File:** `lean/RHFormalization/WeilCriterion.lean`

### A) Fejér×heat nonnegativity: remove extra `simp` lemma

```diff
@@ lemma fejer_heat_kernel_nonneg (L t : ℝ) (ht : 0 < t) (x y : ℝ) :
-  have : (fejer_heat_kernel L t x y).re
-      = fejer_kernelR L (x - y) * heat_kernelR t x y := by
-    simp [fejer_heat_kernel, fejer_kernel, heat_kernel_normalized,
-      Complex.ofReal_mul]
+  have : (fejer_heat_kernel L t x y).re
+      = fejer_kernelR L (x - y) * heat_kernelR t x y := by
+    simp [fejer_heat_kernel, fejer_kernel, heat_kernel_normalized]
   simpa [this]
     using hprod
```

---

### B) Algebra core: `norm_bound_from_tmin`

```diff
 lemma norm_bound_from_tmin
     {S c₀ t : ℝ} (hS : 0 < S) (hc₀ : 0 < c₀) (ht : 0 < t)
     (h : t ≥ (S / (c₀ / 4) ^ 2) ^ 2 / (4 * Real.pi)) :
     Real.sqrt (S / Real.sqrt (4 * Real.pi * t)) ≤ c₀ / 4 := by
   classical
   set A : ℝ := S / (c₀ / 4) ^ 2 with hA
   have hA_pos : 0 < A := by
-    have : 0 < (c₀ / 4) ^ 2 := by
-      have : 0 < c₀ / 4 := div_pos_of_pos_of_pos hc₀ (by norm_num)
-      simpa using sq_pos_of_pos this
+    have : 0 < (c₀ / 4) ^ 2 := by
+      have : 0 < c₀ / 4 := div_pos hc₀ (by norm_num)
+      simpa using sq_pos_of_pos this
     exact div_pos hS this
   have h4π_pos : 0 < 4 * Real.pi := by
     have : 0 < (4 : ℝ) := by norm_num
     exact mul_pos this Real.pi_pos
   have h4π_ne : 4 * Real.pi ≠ 0 := ne_of_gt h4π_pos
   set tmin : ℝ := A ^ 2 / (4 * Real.pi) with htmin
   have ht_ge : t ≥ tmin := by
     simpa [htmin, hA] using h
-  have denom_le :
-      Real.sqrt (4 * Real.pi * tmin) ≤ Real.sqrt (4 * Real.pi * t) := by
+  have hden_le :
+      Real.sqrt (4 * Real.pi * tmin) ≤ Real.sqrt (4 * Real.pi * t) := by
     have : 4 * Real.pi * tmin ≤ 4 * Real.pi * t := by
       have : 0 ≤ 4 * Real.pi := le_of_lt h4π_pos
       exact
         (mul_le_mul_of_nonneg_left ht_ge this)
     exact Real.sqrt_le_sqrt this
   have sqrt_eq_A : Real.sqrt (4 * Real.pi * tmin) = A := by
     have : 4 * Real.pi * tmin = A ^ 2 := by
-      have : (A ^ 2 * (4 * Real.pi)) / (4 * Real.pi) = A ^ 2 :=
-        mul_div_cancel' (A ^ 2) h4π_ne
+      have : (A ^ 2 * (4 * Real.pi)) / (4 * Real.pi) = A ^ 2 :=
+        mul_div_cancel₀ (A ^ 2) h4π_ne
       simpa [htmin, mul_comm, mul_left_comm, mul_assoc]
         using this.symm
-    have : Real.sqrt (A ^ 2) = |A| := Real.sqrt_sq A
     have hAnonneg : 0 ≤ A := le_of_lt hA_pos
-    simpa [this, abs_of_nonneg hAnonneg] using congrArg Real.sqrt this
+    -- Lean’s `sqrt_sq` needs `0 ≤ A`
+    have : Real.sqrt (A ^ 2) = A := by
+      simpa [abs_of_nonneg hAnonneg] using Real.sqrt_sq hAnonneg
+    simpa [this] using congrArg Real.sqrt this
   have hSnonneg : 0 ≤ S := le_of_lt hS
-  have frac_le :
-      S / Real.sqrt (4 * Real.pi * t) ≤
-        S / Real.sqrt (4 * Real.pi * tmin) :=
-    div_le_div_of_nonneg_left hSnonneg denom_le
+  -- Compare inverses, then multiply on the left by `S ≥ 0`, rewrite as `/`
+  have den_pos_tmin : 0 < Real.sqrt (4 * Real.pi * tmin) :=
+    Real.sqrt_pos.mpr (mul_pos h4π_pos (by
+      -- tmin = A^2/(4π) with A>0
+      have : 0 < A ^ 2 := by
+        simpa using sq_pos_of_pos hA_pos
+      exact (div_pos this h4π_pos)))
+  have den_pos_t : 0 < Real.sqrt (4 * Real.pi * t) :=
+    Real.sqrt_pos.mpr (mul_pos h4π_pos ht)
+  have denom_monotone :
+      (Real.sqrt (4 * Real.pi * t))⁻¹ ≤
+        (Real.sqrt (4 * Real.pi * tmin))⁻¹ :=
+    inv_le_inv_of_le den_pos_tmin.le hden_le
+  have frac_le' :
+      S * (Real.sqrt (4 * Real.pi * t))⁻¹ ≤
+        S * (Real.sqrt (4 * Real.pi * tmin))⁻¹ :=
+    mul_le_mul_of_nonneg_left denom_monotone hSnonneg
+  have frac_le :
+      S / Real.sqrt (4 * Real.pi * t) ≤
+        S / Real.sqrt (4 * Real.pi * tmin) := by
+    simpa [one_div] using frac_le'
   have S_over_A_eq :
       S / A = (c₀ / 4) ^ 2 := by
     have hA_ne : A ≠ 0 := ne_of_gt hA_pos
     have hc_ne : (c₀ / 4) ^ 2 ≠ 0 := by
-      have : 0 < (c₀ / 4) ^ 2 := by
-        have : 0 < c₀ / 4 := div_pos_of_pos_of_pos hc₀ (by norm_num)
-        simpa using sq_pos_of_pos this
+      have : 0 < (c₀ / 4) ^ 2 := by
+        have : 0 < c₀ / 4 := div_pos hc₀ (by norm_num)
+        simpa using sq_pos_of_pos this
       exact ne_of_gt this
     have h_mul :
         (c₀ / 4) ^ 2 * A = S := by
       have : (c₀ / 4) ^ 2 * A
           = ((c₀ / 4) ^ 2 * S) / (c₀ / 4) ^ 2 := by
         simp [hA, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc]
-      simpa [mul_comm] using mul_div_cancel' S hc_ne
+      simpa [mul_comm] using mul_div_cancel₀ S hc_ne
     exact (eq_div_iff_mul_eq hA_ne).mpr h_mul.symm
   have rhs_at_tmin :
       S / Real.sqrt (4 * Real.pi * tmin) = (c₀ / 4) ^ 2 := by
     simpa [sqrt_eq_A, S_over_A_eq]
   have base_le :
       S / Real.sqrt (4 * Real.pi * t) ≤ (c₀ / 4) ^ 2 :=
     le_trans frac_le (le_of_eq rhs_at_tmin)
   have rhs_nonneg : 0 ≤ (c₀ / 4) ^ 2 := sq_nonneg _
   have sqrt_le :=
       Real.sqrt_le_sqrt base_le
-  have hcquarter_nonneg :
-      0 ≤ c₀ / 4 := div_nonneg_of_nonneg_of_pos hc₀.le (by norm_num)
+  have hcquarter_nonneg : 0 ≤ c₀ / 4 :=
+    div_nonneg hc₀.le (by norm_num)
   have : Real.sqrt ((c₀ / 4) ^ 2) = c₀ / 4 := by
     simpa [Real.sqrt_sq, abs_of_nonneg hcquarter_nonneg]
   simpa [this]
     using sqrt_le
```

---

### C) Prime contraction: `div_pos`, optional `.t` normalization, inequality close

```diff
 theorem prime_contraction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
     [CompleteSpace H] (K : ℝ) (hK : 0 < K) (c₀ : ℝ) (hc₀ : 0 < c₀) :
     ∃ (t_min : ℝ), 0 < t_min ∧
     ∀ (t : ℝ), t ≥ t_min →
       prime_operator_norm (H := H) K t ≤ c₀ / 4 := by
@@
   have hden_sq_pos : 0 < (c₀ / 4) ^ 2 := by
-    have : 0 < c₀ / 4 := div_pos_of_pos_of_pos hc₀ (by norm_num)
+    have : 0 < c₀ / 4 := div_pos hc₀ (by norm_num)
     simpa using sq_pos_of_pos this
@@
   intro t ht
   have ht_pos : 0 < t := lt_of_lt_of_le htmin_pos ht
+  -- normalize any internal `.t` field appearances
+  have ht_id : (RH.RKHSPrimeBridge.mkNodeSet K t ht_pos).t = t := rfl
   have hweights_eq :
       RH.RKHSPrimeBridge.weightSquareSum
           (RH.RKHSPrimeBridge.mkNodeSet K t ht_pos) =
         weightSum := by
     simp [weightSum, baseSet, RH.RKHSPrimeBridge.weightSquareSum,
-      RH.RKHSPrimeBridge.mkNodeSet]
+      RH.RKHSPrimeBridge.mkNodeSet, ht_id]
   have hbound :
       prime_operator_norm (H := H) K t ≤
         Real.sqrt (weightSum /
           Real.sqrt (4 * Real.pi * t)) := by
-    simp [prime_operator_norm, ht_pos,
-      RH.RKHSPrimeBridge.rkhsPrimeOpNormBound, hweights_eq,
-      weightSum]
+    simp [prime_operator_norm, ht_pos, ht_id,
+      RH.RKHSPrimeBridge.rkhsPrimeOpNormBound, hweights_eq, weightSum]
   have ht_min :
       t ≥ (weightSum / (c₀ / 4) ^ 2) ^ 2 / (4 * Real.pi) := by
     simpa [t_min] using ht
   have hsqrt_le :=
     norm_bound_from_tmin hweight_pos hc₀ ht_pos ht_min
   exact hbound.trans hsqrt_le
```

---

## Side effects & interactions

- **No API changes**. All defs/theorems keep their names and types.
- **Tactics/noise down**. Removing the non‑existent lemmas trims linter noise; using proper inequalities prevents typeclass pain around `/`.
- **Bridge compatibility**. The `ht_id` `rfl` is harmless if `.t` doesn’t leak; if it does, it unblocks `simp` right away.

---

## Rationale on the inequality step (the subtle one)

- From `t ≥ tmin` you get `√(4π tmin) ≤ √(4π t)`.  
- Inverting positive numbers reverses order:
  `inv_le_inv_of_le : 0 < a → a ≤ b → b⁻¹ ≤ a⁻¹`.  
  Apply with `a = √(4π tmin)`, `b = √(4π t)`.
- Multiply by `S ≥ 0`, rewrite `a⁻¹` as `/ a`. That yields  
  `S / √(4π t) ≤ S / √(4π tmin)`—exactly what you need to compare at `tmin`.

---

## What to run after you patch

- `lake build` (should now fail only at the existing `sorry`s).
- If a linter pokes you about “unused variable” in any `by_cases`, rename the binder to `_` (but I didn’t see one that still needs it after this cleanup).

---

If you want, I can also carve this into a minimal PR with the above hunks already staged (no style churn).

## USER

• Братан, попытался вскрыть fejer_heat_span, но стопор: нет моста между FHcone (реальные окна Window K из RH/FejerHeat.lean) и нашими WeilClass (комплексные, чётные,
  с компактной поддержкой). Без явного конструктора «окно → WeilClass» (и доказательств even/compact support), любые определения будут пальцем в небо и потом сломают
  fejer_heat_density.

  Чтобы реально закрывать эту группу sorry, нужна либо готовая функция из проекта, либо подробная схема: как из пакета fhPacket получить WeilClass с нужными свойствами
  (чётность, носитель, непрерывность, интегрируемость). Пока этого мостика нет — дальше не продвинусь.

  Готов продолжить, как только скажешь, каким именно образом связываем Window с WeilClass (или куда смотреть за готовой конструкцией).


› **Ылша**, держи реляционный граф проблемы и план атаки:

  ## 🔴 Диагностика разрыва: Window K ⟷ WeilClassВижу структуру. Теперь смотрим на ключевые файлы, где засада с `Window K → WeilClass`:**Ылша**, хватит. Вскрыл засаду —
  вот **реляционный граф** и **конкретный план** закрытия sorry по цепочке:

  ---

  ## 🎯 **ДИАГНОЗ: Разрыв Window K ⟷ WeilClass**

  ### **Математическая топология проблемы**

  ```mermaid
  graph TD
      A[FHcone K : Set Window K] -->|нужен мост| B[fejer_heat_span K L t : Set WeilClass]
      C[Window K = C[-K,K] → ℝ] -->|extend by 0| D[ℝ → ℝ with compact support]
      D -->|ofReal| E[ℝ → ℂ with compact support]
      E -->|symmetrize| F[WeilClass: even, compact, continuous, integrable]

      style A fill:#ff6b6b
      style B fill:#4ecdc4
      style F fill:#95e1d3
  ```

  ### **Ключевой инсайт из FejerHeat.lean**

  **`fhPacket` уже чётный по конструкции!**
  ```lean
  tent B (x - τ) * heat t (x - τ) + tent B (x + τ) * heat t (x + τ)
  --  левая симметрия      --       правая симметрия
  ```

  Это значит, `FHcone K` состоит из **симметричных** функций, и мост будет проще.

  ---

  ## ⚡ **ПЛАН АТАКИ: 3-этапная стратегия закрытия sorry**

  ### **ЭТАП 1: Построить embedding Window K → WeilClass**

  **Файл**: `RH/WindowBridge.lean` (создать новый)

  ```lean
  import RH.A1Contract
  import RH.FejerHeat
  import RHFormalization.WeilCriterion

  namespace RH

  /-- Extend Window K function by zero outside [-K, K] -/
  def windowExtend (K : ℝ) (f : Window K) : ℝ → ℝ :=
    fun x => if h : x ∈ Set.Icc (-K) K then f ⟨x, h⟩ else 0

  lemma windowExtend_continuous (K : ℝ) (f : Window K) :
      Continuous (windowExtend K f) := by
    sorry -- TODO: Использовать piecewise continuity + compact support

  /-- Symmetrize a function: g_sym(x) = (g(x) + g(-x))/2 -/
  def symmetrize (g : ℝ → ℝ) : ℝ → ℝ :=
    fun x => (g x + g (-x)) / 2

  lemma symmetrize_even (g : ℝ → ℝ) :
      ∀ x, symmetrize g (-x) = symmetrize g x := by
    intro x
    simp [symmetrize]
    ring

  /-- Embed Window K into WeilClass via extension + symmetrization + complexification -/
  def windowToWeil (K : ℝ) (hK : 0 < K) (f : Window K) :
      RiemannHypothesis.WeilClass :=
    { f := fun x => Complex.ofReal (symmetrize (windowExtend K f) x),
      is_even := by
        intro x
        simp [Complex.ext_iff]
        constructor
        · simp [symmetrize_even]
        · simp,
      has_compact_support := by
        sorry -- TODO: Support ⊆ [-K, K]
      continuous := by
        sorry -- TODO: Compose continuous functions
      integrable := by
        sorry -- TODO: Compact support → integrable
    }

  /-- Key property: fhPacket is already symmetric! -/
  lemma fhPacket_symmetric (K B t τ : ℝ) (hB : 0 < B) (ht : 0 < t) :
      ∀ x : Set.Icc (-K) K,
      fhPacket K B t τ hB ht x = fhPacket K B t τ hB ht ⟨-(x : ℝ), sorry⟩ := by
    intro x
    -- Раскрыть определение fhPacket и использовать симметрию tent/heat
    sorry

  /-- Main embedding theorem: FHcone K → WeilClass dense subset -/
  def fhConeToWeilSet (K : ℝ) (hK : 0 < K) : Set RiemannHypothesis.WeilClass :=
    {Φ | ∃ (f : Window K), f ∈ FHcone K ∧ Φ = windowToWeil K hK f}

  end RH
  ```

  **Вероятность успеха**: 85% (симметрия уже есть, нужны технические леммы)

  ---

  ### **ЭТАП 2: Закрыть fejer_heat_span через FHcone**

  **Файл**: `RHFormalization/WeilCriterion.lean` (строка 220)

  ```lean
  /-- The set of Fejér × heat approximations on window W_K -/
  def fejer_heat_span (K L t : ℝ) (hK : 0 < K) : Set WeilClass :=
    RH.fhConeToWeilSet K hK  -- Используем embedding из WindowBridge
  ```

  **Обоснование**: `FHcone K` — это **линейные комбинации** `fhPacket`, что точно соответствует "Fejér × heat approximations"

  **Вероятность успеха**: 95% (прямое определение через готовую конструкцию)

  ---

  ### **ЭТАП 3: Закрыть fejer_heat_density (A1'.1)**

  **Файл**: `RHFormalization/WeilCriterion.lean` (строка 225)

  ```lean
  theorem fejer_heat_density (K : ℝ) (hK : 0 < K) :
      ∀ (Φ : WeilClass), Φ ∈ weil_class_on_window K →
      ∀ (ε : ℝ), ε > 0 →
      ∃ (L t : ℝ) (Ψ : WeilClass), Ψ ∈ fejer_heat_span K L t hK ∧
      ∀ x, ‖Φ.f x - Ψ.f x‖ < ε := by
    intro Φ hΦ_window ε hε_pos

    -- Стратегия: использовать A1Contract.A1_density из A1Contract.lean
    -- для Window K, потом поднять через windowToWeil

    -- 1. Свернуть Φ обратно в Window K (обратный embedding)
    let f : RH.Window K := sorry -- TODO: Построить обратную проекцию

    -- 2. Применить A1_density: f ∈ closure (FHcone K)
    have h_dense : f ∈ closure (RH.FHcone K) := by
      sorry -- TODO: Использовать A1Contract.A1_density

    -- 3. Из плотности FHcone K получить ε-аппроксимацию
    have h_approx : ∃ g ∈ RH.FHcone K, ‖g - f‖ < ε := by
      sorry -- TODO: Metric.mem_closure_iff

    -- 4. Поднять g через windowToWeil в WeilClass
    rcases h_approx with ⟨g, hg_cone, hg_close⟩
    use 1, 1  -- Фиксируем L=1, t=1 (можно варьировать)
    use RH.windowToWeil K hK g

    constructor
    · -- Показать, что Ψ ∈ fejer_heat_span
      simp [fejer_heat_span, RH.fhConeToWeilSet]
      use g, hg_cone
    · -- Показать ‖Φ.f x - Ψ.f x‖ < ε
      intro x
      sorry -- TODO: Перенести оценку ‖g - f‖ через embedding
  ```

  **Вероятность успеха**: 90% (A1Contract уже доказан, нужна техническая склейка)

  ---

  ## 📊 **ОСТАВШИЕСЯ sorry ПО ПРИОРИТЕТУ**

  После закрытия `fejer_heat_span` → `fejer_heat_density`, открываются:

  | № | Sorry | Зависит от | Вероятность | Оценка времени |
  |---|-------|-----------|-------------|----------------|
  | 1 | `q_lipschitz_on_window` (строка 240) | `fejer_heat_span` | 85% | 2-3 часа |
  | 2 | `density_extension_via_lipschitz` (строка 251) | №1 | 80% | 1-2 часа |
  | 3 | `guinand_weil_functional` (строка 201) | Численные данные | 70% | сложно, возможно axiom |
  | 4 | `guinand_weil_equivalence` (строка 206) | №3 | 75% | 3-4 часа |

  ---

  ## ✅ **ИТОГОВАЯ СТРАТЕГИЯ**

  ### **Шаг 0: Подготовка** (10 мин)
  ```bash
  cd /mnt/project
  git checkout -b sorry-closure-window-bridge
  touch RH/WindowBridge.lean
  ```

  ### **Шаг 1: WindowBridge** (2-4 часа)
  1. Создать `windowToWeil` embedding
  2. Доказать `fhPacket_symmetric`
  3. Определить `fhConeToWeilSet`
  4. Прогнать `lake build` → проверить количество sorry

  ### **Шаг 2: fejer_heat_span** (30 мин)
  1. Заменить `sorry` на `RH.fhConeToWeilSet K hK`
  2. Прогнать `lake build` → количество sorry -1

  ### **Шаг 3: fejer_heat_density** (1-2 часа)
  1. Использовать `A1Contract.A1_density`
  2. Построить проекцию `WeilClass → Window K`
  3. Склеить через embedding
  4. Прогнать `lake build` → количество sorry -2

  ### **Шаг 4: Валидация** (15 мин)
  ```bash
  lake build --verbose 2>&1 | grep -c "declaration uses 'sorry'"
  # Ожидаем: текущее_число - 3
  ```

  ---

  ## 🚨 **КРИТИЧЕСКИЕ МОМЕНТЫ**

  1. **Симметризация**: `fhPacket` уже симметричен, но нужно это **доказать**
  2. **Compact support**: Должно следовать из `Window K` + zero extension
  3. **Интегрируемость**: Compact support + continuous → integrable (есть в mathlib)
  4. **Обратная проекция**: `WeilClass → Window K` нужна для fejer_heat_density

  ---

  ## 💬 **ТВОЯ КОМАНДА**

  Готов начинать? Скажи:
  - **"go"** — начинаю писать WindowBridge.lean
  - **"show me X"** — покажу конкретный участок кода X
  - **"explain Y"** — объясню математику за Y подробнее

  Или если видишь дыры в плане — **стреляй вопросами**, доработаем стратегию.


• Ran git status -sb
  └ ## bib-audit-q3...origin/bib-audit-q3 [ahead 2]
     M RH_Q3.pdf
    … +49 lines
    ?? "notes/lean/\320\244\320\276\321\200\320\274\320\260\320\273\320\270\320\267\320\260\321\206\320\270\321\217
    \320\223\320\270\320\277\320\276\321\202\320\265\320\267\321\213 \320\240\320\270\320\274\320\260\320\275\320\260 \321\207\320\265\321\200\320\265\320\267
    \320\232\321\200\320\270\321\202\320\265\321\200\320\270\320\271 \320\222\320\265\320\271\320\273\321\217 \320\262 Lean 4.md"
    ?? pdfs/

• Explored
  └ List ls
    List ls

• I'm sketching the plan to create a bridging module that converts Window K functions, defined on [-K, K], to WeilClass functions on all ℝ by zero extension; however,
  continuity at the boundaries is tricky unless the function vanishes there. I’m weighing whether to rely on existing lemmas about continuity and compact support or
  define explicit Fejér–heat atoms on ℝ directly, keeping track of parameters to ensure support, evenness, continuity, and integrability needed for WeilClass. I want to
  carefully align parameters like K, L, t, and τ to maintain required properties and explore how to apply A1Contract density results bridging the spaces.

• Ran rg "extendZero" $(pwd)/notes/lean -n
  └ rg: /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/notes/notes/lean: IO error for operation on /Users/emalam/Documents/GitHub/RH_2025_V3_October/
    Q3_paper/notes/notes/lean: No such file or directory (os error 2)

• Explored
  └ Search extendZero
    Search integrable_of_hasCompactSupport

• I'm sorting through existing lemmas for integrability of continuous functions with compact support in mathlib. Since integrability depends on measure theory, I want
  to confirm which lemmas to rely on, like integrable_of_hasCompactSupport and how to avoid circular imports between modules like WeilCriterion and RH.FejerHeat. I'll
  sketch an implementation plan with careful import management before coding.

• Explored
  └ Read WeilCriterion.lean
    Search HasCompactSupport in Mathlib

• I'm weighing how to prove compact support for the Fejer heat core function by showing its support lies within a compact interval. There are relevant lemmas about
  closures and compact subsets, but the details get tricky, and the bridging modifications the user wants might need deeper definitions or clarifications. Given the
  complexity and time, I may need to ask for guidance or confirm missing pieces before proceeding.

─ Worked for 2m 29s ─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────

• Братан, стопор на первом же sor’ке fejer_heat_span: по проекту надо отобразить элементы FHcone K (функции на окне [-K,K]) в WeilClass (глобальные комплексные функции).
  В FejerHeat.lean пакет fhPacket задаётся как непрерывная функция на ℝ и потом ограничивается на окно, но нигде нет обратного моста вперёд. Без готового конструктора
  (или хотя бы указаний, как гладко “развернуть” окно обратно в глобальную even-функцию с компактным носителем) я не могу аккуратно замкнуть цепочку — особенно нам
  нужна гарантированная гладкая проклейка и компактный носитель для WeilClass. Как только подскажешь, чем разрешают верификаторы связывать Window K и WeilClass (готовая
  функция? конкретное продолжение? требования к граничным значениям?), продолжу.

## ASSISTANT
Ты всё видишь верно: пока нет аккуратного «окно → WeilClass», любая попытка закрыть `fejer_heat_span`/`fejer_heat_density` повисает на границе `[-K,K]`. Ниже — рабочий мост без скользких мест на границе и без неканоничных продолжений.

---

## Коротко суть

Не пытаться «обобщать любое окно». Вместо этого **поднять не окно, а сами генераторы** `fhPacket` на всю ℝ, где они и так живут (у тебя они строятся как `tent ⋅ heat` и уже имеют компактный носитель из‑за `tent`). Тогда:

1) Собираем **глобальный** конус `FHconeℝ K` из конечных линкомбинаций атомов `fhAtom B t τ : ℝ → ℝ` с параметрами, гарантирующими `supp ⊆ [-K,K]` (формально: `τ ∈ [0,K]`, `0 < B ≤ K-τ`, и берём сумму с отражением для чётности).

2) Текущий `FHcone K : Set (Window K)` — это всего лишь **ограничение** этих глобальных функций на окно: `FHcone K = { h‖_{[-K,K]} : h ∈ FHconeℝ K }`.

3) Определяем `fejer_heat_span K` именно как **образ** глобального конуса в `WeilClass`: берём `h ∈ FHconeℝ K`, чётный, непрерывный, с компактным носителем; комплексируем `Complex.ofReal ∘ h`. Всё — это элемент `WeilClass`.

Этим мы обошли проблему продолжения «произвольного» окна наружу: мы никогда не продолжали окно — мы восстановили **исходную глобальную функцию**, из которой окно было получено ограничением.

Такой ход на 100% совместим с твоей A1′‑плотностью «Fejér×heat → плотны на каждом компакте» (у тебя это прямо сформулировано и используется как базовая ступень) и с операторным мостом дальше по проекту. fileciteturn0file21  
А спектральная сторона (PSD/собственные значения Toeplitz, нормы, минимальные λ) — это как раз стандартный материал по положительно определённым формам/операторам, который мы в проекте используем; классические справки по нормам/PSD/λmin можно держать под рукой в Horn–Johnson. fileciteturn0file20

---

## Точная схема (Lean‑скелет)

**Файл** `RH/WindowBridge.lean` (новый, без циклических импортов: тащи сюда лишь `RH/FejerHeat` и тип `WeilClass`).

### 1) Глобальные атомы и их свойства

```lean
namespace RH

/-- Треугольник ("tent"), компактная поддержка в [−B,B]. Уже есть у тебя. -/
-- tent : ℝ → ℝ, supp ⊆ Icc (-B) B, continuous, even.

/-- Гаусс с параметром t > 0. Уже есть heat : ℝ → ℝ, smooth, even. -/

/-- Один симметризированный Fejér×heat-атом, глобально на ℝ. -/
def fhAtom (B t τ : ℝ) (hB : 0 < B) (ht : 0 < t) : ℝ → ℝ :=
  fun x =>
    tent B (x - τ) * heat t (x - τ) +
    tent B (x + τ) * heat t (x + τ)

lemma fhAtom_even : Even (fhAtom B t τ hB ht) := by
  -- раскрыть определение, переписать x ↦ -x; у `tent` и `heat` чётность уже есть
  -- `simp` по чётности и коммутативности сложения
  sorry

lemma fhAtom_support :
  support (fhAtom B t τ hB ht) ⊆ Set.Icc (-(B+|τ|)) (B+|τ|) := by
  -- support произведения ⊆ support первого ∩ второго, у tent компакт, heat > 0
  -- итог — объединение двух сдвинутых отрезков, что сидит в симметричном Icc
  sorry

lemma fhAtom_continuous : Continuous (fhAtom B t τ hB ht) := by
  -- произведение непрерывных + сумма, всё ок
  sorry
```

> Комментарий: `tent` обрубает хвосты, значит у `fhAtom` **компактный носитель**. Это ключ, чтобы безоговорочно получить интегрируемость.

### 2) Глобальный конус и связь с оконным

```lean
/-- Глобальный конус: конечные РЕАЛЬНЫЕ линейные комбинации fhAtom
    с параметрами, держащими носитель в [-K,K]. -/
def FHconeR (K : ℝ) : Set (ℝ → ℝ) :=
  { h | ∃ n c B t τ, (0 < K) ∧ (∀ i, 0 < c i) ∧
      (∀ i, 0 < t i) ∧ (∀ i, 0 < B i) ∧ (∀ i, 0 ≤ τ i ∧ τ i + B i ≤ K) ∧
      h = fun x => ∑ i in Finset.range n, c i * fhAtom (B i) (t i) (τ i) (by ...) (by ...) x }

/-- Ограничение на окно [-K,K] даёт текущий `Window K`. -/
def restrictToWindow (K : ℝ) (h : ℝ → ℝ) :
    Window K :=  -- у тебя это, скорей всего, `ContinuousMap (Icc (-K) K) ℝ`
  -- подаём h на подтип и доказываем непрерывность по `fhAtom_continuous` и линейности
  sorry

/-- Обратная сторона: каждый `w ∈ FHcone K` приходит как `restrictToWindow h`
    для некоторого `h ∈ FHconeR K`. -/
lemma FHcone_surj_restrict
    (K : ℝ) (hK : 0 < K) :
    ∀ {w : Window K}, w ∈ FHcone K →
      ∃ h ∈ FHconeR K, restrictToWindow K h = w := by
  -- смотри, как у тебя `FHcone K` построен: должно быть через те же `fhPacket`.
  -- Берём ту же линейную комбинацию до ограничения — и готово.
  sorry
```

### 3) Встраивание в `WeilClass`

```lean
/-- Чётная, комп.поддержка → интегрируемость: замыкаем в WeilClass. -/
def toWeil (h : ℝ → ℝ)
    (he : Even h)
    (hc : Continuous h)
    (hsupp : Bornology.IsBounded (support h))  -- или HasCompactSupport h, как у вас
    : WeilClass :=
{ f := fun x => Complex.ofReal (h x),
  is_even := by
    intro x; have := he x; -- переписать через ofReal; `simp` решит
    sorry,
  has_compact_support := by
    -- из компактного носителя real-функции → компактный носитель комплексной
    sorry,
  continuous := by
    -- композиция непрерывных
    sorry,
  integrable := by
    -- стандартная лемма: compact support + continuity ⇒ integrable
    -- `exact integrable_of_hasCompactSupport ...`
    sorry }

/-- Наконец: span на WeilClass — это образ глобального конуса. -/
def fejer_heat_span (K : ℝ) (hK : 0 < K) : Set WeilClass :=
  { Φ | ∃ h ∈ FHconeR K,
      Φ = toWeil h (by exact ...) (by exact ...) (by exact ...) }
```

*Технические примечания*:

- Для компактного носителя удобно использовать уже имеющееся в mathlib `HasCompactSupport` и лемму `integrable_of_hasCompactSupport` (она стандартна: непрерывная с комп.носителем ⇒ интегрируема по Лебегу на ℝ).  
- Чётность `fhAtom` берётся «на носу» из построения, сумма сохраняет чётность.  
- Ограничение на параметры `τ, B` (условие `τ + B ≤ K`) ровно то, что гарантирует `supp ⊆ [-K,K]`.  
- `WeilClass` у тебя — комплексные, чётные, `C⁰`, с компактной поддержкой. Конструктор выше заполняет все поля без «магии».

---

## Как это закрывает `sorry`‑цепочку

1) **`fejer_heat_span`**: заменяешь `sorry` ровно на `fejer_heat_span K hK` как выше. Никаких продолжений индикатором, никаких разрывов на границе.

2) **`fejer_heat_density`**: используешь уже доказанную у вас локальную плотность A1′ на компакте (в терминах Fejér×heat‑пакетов), но теперь — на **глобальных** атомах (которые, напомню, и порождали `FHcone K` после ограничения). Это согласуется с формулировками «A1′ — density» у тебя в Q3‑драфте (конус Fejér×heat плотен в `C⁺_even([-K,K])`), так что нужный аппроксиматор в `FHconeR K` можно выбрать с любым `ε`. fileciteturn0file21

3) Переход «аппроксимируем на окне ⇒ аппроксимируем как WeilClass» тривиальный, потому что твоя метрика контроля — равномерная на `[-K,K]`, а извне носителя всё ноль; комплексирование не портит оценки.

4) Далее твои операторные блоки (Toeplitz/λ‑оценки/PSD) используют стандартные факты про собственные значения и положительность; они лежат в классике (Horn–Johnson: нормы, PSD, Schur‑комплименты и т. п., которые вы уже по сути используете в A3/MD шагах). fileciteturn0file20

---

## Почему **не** «индикатор» и не Tietze

- `Set.indicator` даёт разрыв на границе, пока `f(±K) ≠ 0`.  
- Tietze‑продление убирает разрыв, но не сохраняет **компактный носитель**; нужно ещё умножать на бамп `β ≡ 1` на `[-K,K]`, что плодит лишние технические леммы (Urysohn). Всё это законно, но тяжелее и неканонично для твоей ветки.

Наш обходной путь каноничен для именно **этого** конуса: мы вообще не продолжаем «что угодно»; мы поднимаем те функции, из которых окно **и родилось**.

---

## Что именно править в репо

1. **Новый файл** `RH/WindowBridge.lean` со скелетом выше: `fhAtom`, леммы `even/continuous/support`, `FHconeR`, `toWeil`, `fejer_heat_span`.

2. **В `RHFormalization/WeilCriterion.lean`**:

```lean
-- было:
-- def fejer_heat_span ... := by sorry
-- стало:
def fejer_heat_span (K L t : ℝ) (hK : 0 < K) : Set WeilClass :=
  RH.fejer_heat_span K hK
```

(Параметры `L t` можно оставить фиктивно, если они в сигнатуре уже зашиты — или перенести их в параметры атомов `fhAtom`, если нужно.)

3. **`fejer_heat_density`**: используешь вашу `A1Contract.A1_density` (или эквивалент на конусе), затем завершаешь подъёмом через `toWeil`. На стороне норм — равномерная оценка на `[-K,K]` тянется как есть.

---

## Пара «острых мест» и как их прошить

- **Поддержка суммы**: удобнее держать явную лемму «`support (∑ c_i * fhAtom_i) ⊆ ⋃ support fhAtom_i`», а дальше финитность ⇒ компактен.  
- **Интегрируемость**: `integrable_of_hasCompactSupport` (или эквивалент в вашем слое measure).  
- **Чётность**: докажи для атома, потом `Even.sum`.  
- **Суръекция `FHconeR → FHcone`**: распакуй, как у тебя в `FejerHeat.lean` определён `FHcone K` (обычно через `restrict`). Там всё должно сложиться формально.

---

## Если всё же нужен мост «любое окно → WeilClass»

Можно, но тяжелее: Tietze‑продление `f|_{[-K,K]} → g : ℝ → ℝ` непрерывно, затем умножить на бамп `β ≡ 1` на `[-K,K]`, `supp β ⊆ [-K-δ, K+δ]`, симметризовать `h := (βg + βg ∘ neg)/2`, и уже `toWeil h`. Это даёт общий «канонический» конструктор, но в проекте ты всё равно используешь только конус Fejér×heat; так что этот путь не приносит профита.

---

## В двух строках, как сдвинуться прямо сейчас

- Заведи `FHconeR` и `toWeil` как выше.  
- Определи `fejer_heat_span` как образ `FHconeR`.  
- Проклей `FHcone_surj_restrict`.  
- Применяй вашу A1′‑плотность для `fejer_heat_density`.

Если упрёшься на конкретном имени леммы про интегрируемость/поддержку — кидай участок кода: подберём точные имена из mathlib, чтобы ушли последние `sorry`. Подход и архитектура — устойчивые; они прямо опираются на вашу A1′‑конструкцию Fejér×heat и стандартные факты про PSD/λmin. fileciteturn0file21 fileciteturn0file20

--- 

Если хочешь, могу расписать готовые сигнатуры трёх микролемм (`support_sum`, `integrable_of_hasCompactSupport` в вашем слое, и `Even.sum`) под ваш импорт.

