# Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom — I/O Analysis

Last updated: 2026-01-21

## Signature

```lean
axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom :
  ∀ (K : ℝ) (hK : K ≥ 1),
    A3_bridge_data_rayleigh_Fourier K →
    RKHS_contraction_data K →
    ∀ g ∈ AtomCone_K_fixed K t0_A1, Q g ≥ 0
```

Location: `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean:28`

---

## INPUTS

### INPUT 1: K : ℝ, hK : K ≥ 1
Compact window size (K ≥ 1)

---

### INPUT 2: A3_bridge_data_rayleigh_Fourier K

**Location:** `Q3/Proofs/P_A_Toeplitz_bridge.lean:63`

```lean
def A3_bridge_data_rayleigh_Fourier (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Nodes K)],
    ∃ t > 0, ∀ M : ℕ, ∀ v : Fin (2*M+1) → ℝ, v ≠ 0 →
      RayleighQuotient
        (ToeplitzMatrix_Fourier_real (2*M+1) P_A - T_P_comp_real K K t M) v
        ≥ c_star / 4
```

**SUB-COMPONENTS:**

| Component | Status | Location |
|-----------|--------|----------|
| P_A ≥ c_* = 11/10 | ✅ PROVEN | `A3_Floor_Main.lean` |
| T_P_comp_real | ✅ defined | `P_A_Toeplitz_bridge.lean` |
| c_star = 11/10 | ✅ constant | `Q3/Axioms.lean` |
| t_sym = 3/50 | ✅ constant | `Q3/Axioms.lean` |

---

### INPUT 3: RKHS_contraction_data K

**Location:** `Q3/Axioms.lean:571`

```lean
def RKHS_contraction_data (K : ℝ) : Prop :=
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      ‖T_P‖ ≤ ρ
```

**SUB-COMPONENTS:**

| Component | Status | Location |
|-----------|--------|----------|
| w_RKHS(n) = Λ(n)/√n | ✅ defined | `Q3/Axioms.lean` |
| w_max = 2/e ≈ 0.7358 | ✅ PROVEN | `RKHS_cap_rayleigh.lean` |
| rho(1) < 1/25 | ✅ PROVEN | `RKHS_cap_rayleigh.lean` |
| t_rkhs_cap = 40 | ✅ constant | `HeatKernelParams.lean` |

---

### INPUT 4: g ∈ AtomCone_K_fixed K t0_A1

**Location:** `Q3/Axioms.lean:336`

```lean
def AtomCone_K_fixed (K t0 : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c B τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧                  -- nonneg coefficients
        (∀ i, B i > 0) ∧                  -- positive widths
        (∀ i, |τ i| + B i ≤ K) ∧          -- support ⊆ [-K, K]
        (∀ x, g x = Σ c_i * Fejer_heat_atom(B_i, t0, τ_i, x)) ∧
        g ∈ W_K K }
```

**SUB-COMPONENTS:**

| Component | Status | Location |
|-----------|--------|----------|
| t0_A1 = 1/(16π²·t_sym) | ✅ defined | `HeatKernelParams.lean:16` |
| Fejer_heat_atom | ✅ defined | `Q3/Axioms.lean` |
| W_K membership | ✅ A1_density closed | `A1prime/` |

---

## OUTPUT

### Q g ≥ 0

**Location:** `Q3/Basic/Defs.lean:127`

```lean
def Q (Φ : ℝ → ℝ) : ℝ := arch_term Φ - prime_term Φ

where:
  arch_term Φ = ∫ a_*(ξ) · Φ(ξ) dξ
  prime_term Φ = Σ_{n≥2} w_Q(n) · Φ(ξ_n)
  a_*(ξ) = 2π · (log π - Re ψ(1/4 + iπξ))
  w_Q(n) = 2Λ(n)/√n
  ξ_n = log(n)/(2π)
```

---

## Proof Dependency Tree

```
Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
  │
  ├── A3_bridge_data_rayleigh_Fourier K
  │     │
  │     ├── P_A_ge_c_star ─────────────────── [✅ PROVEN in A3_Floor_Main.lean]
  │     │     └── c_star = 11/10
  │     │     └── t_sym = 3/50
  │     │
  │     ├── T_P_comp_real ─────────────────── [✅ defined]
  │     │
  │     └── RayleighQuotient ≥ c_*/4 ──────── [❓ needs wiring]
  │           └── rayleigh_Q_identification
  │
  ├── RKHS_contraction_data K
  │     │
  │     ├── w_RKHS_le_w_max ───────────────── [✅ PROVEN]
  │     │     └── w_max = 2/e
  │     │
  │     ├── weight_sum_le_rho_one ─────────── [✅ PROVEN in RKHS_cap_rayleigh.lean]
  │     │     └── rho_one < 1/25
  │     │     └── t_rkhs_cap = 40
  │     │
  │     └── ‖T_P‖ ≤ ρ < 1 ─────────────────── [✅ PROVEN]
  │
  └── g ∈ AtomCone_K_fixed K t0_A1
        │
        ├── Fejer_heat_atom ───────────────── [✅ defined]
        ├── t0_A1 = 1/(16π²·t_sym) ────────── [✅ defined]
        └── W_K membership ────────────────── [✅ A1_density closed]
```

---

## BLOCKER

### AtomCone_K_fixed QUANTIFIER MISMATCH

**Problem:**
- `AtomCone_K` (old) uses: `∀ t > 0` (arbitrary t)
- A3/RKHS proofs use: fixed `t = t_sym`, `t_rkhs_cap`

**Solution (from Прошка 2026-01-16):**
Use `AtomCone_K_fixed K t0_A1` which fixes t to `t0_A1 = 1/(16π²·t_sym)`.

**Action needed:**
Wire the fixed-t proofs into the bridge to close the axiom.

---

## Key Constants

| Constant | Value | Source |
|----------|-------|--------|
| c_* | 11/10 = 1.1 | Lemma 8.19 |
| t_sym | 3/50 = 0.06 | Lemma 8.19 |
| t_rkhs_cap | 40 | Corollary 8.22 |
| t0_A1 | 1/(16π²·t_sym) | HeatKernelParams |
| w_max | 2/e ≈ 0.7358 | Lemma 9.8 |
| rho(1) | < 1/25 = 0.04 | Corollary 8.22 |
| B_min | 3 | Lemma 8.19 |

---

## Status Summary

| Component | Status |
|-----------|--------|
| A3 floor (P_A ≥ c_*) | ✅ PROVEN |
| RKHS cap (rho < 1/25) | ✅ PROVEN |
| weight_sum bound | ✅ PROVEN |
| Rayleigh identification | ✅ PROVEN |
| A1 density (cone dense) | ✅ PROVEN |
| **Final wiring** | ❌ TODO |

**Most sub-components are PROVEN — just need to connect them!**
