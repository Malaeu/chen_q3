# Axiom Closure Analysis (2026-01-20)

## Current Status: 7 Axioms

```
Standard (3): propext, Classical.choice, Quot.sound
Level 1 (2):  Weil_criterion, Schur_test
Level 2 (2):  A1_density_WK_axiom, Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
```

## Recently Closed

| Axiom | Method | Date |
|-------|--------|------|
| `digamma_one_fourth_neg` | Aristotle (reflection/duplication formulas) | 2026-01-20 |
| `a_star_pos` | From `digamma_one_fourth_neg` | 2026-01-20 |
| `a_star_continuous` | Mathlib | 2026-01-19 |
| `a_star_bdd_on_compact` | Mathlib (extreme value theorem) | 2026-01-19 |
| `a_star_even` | Mathlib `Gamma_conj` | 2026-01-19 |

---

## Analysis: A1_density_WK_axiom

### Statement

```lean
axiom A1_density_WK_axiom : ∀ (K : ℝ) (hK : K > 0) (t0 : ℝ) (ht0 : t0 > 0),
  ∀ Φ ∈ W_K K, ∀ ε > 0,
    ∃ g ∈ AtomCone_K_fixed K t0,
      sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε
```

**Meaning:** Fejér×heat atoms are dense in W_K (sup-norm topology).

### Current Progress

| Component | Status | File |
|-----------|--------|------|
| HeatKernel_integral | ✅ PROVEN | `Q3/Proofs/A1_density_integrated.lean` |
| HeatKernel_nonneg | ✅ PROVEN | `Q3/Proofs/A1_density_integrated.lean` |
| FejerKernel_bounds | ✅ PROVEN | `Q3/Proofs/A1_density_integrated.lean` |
| FejerKernel_approx_one | ✅ PROVEN | `Q3/Proofs/A1_density_integrated.lean` |
| Convolution approximation | ⚠️ PARTIAL | `aristotle_output/A1_density_main_aristotle.lean` |
| **Triangle inequality step** | ❌ MISSING | Блокер! |

### What's Blocking

The **triangle inequality assembly** step:

```
|Φ(x) - g(x)| ≤ |Φ(x) - (Φ * ρ_t)(x)| + |(Φ * ρ_t)(x) - g(x)| < ε/2 + ε/2
```

Where:
1. First term: heat kernel convolution approximates Φ (uniform continuity)
2. Second term: hat interpolation approximates convolution (mesh refinement)

### Proof Strategy

1. **Step 1:** For Φ ∈ W_K and ε > 0, find t₀ such that `|(Φ * ρ_{t₀}) - Φ| < ε/3` on [-K,K]
   - Uses: uniform continuity of Φ on compact + Gaussian concentration

2. **Step 2:** Discretize `(Φ * ρ_{t₀})` via hat functions (Fejér kernels)
   - `h(x) = Σ_j Φ(τ_j) · Λ_δ(x - τ_j)` where mesh δ is small
   - Show: `|h - (Φ * ρ_{t₀})| < ε/3` (modulus of continuity)

3. **Step 3:** Verify h ∈ AtomCone_K_fixed with margin `|τ_j| + δ ≤ K`

4. **Step 4:** Triangle inequality: `|Φ - h| < 2ε/3 < ε`

### Difficulty: MEDIUM-HARD (3/5)

**Why:**
- Standard approximation theory (textbook material)
- All helpers already proven
- Single clear blocker (triangle inequality)
- Aristotle got close (convolution done)

**Estimated effort:** 2-3 days or 2-3 Aristotle requests

### Key Files

| File | Purpose |
|------|---------|
| `Q3/Axioms.lean:740-760` | Axiom statement |
| `Q3/Proofs/A1_density_integrated.lean` | Helper lemmas |
| `aristotle_output/A1_density_main_aristotle.lean` | Convolution progress |
| `aristotle_output/A1_density_FINAL_assembly_aristotle.lean` | Assembly attempt |

---

## Analysis: Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom

### Statement

```lean
axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom :
  ∀ (K : ℝ) (hK : K ≥ 1),
    A3_bridge_data_rayleigh_Fourier K →
    RKHS_contraction_data K →
    ∀ g ∈ AtomCone_K_fixed K t0_A1, Q g ≥ 0
```

**Meaning:** A3 (Toeplitz spectral gap) + RKHS (contraction) implies Q ≥ 0 on atoms.

### Current Progress

| Component | Status | File |
|-----------|--------|------|
| P_A_ge_c_star (A3 floor) | ✅ PROVEN | `Q3/Proofs/A3_Floor_Main.lean` |
| P_A_continuous | ✅ PROVEN | `Q3/Proofs/A3_Floor_Main.lean` |
| RKHS_contraction_data | ✅ PROVEN | `Q3/Proofs/Bridge.lean` |
| Rayleigh identification | ✅ PROVEN | `Q3/Proofs/Rayleigh_Q_identification.lean` |
| AtomCone_K_fixed | ✅ DEFINED | `Q3/Axioms.lean` |
| **Main integration** | ❌ BLOCKED | Type mismatch |

### What's Blocking

**Type/quantifier mismatch:**
- Aristotle's proof: arbitrary t, arbitrary finite sets
- Q3 needs: fixed t for A3, fixed t for RKHS, atoms with specific t parameter
- File `Q3/Proofs/Q_nonneg_bridge.lean` attempted integration but **doesn't compile**

### Proof Strategy

1. **Rayleigh Quotient Bound:**
   ```
   RQ(Toeplitz[P_A] - T_P_comp, v) ≥ c_star/4
   ```
   Where c_star = 11/10 from A3 floor.

2. **Rayleigh Identification:**
   ```
   RQ = Q(g) - (RKHS correction term)
   ```
   Already proven in `Rayleigh_Q_identification.lean`.

3. **RKHS Contraction:**
   ```
   ‖T_P‖ ≤ ρ < 1
   ```
   So RKHS term is bounded, hence Q ≥ 0.

4. **Integration:** Wire all three together with correct types.

### Difficulty: HARD (4/5)

**Why:**
- Multiple technical layers (spectral, Fourier, RKHS, Toeplitz)
- Type mismatch between components
- Different heat parameters in different parts
- 3-way integration challenge

**Estimated effort:** 4-6 days

### Key Files

| File | Purpose |
|------|---------|
| `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean` | Axiom statement |
| `Q3/Proofs/A3_Floor_Main.lean` | A3 floor theorem |
| `Q3/Proofs/Bridge.lean` | RKHS bridge |
| `Q3/Proofs/Rayleigh_Q_identification.lean` | Rayleigh = Q identity |
| `Q3/Proofs/Q_nonneg_bridge.lean` | Failed integration attempt |

---

## Comparison Summary

| Aspect | A1_density | Q_nonneg |
|--------|------------|----------|
| **Difficulty** | 3/5 (MEDIUM-HARD) | 4/5 (HARD) |
| **Helpers ready** | ✅ All | ✅ All |
| **Blocker** | Triangle inequality | Type mismatch + integration |
| **Math type** | Standard (approximation) | Complex (spectral + RKHS) |
| **Layers** | 1 (convolution) | 3 (A3 + RKHS + Rayleigh) |
| **Estimated time** | 2-3 days | 4-6 days |
| **Aristotle progress** | Good (convolution done) | Components done, wiring missing |

## Recommendation

**Start with A1_density_WK_axiom:**

1. Single clear blocker (triangle inequality)
2. Simpler mathematics (standard approximation theory)
3. Less integration work
4. Higher chance of quick win

**Next steps for A1:**
1. Ask Aristotle to prove triangle inequality assembly
2. Focus prompt on: uniform continuity + hat interpolation + margin condition
3. If Aristotle fails, manual proof using existing helpers

---

## Session Log

**2026-01-20:**
- Closed `digamma_one_fourth_neg` (8 → 7 axioms)
- Analyzed remaining axioms
- Recommendation: A1_density next
