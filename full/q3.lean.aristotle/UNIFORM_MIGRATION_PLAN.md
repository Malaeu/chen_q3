# Plan: Migrate Q3 Lean to Uniform Approach

**Created:** 2026-01-12
**Updated:** 2026-01-13
**Author:** Claude Opus 4.5 (A3_bridge analysis)
**Status:** PARTIALLY COMPLETE

---

## Recent Progress (2026-01-13)

| Item | Status | Notes |
|------|--------|-------|
| Phase 1-5, 7 | ✅ DONE | c_star, uniform axioms added |
| off_diag_exp_sum_axiom | ✅ CLOSED | bridge_v3, signature fixed |
| Phase 6 | OPTIONAL | Downstream updates |

---

## Executive Summary

Paper was updated in December 2025 to use **UNIFORM** approach instead of K-dependent.
Lean code still uses old K-dependent structure. This plan migrates to uniform.

```
OLD (current Lean):              NEW (paper December 2025):
────────────────────             ──────────────────────────
c_arch(K) = inf[-K,K]            c_star = 11/10 (constant)
t_rkhs*(K)                       t_rkhs_unif
M_0(K)                           M_0_unif
K-dependent everywhere           K-independent
```

---

## Phase 1: Add Uniform Constants

### File: `Q3/Basic/Defs.lean` or `Q3/Axioms.lean`

```lean
/-! ## Uniform Archimedean Floor (December 2025 paper update) -/

/-- Uniform Archimedean floor: c* = 11/10
    This is the minimum of P_A(θ) over the entire torus T.
    Proven in A3_Floor_Main.lean -/
def c_star : ℝ := 11 / 10

/-- c* is positive (trivial) -/
lemma c_star_pos : c_star > 0 := by norm_num [c_star]

/-- Uniform M₀ for Szegő-Böttcher discretization -/
def M_0_unif : ℕ := sorry  -- From paper: ⌈C_SB * L_*/c_*⌉

/-- Uniform t_rkhs for RKHS contraction -/
def t_rkhs_unif : ℝ := sorry  -- From paper Corollary
```

---

## Phase 2: Update A3_bridge_axiom

### File: `Q3/Axioms.lean`

**OLD:**
```lean
axiom A3_bridge_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    RayleighQuotient(...) ≥ c_arch K / 4
```

**NEW:**
```lean
/-- Uniform A3 bridge (December 2025 paper update).
    No K-dependency, uses uniform floor c_star. -/
axiom A3_bridge_uniform :
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_star / 4

/-- Old K-dependent version (DEPRECATED, keep for backwards compatibility) -/
theorem A3_bridge_axiom_from_uniform (K : ℝ) (hK : K ≥ 1) :
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    RayleighQuotient(...) ≥ c_arch K / 4 := by
  -- c_star ≤ c_arch(K) for K ≥ some threshold
  -- So c_star/4 ≤ c_arch(K)/4
  obtain ⟨M₀, t, ht, h⟩ := A3_bridge_uniform
  use M₀, t, ht
  intro M hM v hv
  calc RayleighQuotient(...)
    ≥ c_star / 4 := h M hM v hv
    _ ≥ c_arch K / 4 := sorry -- need c_star ≤ c_arch(K)
```

---

## Phase 3: Update A3_bridge_data

### File: `Q3/Axioms.lean`

**OLD:**
```lean
def A3_bridge_data (K : ℝ) : Prop := ...
```

**NEW:**
```lean
/-- Uniform A3 bridge data (no K parameter) -/
def A3_bridge_data_uniform : Prop :=
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    RayleighQuotient (ToeplitzMatrix M a_star - PrimeMatrix t) v ≥ c_star / 4

/-- Old K-dependent (DEPRECATED) -/
def A3_bridge_data (K : ℝ) : Prop := A3_bridge_data_uniform
```

---

## Phase 4: Simplify Q_nonneg_on_atoms

### File: `Q3/Axioms.lean`

**OLD:**
```lean
axiom Q_nonneg_on_atoms_of_A3_RKHS_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  A3_bridge_data K → RKHS_contraction_data K →
  ∀ g ∈ AtomCone_K K, Q g ≥ 0
```

**NEW:**
```lean
/-- Uniform version: A3_bridge + RKHS_contraction ⟹ Q ≥ 0 on atoms -/
axiom Q_nonneg_on_atoms_uniform :
  A3_bridge_data_uniform → RKHS_contraction_data_uniform →
  ∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0
```

---

## Phase 5: Connect to A3_FLOOR

### File: `Q3/Proofs/A3_Bridge_Uniform.lean` (NEW)

```lean
import Q3.Axioms
import A3_Floor_Main  -- or wherever P_A_ge_c_star lives

/-- Main connection: A3_FLOOR provides the uniform floor.

    Proof structure:
    1. A3_FLOOR gives: min_{θ∈T} P_A(θ) ≥ c* = 11/10
    2. Szegő-Böttcher: λ_min(T_M[P_A]) ≥ min P_A - error(M)
    3. For M ≥ M_0_unif: error ≤ c*/2
    4. RKHS_contraction: ‖T_P‖ ≤ c*/4
    5. Combine: λ_min(T_M - T_P) ≥ c* - c*/2 - c*/4 = c*/4
-/
theorem A3_bridge_from_floor :
  A3_bridge_data_uniform := by
  -- Use P_A_ge_c_star from A3_FLOOR
  -- Use Szego_Rayleigh_lower_bound (Tier-1 axiom)
  -- Use RKHS_contraction_uniform
  sorry
```

---

## Phase 6: Update Downstream Files

### Files to update (13 files use c_arch):

| File | Change |
|------|--------|
| `Q3/Axioms.lean` | Add c_star, update axioms |
| `Q3/AxiomsTheorems.lean` | Use uniform versions |
| `Q3/AxiomClosure.lean` | Update closures |
| `Q3/AxiomClosureTheorems.lean` | Update closures |
| `Q3/MainTheorems.lean` | May need c_star |
| `Q3/A3_Bridge.lean` | Primary update |
| `Q3/Clean/AxiomsTier1.lean` | Add c_star to Tier-1 |
| `Q3/Proofs/A3_bridge.lean` | Update to uniform |
| `Q3/Proofs/A3_bridge_integrated.lean` | Update to uniform |
| `Q3/Proofs/Q_nonneg_bridge.lean` | Update dependency |
| `Q3/Proofs/Q_nonneg_on_atoms_integrated.lean` | Update dependency |
| `Q3/CheckAxioms.lean` | Update checks |
| `Q3/Archive/06_T5_aristotle.lean` | Low priority |

---

## Phase 7: Relationship c_star ↔ c_arch(K)

Need to prove (or add as lemma):

```lean
/-- c_star is a lower bound on c_arch(K) for K ≥ K_threshold.

    Since P_A is the periodization of a(ξ)·Φ_{B,t}(ξ), and
    c_arch(K) = inf_{|ξ|≤K} a_star(ξ),
    we have c_star = min_T P_A ≤ c_arch(K) when the support of Φ is in [-K,K].
-/
lemma c_star_le_c_arch (K : ℝ) (hK : K ≥ B_min) : c_star ≤ c_arch K := by
  sorry
```

---

## Execution Order

```
Step 1: Add c_star to Q3/Basic/Defs.lean
        ↓
Step 2: Add A3_bridge_uniform axiom (keep old for compatibility)
        ↓
Step 3: Add A3_bridge_data_uniform
        ↓
Step 4: Create A3_Bridge_Uniform.lean with bridge from A3_FLOOR
        ↓
Step 5: Update Q_nonneg_on_atoms
        ↓
Step 6: Update downstream files one by one
        ↓
Step 7: Deprecate old K-dependent versions
        ↓
Step 8: Run full build, fix any breaks
```

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| Breaking existing proofs | Keep old versions as deprecated |
| c_star ↔ c_arch mismatch | Prove relationship lemma first |
| Szegő domain issue | Use uniform floor on all T, not [-K,K] |
| A3_FLOOR integration | Already proven, just need import |

---

## Success Criteria

- [ ] c_star = 11/10 defined and used
- [ ] A3_bridge_uniform axiom added
- [ ] Old K-dependent versions deprecated
- [ ] A3_FLOOR connected to main chain
- [ ] Full build passes
- [ ] `#print axioms RH_proven` shows no c_arch dependency

---

**Next Action:** Start with Step 1 - add c_star to Defs.lean
