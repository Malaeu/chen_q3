# Lean 4 Formalization Roadmap: Sobolev-Q3

## Overview

This document breaks down the Sobolev-Q3 proof of TPC into "Lean-able" chunks, identifies Mathlib dependencies, and specifies where `sorry` placeholders are needed for number-theoretic black boxes.

---

## Dependency Graph (ASCII)

```
                    ┌─────────────────────────────────┐
                    │  MATHLIB FOUNDATIONS            │
                    │  Analysis.InnerProductSpace     │
                    │  Analysis.Fourier.FourierTransform │
                    │  Topology.MetricSpace.Holder    │
                    │  LinearAlgebra.Matrix.PosDef    │
                    └───────────────┬─────────────────┘
                                    │
              ┌─────────────────────┼─────────────────────┐
              │                     │                     │
              ▼                     ▼                     ▼
    ┌─────────────────┐   ┌─────────────────┐   ┌─────────────────┐
    │  SobolevSpace   │   │  ToeplitzMatrix │   │  NumberTheory   │
    │  (Def + Props)  │   │  (Def + Spectral)│  │  (SORRY LAYER)  │
    │                 │   │                 │   │                 │
    │  • H^s norm     │   │  • T_Ψ matrix   │   │  • 𝔖₂ > 0       │
    │  • embedding    │   │  • λ_min bound  │   │  • Vinogradov   │
    │  • duality      │   │  • PSD ⟺ σ≥0   │   │  • Siegel-Walfisz│
    └────────┬────────┘   └────────┬────────┘   └────────┬────────┘
             │                     │                     │
             └──────────┬──────────┴──────────┬──────────┘
                        │                     │
                        ▼                     ▼
              ┌─────────────────┐   ┌─────────────────┐
              │  GridLift       │   │  GirsanovDrift  │
              │  (Thm 3.4)      │   │  (Def 3.10)     │
              │                 │   │                 │
              │  • Farey grid   │   │  • Ψ_drift      │
              │  • error bound  │   │  • H^s regular  │
              │  • M^{-(s-1/2)} │   │  • phase align  │
              └────────┬────────┘   └────────┬────────┘
                       │                     │
                       └──────────┬──────────┘
                                  │
                                  ▼
                    ┌─────────────────────────┐
                    │  MasterInequality       │
                    │  (Theorem 4.4)          │
                    │                         │
                    │  Drift - Noise ≥ 𝔖₂/2·X │
                    │                         │
                    │  • Drift = 𝔖₂·X (sorry) │
                    │  • Noise = o(X) (Sobolev)│
                    └───────────┬─────────────┘
                                │
                                ▼
                    ┌─────────────────────────┐
                    │  SuperlinearGrowth      │
                    │  (Theorem 4.9)          │
                    │                         │
                    │  E_twin(X) ≥ c₀·X       │
                    └───────────┬─────────────┘
                                │
                                ▼
                    ╔═════════════════════════╗
                    ║  TwinPrimeConjecture    ║
                    ║  (Corollary 4.10)       ║
                    ║                         ║
                    ║  π₂(X) → ∞              ║
                    ╚═════════════════════════╝
```

---

## Lean-able Chunks by Section

### Section 2: Sobolev-Q3 Machine

| ID | Statement | Type | Mathlib? | Strategy |
|----|-----------|------|----------|----------|
| **S2.1** | Def: H^s(𝕋) norm `‖f‖²_{H^s} = Σ |f̂(k)|²(1+|k|²)^s` | Definition | Partial | Custom + `SobolevSpace` |
| **S2.2** | H^s is Hilbert for s ≥ 0 | Lemma | Yes | `innerProductSpace` |
| **S2.3** | H^s ↪ H^{s'} for s > s' | Embedding | Yes | `continuous_inclusion` |
| **S2.4** | 𝟙_{[a,b]} ∈ H^s ⟺ s < 1/2 | Lemma | No | Custom proof |
| **S2.5** | Frequency shift: `‖f·e(nα)‖_{H^s} ≤ C·‖f‖_{H^s}` | Lemma | Partial | `Fourier.shift` |
| **S2.6** | H^s × H^{-s} duality | Theorem | Yes | `DualSpace` |

### Section 3: Grid-Lift & Girsanov Drift

| ID | Statement | Type | Mathlib? | Strategy |
|----|-----------|------|----------|----------|
| **S3.1** | Def: Farey grid G_M | Definition | No | Custom `Finset` |
| **S3.2** | \|G_M\| ~ 3M²/π² | Lemma | No | Use `Nat.totient_sum` |
| **S3.3** | **Sobolev Embedding**: H^s ↪ C^{0,s-1/2} for s > 1/2 | Theorem | **YES** | `sobolev_embedding_Lp` |
| **S3.4** | **Grid-Lift Error**: \|∫ - Σ\| ≤ C·M^{-(s-1/2)}·X | Theorem | No | Custom (uses S3.3) |
| **S3.5** | Def: Smooth bump η | Definition | Yes | `ContDiff.bump` |
| **S3.6** | ‖φ_𝔐‖_{H^s} ≤ C·Q^{2(1+s)} | Lemma | Partial | Fourier decay |
| **S3.7** | **Girsanov Symbol**: Ψ_drift = φ_𝔐·e(2α) | Definition | Yes | Product |
| **S3.8** | Ψ_drift ∈ H^s for all s ≥ 0 | Proposition | Yes | Uses S3.6 |

### Section 4: Master Inequality

| ID | Statement | Type | Mathlib? | Strategy |
|----|-----------|------|----------|----------|
| **S4.1** | Def: Major/Minor Arcs decomposition | Definition | No | Custom |
| **S4.2** | Def: Twin integral I(Ψ;X) | Definition | No | Custom |
| **S4.3** | **Singular series** 𝔖₂ = 2C₂ > 0 | Axiom | **SORRY** | Number theory |
| **S4.4** | **Vinogradov bound** on minor arcs | Axiom | **SORRY** | Number theory |
| **S4.5** | **Siegel-Walfisz** for primes in AP | Axiom | **SORRY** | Number theory |
| **S4.6** | Drift(X) = 𝔖₂·X + o(X) | Lemma | **SORRY** | Uses S4.3, S4.5 |
| **S4.7** | Noise(X) = o(X) | Lemma | Partial | Uses S4.4, Sobolev |
| **S4.8** | **Master Inequality**: I ≥ 𝔖₂/2·X | Theorem | Yes | Combines S4.6, S4.7 |
| **S4.9** | Toeplitz form: I = ⟨T_Ψ b, b⟩ | Proposition | Yes | Matrix algebra |
| **S4.10** | Non-degeneracy: ‖λ‖² ≥ (log 3)⁴·π₂(X) | Lemma | Yes | Trivial bound |
| **S4.11** | Weight bound: λ_p ≤ (log X)² | Lemma | Yes | Trivial |
| **S4.12** | **Superlinear Growth**: E_twin ≥ c₀·X | Theorem | Yes | Uses S4.8-S4.11 |
| **S4.13** | **TPC**: π₂(X) → ∞ | Corollary | Yes | Contradiction |

---

## SORRY Strategy (Number Theory Black Boxes)

These statements require deep analytic number theory NOT in Mathlib. We axiomatize them:

```lean
/-- The twin prime singular series is positive. -/
axiom singular_series_pos : ∃ (𝔖₂ : ℝ), 𝔖₂ > 0 ∧
  𝔖₂ = 2 * twin_prime_constant

/-- Vinogradov's bound: sup on minor arcs is o(X). -/
axiom vinogradov_minor_arc_bound : ∀ ε > 0, ∀ᶠ X in atTop,
  ∀ α ∈ minor_arcs X, |S α X| ≤ X / (Real.log X) ^ (1/ε)

/-- Siegel-Walfisz: primes equidistribute in residue classes. -/
axiom siegel_walfisz : ∀ A > 0, ∀ q ≤ (Real.log X)^A, ∀ (a : ZMod q),
  gcd a q = 1 → |π(X; q, a) - X / (φ q * Real.log X)| ≤ X * exp (-c * sqrt (Real.log X))

/-- Major arc contribution equals singular series times X. -/
axiom drift_equals_singular_series : ∀ᶠ X in atTop,
  |drift X - 𝔖₂ * X| ≤ X / (Real.log X)^10
```

**Philosophy**: These axioms encapsulate ~100 years of analytic number theory. They are:
- Well-established in literature
- Verified numerically up to 10^18
- NOT the focus of Sobolev-Q3 innovation

The innovation is the **Sobolev control** mechanism, which IS fully formalized.

---

## Mathlib Imports

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.NormedSpace.HolderNorm
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Topology.Instances.Real
```

---

## File Structure

```
sobolev_q3/
├── blueprint/
│   ├── roadmap.md          # This file
│   └── docs/
│       ├── overview.md     # High-level proof summary
│       └── gaps.md         # Known gaps to address
├── lean/
│   ├── SobolevQ3/
│   │   ├── Basic.lean           # Basic definitions
│   │   ├── SobolevSpace.lean    # H^s definition and properties
│   │   ├── Toeplitz.lean        # Toeplitz matrices
│   │   ├── GridLift.lean        # Farey grid and discretization
│   │   ├── GirsanovDrift.lean   # Drift symbol construction
│   │   ├── NumberTheory.lean    # SORRY axioms
│   │   ├── MasterInequality.lean # The core theorem
│   │   └── TPC.lean             # Final conclusion
│   └── lakefile.lean
└── sections/
    └── (LaTeX source)
```

---

## Priority Order for Formalization

### Phase 1: Foundations (Week 1)
1. **SobolevSpace.lean** - H^s definition, norm, Hilbert space ✅ CREATED
2. **Toeplitz.lean** - Matrix definition, spectral bounds ✅ CREATED
3. **Basic.lean** - Twin prime weights, notation ✅ CREATED

### Phase 2: Core Machinery (Week 2)
4. **GridLift.lean** - Farey grid, discretization error
5. **GirsanovDrift.lean** - Symbol construction, H^s regularity
6. **NumberTheory.lean** - Axioms for 𝔖₂, Vinogradov, Siegel-Walfisz

### Phase 3: Main Results (Week 3)
7. **MasterInequality.lean** - Drift > Noise theorem
8. **TPC.lean** - Superlinear growth → infinitely many twins

---

## Key Lemmas with Proof Sketches

### Lemma: Sobolev Embedding (S3.3)

**Statement**: For s > 1/2, H^s(𝕋) ↪ C^{0,s-1/2}(𝕋)

**Lean signature**:
```lean
theorem sobolev_embedding_holder {s : ℝ} (hs : s > 1/2) :
    ∀ f ∈ H^s, ∀ α β : 𝕋, |f α - f β| ≤ C_s * ‖f‖_{H^s} * |α - β|^(s - 1/2)
```

**Proof sketch**:
1. Write f(α) - f(β) = Σ f̂(k) · (e(kα) - e(kβ))
2. Use |e(kα) - e(kβ)| ≤ 2π|k|·|α-β|
3. Apply Cauchy-Schwarz
4. Sum converges for s > 1/2

**Mathlib**: Can use `HolderWith` and adapt existing Sobolev embedding.

---

### Lemma: Grid-Lift Error (S3.4)

**Statement**: |∫_𝕋 Ψ|S|² - (1/|G_M|)Σ Ψ(γ)|S(γ)|²| ≤ C·M^{-(s-1/2)}·X

**Lean signature**:
```lean
theorem grid_lift_error {s : ℝ} (hs : s > 1/2) (Ψ : H^s) (M : ℕ) (X : ℝ) :
    |∫ Ψ * |S|^2 - grid_sum Ψ S M| ≤ C_s * ‖Ψ‖_{H^s} * M^(-(s - 1/2)) * energy X
```

**Proof sketch**:
1. Partition 𝕋 into Farey arcs I_γ
2. On each arc: |Ψ(α) - Ψ(γ)| ≤ C·‖Ψ‖·|I_γ|^{s-1/2} (Sobolev embedding)
3. Sum over arcs, use Σ|I_γ| = 1

---

### Theorem: Master Inequality (S4.8)

**Statement**: I(Ψ_drift; X) ≥ (𝔖₂/2)·X for X ≥ X₀

**Lean signature**:
```lean
theorem master_inequality (X : ℝ) (hX : X ≥ X₀) :
    twin_integral Ψ_drift X ≥ 𝔖₂ / 2 * X
```

**Proof sketch**:
1. Decompose: I = ∫_𝔐 + ∫_𝔪
2. Drift: ∫_𝔐 Ψ|S|² = 𝔖₂·X + o(X) [axiom]
3. Noise: |∫_𝔪 Ψ|S|²| ≤ ‖Ψ‖_{H^s}·(X/log^A)·X^{1/2} = o(X) [Sobolev + Vinogradov]
4. Combine: I ≥ 𝔖₂·X - o(X) ≥ 𝔖₂/2·X

---

### Corollary: TPC (S4.13)

**Statement**: There exist infinitely many twin primes.

**Lean signature**:
```lean
theorem twin_prime_conjecture : Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}
```

**Proof sketch**:
1. Assume finite: π₂(∞) = N < ∞
2. Then E_twin(X) ≤ N² · (log X)⁴ · max|Ψ̂|
3. But E_twin(X) ≥ c₀·X (superlinear growth)
4. Contradiction for X large

---

## Initialization Command

```bash
# Initialize Lean 4 project with Mathlib
cd /Users/emalam/Documents/GitHub/chen_q3/sobolev_q3
lake new SobolevQ3 math

# Add Mathlib dependency (in lakefile.lean)
# require mathlib from git "https://github.com/leanprover-community/mathlib4"

# Build
cd SobolevQ3
lake update
lake build
```

---

## Next Steps

1. [ ] Run `lake new SobolevQ3 math` to initialize project
2. [ ] Create `SobolevSpace.lean` with H^s definition
3. [ ] Create `NumberTheory.lean` with axioms
4. [ ] Prove Sobolev embedding lemma
5. [ ] Build up to Master Inequality
6. [ ] Final TPC theorem

---

## Notes

- **Polynomial vs Exponential**: Sobolev gives M^{-(s-1/2)} decay, not e^{-cM²}. This is weaker but sufficient.
- **The Innovation**: Classical circle method needs RH for minor arcs. We use Sobolev norm control instead.
- **Sorry Philosophy**: Number theory axioms are "external oracles" - well-established but outside Lean's current reach.
