# A Spectral Criterion for Twin Primes via Cone–Kernel Separation

## 📚 Overview

This project contains a formal verification effort for the paper
"A Spectral Reformulation of the Twin Prime Conjecture".

**Main Result:** TPC ⟺ R(Φ_X) → ∞ (Spectral Equivalence)

We use **Aristotle** (by Harmonic AI) to generate machine-verified Lean4 proofs
of the key lemmas and theorems.

---

## 📁 Project Structure

```
spectral_twin_primes/
├── README.md                  # This file
├── docs/
│   ├── ARISTOTLE_GUIDE.md     # How to use Aristotle (reverse engineered)
│   └── DECOMPOSITION_PLAN.md  # Paper decomposition into lemmas
├── tex/                       # LaTeX source files (paper)
├── src/                       # Python utilities
│   └── check_aristotle.py     # Check project status
└── lean_aristotle/
    ├── input/                 # Lemmas for Aristotle (Markdown/LaTeX)
    │   ├── 01_cone_kernel_separation.md      ✅
    │   ├── 02_cone_positivity_B1.md          📝
    │   └── 03_universal_scaling.md           📝
    └── output/                # Lean4 proofs from Aristotle
        └── 01_cone_kernel_separation_aristotle.md  ✅
```

---

## 🎯 Verification Status

| # | Lemma/Theorem | Status | Aristotle Time |
|---|---------------|--------|----------------|
| 1 | Cone-Kernel Separation | ✅ VERIFIED | 20 min |
| 2 | Cone Positivity (B₁-strong) | 📝 Ready | - |
| 3 | Universal Energy Scaling | 📝 Ready | - |
| 4 | Finite Stabilization (SC2) | 🔜 TODO | - |
| 5 | Spectral Equivalence | 🔜 TODO | - |

---

## 🚀 Quick Start

### 1. Setup Environment
```bash
# Install Aristotle
uv pip install aristotlelib

# Set API key
export ARISTOTLE_API_KEY="your_key_here"
```

### 2. Run Verification
```bash
# Verify a lemma
cd spectral_twin_primes
aristotle prove-from-file --informal --no-validate-lean-project \
    lean_aristotle/input/02_cone_positivity_B1.md
```

### 3. Check Status
```bash
# List all projects
python src/check_aristotle.py

# Check specific project
python src/check_aristotle.py PROJECT_ID
```

---

## 📖 The Mathematics

### Core Chain
```
Cone-Kernel Separation (pure linear algebra)
    ↓
Cone Positivity: inf_C R(λ) > 0
    ↓
Universal Scaling: Sum(Q) ~ N² × span²
    ↓
Spectral Equivalence: TPC ⟺ R → ∞
```

### Key Definitions
- **ξ_p = log(p)/(2π)** — spectral coordinate
- **K_{pq}** — Gaussian kernel (strictly positive)
- **A_{pq} = (ξ_q - ξ_p) · K_{pq}** — commutator matrix
- **Q = AᵀA** — commutator energy matrix
- **R(λ) = λᵀQλ / λᵀGλ** — Rayleigh quotient
- **C = {λ ≥ 0, λ ≠ 0}** — positive cone

---

## 🔬 Aristotle Details

See `docs/ARISTOTLE_GUIDE.md` for full documentation.

**Key features:**
- IMO Gold Medal level intelligence
- English/LaTeX → Lean4 conversion
- 83% success rate on informal proofs
- Parallel execution supported

---

## 📊 First Verified Proof

**Cone-Kernel Separation** (verified December 2025):

```lean
theorem cone_kernel_separation {N : ℕ} (hN : 1 < N)
  (ξ : Fin N → ℝ) (K : Matrix (Fin N) (Fin N) ℝ)
  (hξ : StrictMono ξ)
  (hK_symm : K.IsSymm)
  (hK_pos : ∀ p q, p ≠ q → 0 < K p q) :
  ∀ v, PositiveCone v → Matrix.mulVec (A_mat ξ K) v ≠ 0
```

Full proof: `lean_aristotle/output/01_cone_kernel_separation_aristotle.md`

---

## 🤝 Credits

- Paper: Ылша (Emalam)
- Verification: Aristotle (Harmonic AI)
- Coordination: Claude (Anthropic)

---

*December 2025*
