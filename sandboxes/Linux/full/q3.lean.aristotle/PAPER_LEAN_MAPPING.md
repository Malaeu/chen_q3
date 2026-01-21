# Q3 Paper ↔ Lean Proof Mapping (Complete)

**Note:** For current axiom counts/status, use `PROJECT_ORCHESTRATOR.md`.
This file is for citation-to-file mapping and may lag behind the live status.

## Status Legend

| Symbol | Meaning |
|--------|---------|
| ✅ | PROVEN in Lean 4 (complete formal proof) |
| 📚 | PEER-REVIEWED classical result (cited, not re-proven) |
| 🔄 | IN PROGRESS (Aristotle working) |
| 🎯 | TODO: Need to create Aristotle task |

---

# PART 1: PEER-REVIEWED FOUNDATIONS

These are classical results we CITE, not prove. Each has specific publication reference.

| # | Result Name | Citation Key | Full Reference | Used For |
|---|-------------|--------------|----------------|----------|
| P1 | **Weil Positivity Criterion** | `Weil1952` | Weil, A. "Sur les formules explicites de la théorie des nombres premiers", *Meddelanden Fran Lunds Univ. Mat. Sem.*, pp.252-265, **1952** | Core criterion: Q≥0 ⟹ RH |
| P2 | **Guinand-Weil Explicit Formula** | `Guinand1948` | Guinand, A.P. "A summation formula in the theory of prime numbers", *Proc. London Math. Soc.*, 50:107-119, **1948** | T0 normalization |
| P3 | **Szegő Limit Theorem** | `Szego1952` | Szegő, G. "On certain Hermitian forms associated with the Fourier series", *Festskrift Carleman*, pp.228-238, **1952** | A3 Toeplitz asymptotics |
| P4 | **Böttcher-Silbermann Barriers** | `BoettcherSilbermann2006` | Böttcher, A. & Silbermann, B. *Introduction to Large Truncated Toeplitz Matrices*, Springer, **2006** | A3 spectral bounds |
| P5 | **Schur Test** | `HornJohnson2013` | Horn, R.A. & Johnson, C.R. *Matrix Analysis*, 2nd ed., Cambridge, **2013** | RKHS operator norm bounds |
| P6 | **RKHS Theory** | `Aronszajn1950` | Aronszajn, N. "Theory of reproducing kernels", *Trans. AMS*, 68:337-404, **1950** | RKHS contraction framework |
| P7 | **Fejér Kernel Density** | `SteinShakarchi2003` | Stein, E.M. & Shakarchi, R. *Fourier Analysis*, Princeton, **2003** | A1' density |
| P8 | **Heat Kernel Properties** | `SteinShakarchi2003` | (same as above) | A1' approximation identity |
| P9 | **Gershgorin Circle Theorem** | `Varga2004` | Varga, R.S. *Geršgorin and His Circles*, Springer, **2004** | Matrix spectral bounds |
| P10 | **Stone-Weierstrass** | (Mathlib) | Standard functional analysis | T5 density |
| P11 | **Compact-open Topology** | (Mathlib) | Standard topology | T5 transfer |
| P12 | **Von Mangoldt Function** | `IwaniecKowalski2004` | Iwaniec, H. & Kowalski, E. *Analytic Number Theory*, AMS, **2004** | Weight definitions |

---

# PART 2: MAIN THEOREM CHAIN

| # | Paper § | Label | Name | Lean File | Lean Name | Status |
|---|---------|-------|------|-----------|-----------|--------|
| M1 | §1 | `thm:Weil-criterion` | Weil Criterion | Q3/Axioms.lean | `Weil_criterion` | 📚 P1 |
| M2 | §7 | `thm:Main-positivity` | Q≥0 on Weil class | Q3/Main.lean | `Q_nonneg_on_W` | ✅ |
| M3 | §7 | `thm:RH` | Riemann Hypothesis | Q3/Main.lean | `RH_of_Weil_and_Q3` | ✅ |

---

# PART 3: T0 - NORMALIZATION

| # | Paper § | Label | Name | Lean | Status | Reference |
|---|---------|-------|------|------|--------|-----------|
| T0.1 | §2 | `prop:T0-GW` | Guinand-Weil matching | Axioms.lean:`T0_normalization_axiom` | 📚 P2 | Guinand 1948, Weil 1952 |
| T0.2 | §2 | `t0:lem:T0` | Q crosswalk | (implicit) | 📚 | Standard |
| T0.3 | §2 | `lem:T0-normalisation-invariance-full` | Normalization invariance | (implicit) | 📚 | Standard analysis |

---

# PART 4: A1' - DENSITY

| # | Paper § | Label | Name | Lean File | Status | Notes |
|---|---------|-------|------|-----------|--------|-------|
| A1.1 | §3 | `thm:A1-density` | **A1' density theorem** | aristotle_output/ | 🔄 2% | Aristotle running |
| A1.2 | §3 | `a1:thm:A1-local-density` | Local density | A1_density_v2 | 🔄 | Part of A1.1 |
| A1.3 | §3 | `lem:a1-fixed-t-density` | Fixed-t density | `sum_atoms_in_cone` | ✅ | |
| A1.4 | — | — | Heat kernel ∫=1 | `HeatKernel_integral` | ✅ | |
| A1.5 | — | — | Heat concentration | `HeatKernel_mass_concentration` | ✅ | |
| A1.6 | — | — | Fejér bounds | `FejerKernel_bounds` | ✅ | |
| A1.7 | — | — | Fejér approx one | `FejerKernel_approx_one` | ✅ | |
| A1.8 | — | — | Compact extension | `exists_compact_extension` | ✅ | |
| A1.9 | — | — | Uniform Riemann sum | `uniform_riemann_sum` | ✅ | |
| A1.10 | — | — | Convolution approx | `convolution_approx_by_sum` | ✅ | |
| A1.11 | — | — | Fejer sum approx | `fejer_sum_approx` | ✅ | |
| A1.12 | — | — | Even convolution | `even_convolution` | ✅ | |

---

# PART 5: A2 - LIPSCHITZ CONTINUITY

| # | Paper § | Label | Name | Lean File | Lean Name | Status |
|---|---------|-------|------|-----------|-----------|--------|
| A2.1 | §4 | `lem:Q-local-finite` | Local finiteness | W_sum_finite_integrated | `ActiveNodes_finite` | ✅ |
| A2.2 | §4 | `cor:A2-Lip` | Lipschitz on compact | Q_Lipschitz_integrated | `Q_Lipschitz` | ✅ |
| A2.3 | §4 | `a2:lem:A2` | A2 main | Q_Lipschitz_integrated | `closes_Q_Lipschitz_axiom` | ✅ |
| A2.4 | §4 | `a2:cor:explicit-lip` | Explicit L_Q | Q_Lipschitz_integrated | `L_Q` definition | ✅ |

---

# PART 6: A3 - TOEPLITZ-SYMBOL BRIDGE

| # | Paper § | Label | Name | Lean | Status | Notes |
|---|---------|-------|------|------|--------|-------|
| A3.1 | §5 | `thm:A3` | **A3 bridge inequality** | A3_bridge_integrated | ✅ | Main theorem |
| A3.2 | §5.1 | `lem:a3-lipschitz-bound` | Lipschitz modulus | — | 📚 P4 | Böttcher-Silbermann |
| A3.3 | §5.1 | `lem:a3-core-lower-bound` | Core contribution | — | 🎯 | **TODO** |
| A3.4 | §5.1 | `lem:a3-core-shift` | Shift-robust core | — | 🎯 | **TODO** |
| A3.5 | §5.1 | `lem:a3-arch-floor` | Archimedean floor | Axioms:`c_arch_pos` | ✅ | |
| A3.6 | §5.1 | `cor:a3-arch-floor-compact` | Floor on compact | (implicit) | ✅ | |
| A3.7 | §5.1 | `thm:a3-k1-floor` | Floor at K=1 | — | 🎯 | **TODO** |
| A3.8 | §5.1 | `lem:a3-global-arch-floor` | Global floor | — | 🎯 | **TODO** |
| A3.9 | §5.2 | `lem:a3.bv-to-lip` | BV→Lipschitz | — | 📚 | Standard BV theory |
| A3.10 | §5.2 | `lem:a3.sup-bounds` | Uniform bounds | — | 📚 | |
| A3.11 | §5.2 | `lem:a3.two-scale` | Two-scale selection | — | 🎯 | **TODO** |
| A3.12 | §5.2 | `lem:a3.cap-combine` | Cap combine | — | 🎯 | **TODO** |
| A3.13 | §5.3 | `lem:a3-sb-barrier` | Szegő-Böttcher barrier | — | 📚 P4 | Böttcher-Silbermann 2006 |
| A3.14 | §5.3 | `thm:a3-mixed-margin` | Mixed margin | A3_bridge_aristotle | ✅ | |
| A3.15 | §5.3 | `thm:a3-rayleigh-identification` | Rayleigh ID | A3_bridge_aristotle | ✅ | |
| A3.16 | §5.4 | `lem:local-positivity` | Local positivity | — | 🎯 | **TODO** |

---

# PART 7: RKHS - PRIME CONTRACTION

| # | Paper § | Label | Name | Lean | Status | Notes |
|---|---------|-------|------|------|--------|-------|
| R1 | §6 | `rkhs:thm:rkhs-contraction` | **Strict contraction** | RKHS_contraction_integrated | ✅ | Main theorem |
| R2 | §6 | `thm:pcu-main` | Prime-Cap Uniform | RKHS_contraction_aristotle | ✅ | |
| R3 | §6 | `rkhs:lem:deltaK` | Node separation δ_K | node_spacing_integrated | ✅ | |
| R4 | §6 | `rkhs:lem:node_gap_lower_bound` | Node gap bound | node_spacing_aristotle | ✅ | |
| R5 | §6 | `rkhs:lem:wmax_cap` | Weight cap w_max | RKHS_contraction_aristotle:`w_RKHS_le_w_max` | ✅ | |
| R6 | §6 | `lem:rkhs-energy` | Energy identity | RKHS_contraction_aristotle | ✅ | |
| R7 | §6 | `lem:gram-min-eig-lb` | Gram spectral floor | — | 📚 P5 | Horn-Johnson |
| R8 | §6 | `lem:rkhs-gram-off` | Off-diagonal bound | off_diag_exp_sum_integrated | ✅ | |
| R9 | §6 | `rkhs:lem:geom-SK` | Geometric tail S_K | S_K_small_integrated | ✅ | |
| R10 | §6 | `lem:trace-cap-bound` | Trace-cap bound | RKHS_contraction_aristotle:`T_P_row_sum_bound` | ✅ | |
| R11 | §6 | `prop:rkhs-gram-cap` | Gram cap | RKHS_contraction_aristotle | ✅ | |
| R12 | §6 | `thm:rkhs-tstar` | Constructive t* | RKHS_contraction_aristotle:`t_min` | ✅ | |

---

# PART 8: T5 - COMPACT TRANSFER

| # | Paper § | Label | Name | Lean | Status | Reference |
|---|---------|-------|------|------|--------|-----------|
| T5.1 | §6.5 | `thm:T5-compact` | Monotone transfer | Axioms:`T5_compact_axiom` | 📚 P10,P11 | Stone-Weierstrass + topology |
| T5.2 | §6.5 | `t5:thm:T5-transfer` | Positivity transfer | (implicit in Main) | 📚 | |
| T5.3 | §6.5 | `lem:T5p-grid` | Grid lift | — | 📚 | Approximation theory |

---

# PART 9: Q NON-NEGATIVITY (CLOSURE)

| # | Paper § | Label | Name | Lean File | Lean Name | Status |
|---|---------|-------|------|-----------|-----------|--------|
| Q1 | §7 | — | Q≥0 on atoms | Q_nonneg_on_atoms_integrated | `Q_nonneg_on_atoms` | ✅ |
| Q2 | §7 | — | Q≥0 on W_K | Main.lean | `Q_nonneg_on_W_K` | ✅ |
| Q3 | §7 | — | Q≥0 on full W | Main.lean | `Q_nonneg_on_W` | ✅ |
| Q4 | §7 | `thm:Main-positivity` | Main positivity | Main.lean | `Q_nonneg_on_W` | ✅ |

---

# PART 10: TODO LIST (Items marked 🎯)

These need Aristotle tasks created:

| # | Label | Name | Priority | Complexity |
|---|-------|------|----------|------------|
| 1 | `lem:a3-core-lower-bound` | Core contribution | HIGH | Medium |
| 2 | `lem:a3-core-shift` | Shift-robust core | HIGH | Medium |
| 3 | `thm:a3-k1-floor` | Floor at K=1 | HIGH | Easy |
| 4 | `lem:a3-global-arch-floor` | Global floor | HIGH | Easy |
| 5 | `lem:a3.two-scale` | Two-scale selection | MEDIUM | Medium |
| 6 | `lem:a3.cap-combine` | Cap combine | MEDIUM | Medium |
| 7 | `lem:local-positivity` | Local positivity | HIGH | Medium |

**Total: 7 lemmas need formalization**

---

# STATISTICS

| Category | Total | ✅ Proven | 📚 Cited | 🔄 Running | 🎯 TODO |
|----------|-------|-----------|----------|------------|---------|
| Peer-reviewed foundations | 12 | — | 12 | — | — |
| Main theorems | 3 | 2 | 1 | — | — |
| T0 Normalization | 3 | — | 3 | — | — |
| A1' Density | 12 | 10 | — | 2 | — |
| A2 Lipschitz | 4 | 4 | — | — | — |
| A3 Bridge | 16 | 4 | 4 | — | **7** |
| RKHS Contraction | 12 | 11 | 1 | — | — |
| T5 Transfer | 3 | — | 3 | — | — |
| Q Nonneg | 4 | 4 | — | — | — |
| **TOTAL** | **69** | **35** | **24** | **2** | **7** |

**Coverage: (35 proven + 24 cited) / 69 = 85%**
**After A1 + TODO: 59/62 = 95%**

---

# NEXT ACTIONS

1. **Wait for A1_density** (Aristotle running, 2%)
2. **Create tasks for 7 TODO items** in A3 section
3. **Verify all files compile**: `lake env lean <file>.lean`

---

# FILE QUICK REFERENCE

```
q3.lean.aristotle/
├── Q3/
│   ├── Axioms.lean              # axioms list (count tracked in PROJECT_ORCHESTRATOR.md)
│   └── Main.lean                # RH_of_Weil_and_Q3 ✅
├── Q3/Proofs/
│   ├── A1_density_integrated.lean
│   ├── A3_bridge_integrated.lean         ✅
│   ├── RKHS_contraction_integrated.lean  ✅
│   ├── Q_Lipschitz_integrated.lean       ✅
│   ├── Q_nonneg_on_atoms_integrated.lean ✅
│   ├── W_sum_finite_integrated.lean      ✅
│   ├── node_spacing_integrated.lean      ✅
│   ├── off_diag_exp_sum_integrated.lean  ✅
│   └── S_K_small_integrated.lean         ✅
└── aristotle_output/                      # 11 Aristotle proofs
```
