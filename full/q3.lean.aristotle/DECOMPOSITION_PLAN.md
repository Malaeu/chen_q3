# Q3 PAPER: FULL LEAN FORMALIZATION VIA ARISTOTLE

## OVERVIEW

**Paper:** RH_Q3.pdf (~60 pages)
**Goal:** Complete Lean4 formalization of Riemann Hypothesis proof via Weil criterion
**Total Theorems/Lemmas:** ~111 statements

---

## TWO PATHS

### PATH A: FORMALIZATION (Manual Specs)
- We write detailed specifications for each theorem
- Include proof sketches from paper
- Aristotle verifies and produces Lean code
- **Pros:** Full control, matches paper exactly
- **Cons:** Labor intensive

### PATH B: DISCOVERY (Autonomous Proofs)
- We give theorem statements only
- Aristotle attempts to prove independently
- **Pros:** Tests Aristotle's capabilities, may find better proofs
- **Cons:** May fail on hard theorems

---

## SECTION BREAKDOWN (by theorem count)

### PRIORITY 1: CORE THEOREMS (45 theorems)

| File | Count | Description |
|------|-------|-------------|
| RKHS/prime_cap.tex | 11 | Prime operator cap ‖T_P‖ bound |
| RKHS/main.tex | 10 | RKHS framework core |
| A3/symbol_floor.tex | 8 | Toeplitz symbol estimates |
| A3/main.tex | 7 | A3 main Szegő-Böttcher bridge |
| A3/matrix_guard.tex | 6 | Matrix inequality guards |
| IND_AB/MD_2_3_base_interval.tex | 5 | Induction base case |

### PRIORITY 2: SUPPORTING LEMMAS (35 theorems)

| File | Count | Description |
|------|-------|-------------|
| T5/lemmas.tex | 4 | Compact transfer lemmas |
| RKHS/core.tex | 4 | RKHS core definitions |
| A2.tex | 4 | Lipschitz control of Q |
| T0.tex | 3 | Guinand-Weil normalization |
| T5/summary.tex | 3 | T5 summary theorems |
| RKHS/prime_norm_leq_rho.tex | 3 | Prime norm bounds |
| A3/rayleigh_bridge.tex | 3 | Rayleigh quotient bridge |
| A3/fejer_modulus.tex | 3 | Fejér kernel estimates |
| A3/calibration.tex | 3 | Parameter calibration |
| A3/arch_bounds.tex | 3 | Archimedean bounds |
| A1prime.tex | 3 | Local density A1' |

### PRIORITY 3: AUXILIARY (31 theorems)

| File | Count | Description |
|------|-------|-------------|
| IND_AB/* | 7 | Induction machinery |
| D3/* | 7 | D3 lock mechanism |
| T5/* | 6 | Compact transfer details |
| RKHS/* | 6 | RKHS remaining |
| Others | 5 | Weil linkage, intro, etc. |

---

## PROOF CHAIN STRUCTURE

```
T0 (Guinand-Weil normalization)
    ↓
A1' (Local density - Fejér×heat dense)
    ↓
A2 (Lipschitz control of Q)
    ↓
A3 (Toeplitz-Symbol bridge via Szegő-Böttcher)
    ↓
RKHS (Prime operator contraction: ‖T_P‖ ≤ c₀(K)/4)
    ↓
T5 (Compact-by-compact transfer)
    ↓
Main_closure (Assembly)
    ↓
═══════════════════════════════════════════
║ MAIN THEOREM: Q(Φ) ≥ 0 for all Φ ∈ W    ║
║                                          ║
║ Via Weil criterion ⟹ RIEMANN HYPOTHESIS  ║
═══════════════════════════════════════════
```

---

## INPUT FILE NAMING CONVENTION

```
input/
├── 01_T0_normalization.md          # T0: Guinand-Weil
├── 02_A1prime_local_density.md     # A1': Fejér×heat
├── 03_A2_lipschitz.md              # A2: Lipschitz control
├── 04_A3_toeplitz_main.md          # A3: Szegő bridge
├── 05_A3_symbol_floor.md           # A3: Symbol estimates
├── 06_A3_matrix_guard.md           # A3: Matrix guards
├── ...
├── 20_RKHS_prime_cap.md            # RKHS: ‖T_P‖ bound
├── 21_RKHS_main.md                 # RKHS: Framework
├── ...
├── 30_T5_transfer.md               # T5: Compact transfer
├── ...
├── 40_Main_closure.md              # Final assembly
└── 99_DISCOVERY_*.md               # Path B: Autonomous
```

---

## EXECUTION PLAN

### Phase 1: Foundation (Week 1)
1. T0: Guinand-Weil normalization
2. A1': Local density lemmas
3. A2: Lipschitz control

### Phase 2: Toeplitz-Symbol (Week 2)
4. A3/main.tex theorems
5. A3/symbol_floor.tex
6. A3/matrix_guard.tex
7. A3/calibration.tex

### Phase 3: RKHS (Week 3)
8. RKHS/core.tex
9. RKHS/main.tex
10. RKHS/prime_cap.tex (KEY!)
11. RKHS/prime_norm_leq_rho.tex

### Phase 4: Transfer & Assembly (Week 4)
12. T5 compact transfer
13. IND_AB induction
14. D3 lock mechanism
15. Main_closure assembly

### Phase 5: Discovery Mode
16. Give Aristotle key theorems without proofs
17. See what it can prove independently
18. Compare with our formalization

---

## SUCCESS CRITERIA

- [ ] All 111 theorems have Lean statements
- [ ] Core chain (T0 → A1' → A2 → A3 → RKHS → T5 → Main) verified
- [ ] Main theorem Q(Φ) ≥ 0 has complete proof
- [ ] All sorry statements analyzed and categorized
- [ ] Discovery mode results documented

---

## FILES TO READ FIRST

1. `/full/sections/T0.tex` - Starting point
2. `/full/sections/A1prime.tex` - Local density
3. `/full/sections/A3/main.tex` - Key bridge
4. `/full/sections/RKHS/prime_cap.tex` - Critical bound
5. `/full/sections/Main_closure.tex` - Final assembly

---

## ARISTOTLE USAGE

```bash
# Path A: Formalization
aristotle prove-from-file --informal --no-validate-lean-project input/01_T0_normalization.md

# Path B: Discovery
aristotle prove-from-file --informal input/99_DISCOVERY_main_theorem.md

# Monitor progress
aristotle list-projects --limit 20
```
