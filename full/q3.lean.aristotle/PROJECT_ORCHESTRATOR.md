# PROJECT ORCHESTRATOR - Q3
## Lean Formalization of Riemann Hypothesis

Last Updated: 2026-01-26
Single entry point: read this file at session start.

## Quick Start

1) Read this file.
2) Use "Current State" and "Active Next Step".
3) Only open linked files if needed.
3.5) Chain summary: `docs/CHAIN_STATUS.md` (single-scale t_critical mainline).
3.6) Knowledge base index: `ACTIVE/KNOWLEDGE_BASE.md` (link-first map).
4) Documentation discipline: update `docs/INSIGHTS.md` and
   `FORMALIZATION_STATS.md` instead of creating new docs.
5) **Застрял > 30 мин?** → Запроси Прошку (см. `docs/INSIGHTS.md` секция "Прошка").
6) Hub for active docs/db/scripts: `ACTIVE/` (symlink index).

## Current State (short)

- A3_FLOOR is proven and integrated: `P_A_ge_c_star` from
  `A3_Floor_Main.lean` is used in the Fourier A3 bridge.
- Fourier A3 bridge is wired: `Q3/Atoms_Positive.lean` now depends on
  `A3_bridge_data_rayleigh_Fourier` and the axiom
  `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.
- `Q_Lipschitz_on_W_K` is a theorem; arch/prime Lipschitz bridge axioms are closed
  in `Q3/Proofs/Q_Lipschitz.lean`.
- `mem_nodes_finset_of_mem_Q3Nodes` is a theorem in `Q3/Proofs/Bridge.lean`.
- RKHS contraction is now bridged: `RKHS_contraction_axiom` is no longer in
  `#print axioms` for `Q3.Main.RH_of_Weil_and_Q3` (see `Q3/Proofs/Bridge.lean`,
  wired in `Q3/AxiomsTheorems.lean`).
- `A1_density_WK_thm` is proven in `Q3/Proofs/A1_density.lean` and wired in
  `Q3/T5_Transfer.lean`, so `A1_density_WK_axiom` is gone from the main chain.
- RKHS cap is PROVEN in `Q3/Proofs/RKHS_cap_rayleigh.lean`:
  `weight_sum_le_rho_one` + `rkhs_cap_rayleigh_tcap` with `t_rkhs_cap = 40`.
- C1 compression identity is formalized (basisFun + dictionary embedding) in
  `Q3/Proofs/RKHS_cap_rayleigh.lean` (search `compression identity`).
- New one-scale A3 bridge scaffolding (no two-scale): `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`
  (fixed-`t` bridge + generic weight-sum → Rayleigh cap lemma in `Q3/Proofs/RKHS_cap_generic.lean`).
- Single-scale parameter source: `Q3/Proofs/Q_nonneg_t_critical.lean`
  (defines `t_critical = 3/20` and `t0_critical`).
- Atom positivity/T5 transfer now use `t0_critical` (t = 0.15) for `AtomCone_K_fixed`;
  BaseAtomCone guard lemma added in `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Mainline now uses `W_K_tau0` / `Weil_cone_tau0` (τ = 0, B-range) and
  `Weil_criterion_tau0`; the τ‑uniform prime‑term axiom is removed from the chain.
- `Schur_test` remains in the codebase but is **off‑chain** for the current mainline.
- Single-scale prime cap (tau = 0) is now a direct numeric bound:
  `rho_one ≤ c_star/4` in `Q3/Proofs/SingleScale_Assumptions.lean`.
- Helper lemma for “unitary conjugation preserves opNorm” added:
  `Q3/Proofs/OpNorm_Unitary.lean` (used in the `hA` decision tree, see `docs/INSIGHTS.md`).
- Legacy: `A3_bridge_axiom` (sampling Toeplitz + a_star) is still in `Q3/Axioms.lean`
  but no longer appears in the main chain.

## Wiring vs Closing (definition)

- wiring: replace an axiom in `Q3/AxiomsTheorems.lean` with a theorem. This only
  reduces `#print axioms` if the theorem is itself axiom-free.
- closing: provide a proof with no new axioms, so the axiom disappears from
  `#print axioms`.

## Axiom Count (verified)

Command:
```bash
./scripts/check_axioms.sh
# or manually:
echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin 2>&1 | rg -v "^info:"
```

Result: **6 axioms** (3 project + 3 kernel/standard)

- Kernel/standard: `propext`, `Classical.choice`, `Quot.sound`
- Level 1 (Classical Literature): `Weil_criterion_tau0`
- Level 2 (One‑scale numeric certificates @ t_critical):
  `Proofs.PrimeCert.prime_b_grid_val_le_margin`,
  `Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange`
- Legacy (off‑chain):
  `Schur_test` (classical), `prime_term_le_at_t_critical_axiom` (τ‑uniform bound; false‑for‑now)

**Closed axioms (history):**
- `a_star_pos` → closed via positivity (2026-01-21)
- `a_star_continuous` → closed via Mathlib Gamma continuity
- `a_star_bdd_on_compact` → closed via continuous + compact
- `a_star_even` → closed via Mathlib Gamma_conj (2026-01-20)
- `A1_density_WK_axiom` → closed via bounded hat interpolation (h_even as mass bound)
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` → closed via Q_nonneg_atoms_closure (2026-01-24)
- `SingleScale.continuous_P_A_shift` → closed via `ShiftedWindows.P_A_shift_continuous` (2026-01-24)

## Critical Chain (ASCII)

```
RH_of_Weil_and_Q3
  |
  +-- Weil_criterion_tau0 [AX external]
  |
  +-- Q_nonneg_on_Weil_cone_tau0 [OK]
       |
       +-- T5_transfer_tau0 [OK]
            |
            +-- Q_Lipschitz_on_W_K [OK]
            +-- Q_nonneg_on_base_atoms_brange [OK]
                 |
                 +-- one‑scale @ t_critical [OK]
                      |
                      +-- PrimeCert: prime_b_grid_val_le_margin [AX cert]
                      +-- PrimeCert: prime_margin_Lipschitz_on_Brange [AX cert]
```

## 🚨🚨🚨 CRITICAL: LaTeX Proof Gap Discovered (2026-01-22) 🚨🚨🚨

**FINDING:** Numerical verification shows Q(Φ_{t_sym}) = -16.29 < 0, contradicting Theorem A3.

**ROOT CAUSE:** The LaTeX proof conflates TWO DIFFERENT T_P operators:

1. **Rayleigh T_P^{(M)}** (rayleigh_bridge.tex): `Σ w(n)·Φ_{B,t}(ξ_n)·|v_n⟩⟨v_n|`
   - Includes Fejér×heat damping factor `Φ_{B,t}(ξ_n)`
   
2. **RKHS T_P** (RKHS/main.tex): `Σ w_RKHS(n)·|k_n⟩⟨k_n|`
   - NO Fejér×heat factor — just `w_RKHS(n) = Λ(n)/√n`

**THE GAP:** Theorem A3 claims `λ_min(T_M[P_A] - T_P) ≥ c_*/4` using:
- P_A built with t_sym = 0.06
- ||T_P|| bound from RKHS (which uses different operator!)

**Numerical verification (B=3, t_sym=0.06):**
- Arch term: ∫ P_A dθ = 11.06
- Prime term: Σ w(n)·Φ(ξ_n) = 27.35
- **Q = -16.29 < 0** ← CONTRADICTS THEOREM

**FULL ANALYSIS:** `docs/LATEX_PROOF_GAP_ANALYSIS.md`

**STATUS:** `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` is closed via the
single‑scale chain; mainline now uses the τ = 0 cone (`Weil_cone_tau0`) and
`Weil_criterion_tau0`. The τ‑uniform prime‑term axiom is off‑chain.
Mathematical consultation with Proshka required to remove those assumptions.

**PIVOT STATUS:** one‑scale parameterization at `t = t_critical` is now the mainline,
with τ = 0 cone (`Weil_cone_tau0`) and `Weil_criterion_tau0`.
Decision tree + file pointers live in `docs/INSIGHTS.md` (search for “нетривиальное hA”).

---

## Active Next Step (current mainline)

1) Validate/close PrimeCert axioms:
   `prime_b_grid_val_le_margin`, `prime_margin_Lipschitz_on_Brange`.
2) Keep `Weil_criterion_tau0` as external classical axiom.
3) Revisit τ‑uniform bounds only after a new kernel model (optional, off‑chain).

### What does “which branch?” mean (for a normal git user)

There are two different meanings of “ветка”:

1) **Git branch** (what `git switch` changes): currently we work on `projekt_2A`.
2) **Proof-architecture branch** (inside one git branch): “A3_FLOOR/Fourier Toeplitz” vs “old RKHS operator”.

Quick way to orient a fresh session:

```bash
git branch --show-current
git log -n 1 --oneline
sed -n '1,80p' full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
```

### Two parallel work streams (recommended)

**Stream A (NOW, closes chain fast): Option 2 = Schur/weight_sum cap (no RKHS embedding)**

- The “cap” is already formalized for the Rayleigh/compression operator:
  `Q3/Proofs/RKHS_cap_rayleigh.lean` (`T_P_comp_real_opNorm_le_weight_sum`, `weight_sum_le_rho_one`, `rkhs_cap_rayleigh_tcap`).
- This stream is about **wiring/porting it to the one-scale `t_critical` chain** (not about Moore–Aronszajn).

**Stream B (PARALLEL, infrastructure): Option 1 = true Gaussian/RKHS kernel model**

- Aristotle tasks live in `full/q3.lean.aristotle/aristotle_input/`.
- Current task (kernel identity): `aristotle_input/gaussian_rkhs_kernel_v1.lean` + `.md`.
- Goal: extract hole-free lemmas from Aristotle output and then implement the RKHS interface in-project.

Rule: do Stream A on the main branch to keep momentum; do Stream B via small, self-contained Aristotle tasks
so we never block the main closure on analytic infrastructure.

## ✅ RESOLVED: AtomCone_K_fixed Quantifier Gap (2026-01-26)

**Resolution:** the fixed‑t cone is now part of the formal chain.
- `AtomCone_K_fixed` + `AtomCone_K_fixed_subset` are in `Q3/Axioms.lean`.
- T5 transfer uses `t0_critical` and `AtomCone_K_fixed`.
- Mainline uses the τ = 0 cone: `BaseAtomCone_K_brange` → `W_K_tau0` → `Weil_cone_tau0`.

**Details:** `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`

## Closure Tracker (remaining axioms)

| Axiom | Current proof source | Blocker | Next action | Status |
|------|-----------------------|---------|-------------|--------|
| `Weil_criterion_tau0` | External (classical) | None | Classical result, keep as axiom | **EXTERNAL** |
| `Proofs.PrimeCert.prime_b_grid_val_le_margin` | Numeric certificate | Cert proof/validation | close or keep as cert axiom | **AXIOM (cert)** |
| `Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange` | Numeric certificate | Cert proof/validation | close or keep as cert axiom | **AXIOM (cert)** |

## Progress Log (2026-01-16)

**P_A_continuous**:
- CLOSED in `A3_Floor_Main.lean` (local finiteness + periodicity proof)

**Q_nonneg_on_atoms (Rayleigh-Q identification)**:
- `Q3/Proofs/Rayleigh_Q_identification.lean` COMPLETE:
  - `basis0`, `i0`, `basis0_norm_sq`, `basis0_ne_zero`
  - `quadForm_basis0`, `rayleigh_basis0`, `rayleigh_basis0_sub`
  - `ToeplitzEntry_diag`, `ToeplitzEntry_diag_re`, `ToeplitzMatrix_Fourier_real_diag`
  - `fourier_index_i0`, `prime_vec_i0`, `T_P_comp_real_diag`
  - `integral_P_A_eq_arch_term` (periodization) ✅
  - `rayleigh_Q_identification`, `rayleigh_Q_eq_Q` ✅
- Done (2026-01-24): wired into `Atoms_Positive.lean` via `Q_nonneg_atoms_closure` (axiom closed).

**Aristotle projects (Rayleigh variants)**:
- 200eb072, 5e36515f, e9f53e97, eeca690a (Rayleigh sandbox variants)

## Legacy / History (2026-01-14)

**NEW (2026-01-14)**: Rayleigh lower bound PROVEN via Aristotle!
- V1 (pure informal): `aristotle_output/rayleigh_v1.lean` — COMPLETE, 0 sorry
- V2 (sandbox): `aristotle_output/rayleigh_v2.lean` — helpers only, main sorry

**A3_bridge Aristotle runs (2026-01-14)**:
- **V1 (`4c2ed336`)**: COMPLETE! Real T_P bounds proven (see below)
- V2 (`f6a9eed5`): исправленный — skipped (V1/V3 better)
- **V3 (`22378a11`)**: по Прошкиному скелету — **COMPLETE! 0 sorry!**
- **V4 (`c35f3088`)**: COMPLETE! 309 lines, 0 sorry — bounds for direct-indexed T_P

**V1 SURPRISE**: `aristotle_output/A3_bridge_closure_v1.lean`
- `w_RKHS_le_w_max`: ✅ w_RKHS(n) ≤ w_max = 2/e
- `w_max_lt_three_quarters_c_star`: ✅ **w_max < 3c*/4** (key inequality!)
- `T_P_tendsto_zero_of_ne`: ✅ off-diagonal → 0 as t → 0
- `exists_t_max_row_sum_le_for_M`: ✅ ∀ M, ∃ t: ||T_P|| ≤ 3c*/4
- **CLARIFIED**: V1/V4 prove `∀M ∃t(M)` for DIRECT-INDEXED T_P. See below.

**V4 COMPLETE**: `aristotle_output/A3_bridge_v4_real_TP.lean`
- 309 lines, 14 declarations, 0 sorry
- Main: `T_P_norm_lt_three_quarters_c_star (M : ℕ) : ∃ t > 0, bound`
- Useful helpers: `w_RKHS_le_w_max`, `S_off_tendsto_zero`, `T_P_row_sum_bound`

**⚠️ CRITICAL INSIGHT: T_P Definition Mismatch (2026-01-14)**

V1/V4 use **direct-indexed T_P**:
```lean
T_P i j = sqrt(w_RKHS i) * sqrt(w_RKHS j) * exp(-(ξᵢ - ξⱼ)²/4t)
```
This has ||T_P|| → ∞ as M → ∞, so uniform t is IMPOSSIBLE.

Q3 tex (rayleigh_bridge.tex) uses **compression T_P**:
```lean
T_P^{(M)} i j = ∑ n : Nodes K, w_Q n * Φ(ξₙ) * v_n[i] * v_n[j]
```
This has ||T_P^{(M)}|| ≤ ||T_P|| (compression), so uniform t IS possible.

**V1/V4 status**: Useful for local bounds, sanity checks. NOT for uniform A3_bridge.

**🚀 V5 (`1cac53dd`) — RAYLEIGH-FIRST (2026-01-14)**: ✅ **COMPLETE!**
- Input: `aristotle_input/A3_bridge_RAYLEIGH_FIRST.md` (from Proshka)
- Output: `aristotle_output/A3_bridge_rayleigh_first_v5.lean` — **120 lines, 0 sorry!**
- **No SB, No M₀** — Rayleigh for Toeplitz; RKHS cap now at `t_rkhs_cap=40`
- **T_P_comp** — rank-one sum (compression, correct definition!)

**V5 proven lemmas:**
- `quadForm_sub`, `rayleighQ_sub` — quadratic form algebra
- `cstar_sub_rho_ge_quarter` — c* - 1/25 ≥ c*/4 (norm_num)
- `A3_bridge_rayleigh_first` — **MAIN THEOREM**

**Dependencies (hypotheses in V5):**
1. `h_rayleigh_lower_bound` — from `rayleigh_v1.lean` ✅
2. `h_floor` — from A3_FLOOR ✅
3. `h_cap` — **PROVEN** in `Q3/Proofs/RKHS_cap_rayleigh.lean`
   (`weight_sum_le_rho_one`, `rkhs_cap_rayleigh_tcap`, `t_rkhs_cap=40`)

**V3 SUCCESS**: `aristotle_output/A3_bridge_v3_proshka.lean`
- Все 4 леммы доказаны
- НО: P_A=const, T_P=0 (placeholder'ы)
- Общие леммы (rayleigh, quadform_sub) переиспользуемы

**INSIGHT**: Прошка показал что SB не нужен; RKHS cap ≤ `rho_one = 1/25`
(в реализации с `t_rkhs_cap=40`).
Полный скелет: `aristotle_input/A3_bridge_PROSHKA_SKELETON.md`

Closed (recent):
- `RKHS_contraction_axiom` → bridged in `Q3/Proofs/Bridge.lean`, wired in `Q3/AxiomsTheorems.lean`

### A1_density Definitional Issue - RESOLVED (Option 2)

**Problem**: AtomCone_K requires `g ∈ W_K K` which includes `support g ⊆ [-K, K]`.
However, atoms with centers τ ∈ [-K, K] and widths B ≤ K have support in [-2K, 2K].

**Solution (Option 2)**: Changed AtomCone_K definition to require `|τ| + B ≤ K` instead
of separate `|τ| ≤ K` and `B ≤ K`. This matches Lemma 6.4 (Fixed-t₀ cone density).

**What was done**:
- Changed `AtomCone_K` in `Q3/Axioms.lean` and `Q3/Proofs/A1_density.lean`
- Added support control lemmas: `FejerKernel_eq_zero_of_abs_ge`,
  `Atom_eq_zero_outside_window`, `sum_atoms_eq_zero_outside`
- `hg_supp` now uses these lemmas (conditional on `hτB_cond`)
- Updated `W_K` to require `Continuous` (global), matching Q3 text (`C_c` tests).
  This enables the heat-kernel identity lemma for `h_approx`.

**Proven in A1_density_WK_thm**:
- Zero case: handled via n=0 representation
- hg_cont: continuity of sum of atoms
- hg_even: evenness (atoms are even in x)
- hg_nonneg: nonnegativity (nonneg weights × nonneg atoms)
- hg_supp: support containment (uses new margin condition)

**A1_density status:** `A1_density_WK_thm` is fully proven and wired into
`Q3/T5_Transfer.lean`. No remaining sorries in `Q3/Proofs/A1_density.lean`.

## Key Files (open only as needed)

- `PROJECT_WORKFLOW.md` - workflow loop + Aristotle rules (no status)
- `PROJECT_ASCII.md` - diagram (derived from this file)
- `docs/INSIGHTS.md` - collected project insights (do not create new docs)
- `FORMALIZATION_STATS.md` - quantitative stats snapshot
- `docs/PROJECT_SPECS.md` - spec/invariants for Proshka check (Rayleigh plan)
- `docs/Q3_PDF_STRUCTURE.md` - **FULL theorem/lemma trace from RH_Q3.pdf**
- `docs/PDF_DB_COVERAGE.md` - 80% coverage report (PDF vs DB)
- `PROOF_MAP_NEW_KERNEL.md` + `A3_FLOOR_ROADMAP.md` - A3_FLOOR status
- `Q3/Axioms.lean` and `Q3/AxiomsTheorems.lean` - axioms and wiring
- `Q3/Proofs/Q_Lipschitz.lean` - real proof of Q_Lipschitz
- `Q3/Proofs/Bridge.lean` + `Q3/Proofs/RKHS_contraction_bridge.lean`
- `Q3/Proofs/A3_Bridge_Uniform.lean`
- `Q3/Proofs/Q_Nonneg_Bridge.lean`
- `Q3/Proofs/A1_density.lean`
- `aristotle_db/parse_lean.py` - DB import

## Progress Tracking (DB)

```bash
python3 aristotle_db/parse_lean.py list-docs
python3 aristotle_db/parse_lean.py list-lemmas Q_Lipschitz
```

## Update Rule

After closing a step:
- run `lake env lean <file>`
- re-import to DB (`aristotle_db/parse_lean.py import ...`)
- update this file and `PROJECT_ASCII.md`

## Future: Community Presentation

After Tier-2 closure -> present to Talia Ringer / Lean Zulip.
See `PHILOSOPHY_OF_PROOF.md` for the pitch.

## Build / Verify

```bash
cd /media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/q3.lean.aristotle
lake build Q3.Main
```

```bash
./scripts/check_axioms.sh
```

```bash
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>&1 | rg -v "^info:"
```

## Change Log (recent)

- 2026-01-22: **CRITICAL LaTeX PROOF GAP DISCOVERED**
  - Numerical verification: Q(Φ_{B=3,t=0.06}) = -16.29 < 0
  - Root cause: Two different T_P operators conflated in proof
  - Rayleigh T_P uses Φ weights, RKHS T_P does not
  - "Two-scale decoupling" is mathematically invalid
  - Created: `docs/LATEX_PROOF_GAP_ANALYSIS.md`
  - Status: **BLOCKED** — need mathematical consultation

- 2026-01-20: **Schur_test investigation** — L2 vs L∞ norm mismatch
  - Attempted to close `Schur_test` axiom using Mathlib
  - Created `Q3/Proofs/Schur_Test.lean` with L∞ proof
  - CANNOT wire: project uses L2 (spectral) norm, Mathlib proof uses L∞ (row-sum)
  - Full L2 proof requires Gershgorin + spectral norm theory
  - See: `docs/insights/schur_test_l2_vs_linfty_2026_01_20.md`

- 2026-01-20: **Phase A file refactoring** completed
  - Renamed v19/v20/v22/v2/v3 files to clean names
  - Updated all imports across project
  - Updated check_axioms.sh with correct counts (11 total, 8 project)
  - Updated CLAUDE.md paths (Mac → Linux)

- 2026-01-16: **BLOCKER DISCOVERED** — A3_bridge closure blocked by symbol mismatch!
  - `A3_bridge_data` uses sampling Toeplitz with `a_star` (mathematically WRONG: a_star → -∞)
  - `A3_bridge_data_rayleigh_Fourier` uses Fourier Toeplitz with `P_A` (CORRECT and PROVEN)
  - Types are mathematically incompatible — cannot bridge directly
  - **NEW PLAN:** Refactor chain to Fourier formulation + prove Rayleigh-Q identification (Theorem 3.3)
  - See: `TRICKS_LIBRARY.md`, `docs/insights/a_star_vs_p_a_dossier.md`

- 2026-01-15: **weight_sum_bound PROVEN** via Aristotle — 7 parallel submissions, ALL complete!
  - All 7 variants: 0 sorry, line counts 197-242
  - **v1_copy1 (197 lines)** — SHORTEST, recommended
  - Files: `aristotle_output/weight_sum_variants/v0_original.lean` through `v6_copy6.lean`
  - Analysis: `aristotle_output/weight_sum_variants/ANALYSIS.md`
  - **Proshka insights**: `suffices` > `have` ladders, minimal `aesop` (<2), π-free bounds more stable
  - **New guidelines**: `aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`
  - Job IDs: fb91fbb3, ee8bc919, 78a7d870, e648f487, caf3e4c0, ba71a35a, c020a6a2

- 2026-01-14: **Rayleigh Lower Bound PROVEN** via Aristotle!
  Two parallel Aristotle jobs submitted:
  - V1 (pure informal): project `5990b601-ed48-442b-a4d3-5d8a18b444e3` → COMPLETE
  - V2 (sandbox): project `e9f8b481-8f80-4bdd-b798-be5c796eeead` → helpers only

  **V1 is the winner**: `aristotle_output/rayleigh_v1.lean` has COMPLETE proof (0 sorry):
  - `toeplitz_integrand_eq`, `toeplitz_quadratic_form`, `integral_exp_2pi_n_theta`
  - `parseval_trig_poly`, `rayleigh_lower_bound` (MAIN THEOREM)

  Key result: For Toeplitz matrix T with symbol P ≥ m, Rayleigh quotient ≥ m.
  Legacy note: this was previously wired into `A3_bridge_axiom` (sampling path).

- 2026-01-14: Wired `Q3.Theorems.A1_density_WK` into `Q3/T5_Transfer.lean`.
  `A1_density_WK_axiom` is now removed from `#print axioms` (total axioms: 9).

- 2026-01-14: Submitted Aristotle job `hat_interpolation_approx.md`
  (project `18bfe8c7-4620-41d4-be62-489409168e95`) with corrected boundary
  condition `f(-K)=f(K)=0`.

- 2026-01-14: Cleaned `aristotle_output/A1_density_hat_chain.lean` by replacing
  `exact?` with `FejerKernel_partition_unity`, switching `ring`→`ring_nf`, and
  removing unused variables; file compiles with no warnings.

- 2026-01-14: Submitted `A1_density_hat_chain` to Aristotle (project `e90d4213`).
  Plan: rewrite A1_density_WK_thm using hat-chain (Lemma 6.4) instead of
  convolution + Riemann sum. This avoids B vs B' mismatch and asymmetric sums.
  Key insight: W_K boundary vanishing (Φ(±K)=0) follows from global continuity.

- 2026-01-14: Integrated hat interpolation proof into
  `Q3/Proofs/HatInterpolation.lean` (namespaced) and wired
  `hat_interpolation_approx` in `Q3/Proofs/A1_density.lean`
  with `max_comm` rewrite. Remaining sorry: `h_approx` only.

- 2026-01-14: Created `aristotle_output/HatInterpolationBridge.lean` bridge file.
  Aristotle proof uses `FejerKernel δ x := max (1 - |x|/δ) 0` while A1_density uses
  `max 0 (1 - |x|/B)`. Bridge converts between them via `max_comm`.
  **BLOCKER**: Direct import causes FejerKernel name conflict (both at top level).
  **TODO**: Refactor A1_density to use `Q3.Fejer_kernel` from Axioms.lean, or add namespace.
  Current status: 2 sorries in A1_density.lean (hat_interpolation_approx + h_approx).
  Build passes (axiom count tracked in the "Axiom Count" section above).

- 2026-01-14: **Aristotle COMPLETE** for `hat_interpolation_approx`!
  KEY FINDING: Original lemma signature was WRONG — proved counterexample for f(x)=1.
  **Fix**: Added `hf_boundary : f (-K) = 0 ∧ f K = 0` hypothesis.
  With margin condition |τᵢ| + δ ≤ K, all hats vanish at ±K.
  Full proof in `aristotle_output/hat_interpolation_approx.lean`.

- 2026-01-14: `hat_interpolation_approx` scaffolded in A1_density.lean — proved
  grid membership `hτ_in`, margin condition `hτ_margin`; 1 sorry remains
  `h_approx_bound` (approximation chain). Aristotle processing two projects:
  `bcec962f-4686-493e-b057-19695ddfc7b6` (hat_interpolation_approx),
  `9dda8778-857e-42cf-a669-aad1a2e04d5b` (A1_density_hat_full_v1 at 3%).

- 2026-01-14: Recreated Aristotle skill at `~/.codex/skills/aristotle/`,
  updated workflow docs to use CLI/Python API, submitted
  `aristotle_input/A1_density_hat_full_v1.md` (project `9dda8778-857e-42cf-a669-aad1a2e04d5b`).

- 2026-01-14: Updated `docs/PROJECT_SPECS.md` to the Rayleigh plan (no SB as blocker);
  added Aristotle input drafts `aristotle_input/A1_density_hat_full_v1.md` and
  `aristotle_input/A1_density_hat_only_v1.md`.

- 2026-01-14: Fixed HeatKernel derivative/Lipschitz proofs in
  `Q3/Proofs/A1_density.lean`; remaining sorries now only
  `hat_interpolation_approx` + `h_approx`.

- 2026-01-13: `A1_density_WK_thm` hτB_cond CLOSED! Changed `uniform_riemann_sum` to
  return `Set.Ioo` (strictly inside) instead of `Set.Icc`. Grid uses midpoints so
  all points y satisfy |y| < K. Compute margin = K - max{|y|}, set B' = min B margin.
  Also return `s.Nonempty` from both `uniform_riemann_sum` and `convolution_approx_by_sum`.
  Only 1 sorry remains: h_approx (triangle inequality chain).
- 2026-01-13: `A1_density_WK_thm` hg_mem proof mostly complete - proved continuity,
  evenness, nonnegativity; 2 sorries remain (hg_supp blocked by definitional issue,
  h_approx needs triangle inequality). Identified AtomCone_K support issue.
- 2026-01-13: `A1_density_WK_thm` circular dependency removed; now uses local lemmas
  with 4 `sorry` placeholders (support, nonneg, AtomCone membership, triangle ineq).
- 2026-01-13: DB import: Bridge.lean (13 decls), RKHS_contraction_bridge.lean (10 decls).
- 2026-01-13: Fixed `scripts/check_axioms.sh` (--stdin flag, correct axiom counting).
- 2026-01-13: Updated orchestrator to be the single entry point and clarified
  wiring vs closing.
- 2026-01-13: Closed arch/prime Lipschitz bridge axioms in `Q3/Proofs/Q_Lipschitz.lean`.
- 2026-01-13: `mem_nodes_finset_of_mem_Q3Nodes` proved in `Q3/Proofs/Bridge.lean`.
- 2026-01-13: `Q3/Proofs/RKHS_contraction_bridge.lean` compiles; DB import updated.
- 2026-01-13: Fixed `Q3/T5_Transfer.lean` AtomCone subset pattern; `lake build Q3.Main`
  passes; `RKHS_contraction_axiom` removed from main axiom list (total now 10).
