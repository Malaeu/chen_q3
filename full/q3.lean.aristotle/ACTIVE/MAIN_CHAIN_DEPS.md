# Main Chain Dependencies vs Repo Legacy (2026-01-29 13:10)

**Purpose:** Separate *actual main-chain blockers* from legacy/sandbox noise.  
**Current status:** Main-chain depends on **2 Q3 data axioms** + 2 classical.  
**Next action:** Close the PrimeCert cert‑data axioms
`prime_b_grid_bounds_data` and `prime_heat_bounds_data`.  
**Links:** `Q3/CheckAxioms.lean` · `Q3/Main.lean` · `ACTIVE/orchestrator.md`

---

Purpose: separate *what actually blocks RH in the current main chain* from
legacy/sandbox files that inflate raw axiom/sorry counts.

## 1) Source of truth (do this first)

Run:
- `lake env lean Q3/CheckAxioms.lean`

This prints the *actual axioms used by* `Q3.Main.RH_of_Weil_and_Q3`.

## 2) Main-chain dependencies (current)

From `#print axioms Q3.Main.RH_of_Weil_and_Q3`:

- Tier-1 / classical:
  - `Q3.Weil_criterion_tau0`
  - (Note) `Q3.Schur_test` exists in `Q3/Axioms.lean`, but is **not** in the current
    `#print axioms Q3.Main.RH_of_Weil_and_Q3` output (verify via `Q3/CheckAxioms.lean`).

- Tier-2 / Q3-specific (τ=0 mainline):
  - `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
  - `Q3.Proofs.PrimeCert.prime_heat_bounds_data`

Standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) are always present.

## 3) Load-bearing file map (what to close first)

| Node / Axiom | File | Why it blocks the chain |
|---|---|---|
| `prime_b_grid_bounds_data` | `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` | Grid arch/prime bounds data |
| `prime_heat_bounds_data` | `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean` | Heat-weighted arch/prime bounds data |
| `Weil_criterion_tau0` | `Q3/Axioms.lean` | classical bridge `Q >= 0` ⇒ RH (τ = 0 mainline) |
| `Schur_test` | `Q3/Axioms.lean` | legacy / off‑chain in current mainline |

## 4) Why raw counts look huge

Raw `rg` counts include:
- `Q3/Clean/**` (clean-room / tier experiments)
- `Q3/Archive/**` and `archive/**`
- `aristotle_output/**`
- legacy two-scale files

These are **not** imported by `Q3/Main.lean` and do not affect the current main chain.

## 6) Off‑chain notes

- `Q3.prime_term_le_at_t_critical_axiom` lives in `Q3/Proofs/Q_nonneg_t_critical.lean`
  for the **τ ≠ 0** path; the τ=0 mainline does **not** depend on it.

## 5) Quick commands (sanity check)

- Main-chain deps: `lake env lean Q3/CheckAxioms.lean`
- Raw counts (inflated):
  - `rg -n "^\s*axiom\b" Q3 --type=lean | wc -l`
  - `rg -n "\bsorry\b" Q3 --type=lean | wc -l`
