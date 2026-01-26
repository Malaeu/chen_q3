# Main Chain Dependencies vs Repo Legacy (2026-01-27 00:47)

**Purpose:** Separate *actual main-chain blockers* from legacy/sandbox noise.  
**Current status:** Main-chain depends on **2 Q3 axioms** + 2 classical.  
**Next action:** Close `prime_cert_margin_on_Brange_axiom` then `prime_term_le_at_t_critical_axiom`.  
**Links:** `Q3/CheckAxioms.lean` · `Q3/Main.lean` · `ACTIVE/orchestrator.md`

---

Purpose: separate *what actually blocks RH in the current main chain* from
legacy/sandbox files that inflate raw axiom/sorry counts.

## 1) Source of truth (do this first)

Run:
- `lake env lean Q3/CheckAxioms.lean`

This prints the *actual axioms used by* `Q3.Main.RH_of_Weil_and_Q3`.

## 2) Main-chain dependencies (current)

From `Q3/CheckAxioms.lean`:

- Tier-1 / classical:
  - `Q3.Weil_criterion`
  - `Q3.Schur_test`

- Tier-2 / Q3-specific:
  - `Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom`
  - `Q3.prime_term_le_at_t_critical_axiom`

Standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) are always present.

## 3) Load-bearing file map (what to close first)

| Node / Axiom | File | Why it blocks the chain |
|---|---|---|
| `prime_cert_margin_on_Brange_axiom` | `Q3/Proofs/PrimeCert/Brange_2046.lean` | B-range margin certificate at `t_critical` |
| `prime_term_le_at_t_critical_axiom` | `Q3/Proofs/Q_nonneg_t_critical.lean` | prime-term cap used by mainline |
| `Weil_criterion` | `Q3/Axioms.lean` | classical bridge `Q >= 0` ⇒ RH |
| `Schur_test` | `Q3/Axioms.lean` | matrix norm bound in RKHS chain |

## 4) Why raw counts look huge

Raw `rg` counts include:
- `Q3/Clean/**` (clean-room / tier experiments)
- `Q3/Archive/**` and `archive/**`
- `aristotle_output/**`
- legacy two-scale files

These are **not** imported by `Q3/Main.lean` and do not affect the current main chain.

## 5) Quick commands (sanity check)

- Main-chain deps: `lake env lean Q3/CheckAxioms.lean`
- Raw counts (inflated):
  - `rg -n "^\s*axiom\b" Q3 --type=lean | wc -l`
  - `rg -n "\bsorry\b" Q3 --type=lean | wc -l`
