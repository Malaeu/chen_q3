# Main Chain Dependencies vs Repo Legacy (2026-03-06 16:40)

**Status:** support snapshot only; read this only after `PROJECT_ORCHESTRATOR.md`.
This file does not decide the active frontier or queue state.

**Purpose:** Supporting dependency snapshot separating *actual main-chain blockers* from legacy/sandbox noise.  
**Current status:** compiled `Q3.Main.RH_of_Weil_and_Q3` now depends on
**2 project axioms**:
`Q3.Weil_criterion` and `Q3.prime_term_le_at_t_critical_axiom`.
Standard axioms are the usual 3:
`propext`, `Classical.choice`, `Quot.sound`.  
**Next action:** repair the scalar shifted-atom node honestly and stop treating
old `τ=0`/PathB dashboards as if they were still the active RH chain.
**Decision (2026-03-06):** source of truth is the live shifted-atom route
coming from `Q3/Main.lean`, not the older `τ=0` certificate branch.
**Links:** `Q3/CheckAxioms.lean` · `Q3/Main.lean` · `ACTIVE/orchestrator.md`

---

Purpose: separate *what actually blocks RH in the current main chain* from
legacy/sandbox files that inflate raw axiom/sorry counts.

## 1) Source of truth (do this first)

Run:
- `lake env lean Q3/CheckAxioms.lean`

This prints the *actual axioms used by* `Q3.Main.RH_of_Weil_and_Q3`.

## 2) Main-chain dependencies (current)

From
`printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin`:

- Tier-1 / classical:
  - `Q3.Weil_criterion`

- Tier-2 / Q3-specific (active shifted-atom route):
  - `Q3.prime_term_le_at_t_critical_axiom`

Notes (2026-03-06):
- Активная цепочка идёт через
  `Q3.Main -> Q3.RH_of_shifted_atom_route -> PaperMainlineAtomRoute ->
   CompatibilityReduction -> Q_nonneg_t_critical`.
- `Q3.Weil_criterion_tau0`, `Q3.prime_cert_margin_from_pathB`,
  `Q3.prime_cert_margin_from_rkhs` и PrimeCert cert-data
  **не входят** в текущий `#print axioms Q3.Main.RH_of_Weil_and_Q3`.
- Теоремы `Q_phi_shift_pair_nonneg_t_critical` и
  `Q_Fejer_heat_atom_nonneg_t_critical` уже экспортированы, но пока разворачиваются
  в тот же scalar placeholder.
- Локальная численная запись в `docs/INSIGHTS.md` уже помечает полный
  `τ`-uniform scalar claim как false-for-now, так что чинить надо контракт,
  а не только имя аксиомы.

Standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) are always present.

## 3) Load-bearing file map (what to close first)

| Node / Axiom | File | Why it blocks the chain |
|---|---|---|
| `prime_term_le_at_t_critical_axiom` | `Q3/Proofs/Q_nonneg_t_critical.lean` | единственный project placeholder в active shifted-atom scalar node |
| `Weil_criterion` | `Q3/Axioms.lean` | classical bridge `Q >= 0` on `Weil_cone` ⇒ RH |
| `Q_phi_shift_nonneg_t_critical` | `Q3/Proofs/Q_nonneg_t_critical.lean` | theorem wrapper directly fed by the scalar axiom |
| `Q_Fejer_heat_atom_nonneg_t_critical` | `Q3/Proofs/Q_nonneg_t_critical.lean` | paper-facing scalar theorem name, but not yet independent |
| `CompatibilityReduction` | `Q3/Proofs/CompatibilityReduction.lean` | closure machinery is theoremized and ready once scalar node is honest |

## 4) Why raw counts look huge

Raw `rg` counts include:
- `Q3/Clean/**` (clean-room / tier experiments)
- `Q3/Archive/**` and `archive/**`
- `aristotle_output/**`
- legacy two-scale files

These are **not** imported by `Q3/Main.lean` and do not affect the current main chain.

## 6) Off‑chain notes

- The older `τ=0` branch (`Weil_criterion_tau0`, `prime_cert_margin_from_pathB`,
  `prime_cert_margin_from_rkhs`, PrimeCert data axioms) remains useful as
  archive / fallback analysis, but is **not** the active `Q3.Main` chain anymore.
- Raw repo references to those names are expected in legacy files and notes.

## 5) Quick commands (sanity check)

- Main-chain deps: `lake env lean Q3/CheckAxioms.lean`
- Raw counts (inflated):
  - `rg -n "^\s*axiom\b" Q3 --type=lean | wc -l`
  - `rg -n "\bsorry\b" Q3 --type=lean | wc -l`
