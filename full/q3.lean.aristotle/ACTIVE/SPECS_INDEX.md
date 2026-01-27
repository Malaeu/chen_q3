# Specs Index (curated)

**Purpose:** Curated spec sources + constants; legacy vs mainline.  
**Current status:** Mainline constants listed below; legacy specs are inputs only.  
**Next action:** If updating constants, also update `ACTIVE/chain_status.md`.  
**Links:** `ACTIVE/MAIN_CHAIN_DEPS.md` · `ACTIVE/chain_status.md`

---

Purpose: single place to find spec sources + current-status notes.
Keep this short; details stay in linked docs.

## Linked spec sources (legacy/inputs)

- `spec_critical_constants_rh_q3.md`
  - Source: RH_Q3.pdf pages 32-36 constants (two-scale context).
- `spec_rh_q3_decomposition.md`
  - Source: RH_Q3 decomposition / ERS analysis (uniform/two-scale framing).
- `spec_formalizing_rh_insights.md`
  - Source: process insights from FormalizingRiemannHypothesis.
- `spec_high_ers_constants.md`
  - Source: ERS-based critical constants (t_sym/t_rkhs era).
- `ERS_SUMMARY.md`
  - Consolidated ERS overview (legacy).

These four are **inputs/legacy**. They are useful for background but are not
canonical for the current single-scale chain. Use `ACTIVE/chain_status.md`
for the mainline.

## Canonical constants (mainline)

| Constant | Value | Lean source | Status |
|---|---:|---|---|
| `c_star` | 11/10 | `Q3/Axioms.lean` | mainline |
| `c_star/4` | 11/40 | `Q3/Axioms.lean` | mainline target |
| `B_min` | 3 | `Q3/Proofs/A3_Floor_Main.lean` | mainline |
| `t_critical` | 3/20 | `Q3/Proofs/Params_Critical.lean` | mainline |
| `t0_critical` | 1/(16π²·t_critical) | `Q3/Proofs/Params_Critical.lean` | mainline |
| `t_rkhs_cap` | 40 | `Q3/Proofs/A3_bridge_rayleigh_first.lean` | auxiliary cap |
| `rho_one` | 1/25 | `Q3/Proofs/A3_bridge_rayleigh_first.lean` | auxiliary cap |
| `rho_oneK` | exp(8π² t_rkhs_cap K²)·rho_one | `Q3/Proofs/RKHS_cap_rayleigh.lean` | auxiliary cap |

## Legacy constants (two-scale branch)

These appear in the older spec docs and are **not** canonical now:
- `t_sym = 3/50`
- `t^{unif}_{*,rkhs} = 1`
- `C_SB = 4` (Szego-Bottcher barrier constant)
- `M_0^{unif}`

If you cite any of these, mark as legacy in the doc.

## Where to update

- Canonical chain: `ACTIVE/chain_status.md`
- Axiom list: `ACTIVE/orchestrator.md`
- Mainline specs: this file + `ACTIVE/Q3_BLOCK_MAP.md`
