# Checklist Audit 2026-01-17 (RH_Q3 dependency chain)

Scope: verify the RH_Q3 dependency map (T0 -> A1' -> A2 -> RKHS transfer -> A3 -> Q>=0 -> RH)
against the current TeX sources, project specs, and Lean files.

Legend:
- Paper: TeX label and file
- Specs: internal specs pointer
- Lean: relevant file/lemma
- Status: OK / TODO (axiom/sorry/timeout)
Guard script: `full/q3.lean.aristotle/scripts/check_audit_invariants.sh`

## 0. Dependency map
- Paper: `full/sections/Weil_pack.tex` (Remark `rem:weil-dependency`),
  `full/sections/introduction.tex` (table "Dependency map for the analytic chain")
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Sections 0-6)
- Lean: `Q3/Main.lean` (high-level chain overview)
- Status: OK

## 1. T0 normalization (Guinand-Weil crosswalk)
- Paper: `full/sections/T0.tex` (Prop `prop:T0-GW`, Lemma `t0:lem:T0`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Section 1)
- Lean:
  - `Q3/Main.lean:T0_normalization` (definitional `Q = arch_term - prime_term`)
  - `Q3/Archive/01_T0_aristotle.lean` (full crosswalk proof)
- Status: OK (formal crosswalk lives in archive; main uses definitional Q)

## 2. A1' density (Fejer x heat cone dense on W_K)
- Paper: `full/sections/A1prime.tex` (Theorem `a1:thm:A1-local-density`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Section 3)
- Lean:
  - `Q3/Proofs/A1_Density_Bridge.lean` (uses `Q3.Axioms`)
  - `Q3/Clean/TheoremsTier2.lean:Q3.Clean.Theorems.A1_density`
- Status: TODO (axiom-backed)

## 3. A2 Lipschitz continuity
- Paper: `full/sections/A2.tex` (Lemma `a2:lem:A2`, Cor `a2:cor:explicit-lip`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Section 3)
- Lean:
  - `Q3/Proofs/Q_Lipschitz_Bridge.lean` (clean bridge, no sorry)
  - `Q3/Proofs/Q_Lipschitz.lean` (axiom-backed)
- Status: DONE (clean bridge proven; axioms remain in main proof file)

## 4. RKHS transfer and prime cap
- Paper:
  - `full/sections/RKHS/weil_isometry.tex` (Lemma `lem:rkhs-weil-isometry`)
  - `full/sections/RKHS/core.tex` (Lemma `lem:rkhs-rayleigh-sampling-id`)
  - `full/sections/RKHS/prime_cap.tex` (Cor `cor:uniform-prime-cap`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Sections 3, 5)
- Lean:
  - `Q3/Proofs/Off_Diag_Exp_Sum_Bridge.lean` (now closes via root proof)
  - `Q3/Proofs/RKHS_Contraction_Bridge.lean` (clean bridge, no sorry)
  - `Q3/Proofs/RKHS_cap_rayleigh.lean` (rayleigh-style cap)
- Status: DONE (contraction bridge proven)

## 5. Period-1 normalization / Rayleigh identification
- Paper:
  - `full/sections/A3/calibration.tex` (normalization audit)
  - `full/sections/A3/rayleigh_bridge.tex` (Theorem `thm:a3-rayleigh-identification`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Rayleigh bridge notes)
- Lean:
  - `Q3/Proofs/Rayleigh_Q_identification.lean` (scaled form fixed)
  - `integral_P_A_eq_arch_term` proven (periodization closed)
- Status: DONE (Rayleigh identification complete; wiring to atoms pending)

## 6. A3 uniform bridge / floor
- Paper: `full/sections/A3/main.tex` (Theorem `thm:A3`),
  `full/sections/A3/symbol_floor.tex` (Lemma `lem:uniform-arch-floor`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Sections 3, 5)
- Lean:
  - `A3_Floor_Main.lean` (arch floor proof)
  - `Q3/Proofs/A3_Bridge_Simple.lean` (clean bridge; uses Tier-1 axioms)
- Status: TODO (bridge is heuristic / Tier-1 axioms)

## 7. Weil closure / RH
- Paper: `full/sections/Main_closure.tex` (Theorem `thm:Main-positivity`),
  `full/sections/Weil_pack.tex` (Theorem `thm:weil-sufficiency-pack`),
  `full/sections/Weil_linkage.tex` (Weil criterion)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Section 6)
- Lean:
  - `Q3/Main.lean` (assembly uses axioms / Tier-2 bridges)
- Status: TODO (depends on A1', A2, RKHS, A3)

## 8. Normalization mismatch check (2M+1 scaling)
- Paper: `full/sections/A3/rayleigh_bridge.tex` (discussion of scaling by `2M+1`)
- Specs: `full/q3.lean.aristotle/docs/PROJECT_SPECS.md` (Rayleigh bridge section)
- Lean: `Q3/Proofs/Rayleigh_Q_identification.lean` (rescaled form)
- Status: OK

## Open issues captured for follow-up
- (none from Rayleigh identification; wiring into atoms remains in main tracker)

## 9. Addendum: normalization and chain guardrails (Jan 17 checklist)
- Weights (w_Q vs w_RKHS):
  - Paper: `full/sections/introduction.tex`, `full/sections/scope_notation.tex`
  - Lean: `Q3/Basic/Defs.lean` (Q uses w_Q), RKHS proofs use undoubled weights
  - Status: OK (paper/Lean consistent)
- Prime-vector scaling (2M+1) only on the prime block:
  - Paper: `full/sections/A3/rayleigh_bridge.tex` (Theorem `thm:a3-rayleigh-identification`)
  - Lean: `Q3/Proofs/Rayleigh_Q_identification.lean` (scaled form fixed)
  - Status: OK
- Sampling span condition (M >= B for general p):
  - Paper: `full/sections/RKHS/core.tex` (Remark "Finite support and the threshold M")
  - Lean: no standalone lemma for general p yet (p = 1 case does not need it)
  - Status: TODO (only if general sampling lemma is introduced)
- Two-scale separation (t_sym vs t_rkhs):
  - Paper: `full/sections/scope_notation.tex`, `full/sections/A3/main.tex`
  - Lean: uses distinct parameters in A3/RKHS bridges
  - Status: OK
- Legacy constants / scale-error data kept out of mainline:
  - Paper: `full/sections/A3/param_tables.tex` (legacy notes), Appendix legacy sections
  - Status: OK (legacy confined to appendix)
- Discretization/Szego-Bottcher guard:
  - Paper: `full/sections/A3/matrix_guard.tex`, `full/sections/A3/main.tex`
  - Lean: A3 bridge uses floor + discretization in the axiomatic wrapper
  - Status: OK (paper), TODO (Lean bridge is axiomatic)
