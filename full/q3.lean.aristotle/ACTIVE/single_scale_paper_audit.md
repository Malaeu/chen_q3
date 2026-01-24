# Single-scale paper audit (2026-01-24)

Goal: verify whether the *paper* matches the single-scale mainline
(t_critical = 3/20, tau = 0) and map the 3 remaining SingleScale axioms
onto exact LaTeX locations.

## Summary (fast read)

- The paper chain **is stated as complete**, and the main paper files have now
  been **aligned to single-scale** (t_critical = 3/20, tau = 0).
- The three SingleScale axioms now have paper analogs that **use t_critical**
  (paper3_* files updated). Legacy two-scale mentions were removed there.
- Action: keep an eye on other legacy drafts; if they still mention two-scale,
  mark as legacy or update in a follow-up sweep.

## Axiom-to-paper map (single-scale mismatch audit)

### 1) SingleScale.continuous_P_A_shift

- Lean axiom: `SingleScale.continuous_P_A_shift`
- Paper analog:
  - `full/sections/A2.tex` (Lipschitz / continuity of Q on compact windows)
- Status:
  - Continuity is **proved on paper**; single-scale is now referenced in the
    mainline papers. (A2 itself is t-agnostic.)
- Follow-up:
  - If any local draft still binds A2 to legacy t_sym, mark as legacy.

### 2) SingleScale.rayleigh_basis0_shift_ge_cstar_quarter

- Lean axiom: `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
- Paper analog:
  - `full/sections/A3/main.tex` (A3 Toeplitz bridge)
  - `full/sections/Main_closure.tex` (main positivity closure)
  - NOTE: legacy numeric comment exists in `full/sections/A3/symbol_floor.tex`
    with `t_sym = 3/50`.
- Status:
  - Updated in `paper3_weil_rh/main*.tex` and `paper3_rh_synthesis/main*.tex`
    to use **t_critical = 3/20**.
- Follow-up:
  - Check any remaining legacy paper fragments for `t_sym` or two-scale wording.

### 3) SingleScale.rho_oneK_tcritical_le_cstar_quarter

- Lean axiom: `SingleScale.rho_oneK_tcritical_le_cstar_quarter`
- Paper analog:
  - `full/sections/RKHS/prime_cap.tex`
  - `full/sections/RKHS/main.tex`
- Status:
  - Updated in `paper3_weil_rh/main*.tex` and `paper3_rh_synthesis/main*.tex`
    to use **t_critical = 3/20** and `rho(t_critical) ≤ c_*/4`.

## Mainline paper chain anchor

- Core closure statement:
  - `full/sections/Main_closure.tex` (Theorem "Main positivity on W")
- This is the right place to ensure the single-scale parameterization is
  consistent with the three SingleScale axioms.

## Action items (paper sync)

1) Update A2 section to explicitly fix t = t_critical for the Fejer x heat
   generators used in the mainline chain.
2) Update A3 section: remove or annotate t_sym=3/50; restate the bridge at
   t = t_critical.
3) Update RKHS cap section to bind the cap to t_critical.
4) Re-scan for any remaining two-scale wording and mark as legacy.
