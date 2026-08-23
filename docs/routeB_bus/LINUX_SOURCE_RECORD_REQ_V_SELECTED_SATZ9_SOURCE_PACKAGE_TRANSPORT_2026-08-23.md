# SOURCE RECORD — selected Satz-9 source package transport (Linux-тело за Codex)

```yaml
PRIMARY: SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict de86b9bc — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: f91455e70fc008505b7e6fbd776b609dd5fef2f3

COMMIT: SAME_COMMIT_AS_THIS_RECORD

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedSatz9SourcePackageTransport.lean
LEAN_GIT_BLOB: 18ebe540a40e9316f5ed8ebbeb40eafdb70a8bc0
LEAN_SHA256: 4fb9a1356b05a8dd54712e8acaaf1cb01039f4b66538f56e16e1babfb73c97ba
LEAN_LINES: 89

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

SCHEMA_REPAIR_APPLIED_PER_PRIOR_VERDICT:
  base_head_now_actual_parent: true
  field_name_now_EXPECTED_AXIOM_PROFILES_plural: true

PUBLIC_SURFACE:
  - Q3.RouteB.selectedSatz9SourceData_at_projectTheta_degree_zero_four

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.selectedSatz9SourceData_at_projectTheta_degree_zero_four:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - W13_7E_SELECTED_THETA_PACKAGE_TRANSPORT
    - SELECTED_SOURCE_PHYSICAL_DATA_AT_PROJECT_THETA
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "0 < selectedFerrersPaperLambda k: Real.sqrt_pos.mpr + positivity on (k+2:ℝ)"
  - "exact parameter identity: selectedFerrersPaperGamma_sq_eq_jacobiG unfolded
     through selectedFerrersPaperGamma, giving
     (2*pi*selectedFerrersPaperLambda(k)^2)^2 = mode4JacobiG(k+2) literally"
  - "finiteLimit_selected_theta_equality_degree_zero_four_modular (k+2)
     (5*(k+2)) (by omega) (by omega) (selectedFerrersPreAnchorSeparation k) P
     — the exact V3.2 rank-two bind, K = 5*(k+2) matching the
     precommitted separation supplier"
  - "P.evenBranch_regular 0 and P.evenBranch_regular 2 — source-regular
     eigenvalues, no project function involved yet"
  - "regularEvenSpheroidalEigenvalue_physicalSatz9SourceData applied twice"
  - "rewrite source eigenvalues to project carrier values via the V3.2
     equality and rewrite the common +G shift"

DEVIATION_FROM_DIRECTIVE_PROOF_ROUTE:
  - "Direct `rw [← hGeq] at hreg` on P.evenBranch_regular's result fails:
     `mode4JacobiG (k+2)` also occurs inside P's own type (P :
     BookRegularEvenSpectrumEven (mode4JacobiG (k+2))), so abstracting it
     for the rewrite motive breaks P.evenBranch's dependent typing
     (\"motive is not type correct\"). Repaired by `generalize ... at hreg0`
     first, replacing `P.evenBranch j` by a fresh opaque real `Lj` in hreg0
     BEFORE rewriting the parameter, then reassembling the goal via a plain
     ℝ equality `mode4ClassicalEvenEigenvalue ... j = Lj` (V3.2 equality
     composed with the generalize equation). No mathematical content
     changed; the fix is purely about avoiding a dependent-motive rewrite."

FORBIDDEN_CHECK:
  P_or_evenBranch_defined_from_mode4ClassicalEvenEigenvalue: not_present
  selected_project_Ferrers_mode_used_as_Satz9SourceData_p: not_used
  source_spectrum_package_chosen_inside_theorem: not_chosen (P is a
    universally quantified argument)
  same_theta_inferred_from_same_G_without_V3_2: not_present
    (finiteLimit_selected_theta_equality_degree_zero_four_modular consumed
    explicitly for both ranks)
  common_plus_mode4JacobiG_shift_dropped: not_dropped
  project_ordinal_2_identified_with_source_full_degree_2: not_present
    (only ordinal equality via V3.2, no degree field anywhere)
  source_degree_identified_with_split_degree: not_present
  Satz9_rate_hypothesis_or_paper_axiom_added: not_added
  ProjectModeData_or_F72_1A_or_F72_1C_bundled: not_bundled
  V3_2_or_admitted_physical_lift_source_edited: none_edited
  sorry_or_admit_or_typed_hole: none
  theorem_weakening: none (TARGET_SHAPE дословно)

GATE:
  ROUNDS: 3 (dependent-motive rewrite repaired via generalize; then a
    docstring substring "admitted" tripped the q3_check hole scanner —
    same class of trap as commit 4961b0a0/a4ceb33a — reworded to "ratified")
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedSatz9SourcePackageTransport.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedSatz9SourcePackageTransport — Build completed successfully (7856 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedSatz9SourcePackageTransport.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT_LEAN
NEXT_LOAD_BEARING_GAP: F72_1A_CENTER_NORMALIZED_SATZ9_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
