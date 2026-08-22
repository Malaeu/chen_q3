# SOURCE RECORD — V3.2 finite-limit / source selected-theta modular bind (Linux-тело за Codex)

```yaml
PRIMARY: FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND
DATE: 2026-08-22
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 8fd8ab3f — CODEX DIRECTIVE V3.2
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 8fd8ab3f215ae9d16f8e4dc51e08feba4f18c908

COMMIT: SAME_COMMIT_AS_THIS_RECORD

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FiniteLimitSelectedThetaModularBind.lean
LEAN_GIT_BLOB: 86321e54639ae41e423bf737d3cdab56d90e0561
LEAN_SHA256: f16b146869a0c2ce36534a6996ecfb402e5b7b1885d32b7540001d7f87f19f21
LEAN_LINES: 104

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_V3_2_FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND_2026-08-22.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.finiteLimit_source_evenBranch_agree_through_rank_two
  - Q3.RouteB.finiteLimit_selected_theta_equality_degree_zero_four_modular

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.finiteLimit_source_evenBranch_agree_through_rank_two:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.finiteLimit_selected_theta_equality_degree_zero_four_modular:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - PROJECT_BRANCH_INHABITANT
    - SOURCE_RANK_TWO_CUTOFF
    - W13_7_SELECTED_THETA_EQUALITY_DEGREE_ZERO_FOUR
  OPENS: []

ASSEMBLY_AS_MANDATED:
  hG: "0 < mode4JacobiG mProject, unfold + positivity"
  hsetOf: "range P.evenBranch ∩ Iio 20 = {Λ | Λ<20 ∧ ∃r, P.evenBranch r = Λ}, ext + simp [and_comm]"
  hrange: "rw [hsetOf, V3.0 (mode4FiniteLimitCharacteristicRangeEquality), U2.4 (mode4ModularCharacteristicRangeEquality)]"
  haLocal: "mode4ClassicalEvenEigenvalue_lt_of_index_lt_of_upper_lt_twenty (supplier, unproved here)"
  haCut: "mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three (supplier, unproved here)"
  final: "eq_of_cutoffLocalStrictMono_of_low_range_eq P.evenBranch_strictMono haLocal hrange haCut"
  theorem_2: "projects theorem 1 at j=0 and j=2 via (hall 0 _).1, (hall 2 _).1"

DEVIATION_FROM_DIRECTIVE_PROOF_ROUTE:
  - "used mode4JacobiG mProject inline throughout instead of a `set`/`let` G
     abbreviation — an initial `set G := ... with hGdef` version produced a
     spurious type-mismatch (P shown as P✝ in the error) against the literal
     goal statement (which is stated in mode4JacobiG mProject, not folded);
     switching to fully inline mode4JacobiG mProject removed the mismatch.
     No lemma content changed, only local naming style."

FORBIDDEN_CHECK:
  projectBranch_defined_as_P_evenBranch: not_present
  P_instantiated_with_Classical_choose: not_present
  imported_G6N1SelectedThetaEqualityDegreeZeroFourModular: not_imported
  used_selected_theta_equality_degree_zero_four_modular: not_used
  global_StrictMono_of_mode4ClassicalEvenEigenvalue_assumed: not_assumed
  separate_source_cutoff_hypothesis_added: not_added
  numeric_hsrcCut_probe_used: not_used
  source_degree_identified_with_split_degree: not_present
  edited_V3_0_V3_1_U2_3_U2_4_U2_5: none_edited
  mixed_source_project_structure_created: none
  paper_axiom_or_typed_hole: none
  sorry_or_admit: none
  theorem_weakening: none (TARGET_SHAPE_1/2 дословно)

GATE:
  ROUNDS: 2 (первая версия: спуриозный P✝-мисматч из-за `set`; вторая версия
    компилируется с первого содержательного прогона доказательства)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1FiniteLimitSelectedThetaModularBind.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1FiniteLimitSelectedThetaModularBind — Build completed successfully (7808 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1FiniteLimitSelectedThetaModularBind.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: обе декларации [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: V3_2_FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND_LEAN
NEXT_LOAD_BEARING_GAP: SATZ9_FIRST_KIND_SOURCE_DATA_PHYSICAL_LIFT
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
