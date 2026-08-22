# SOURCE RECORD — V3.1 cutoff-local ordered enumeration lock (Linux-тело за Codex)

```yaml
PRIMARY: CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK
DATE: 2026-08-22
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 0ca5991a — CODEX DIRECTIVE V3.1
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 0ca5991ac8e466672e6599ba8d6fbdbb0575459e

COMMIT: SAME_COMMIT_AS_THIS_RECORD

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CutoffLocalOrderedEnumerationLock.lean
LEAN_GIT_BLOB: 9a8df2373b5a4ec6b65fb7adcb5975cd3236dd12
LEAN_SHA256: b84f47811c1a1af489009e8babfc72758870658b335ad808a3d2336c2aaac1ef
LEAN_LINES: 122

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_V3_1_CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK_2026-08-22.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE  # содержимое не может нести собственный хеш;
  # значение печатает `git ls-tree <COMMIT> -- <SOURCE_RECORD_PATH>` и продублировано
  # в сообщении к судье

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.eq_of_cutoffLocalStrictMono_of_low_range_eq

PLANT:
  name: RANK_SWAP_WITH_EQUAL_LOW_RANGE
  lean_name: Q3.RouteB.D0Pstar.cutoffLocal_rank_swap_plant
  data: "b n = n; a = b ∘ σ, σ меняет ранги 0 и 1; C = 2; R = 1"
  demonstrates: haLocal необходим — низкие range и cutoff-данные совпадают,
    почленное равенство падает на ранге 0

EXPECTED_AXIOM_PROFILES:
  eq_of_cutoffLocalStrictMono_of_low_range_eq:
    - propext
    - Classical.choice
    - Quot.sound
  cutoffLocal_rank_swap_plant:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - GLOBAL_PROJECT_STRICTMONO_OVERSTRENGTH
    - HSRC_CUT_AS_SEPARATE_INPUT
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - strong induction (Nat.strong_induction_on)
  - lower-rank equality from IH
  - a(j) через hrange в b(m); m < j исключён через haLocal + IH
  - b(j) ≤ a(j) < C из StrictMono b (source cutoff — ВЫХОД, не вход)
  - b(j) через hrange в a(n); n < j исключён через StrictMono b + IH
  - a(j) ≤ a(n) = b(j) через haLocal при a(n) < C
  - антисимметрия

FORBIDDEN_CHECK:
  global_StrictMono_a: not_used
  separate_source_cutoff_hypothesis: not_present
  numeric_hsrcCut: not_used
  DLMF_spheroidal_finite_limit_imports: none (единственный импорт — G6N1OrderedEnumerationLock)
  edited_locked_files: none
  V3_2_bundled: false
  sorry_or_typed_hole: none
  theorem_weakening: none (TARGET_SHAPE дословно, Unicode ∧/≤ за ASCII and/<=)

GATE:
  ROUNDS: 2 (plant: interval_cases отсутствует + недожатый norm_num → 0 ошибок)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1CutoffLocalOrderedEnumerationLock.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1CutoffLocalOrderedEnumerationLock — Build completed successfully (749 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1CutoffLocalOrderedEnumerationLock.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: обе декларации [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: V3_1_CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK_LEAN
NEXT_LOAD_BEARING_GAP: FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
