# SOURCE RECORD — L73.4 explicit target support tail (Linux-тело за Codex)

```yaml
PRIMARY: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 405777bc — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 405777bc8e905655141b9abcc6994db2b8970872
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selectedFerrersExplicitTargetTail full EStar error
  moving threshold target tail\" exited 0 — кандидатов нет, имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
LEAN_GIT_BLOB: 69b1613b19dd76553cacd9112c38f8ea85c1aa7b
LEAN_SHA256: 751471675dbd8f72f5e4cdf1a257a8519c17e0773d89818276fbcf7cfdbf941e
LEAN_LINES: 508

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_4_EXPLICIT_TARGET_SUPPORT_TAIL_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrersExplicitTargetTail       # def, индекс M+n+1, фактор 4
  - Q3.RouteB.D0Pstar.selectedFerrersFullEStarError           # def
  - Q3.RouteB.D0Pstar.selectedFerrersFullEStarError_eq_main_sub_targetTail
  - Q3.RouteB.D0Pstar.selectedFerrersExplicitTargetTail_bound

PRIVATE_DECLARATIONS:
  - dynamicMainCount_does_not_cover_noncompact_target_plant  # REQUIRED
  - exp_linear_bound' / s4_exp_bound (s⁴e^{−s}≤256) / s3_exp_bound (s³e^{−s}≤27)
  - explicitCCMLimitH_inverse_four_decay   # ‖h(x)‖ ≤ 33/x⁴ для ВСЕХ x>0
    (подстановка s=πx² точная, без large-x ограничения; ‖h‖·x⁴π² ≤ 296.5 ≤ 297,
     π² > 9 ⇒ ≤ 33/x⁴; локальная передоказка — upstream inverse-square факт приватен)
  - target_comb_norm_bound  # ‖4h((M+n+1)u)‖ ≤ 132/(λ²u²)·1/(n+1)²  из (ru)⁴ ≥ λ²((n+1)u)²
  - inverse_square_summable

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrersFullEStarError_eq_main_sub_targetTail:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.D0Pstar.selectedFerrersExplicitTargetTail_bound:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - EXPLICIT_CCM_LIMIT_ESTAR_BEYOND_PROLATE_WINDOW_TAIL
    - SELECTED_FERRERS_FULL_ESTAR_POINTWISE_ERROR_DECOMPOSITION
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "хвост определён с индексом mainCount+n+1 и фактором 4 (пункт 2)"
  - "абсолютная суммируемость из локального inverse-four-распада (пункт 3)"
  - "точное источниковое усечение: r ≥ M+1 ⇒ ru > λ (Nat.lt_floor_add_one) ⇒
     h0/h4 вне носителя ⇒ prolateCombination = 0; E⋆(q) = конечная сумма через
     hasSum_sum_of_ne_finset_zero на (range M).map succPNat (пункт 4)"
  - "ℕ+→ℕ переиндексация через Equiv.pnatEquivNat.symm.tsum_eq; сплит
     Summable.sum_add_tsum_nat_add M; тождество full = main − tail собрано
     через generalize сумм в опаки + ring (пункт 5)"
  - "почленная оценка (ru)⁴ ≥ λ²·((n+1)u)² из ru>λ и r≥n+1 (пункт 6)"
  - "суммирование против Σ1/(n+1)² (Z как tsum, ненегативность tsum_nonneg;
     константа C = 132·Z, БЕЗ численного значения Z) (пункт 7)"
  - "λu ≥ 1 даёт C/(λ²u^{3/2}) ≤ C/(λ√u) (пункт 8)"
  - "#print axioms обеих публичных теорем (пункт 9)"

FORBIDDEN_CHECK:
  explicitCCMLimitH_treated_as_compactly_supported: no (в этом и содержание)
  full_error_claimed_equal_main: no (точный сплит с хвостом)
  factor_four_omitted_or_duplicated: no (ровно один, в хвосте как в определении)
  static_k_plus_2_target_cutoff: not_used (динамический M+n+1)
  target_tail_decay_as_hypothesis: not_added (доказан локально)
  full_error_split_as_hypothesis: not_added (доказан)
  numerical_constant_fitted: no (33 из 296.5/9; C = 132·Z символчески)
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 4 (плант через sum_range_succ; Complex.norm_exp через
    ofReal-предформу; ring_nf-расхождение атомов в финальной сборке — почин
    через generalize сумм в опаки перед ring; два лишних ring после
    закрывшего field_simp. Предсказанный TSUM_PNAT_NAT_REINDEX сбой
    частично выстрелил — согласование (i+M)+1 vs M+n+1 через omega-rw
    внутри tsum_congr)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail — Build completed successfully (7850 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: обе публичные теоремы
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL_LEAN
NEXT_LOAD_BEARING_GAP: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
