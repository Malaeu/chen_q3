# SOURCE RECORD — L73.3 selected Ferrers E-star window main error (Linux-тело за Codex)

```yaml
PRIMARY: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 19ee838c — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 19ee838c45f936a929f1989b2888ddc4e04b2fb4
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selectedFerrersEStarMainCount EStar window main error
  dynamic floor count\" exited 0 — ни одного кандидата, имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean
LEAN_GIT_BLOB: f13703ffa04009132e80eeeacde63d3a1f807bc8
LEAN_SHA256: 75aa19b608f674e74b98ceffd520c379376a5afe1d8398a6924967a4068ca914
LEAN_LINES: 186

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrersEStarMainCount           # def, floor(λ/u)
  - Q3.RouteB.D0Pstar.selectedFerrersEStarWindowMainError     # def, √u-взвешенная сумма
  - Q3.RouteB.D0Pstar.selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates

PRIVATE_DECLARATIONS:
  - eStarMainSum_cardinalityFactor_plant  # REQUIRED: ‖Σ_{range 4} 1‖ = 4 ∧ ¬(≤1)

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "F72.6 вызван, получены C ≥ 0 и eventual точечный packet-rate (пункт 2)"
  - "k из eventual-события, u ∈ sourceWindow = Icc λ⁻¹ λ; 0 < λ и 0 < u
     (из λ⁻¹ ≤ u) (пункты 3-4)"
  - "Nat.floor_le даёт (M:ℝ) ≤ λ/u (пункт 4)"
  - "для n < M: (n+1) ≤ M ≤ λ/u ⇒ (n+1)·u ≤ λ (div_mul_cancel₀), низ из
     позитивности — точка в Icc(−λ,λ) (пункт 5)"
  - "F72.6-rate почленно (пункт 6)"
  - "norm_sum_le + Finset.sum_const + card_range + floor-граница; точное
     тождество через s := √u, s² = u (Real.sq_sqrt), s·(λ/s²)·(C/λ²) =
     C/(λ·s) — field_simp; НЕТ подгонки (пункт 7)"
  - "бесконечный target-хвост НЕ разворачивался и НЕ оценивался (пункт 8)"

FORBIDDEN_CHECK:
  static_range_k_plus_2_summation: not_used (динамический floor(λ/u) —
    статический диапазон переоценил бы на фактор порядка λ у верхнего края)
  full_EStar_difference_claimed: not_claimed (докстринг явно оставляет
    target-хвост в L73.4)
  Mellin_integration_performed: none (L73.5)
  free_EStar_main_error_premise_accepted: not_present (rate только из F72.6)
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 2 (единственный сбой — ring после закрывшего цель field_simp,
    «No goals»; предсказанный NAT_FLOOR_CAST_OR_FINSET_RANGE сбой не
    выстрелил)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersEStarWindowMainError — Build completed successfully (7849 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR_LEAN
NEXT_LOAD_BEARING_GAP: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
