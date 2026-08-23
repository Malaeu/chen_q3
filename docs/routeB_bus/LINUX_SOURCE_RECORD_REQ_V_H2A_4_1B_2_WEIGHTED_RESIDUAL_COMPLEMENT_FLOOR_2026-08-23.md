# SOURCE RECORD — H2A.4.1B.2 weighted residual to eventual complement floor (Linux-тело за Codex)

```yaml
PRIMARY: H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict b3e0e6ea — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: b3e0e6ea2d19a398df184f81d0de7917e54718b4
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок; fetch origin/rh_clean
  перед коммитом — новых [Proshka]-коммитов нет; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"weighted residual complement floor\" exited 0 —
  такой теоремы нет ни под каким именем; каталог показывает только
  Temple-цепь (rayleigh_excess) и Goal058-развилку 2026-08-13 (residual
  заменён на parity-weighted energy — эта веха подтверждает выбранное
  направление); имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean
LEAN_GIT_BLOB: 3840090d77d04b4881e539a86a3924e310df31a0
LEAN_SHA256: c761d2b83b30a929c36bae7fb8757f3314e1088bac420a6e5c98a5f5589d72c5
LEAN_LINES: 357

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_2_WEIGHTED_RESIDUAL_COMPLEMENT_FLOOR_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:   # ровно один, как в вердикте
  - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance

PUBLIC_SURFACE:   # ровно одна теорема, judge-verbatim shape
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
    # (P)(β0)(hβ0: 0<β0)(hη: η_k → 0)(hweighted: √η_k·√E_k → 0)
    # (heven/hodd: eventual секторные floors с β0 в literal H2A.1-форме) ⊢
    # ∀ᶠ k, complexTrialComplementFloor M_k q_k a_k (β0/2)
    # — ФИКСИРОВАННАЯ константа β0/2, не Tendsto и не переменная положительность

PRIVATE_DECLARATIONS:
  - weighted_residual_is_load_bearing_plant   # REQUIRED:
    # η_n = (n+2)⁻², ρ_n = (n+2)²: η → 0, √η·ρ = n+2 НЕ → 0,
    # и betaEff-выражение с floor 1 отрицательно ∀n —
    # odd-mass decay сам по себе floor не держит
  - residual_decay_is_not_necessary_plant     # REQUIRED:
    # η_n = 0, ρ_n = n (неограничен): betaEff = 1 ТОЧНО ∀n —
    # распад residual'а никогда не был консюмером
  - selected_oddMass_nonneg / dot_star_self_re_nonneg  # локальная рутина

EXPECTED_AXIOM_PROFILES: >-
  публичная теорема и оба планта:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR
    - RESIDUAL_DECAY_NOT_REQUIRED_FOR_H2A_EFFECTIVE_FLOOR
  OPENS: []

PROOF_ROUTE_AS_MANDATED:   # 9 шагов вердикта, исполнены дословно
  - "ask.sh преflight выполнен; существующего поставщика нет (шаг 1)"
  - "eventual-множества hη/hweighted/heven/hodd пересечены filter_upwards
     (шаг 2)"
  - "из hη eventually η < 1; неотрицательность η — локальная сумма
     normSq (шаг 3)"
  - "ρ_k := √(residualEnergy); E = ρ² из sq_sqrt + energy_nonneg
     (H2A.4.0, публичная) (шаг 4)"
  - "контаминация переписана как ((2+√η)/√(1−η))·(√η·ρ) точным
     тождеством 2√η+η = (2+√η)·√η (mul_self_sqrt) (шаг 5)"
  - "коэффициент → 2 (Tendsto-алгебра: sqrt/sub/div), контаминация → 0
     по hweighted; полный effective floor F_k → β0 (шаг 6)"
  - "eventually β0/2 ≤ F_k из eventually_const_le (half_lt_self)
     (шаг 7)"
  - "receiver H2A.1 применён с βp = βm = β0 (min_self), ρ = ρ_k,
     betaEff = F_k (дефинициональное равенство) (шаг 8)"
  - "downgrade F_k → β0/2 раскрытием complexTrialComplementFloor:
     β0/2·(неотр.) ≤ F_k·(неотр.) ≤ форма; никакой новой спектральной
     теоремы (шаг 9)"
  - "#print axioms теоремы и обоих плантов"

FORBIDDEN_CHECK:
  rho_to_zero_assumed: no (плант 2 держит; нигде не входит)
  weighted_control_replaced_by_oddMass_alone: no (плант 1 держит)
  ccmEtaFinite_called_odd_mass: no (ccmEtaFinite в файле не фигурирует;
    firewall вердикта соблюдён)
  source_action_split_imported: no (ровно один импорт — Variance)
  weighted_residual_source_rate_claimed: no (docstring явно оставляет
    H2A_4_1B_3 открытым)
  selected_row_schedule_scale_shift_changed: no
  sector_floor_suppliers_ground_Theorem510_real_zeros_bundled: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 2 (все ремонты — знакомая нормальная форма: sqrt_le_one вместо
    глобального rw единицы; star-vs-starRingEnd каст; явная типизация
    tendsto_const_nhds; set-лямбда через show вместо rw [hF].
    Предсказанный FILTER_EVENTUAL_SQRT_EFFECTIVE_FLOOR_NORMAL_FORM сбой
    выстрелил ЧАСТИЧНО — только эти нормальные формы, нулевая новая
    математика; сама Filter/sqrt-цепь прошла с первого раза)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersWeightedResidualComplementFloor — Build completed successfully (7927 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: публичная теорема + оба планта
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ (grep = 0)

SUCCESS_CODE: H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN
NEXT_LOAD_BEARING_GAP: H2A_4_1B_3_SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
