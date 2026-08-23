# SOURCE RECORD — H2A.4.1B.3C.0 selected Ferrers center-coefficient inverse-log floor (Linux-тело за Codex)

```yaml
PRIMARY: H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 580e0a00 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 580e0a003ae269100cd46561b3469d85b4ab0548
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок; fetch origin/rh_clean
  перед коммитом — новых [Proshka]-коммитов нет; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selected Ferrers center coefficient log floor\" +
  ./ask.sh \"scaled projection norm target global L2\" — оба exited 0;
  floor-машинерии нет; глобальной L²-оценки цели нет; имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean
LEAN_GIT_BLOB: a237de2ae6457423ab25ff016a649494cd944e66
LEAN_SHA256: dc98d27049f366eab9898c8c78baa8c1a3ce3591f220cf4400a937657db41e18
LEAN_LINES: 1500

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_FLOOR_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:   # ровно один, как в вердикте
  - Q3.Proofs.RouteB.G6N1SelectedFerrersCommutatorResidualDefect

PUBLIC_SURFACE:   # все три имени из вердикта
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCM_log_mul_centerCoeff_normSq_eq_anchor_div_scaledProjectionNormSq
    # TARGET SHAPE 1, ТОЧНОЕ ТОЖДЕСТВО: L_k·|q₀|² =
    # normSq(s_k·Gwin_k(0)) / ‖s_k • (gTrial_m_N … : H_m)‖² — через
    # q₀ = sT·⟨V₀,gL⟩ (локальная c_n-копия + zero-mode) и
    # Gwin(0) = √L·⟨V₀,gL⟩; sourceScale ВНУТРИ scaled-вектора,
    # никакого fitted-нормализатора
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates
    # TARGET SHAPE 2: hmode/hχ verbatim, let P := конструктор;
    # ∃ cCenter > 0, ∀ᶠ k, cCenter ≤ L_k·normSq(q₀); cCenter =
    # (‖Ξ₀‖²/4)/(1+√Mt)² — ВЫВЕДЕН: числитель eventually ≥ ‖Ξ₀‖²/4
    # (муntz z=0 + centeredXi_zero_ne_zero), знаменатель eventually
    # ≤ (1+√Mt)² (‖e_k‖ ≤ 1 из L73-цепи + contractivity P_m_N +
    # ГЛОБАЛЬНАЯ ‖G‖² ≤ Mt := 2(132Z₄)²/7); поточечное ≠ 0 как rate
    # НЕ использовано
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_logWeightedCommutatorEnergy_of_modeAndChiRates
    # TARGET SHAPE 3, denominator-free receiver: те же hmode/hχ;
    # из Tendsto (L_k·η_k·‖Γ_k‖²) → 0 следует √η·√E_res → 0 —
    # через inverse-log floor → R_k → 0 (squeeze) → существующий
    # 3B-receiver; R_k → 0 отдельно НЕ предполагается

PRIVATE_DECLARATIONS:
  - pointwise_center_nonzero_without_log_floor_plant  # REQUIRED:
    # unit-ряды ((n+2)⁻¹, √(1−(n+2)⁻²)): q₀ ≠ 0 ∀n, но
    # L_n·|q₀|² = (n+2)⁻¹ → 0 — «q₀ ≠ 0 → floor» мёртв
  - anchor_without_scaled_projection_upper_bound_does_not_force_center_floor_plant
    # REQUIRED: anchor ≡ 1 при denom = (n+1)² → ∞: identity-ratio → 0 —
    # глобальный cap на scaled projection несущий
  - target_norm_sq_le_global  # НОВАЯ АНАЛИТИКА: ‖toLp G‖² ≤ 2(132Z₄)²/7
    # на КАЖДОМ окне — двусторонний распад u^{∓7/2}
    # (E_star_norm_bound + E_star_explicitCCMLimitH_inv), сплит окна в 1
    # (Icc ∪ Ioc, setIntegral_union), мажоранты C²u⁶ (integral_pow) и
    # C²u⁻⁸ (integral_rpow); λ⁵-оценка НЕ использована
  - lp_norm_sq_eq_integral / local_err_norm_sq_le  # ‖·‖²-как-интеграл;
    # оконная ошибка ‖s·gL − G‖² ≤ Cf²/λ (локальные копии паттернов)
  - norm_P_m_N_apply_le  # contractivity проекции (letI-инстансы + Submodule.norm_orthogonalProjection_apply_le)
  - inner_V_P_eq' / c_n_eq_sT_inner' / zero_mem_modeSet' / local_L_pos /
    local_oddMass_nonneg'  # локальные копии приватных хелперов
  - blockA/blockC/blockB2  # литеральные копии приватного E⋆-стека H2A.3
    # (decay chain, continuity trio, λ-леммы, window_l2_integral_le,
    # isFiniteMeasure, memLp_G)

EXPECTED_AXIOM_PROFILES: >-
  все 3 публичные теоремы и оба планта:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_CENTER_COEFFICIENT_ANCHOR_IDENTITY
    - SELECTED_FERRERS_CENTER_COEFFICIENT_INVERSE_LOG_FLOOR
    - SELECTED_FERRERS_RATIO_DENOMINATOR_REMOVAL
    - SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_TO_WEIGHTED_RESIDUAL_RECEIVER
  OPENS:
    - SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE

PROOF_ROUTE_AS_MANDATED:
  - "оба ask.sh-преflight'а выполнены"
  - "identity: q₀ через sT·⟨V₀,gL⟩ (проекция сохраняет нулевую моду),
     Gwin(0)-identity, field_simp при s ≠ 0, ‖gN‖ ≠ 0"
  - "числитель floor'а: муntz-предел на shell при z=0 + Ξ₀ ≠ 0 ⇒
     eventually ‖s·Gwin(0)‖ ≥ ‖Ξ₀‖/2"
  - "знаменатель: ‖s·P g‖ = ‖P(s·g)‖ ≤ ‖s·g‖ ≤ ‖e‖+‖G‖ ≤ 1+√Mt
     eventually (L73-полная ошибка + λ-рост из mCofinal + глобальный
     target-cap)"
  - "receiver: floor ⇒ R ≤ (LηG)/cCenter ⇒ squeeze ⇒ 3B-receiver;
     никакой новой гипотезы"
  - "#print axioms всех трёх теорем и обоих плантов"

FORBIDDEN_CHECK:
  uniform_constant_lower_bound_on_q0: no (только L·|q₀|²-масштаб)
  pointwise_nonzero_as_rate: no (плант 1 держит)
  fitted_sourceScale_bound: no (масштаб внутри вектора)
  lambda5_target_norm_as_final_floor: no (глобальный 2(132Z₄)²/7;
    плант 2 держит несущесть cap'а)
  betaEnergy_rate: no
  GammaEnergy_decay_claimed: no (receiver условный)
  row_sums_ambient_opNorm: no
  target_error_termwise_split_replacing_Gamma: no (Γ не фигурирует
    иначе как через 3B-receiver)
  sector_floors_ground_Theorem510_RH: no
  H2A_3_or_3B_edited: no
  sorry_admit_hole_paper_axiom_numerics_weakening: none

GATE:
  ROUNDS: 5 (тип-выведение ∀-биндера в планте; Pi.inv_apply; полное имя
    Submodule.norm_orthogonalProjection_apply_le; beta-нередуцированные
    show-формы в setIntegral_congr_fun; sqrt-square ring-нормализация;
    integral_pow root-имя; div_le_div_iff₀; одношаговый calc съел
    следующую строку — заменён exact. Предсказанный
    TARGET_GLOBAL_L2_MEMLP_OR_PROJECTED_NORM_NORMAL_FORM сбой выстрелил
    ЧАСТИЧНО — только нормальные формы; сама глобальная L²-оценка и
    identity прошли по плану; нулевая новая математика в ремонтах)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersCenterCoefficientFloor — Build completed successfully (7929 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все 3 публичные + оба планта
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ (grep = 0)

SUCCESS_CODE: H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN
NEXT_LOAD_BEARING_GAP: H2A_4_1B_3C_1_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
