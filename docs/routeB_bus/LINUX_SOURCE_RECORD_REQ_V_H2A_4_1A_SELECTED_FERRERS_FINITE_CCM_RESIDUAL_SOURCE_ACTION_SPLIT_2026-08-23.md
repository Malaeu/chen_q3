# SOURCE RECORD — H2A.4.1A selected Ferrers finite Riesz source-action split (Linux-тело за Codex)

```yaml
PRIMARY: H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict e0c47c3b — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: e0c47c3bfc06a7251d4f34c5126377ec36f8ecfd
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок; fetch origin/rh_clean
  перед коммитом — новых [Proshka]-коммитов нет; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selected Ferrers factor four target Hilbert vector
  projection source action split Riesz budget\" exited 0 — split-объектов
  нет нигде; P_m_N (H_m →L E_m_N, orthogonalProjection) существует;
  имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
LEAN_GIT_BLOB: 9db9c3bee39dd8f958c3df25762c9733054d0276
LEAN_SHA256: 2f85ea8890f83aa397dd193d9b0c8e6e527c9c25af3f2df7a666540715b0983e
LEAN_LINES: 811

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1A_SELECTED_FERRERS_FINITE_CCM_RESIDUAL_SOURCE_ACTION_SPLIT_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance
  - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail

PUBLIC_SURFACE:   # все 7 имён из вердикта
  - Q3.RouteB.D0Pstar.selectedFerrersFactorFourTargetVector
    # G_k := MemLp.toLp (E_star (4·explicitCCMLimitH)) — в H_m(i_k)
  - Q3.RouteB.D0Pstar.selectedFerrersScaledPhysicalErrorVector
    # e_k := s_k • gTrial_k − G_k — в H_m(i_k)
  - Q3.RouteB.D0Pstar.selectedFerrersFactorFourTargetProjection   # gE_k = P_m_N G_k
  - Q3.RouteB.D0Pstar.selectedFerrersScaledPhysicalErrorProjection # eE_k = P_m_N e_k
  - Q3.RouteB.D0Pstar.selectedFerrers_sourceScale_smul_kTrial_eq_normalizer_smul_error_add_target
    # EXACT_VECTOR_IDENTITY: s_k • x_k = t_k • (eE_k + gE_k) —
    # линейность проекции + sub_add_cancel + smul_comm; kTrial = t•P(gL) defeq
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteRieszDefect_sourceScale_split
    # EXACT_ACTION_IDENTITY: s_k•(R x_k − a_k x_k) =
    #   t_k•((R eE_k − a_k eE_k) + (R gE_k − a_k gE_k)) —
    # линейность R (map_smul/map_add) + smul-алгебра + abel; НИЧЕГО не оценено
  - Q3.RouteB.D0Pstar.norm_sourceScale_mul_selectedFerrersFiniteRieszDefect_le_action_budget
    # EXACT_NORM_BUDGET: ‖s_k‖·‖R x_k − a_k x_k‖ ≤ t_k·(‖A_k-term‖ + ‖T_k-term‖) —
    # norm_smul + norm_add_le + t_k ≥ 0; RATE_CONTENT: none

PRIVATE_DECLARATIONS:
  - vanishing_Hilbert_error_without_uniform_Riesz_action_does_not_control_residual_plant
    # REQUIRED (Lean-версия ABSTRACT_FALSIFIER): Fin 2, K n = diag(0, n+2),
    # y = e₀ (точный нуль-собственный), q n = (√(1−c²), c), c = (n+2)⁻¹:
    # unit ∀n, Hilbert-error → 0 (мажоранта 3c², squeeze), residual
    # energy = 1−c² ≥ 3/4 ∀n — L²-tracking без uniform action bound
    # residual НЕ контролирует
  - exact_target_match_without_target_action_theorem_does_not_control_residual_plant
    # REQUIRED: Fin 3, K = [[0,1,0],[1,0,1],[0,1,0]], q = y = (0,1,0):
    # error ТОЧНО 0, residual energy = 2 — идеальное совпадение с целью
    # без action-теоремы цели ничего не даёт
  - memLp_G и его стек (isFiniteMeasure_dStar_Im, continuousOn_G_Im,
    E_star_norm_bound, decay chain, continuity trio, E_star_four_mul_eq,
    lambda_m_gen_*, Im_subset_Ioi) — ЛИТЕРАЛЬНЫЕ копии приватного
    блока H2A.3 (upstream приватен, H2A.3 редактировать запрещено;
    предсказание P_H2A41A_2 судьи об этом трении подтверждено)

EXPECTED_AXIOM_PROFILES: >-
  все 3 публичные теоремы и оба планта:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_FACTOR_FOUR_TARGET_HILBERT_OBJECT_LOCK
    - SELECTED_FERRERS_SCALED_PHYSICAL_ERROR_PROJECTION_LOCK
    - SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_EXACT_SPLIT
    - SELECTED_FERRERS_RESIDUAL_SOURCE_ACTION_BUDGET
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен и записан"
  - "цель и ошибка экспонированы как window-Hilbert векторы; обе
     спроецированы в ОДИН selected E_m_N той же P_m_N"
  - "vector identity: P(e + G) = P(s•gL) ⇒ s•x = t•(eE+gE) — чистая
     линейность, kTrial дефеквивалентно t•P(gL)"
  - "action identity: применение R и a-сдвига к vector identity;
     ни один член не оценён"
  - "norm budget: norm_smul + norm_add_le; t_k ≥ 0 из определения
     нормализатора; НИКАКОГО rate"
  - "оба планта доказаны; никакой decay нигде не заявлен"
  - "#print axioms всех 3 публичных теорем и обоих плантов"

FORBIDDEN_CHECK:
  Riesz_action_decay_from_Hm_or_L2_error: no (плант 1 держит)
  target_defect_zero_from_inversion_evenness: no (плант 2 держит)
  target_defect_zero_from_L73_convergence: no
  ambient_A_m_action_substituted: no
  compression_claimed: no (docstring отрицает)
  abstract_source_action_rate_hypothesis_receiver: no (никаких новых гипотез)
  row_sums_or_operator_norm_as_rate: no
  rayleigh_shift_replaced: no
  selected_shell_or_row_replaced: no
  H2A_0_through_H2A_4_0_or_L73_edited: no
  sector_floors_ground_Theorem510_real_zeros_bundled: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 4 (все три публичные теоремы и плант 2 GREEN с ПЕРВОГО прогона;
    ремонты только в планте 1: sqrt_le_one вместо rw-глобальной замены
    единицы; nlinarith-хинты произведений для b-оценок; ℂ-каст
    mul_inv_cancel₀ через exact_mod_cast. Предсказанный
    FACTOR_FOUR_TARGET_MEMLP_PUBLIC_OBJECT-сбой закрыт локальной копией
    H2A.3-блока — ровно как предсказано P_H2A41A_2)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit — Build completed successfully (7927 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все 3 публичные + 2 планта
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ (grep = 0)

SUCCESS_CODE: H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN
NEXT_LOAD_BEARING_GAP: H2A_4_1B_SELECTED_FERRERS_ERROR_AND_TARGET_FINITE_FORM_ACTION_DECAY
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
