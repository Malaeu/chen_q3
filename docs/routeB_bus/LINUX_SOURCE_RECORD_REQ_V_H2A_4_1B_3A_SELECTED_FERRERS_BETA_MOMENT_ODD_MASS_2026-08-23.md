# SOURCE RECORD — H2A.4.1B.3A selected Ferrers beta-moment odd-mass bound (Linux-тело за Codex)

```yaml
PRIMARY: H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict af4ca219 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: af4ca2194537f6104c696e6ac4642d928e5909ff
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок; fetch origin/rh_clean
  перед коммитом — новых [Proshka]-коммитов нет; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selected Ferrers beta moment odd mass\" +
  ./ask.sh \"ccmBetaFinite odd part Cauchy Schwarz\" — оба exited 0;
  beta-moment-объектов нет; ccmBetaFinite/_neg/_center и
  dotProduct_eq_zero_of_even (вещественная, с xiEven-гипотезой) найдены —
  комплексная selected-версия отсутствует; имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean
LEAN_GIT_BLOB: bb9156e9990210c4c8eb51d6c685b7e8dcd8d0ff
LEAN_SHA256: e6faf993d43c1d934200b91a0a5bfe428b5fb8a5cc4f778bb8f382928944abcf
LEAN_LINES: 394

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:   # ровно два, как в вердикте
  - Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
  - Q3.Proofs.RouteB.CCMFiniteWeilShiftedRankOne

PUBLIC_SURFACE:   # все 7 имён из вердикта, mandatory shapes соблюдены
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMBetaVector
    # j ↦ ((ccmBetaFinite i_k.m i_k.N j : ℝ) : ℂ) — точный source-β,
    # комплексный каст явный
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMBetaMoment
    # betaVector ⬝ᵥ selectedRow
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMBetaEnergy
    # Σ_j (ccmBetaFinite …)² — рост НЕ контролируется здесь (docstring)
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMModeWeightedRow
    # j ↦ ((ccmModeFinite i_k.N j : ℤ) : ℂ) · row_j — точный D·q
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMBetaMoment_eq_center_modeWeighted_sourceAction
    # C04/C10 SOURCE LOCK: β⬝q = (M·(D q))_center — из literal
    # β_j = n_j·M_{j,center}, точной симметрии ccmWeilMatFinite
    # (transpose_eq c hm/hN) и одной конечной суммы; касты сохранены
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMBetaMoment_eq_beta_dot_oddPart
    # ODDNESS LOCK: source-β отражённо-нечётен (ccmBetaFinite_neg) ⇒
    # аннулирует selected-чётную часть; β⬝q = β⬝oddPart — reindex
    # инволюцией, 2S = 0 в ℂ
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMBetaMoment_normSq_le_betaEnergy_mul_oddMass
    # normSq(β⬝q) ≤ betaEnergy · oddMass — norm_sum_le + конечный
    # вещественный Коши-Шварц (Finset.sum_mul_sq_le_sq_mul_sq) + sq_abs
    # + normSq_eq_norm_sq; oddPart-норма² = literal oddMass (def)

PRIVATE_DECLARATIONS:
  - allOnesMoment_does_not_determine_betaMoment_plant  # REQUIRED:
    # Fin 3, allOnes=(1,1,1), β=(−1,0,1), q1=(1,0,0), q2=(0,1,0):
    # оба allOnes-момента = 1, β-моменты −1 и 0 — подмена
    # ccmEtaFinite⬝q / unweighted-значения на β-момент убита
  - beta_oddness_is_load_bearing_plant                 # REQUIRED:
    # Fin 3, swap(0,2), q=(0,1,0) точно чётен (odd mass 0),
    # произвольный чётный β=(0,1,0) даёт β-момент 1 — oddMass-bound
    # верен ТОЛЬКО для source-β с его доказанной нечётностью
  - selected_m_ge_two / selected_N_ge_one  # расписание m=N=rank+2 через
    # ПУБЛИЧНЫЙ H2A.3-crosswalk (index_eq_preAnchorIndex) — приватный
    # tail-shift не инспектировался
  - selectedNegEquiv  # локальная инволюция-Equiv для reindex

EXPECTED_AXIOM_PROFILES: >-
  все 3 публичные теоремы и оба планта:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_BETA_MOMENT_SOURCE_CROSSWALK
    - SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND
  OPENS: []

PROOF_ROUTE_AS_MANDATED:   # 5 шагов вердикта, исполнены дословно
  - "оба ask.sh-преflight'а выполнены и записаны"
  - "rank восстановлен публичным H2A.3-crosswalk; m=N=rank+2 даёт
     hm: 2 ≤ m и hN: 1 ≤ N для source-теорем; приватный tail-shift не
     тронут (шаг 1)"
  - "center-action из literal β_j = n_j·M_{j,center}, точной симметрии
     матрицы и одной конечной суммы; комплексный каст сохранён явно
     (push_cast поверх явных ofReal/intCast) (шаг 2)"
  - "ccmBetaFinite_neg + reindex инволюцией ⇒ β аннулирует чётную часть;
     β-момент = паринг с literal selectedFerrersFiniteCCMOddPart (шаг 3)"
  - "конечный комплексный Коши-Шварц: norm_sum_le → вещественный CS
     (Finset.sum_mul_sq_le_sq_mul_sq) в точном евклидовом носителе;
     β-норма² переписана в betaEnergy (sq_abs), oddPart-норма² — в
     literal oddMass (шаг 4)"
  - "#print axioms всех 3 публичных теорем и обоих плантов (шаг 5)"

FORBIDDEN_CHECK:
  betaMoment_identified_with_ccmEtaFinite_dot_q: no (плант 1 держит)
  betaMoment_identified_with_Gwin0_Mellin_or_center_coefficient: no
    (center-action теорема — противоположный crosswalk: моД-ВЗВЕШЕННОЕ
    действие, не unweighted значение)
  betaMoment_smallness_claimed_from_oddMass_without_betaEnergy: no
    (docstring bound-теоремы явно отрицает)
  absolute_row_sums_or_ambient_operator_norm: no
  beta_energy_rate_hypothesis_added: no
  weighted_residual_source_rate_claimed: no
  selected_row_matrix_shift_tailShift_scale_schedule_changed: no
  H2A_4_1A_imported_to_rename_triangle_budget: no (импорта нет)
  numerics_paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 3 (transpose-rfl через conv_rhs + show; dotProduct-раскрытие
    show-defeq вместо Σ-паттерна; reindex переведён на Σ-базу с
    rfl-мостом к dotProduct; nth_rewrite 1 против двойной замены S в
    S = −S; linear_combination hneg для 2S = 0. Предсказанный
    COMPLEX_DOTPRODUCT_WITHLP_OR_SELECTED_TAIL_HN_NORMAL_FORM сбой
    выстрелил ЧАСТИЧНО — только dotProduct/Σ-нормальные формы; hN-шов
    прошёл через публичный crosswalk с первого раза; нулевая новая
    математика)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersBetaMomentOddMass — Build completed successfully (7925 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все 3 публичные + оба планта
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ (grep = 0)

SUCCESS_CODE: H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN
NEXT_LOAD_BEARING_GAP: H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_DEFECT_WEIGHTED_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
