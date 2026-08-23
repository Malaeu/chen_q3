# SOURCE RECORD — H2A.4.0 selected Ferrers finite CCM residual variance lock (Linux-тело за Codex)

```yaml
PRIMARY: H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict bba4c35e — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: bba4c35eaee0b91f345d354116460f8c7c166bbf
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок; fetch origin/rh_clean
  перед коммитом — новых [Proshka]-коммитов нет; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selected Ferrers finite CCM residual variance second
  moment Riesz defect crosswalk\" exited 0 — variance/Riesz-замка нет нигде;
  Temple-неравенства (rayleigh_excess_le_residual_sq_div_gap_sub) ЖДУТ
  именно такой скаляр; sourceCCMFiniteRieszOperator/ccmFiniteSynthesisEquiv
  существуют, их apply-леммы приватны; имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean
LEAN_GIT_BLOB: 90003d95866658ae9cb7c103324951665bcff6fc
LEAN_SHA256: 052fdda44d2be65e9e7f76e6a9651d5903dac5dd3ed9485a108562422df35597
LEAN_LINES: 537

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_0_SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
  - Q3.Proofs.RouteB.D0PstarCCMFiniteRieszOperator

PUBLIC_SURFACE:   # все 7 имён из вердикта
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidualEnergy
    # def: (star r ⬝ᵥ r).re — один source-faithful скаляр
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMSecondMoment
    # def: (star (K·q) ⬝ᵥ (K·q)).re
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidualEnergy_nonneg
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidualEnergy_eq_norm_sq
    # = ‖WithLp.toLp 2 r‖² (EuclideanSpace)
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidualEnergy_eq_secondMoment_sub_rayleigh_sq
    # VARIANCE IDENTITY: ρ² = M₂ − a²; через unit-норму, эрмитову
    # вещественность Рэлея и ортогональность residual — сдвиг НЕ менялся
  - Q3.RouteB.D0Pstar.ccmFiniteSynthesis_selectedFerrersFiniteCCMResidual_eq_finiteRieszDefect
    # RIESZ CROSSWALK: synthesis(residual) = coe(Riesz(xE) − a•xE),
    # xE = тот же selected kTrial; равенство в H_m
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidualEnergy_eq_finiteRieszDefect_norm_sq
    # ρ² = ‖Riesz(xE) − a•xE‖² в E_m_N — литеральный объект для H2A.4.1

PRIVATE_DECLARATIONS:
  - exact_even_unit_row_can_have_nonzero_rayleigh_residual_plant  # REQUIRED:
    # Fin 3, J = swap(0,2), K = [[0,1,0],[1,0,1],[0,1,0]], q = (0,1,0):
    # K,J эрмитовы, J² = 1, KJ = JK, q unit и ТОЧНО J-чётен (odd mass 0),
    # Rayleigh = 0, residual = (1,0,1), residual energy = 2 —
    # oddMass = 0 ⇏ residual = 0, вывод H2A.4 из H2A.3 убит
  - dot_star_self_re / dot_conj_swap          # dot-алгебра
  - hermitian_quadratic_real'                 # локальная копия (upstream приватна)
  - norm_selected_synthesis_sq'               # локальная копия через
    # ccmModeFinite_injective (публичную)
  - localModeEquivalence / localModeOrthonormalBasis /
    coe_localModeOrthonormalBasis_apply       # ЛИТЕРАЛЬНЫЕ копии приватного
    # Riesz-стека upstream
  - ccmFiniteSynthesisEquiv_eq_localBasis     # rfl-МОСТ (kernel-defeq сквозь
    # приватное имя; maxHeartbeats 40M) — интерфейс НЕ подменён
  - localSynthesisEquiv_apply_toLp            # передоказанная generic
    # application-лемма (mandated re-proof)
  - localOperatorEuclidean / localOperatorEuclidean_apply_toLp
  - sourceCCMFiniteRieszOperator_eq_localConj # rfl-МОСТ conj-разложения
  - riesz_conj_apply / riesz_apply_selected   # действие Riesz на selected
    # kTrial через synthesisEquiv-транспорт selected-строки
  - synthesisEquiv_selectedRow_eq_kTrial      # synthEquiv(toLp row) = kTrial

EXPECTED_AXIOM_PROFILES: >-
  все 5 публичных теорем и плант:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_FINITE_CCM_RESIDUAL_ENERGY_OBJECT_LOCK
    - SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_IDENTITY
    - SELECTED_FERRERS_FINITE_RIESZ_RESIDUAL_CROSSWALK
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен и записан (пункт 1)"
  - "P, shell, PairIndex, row, matrix, Rayleigh — дефеквивалентно H2A.2;
     ни один объект не переопределён (пункт 2)"
  - "residual energy = евклидова норма² из точного комплексного dot;
     строка НЕ переведена в вещественную (пункт 3)"
  - "r = Kq − aq раскрыт ПОСЛЕ unit-нормы, эрмитовой вещественности Рэлея
     и residual-ортогональности; ровно ‖r‖² = ‖Kq‖² − a² (пункт 4)"
  - "selected-строка транспортирована через ccmFiniteSynthesisEquiv;
     передоказана только приватная generic application-лемма — двумя
     rfl-мостами и литеральными локальными копиями, БЕЗ
     ProlateCanonicalSourceData (пункт 5)"
  - "ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial отождествил
     selected synthesis с тем же selected kTrial; результат — равенство
     в H_m после коэрции точного E_m_N Riesz-дефекта (пункт 6)"
  - "Riesz-норма из изометрии (Submodule.norm_coe + ортонормальный
     синтез), НЕ из ambient-оператора (пункт 7)"
  - "#print axioms всех публичных теорем и планта (пункт 8)"

FORBIDDEN_CHECK:
  residual_decay_inferred_from_odd_mass: no (плант держит)
  residual_decay_inferred_from_hmode_hchi: no (никакого rate вообще)
  selectedNormalizedGalerkinResidual_used: no
  projection_minus_full_gTrial_substituted: no
  ProlateCanonicalSourceData_as_selected_shell: no (rfl-мосты к публичным
    именам, не к S-интерфейсу)
  ambient_associated_Weil_operator_A_m_defined_or_invoked: no
  compression_claim: no (docstring явно отрицает)
  rayleigh_shift_replaced_or_fitted: no
  operator_norm_or_row_sum_as_source_residual_rate: no
  residual_or_second_moment_rate_assumed: no
  sector_floor_claims: no
  H2A_4_1_H2A_5_simple_ground_Theorem510_bundled: no
  H2A_0_through_H2A_3_or_L73_edited: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 5 (скобочный баланс двойной коэрции E_m_N→H_m; планты Fin 3
    требовали cons_val_two/tail_cons; rfl-мост базисов прошёл ТОЛЬКО с
    maxHeartbeats 40M — kernel-defeq сквозь приватную конструкцию
    OrthonormalBasis.span/map/reindex; LinearEquiv.conj_apply_apply
    оказался symm-формой (x в целевом пространстве) — закрыт
    show-конверсией + LinearIsometryEquiv.symm_apply_apply; хвостовые
    ring/rfl после закрывающих field_simp/rw убраны. Предсказанный
    DEPENDENT_E_M_N_SUBTYPE_COERCION_OR_COMPLEX_INNER_NORMAL_FORM сбой
    выстрелил ТОЧНО — subtype-коэрция и комплексная normal form;
    нулевая новая математика)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance — Build completed successfully (7926 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все 5 публичных + плант
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ (grep = 0)

SUCCESS_CODE: H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN
NEXT_LOAD_BEARING_GAP: H2A_4_1_SELECTED_FERRERS_RESIDUAL_VARIANCE_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
