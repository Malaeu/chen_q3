# SOURCE RECORD — H2A.2 selected Ferrers H2a source-quantities lock (Linux-тело за Codex)

```yaml
PRIMARY: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 7a090cd0 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 7a090cd04727eeedcd53251f6457073420f21291
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selected Ferrers complex reflection Rayleigh residual
  odd mass physical reflection defect\" exited 0 — образец-машинерия найдена
  ТОЛЬКО на интерфейсе ProlateCanonicalSourceData
  (D0PstarSourceCCMOddMassReflectionDefect); ccmNegFinite/centrosymmetry
  существуют; selected-версий нет, имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
LEAN_GIT_BLOB: 2ef1c66a6489f54f8722459f0755f3105f852123
LEAN_SHA256: 2b0a049ca073cbf36812f01c39c0dc2466690eebe6fd824f6bd7a8b7ae61727b
LEAN_LINES: 616

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow
  - Q3.Proofs.RouteB.CCMComplexTrialReflectionContaminationFloor

PUBLIC_SURFACE:   # все 14 имён из вердикта
  - Q3.RouteB.D0Pstar.ccmComplexReflectionMatrix           # def, δ_{k,neg j}
  - Q3.RouteB.D0Pstar.ccmComplexReflectionMatrix_mulVec    # (R*ᵥx) j = x (neg j)
  - Q3.RouteB.D0Pstar.ccmComplexReflectionMatrix_isHermitian
  - Q3.RouteB.D0Pstar.ccmComplexReflectionMatrix_sq        # R*R = 1
  - Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix
    # из точной центросимметрии ccmWeilTauN1_neg_neg; hN-гипотеза upstream
    # фиктивна — локальная передоказка центросимметрии БЕЗ hN, теорема
    # сильнее вердиктного минимума
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMRayleigh     # re(q*·M·q)
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidual     # M·q − Ray•q
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMOddPart      # (q_j − q_{neg j})/2
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMOddMass      # Σ normSq oddPart
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMReflectionDefect
    # kTrial-синтез − синтез отражённой строки, тот же PairIndex
  - Q3.RouteB.D0Pstar.ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial
    # ПУБЛИЧНАЯ передоказка (H2A.0-хелпер приватен; интерфейсная
    # подстановка не использована)
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMOddMass_eq_quarter_norm_reflectionDefect_sq
    # РЕШАЮЩЕЕ ТОЖДЕСТВО: oddMass = (1/4)·‖defect‖², через ортонормальный
    # конечный синтез (V_n_m_orthonormal ∘ инжективность ccmModeFinite)
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMResidual_orthogonal
    # q* ⬝ residual = 0 из selected-unit-теоремы + эрмитовой вещественности
    # Рэлея; сдвиг НЕ выбирался
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMComplementFloor_of_sectorFloors_oddMass_residual
    # литеральный receiver H2A.1 на selected-объектах; открыты ровно
    # четыре количественных входа: even-floor, odd-floor, η<1 + ρ-bound,
    # betaEff>0

PRIVATE_DECLARATIONS:
  - unit_norm_does_not_determine_reflection_mass_plant  # REQUIRED:
    # Fin 3, swap 0↔2; unit-ряды [2/3,1/3,2/3] (масса 0) и [1,0,0]
    # (масса 1/2) — как в вердикте дословно
  - wrong_shift_breaks_residual_orthogonality_plant     # REQUIRED:
    # diag(0,1) на Fin 2, q = e0: точный Рэлей ⇒ residual ⊥ q;
    # сдвиг c = 1 ⇒ q*⬝residual = −1 ≠ 0
  - ccmNegFinite_invol / ccmNegFinite_eq_comm
  - selectedModeEquiv' / selected_finite_sum_reindex'   # carrier-reindex
  - norm_selected_synthesis_sq   # ‖synthesis c‖² = Σ normSq c
  - hermitian_quadratic_real     # q*·A·q вещественно для эрмитовой A

EXPECTED_AXIOM_PROFILES: >-
  все 8 публичных теорем и оба планта:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_COMPLEX_REFLECTION_OBJECT_LOCK
    - SELECTED_FERRERS_RAYLEIGH_RESIDUAL_OBJECT_LOCK
    - SELECTED_FERRERS_ODD_MASS_OBJECT_LOCK
    - SELECTED_FERRERS_ODD_MASS_PHYSICAL_REFLECTION_DEFECT_REPRESENTATION
    - SELECTED_FERRERS_H2A1_LITERAL_SOURCE_RECEIVER
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "отражение определено на литеральном CCM-носителе (пункт 2)"
  - "действие/эрмитовость/квадрат из ccmNegFinite-инволюции; старая
     вещественная строка НЕ импортирована и НЕ коэрцирована (пункт 3)"
  - "коммутация из существующей точной центросимметрии
     (ccmWeilTauN1_neg_neg + ccmModeFinite_neg) (пункт 4)"
  - "Рэлей/резидуал от точной selected-строки; ортогональность из
     unit-теоремы + эрмитовой вещественности, НЕ выбором сдвига (пункт 5)"
  - "синтез = kTrial передоказан ПУБЛИЧНО (пункт 6)"
  - "oddMass = (1/4)‖defect‖² через ортонормальный синтез (пункт 7)"
  - "H2A.1 инстанцирован литерально; остаются только настоящие
     количественные входы (пункт 8)"
  - "#print axioms всех публичных теорем и обоих плантов (пункт 9)"

STOP_CONDITION_CHECK:
  physical_defect_identity_on_same_selected_row_and_PairIndex: PROVED
  ProlateCanonicalSourceData_substitution_needed: no
  stop_triggered: no

FORBIDDEN_CHECK:
  ProlateCanonicalSourceData_substituted: no
  old_sourceCCMComplexRow_reused_as_defeq: no (selected-строка своя)
  selected_row_coerced_to_real: no
  parity_inferred_from_unit_norm_or_evenness: no (плант 1 держит)
  row_replaced_by_even_projection: no
  fixed_or_fitted_shift: no (точный Рэлей; плант 2 держит)
  reflection_or_carrier_identity_hidden_behind_simp: no (действие —
    отдельная публичная теорема)
  sector_floor_rate_or_residual_rate_as_structure_field: no (гипотезы
    теоремы-receiver-а)
  cofinal_floor_simple_ground_Theorem510_real_zeros_bundled: no
  H2A_0_H2A_1_L73_edited: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 3 (rw-show-синтаксис развёрнут в have-функцию; направление
    exact_mod_cast; приватность preAnchorTailIndex обойдена локальной
    передоказкой центросимметрии без фиктивного hN. Предсказанный
    DEPENDENT_SELECTED_INDEX_OR_COMPLEX_REFLECTION_MATRIX_NORMAL_FORM
    сбой выстрелил ЧАСТИЧНО — только направление каста и приватный
    индекс; P_H2A2_1/2/3 все подтверждаются)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities — Build completed successfully (7921 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все 8 публичных + 2 планта
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN
NEXT_LOAD_BEARING_GAP: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
