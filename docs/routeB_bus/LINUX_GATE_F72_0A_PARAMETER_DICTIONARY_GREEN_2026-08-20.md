# LINUX GATE — F72.0A параметрический словарь: GREEN

```yaml
DATE: 2026-08-20
FLOOR: F72_0A_SELECTED_FERRERS_PROJECT_PARAMETER_DICTIONARY
DIRECTIVE: PROSHKA_VERDICT_REQ_2026_08_20_G_F72_0_SELECTED_FERRERS_PAPER_OBJECT_DICTIONARY_2026-08-20.md
WRITTEN_BY: Linux-тело за Codex (владелец поручил в чате; Codex ещё не поднят)
FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean
GIT_BLOB: 10e9e9729dd320dc5793aa013fabc0a73eba7c61
SHA256: 6dae5ff2ea966f34928c6510952254d38569d24ac277021a0bb58851a49eb489
LINES: 148

ROUNDS:
  R1: сборка зависимости (D0Mode4FerrersDimensionlessFourierScaling не был собран)
  R2: 0 ошибок содержательного прогона

CHECKS:
  lake_env_lean: EXIT 0
  lake_build: "Build completed successfully (7835 jobs)" EXIT 0
  q3_check: "q3_check ok" EXIT 0
  axiom_profiles: 9 деклараций [propext, Classical.choice, Quot.sound];
    selectedFerrersPaperDegree — вообще без аксиом (чистое определение)
  sorryAx: НЕТ

DIRECTIVE_ITEMS_DELIVERED:
  1_degree: selectedFerrersPaperDegree j = 2*j
  2_lambda: selectedFerrersPaperLambda k = sqrt (k+2)
  3_gamma: selectedFerrersPaperGamma k = 2*pi*lambda^2
  4_gamma_value: selectedFerrersPaperGamma_eq — 2*pi*(k+2)
  5_gamma_sq: selectedFerrersPaperGamma_sq_eq_jacobiG — = mode4JacobiG (k+2)
  6_degree_values: degree 0 = 0, degree 2 = 4 (оба @[simp])
  7_pair_lock: lambda пары = paperLambda; h0/h4 = точные selected Ferrers моды;
    chi0, chi2 ненулевые — всё переэкспортировано из pair_spec

BONUS_NOT_REQUESTED:
  selectedFerrersPaperGamma_eq_slepianC: gamma = mode4SlepianC (k+2)
  зачем: mode4SlepianC (2*pi*mProject) УЖЕ лежал на полке; без этой связки
    словарь завёл бы второй параметр ширины полосы рядом с существующим.
    W9-гигиена: связываем, а не плодим.
  selectedFerrersPaperLambda_eq_lambda_m: окно расписания = D0-окно индекса

FORBIDDEN_RESPECTED:
  no_ps_n_defined: true
  no_project_mode_eq_scalar_mul_ps: true
  no_satz9_or_fuchs_hypothesis: true
  no_factor_four: true
  ccm_lemma_73_port_untouched: true
  f72_1_and_f72_3_not_started: true
  no_sorry_admit_axiom_native_decide: true

SUCCESS_CODE: F72_0A_SELECTED_FERRERS_PROJECT_PARAMETER_DICTIONARY_LEAN

WHAT_THIS_DOES_NOT_MEAN: стена L73.2 не сдвинулась. F72.0B (литеральная привязка
  к ps_n) остаётся открытой, F72.1 (Satz 9) — главная стена, источника нет.
  Это параметрический замок, а не аналитика.

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```
