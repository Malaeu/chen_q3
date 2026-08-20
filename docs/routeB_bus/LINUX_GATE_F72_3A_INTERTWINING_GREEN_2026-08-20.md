# LINUX GATE — F72.3A сплетение операторов: GREEN

```yaml
DATE: 2026-08-20
FLOOR: F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING
NAMED_BY: судья, вердикт REQ-2026-08-20-H («следующий локальный замок»)
WRITTEN_BY: Linux-тело (Codex ещё не поднят; владелец поручил перенимать его задачи)
FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FuchsProjectOperatorIntertwining.lean
GIT_BLOB: 59610d91c2db6dce29f68d622ed3cdabcd8dd9c9
SHA256: 285c03917894bd1ff2d18858dc4335c332af71dac7a1bd5489a547f5063304ea
LINES: 133

PROVED:
  statement: >-
    paperFiniteFourierAction (paperWindowRadius lambda) (paperRescale h) t
      = sqrt (2*pi) * paperRescale (finiteFourierAction lambda h) t
  hypotheses: 0 <= lambda — и всё. Никаких аналитических посылок.
  content: одна линейная замена переменной s = sqrt(2*pi)*y, работающая
    потому что 2*pi / sqrt(2*pi) = sqrt(2*pi)

NEW_OBJECTS:
  paperWindowRadius lambda = sqrt (2*pi) * lambda      # это Fuchs-овское a
  paperRescale h s = (2*pi)^(-1/4) * h (s / sqrt(2*pi))  # унитарная перенормировка U
  paperFiniteFourierAction a f t = ∫ s in Icc (-a) a, exp (I*s*t) * f s  # Fuchs-овский F_a
  почему это не новые входы: все три — определения в НАШИХ терминах, каждое
    раскрывается до уже существующих объектов; ни одно не постулирует свойство

ROUNDS:
  R1: 2 ошибки (nlinarith не связал r^2 с r*r; ring без цели)
  R2: 1 ошибка (real_smul уже закрыл цель, хвост лишний)
  R3: 0 ошибок

CHECKS:
  lake_env_lean: EXIT 0
  lake_build: "Build completed successfully (7836 jobs)" EXIT 0
  q3_check: "q3_check ok" EXIT 0
  axiom_profiles: 5 деклараций [propext, Classical.choice, Quot.sound]
  sorryAx: НЕТ

W9_LEDGER:
  CLOSES: [F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING]
  OPENS: []

NOT_DONE_DELIBERATELY:
  eigenvalue_map: Lambda_0 = chi0^2, Lambda_4 = chi2^2 — ВТОРАЯ половина замка
    судьи, здесь НЕ доказана. Это следующий шаг, и он про собственные числа,
    а не про операторы.
  ps_n_not_defined: true
  satz9_and_fuchs_theorem1_not_assumed: true
  ccm_lemma_73_port_untouched: true

WHY_THIS_MATTERS: kill REQ-2026-08-20-E умер ровно на таком несовпадении —
  множитель 1/4 у Меллина. Здесь пересчёт ДОКАЗАН, а не предположен, поэтому
  ни один потребитель ниже не сможет его тихо проглотить.

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```
